import pandas as pd
import sqlparse
import re
import ast
import json
from typing import Dict, List, Tuple, Optional, Set
from flask import Flask, request, jsonify, render_template_string, send_file
import os
from datetime import datetime
from collections import defaultdict, OrderedDict
import io

class SASAnalyzer:
    def __init__(self):
        self.sas_patterns = {
            'libname': r'libname\s+(\w+)\s+[\'"]?([^\'";]+)[\'"]?\s*;',
            'data_step': r'data\s+([^;]+);(.*?)run\s*;',
            'proc_sql': r'proc\s+sql[^;]*(?:;\s*title[^;]*;)?(.*?)quit\s*;',
            'proc_print': r'proc\s+print[^;]*(?:;\s*title[^;]*;)?(.*?)run\s*;',
            'proc_means': r'proc\s+means[^;]*(?:;\s*title[^;]*;)?(.*?)run\s*;',
            'proc_summary': r'proc\s+summary[^;]*(?:;\s*title[^;]*;)?(.*?)run\s*;',
            'proc_sort': r'proc\s+sort[^;]*(?:;\s*title[^;]*;)?(.*?)run\s*;',
            'proc_freq': r'proc\s+freq[^;]*(?:;\s*title[^;]*;)?(.*?)run\s*;',
            'proc_contents': r'proc\s+contents[^;]*(?:;\s*title[^;]*;)?(.*?)run\s*;',
            'where_clause': r'where\s+([^;]+);',
            'keep_drop': r'(keep|drop)\s*=\s*([^;]+);',
            'merge_join': r'merge\s+([^;]+);',
            'set_statement': r'set\s+([^;]+);',
            'by_statement': r'by\s+([^;]+);',
            'if_statement': r'if\s+([^;]+)\s*;',
            'var_statement': r'var\s+([^;]+);',
            'class_statement': r'class\s+([^;]+);',
            'output_statement': r'output\s+out\s*=\s*(\w+)\s+([^;]+);',
            'tables_statement': r'tables\s+([^;]+);',
            'weight_statement': r'weight\s+([^;]+);',
            'input_statement': r'input\s+([^;]+);',
            'datalines_statement': r'datalines\s*;(.*?)(?:\s*;\s*|\s*run\s*;)',
            'macro_definition': r'%macro\s+(\w+)[^;]*(.*?)%mend\s+\1;',
        }
        
        self.sas_functions = {
            'put': 'CAST', 'input': 'CAST', 'substr': 'SUBSTRING', 'strip': 'TRIM',
            'compress': 'REPLACE', 'intck': 'DATEDIFF', 'intnx': 'DATEADD',
            'today': 'CURRENT_DATE', 'year': 'YEAR', 'month': 'MONTH', 'day': 'DAY',
            'sum': 'SUM', 'mean': 'AVG', 'min': 'MIN', 'max': 'MAX', 'count': 'COUNT',
            'n': 'COUNT', 'nmiss': 'COUNT_CASE_WHEN_NULL', 'std': 'STDDEV', 'var': 'VARIANCE'
        }
    
    def parse_sas_code(self, sas_code: str) -> Dict:
        try:
            sas_code = self._remove_comments(sas_code)
            sas_code = self._clean_sas_code(sas_code)
            
            components = {
                'data_steps': [], 'procedures': [], 'variables': set(), 'filters': [],
                'tables': set(), 'functions_used': set(), 'table_dependencies': {},
                'table_usage': defaultdict(list), 'datalines_tables': {}, 
                'libraries': {}, 'macros': {}
            }
            
            libname_matches = re.findall(self.sas_patterns['libname'], sas_code, re.IGNORECASE)
            for libname, path in libname_matches:
                components['libraries'][libname] = path
            
            macro_matches = re.findall(self.sas_patterns['macro_definition'], sas_code, re.DOTALL | re.IGNORECASE)
            for macro_name, macro_content in macro_matches:
                components['macros'][macro_name] = macro_content.strip()
            
            data_steps = re.findall(self.sas_patterns['data_step'], sas_code, re.DOTALL | re.IGNORECASE)
            for table_name, step_content in data_steps:
                table_name = table_name.strip()
                datalines_data = self._extract_datalines(step_content)
                if datalines_data:
                    components['datalines_tables'][table_name] = datalines_data
                    source_tables = []
                else:
                    source_tables = self._extract_source_tables(step_content)
                
                step_info = {
                    'table_name': table_name, 'content': step_content, 'source_tables': source_tables,
                    'operations': self._extract_operations(step_content), 'step_type': 'DATA_STEP',
                    'has_datalines': bool(datalines_data)
                }
                components['data_steps'].append(step_info)
                components['tables'].add(table_name)
                components['table_dependencies'][table_name] = source_tables
                
                for source_table in source_tables:
                    components['table_usage'][source_table].append({
                        'type': 'DATA_STEP', 'target': table_name, 'content': step_content
                    })
                
                variables = self._extract_variables(step_content)
                components['variables'].update(variables)
                functions = self._extract_functions(step_content)
                components['functions_used'].update(functions)
            
            self._extract_procedures(sas_code, components)
            components['variables'] = list(components['variables'])
            components['tables'] = list(components['tables'])
            components['functions_used'] = list(components['functions_used'])
            
            return components
            
        except Exception as e:
            print(f"Error in parse_sas_code: {str(e)}")
            return {'data_steps': [], 'procedures': [], 'variables': [], 'filters': [],
                    'tables': [], 'functions_used': [], 'table_dependencies': {},
                    'table_usage': defaultdict(list), 'datalines_tables': {},
                    'libraries': {}, 'macros': {}}
    
    def _extract_datalines(self, content: str) -> Optional[List[Dict]]:
        try:
            datalines_match = re.search(self.sas_patterns['datalines_statement'], content, re.DOTALL | re.IGNORECASE)
            if not datalines_match:
                return None
            datalines_content = datalines_match.group(1).strip()
            input_match = re.search(r'input\s+([^;]+);', content, re.IGNORECASE)
            if not input_match:
                return None
            input_vars = [var.strip().rstrip('$') for var in input_match.group(1).split()]
            rows = []
            for line in datalines_content.split('\n'):
                line = line.strip()
                if line and not line.startswith(';'):
                    values = line.split()
                    if len(values) >= len(input_vars):
                        row = {}
                        for i, var in enumerate(input_vars):
                            if i < len(values):
                                row[var] = values[i]
                        rows.append(row)
            return rows
        except:
            return None
    
    def _remove_comments(self, sas_code: str) -> str:
        sas_code = re.sub(r'/\*.*?\*/', '', sas_code, flags=re.DOTALL)
        sas_code = re.sub(r'^\s*\*.*$', '', sas_code, flags=re.MULTILINE)
        return sas_code
    
    def _clean_sas_code(self, sas_code: str) -> str:
        sas_code = re.sub(r'[ \t]+', ' ', sas_code)
        sas_code = re.sub(r'\s*;\s*', ';\n', sas_code)
        return sas_code
    
    def _extract_source_tables(self, content: str) -> List[str]:
        tables = []
        set_matches = re.findall(r'set\s+([^;]+);', content, re.IGNORECASE)
        for match in set_matches:
            tables.extend([tbl.strip() for tbl in match.split()])
        merge_matches = re.findall(r'merge\s+([^;]+);', content, re.IGNORECASE)
        for match in merge_matches:
            tables.extend([tbl.strip() for tbl in match.split()])
        return tables
    
    def _extract_operations(self, content: str) -> Dict:
        operations = {
            'where': [], 'keep': [], 'drop': [], 'if': [], 'by': [], 'var': [], 'class': [],
            'rename': [], 'length': [], 'format': [], 'informat': [], 'input': [],
            'merge': [], 'set': [], 'calculated_fields': []
        }
        try:
            where_matches = re.findall(r'where\s+([^;]+);', content, re.IGNORECASE)
            operations['where'] = [w.strip().rstrip(';') for w in where_matches]
            
            keep_matches = re.findall(r'keep\s*=\s*([^;]+);', content, re.IGNORECASE)
            if keep_matches:
                operations['keep'] = [col.strip() for col in keep_matches[0].split()]
            
            drop_matches = re.findall(r'drop\s*=\s*([^;]+);', content, re.IGNORECASE)
            if drop_matches:
                operations['drop'] = [col.strip() for col in drop_matches[0].split()]
            
            if_matches = re.findall(r'if\s+([^;]+);', content, re.IGNORECASE)
            operations['if'] = [i.strip().rstrip(';') for i in if_matches]
            
            by_matches = re.findall(r'by\s+([^;]+);', content, re.IGNORECASE)
            if by_matches:
                operations['by'] = [col.strip() for col in by_matches[0].split()]
            
            var_matches = re.findall(r'var\s+([^;]+);', content, re.IGNORECASE)
            if var_matches:
                operations['var'] = [col.strip() for col in var_matches[0].split()]
            
            input_matches = re.findall(r'input\s+([^;]+);', content, re.IGNORECASE)
            if input_matches:
                input_vars = []
                for var in input_matches[0].split():
                    var = var.strip().rstrip('$')
                    input_vars.append(var)
                operations['input'] = input_vars
            
            merge_matches = re.findall(r'merge\s+([^;]+);', content, re.IGNORECASE)
            if merge_matches:
                operations['merge'] = [tbl.strip() for tbl in merge_matches[0].split()]
            
            set_matches = re.findall(r'set\s+([^;]+);', content, re.IGNORECASE)
            if set_matches:
                operations['set'] = [tbl.strip() for tbl in set_matches[0].split()]
            
            # Extract calculated fields
            calc_matches = re.findall(r'(\w+)\s*=\s*([^;]+);', content)
            for var_name, expression in calc_matches:
                if var_name not in ['keep', 'drop', 'where', 'if', 'by']:
                    operations['calculated_fields'].append({
                        'name': var_name.strip(),
                        'expression': expression.strip()
                    })
        except Exception as e:
            print(f"Error extracting operations: {str(e)}")
        return operations
    
    def _extract_variables(self, content: str) -> List[str]:
        variables = []
        try:
            keep_drop_matches = re.findall(r'(keep|drop)\s*=\s*([^;]+);', content, re.IGNORECASE)
            for _, cols in keep_drop_matches:
                variables.extend([col.strip() for col in cols.split()])
            
            assignment_matches = re.findall(r'(\w+)\s*=', content)
            variables.extend(assignment_matches)
            
            select_matches = re.findall(r'select\s+([^;]+)(?:from|$)', content, re.IGNORECASE)
            for match in select_matches:
                columns = re.findall(r'(\w+)(?:\s+as\s+\w+)?(?:\s*,\s*|$)', match)
                variables.extend(columns)
            
            input_matches = re.findall(r'input\s+([^;]+);', content, re.IGNORECASE)
            for match in input_matches:
                for var in match.split():
                    var = var.strip().rstrip('$')
                    variables.append(var)
        except Exception as e:
            print(f"Error extracting variables: {str(e)}")
        return list(set(variables))
    
    def _extract_functions(self, content: str) -> List[str]:
        functions = []
        try:
            for sas_func in self.sas_functions.keys():
                if re.search(r'\b' + sas_func + r'\s*\(', content, re.IGNORECASE):
                    functions.append(sas_func)
        except Exception as e:
            print(f"Error extracting functions: {str(e)}")
        return functions
    
    def _extract_procedures(self, sas_code: str, components: Dict):
        procedure_patterns = {
            'SQL': self.sas_patterns['proc_sql'], 'SUMMARY': self.sas_patterns['proc_summary'],
            'MEANS': self.sas_patterns['proc_means'], 'SORT': self.sas_patterns['proc_sort'],
            'PRINT': self.sas_patterns['proc_print'], 'FREQ': self.sas_patterns['proc_freq'],
            'CONTENTS': self.sas_patterns['proc_contents']
        }
        
        for proc_type, pattern in procedure_patterns.items():
            try:
                procs = re.findall(pattern, sas_code, re.DOTALL | re.IGNORECASE)
                for proc_content in procs:
                    data_sources = self._extract_procedure_data_sources(proc_content, proc_type)
                    for data_source in data_sources:
                        components['table_usage'][data_source].append({
                            'type': f'PROC_{proc_type}', 'target': f'proc_{proc_type.lower()}', 'content': proc_content
                        })
                    clean_content = re.sub(r'title\s+[^;]*;', '', proc_content, flags=re.IGNORECASE)
                    components['procedures'].append({
                        'type': proc_type, 'content': clean_content.strip(),
                        'original_content': proc_content.strip(), 'data_sources': data_sources
                    })
            except Exception as e:
                print(f"Error extracting procedure {proc_type}: {str(e)}")
    
    def _extract_procedure_data_sources(self, proc_content: str, proc_type: str) -> List[str]:
        data_sources = []
        try:
            data_match = re.search(r'data\s*=\s*(\w+)', proc_content, re.IGNORECASE)
            if data_match:
                data_sources.append(data_match.group(1))
            if proc_type == 'SQL':
                from_matches = re.findall(r'from\s+(\w+)', proc_content, re.IGNORECASE)
                data_sources.extend(from_matches)
        except Exception as e:
            print(f"Error extracting procedure data sources: {str(e)}")
        return list(set(data_sources))

class SASFunctionTranslator:
    def __init__(self):
        self.function_map = {
            'put': self._translate_put, 'input': self._translate_input, 'substr': self._translate_substr,
            'strip': self._translate_strip, 'compress': self._translate_compress, 'intck': self._translate_intck,
            'intnx': self._translate_intnx, 'today': self._translate_today, 'year': self._translate_year,
            'month': self._translate_month, 'day': self._translate_day, 'nmiss': self._translate_nmiss,
            'std': self._translate_std, 'var': self._translate_var
        }
    
    def translate(self, expression: str) -> str:
        # Convert SAS date literals first
        expression = self._convert_sas_date_literals(expression)
        
        for sas_func, translator in self.function_map.items():
            pattern = r'\b' + sas_func + r'\s*\('
            if re.search(pattern, expression, re.IGNORECASE):
                expression = self._translate_function(expression, sas_func, translator)
        return expression
    
    def _convert_sas_date_literals(self, expression: str) -> str:
        """Convert SAS date literals like '01JAN2024'd to SQL date format"""
        # Pattern for SAS date literals: 'ddmmmyyyy'd
        pattern = r"'(\d{2}[A-Z]{3}\d{4})'d"
        
        def convert_date(match):
            sas_date = match.group(1)
            # Convert to SQL date format: 'yyyy-mm-dd'
            day = sas_date[:2]
            month = sas_date[2:5].upper()
            year = sas_date[5:]
            
            month_map = {
                'JAN': '01', 'FEB': '02', 'MAR': '03', 'APR': '04',
                'MAY': '05', 'JUN': '06', 'JUL': '07', 'AUG': '08',
                'SEP': '09', 'OCT': '10', 'NOV': '11', 'DEC': '12'
            }
            
            sql_month = month_map.get(month, '01')
            sql_date = f"'{year}-{sql_month}-{day}'"
            return sql_date
        
        return re.sub(pattern, convert_date, expression, flags=re.IGNORECASE)
    
    def _translate_function(self, expression: str, sas_func: str, translator) -> str:
        pattern = r'(\b' + sas_func + r'\s*\()(.*?)(\))'
        def replace_func(match):
            full_match = match.group(0)
            inner_args = match.group(2)
            try:
                return translator(inner_args)
            except:
                return full_match
        return re.sub(pattern, replace_func, expression, flags=re.IGNORECASE)
    
    def _translate_put(self, args: str) -> str:
        parts = [part.strip() for part in args.split(',')]
        if len(parts) >= 2:
            return f"CAST({parts[0]} AS VARCHAR)"
        return f"CAST({args} AS VARCHAR)"
    
    def _translate_input(self, args: str) -> str:
        parts = [part.strip() for part in args.split(',')]
        if len(parts) >= 2:
            return f"CAST({parts[0]} AS NUMERIC)"
        return f"CAST({args} AS NUMERIC)"
    
    def _translate_substr(self, args: str) -> str:
        parts = [part.strip() for part in args.split(',')]
        if len(parts) >= 3:
            return f"SUBSTRING({parts[0]}, {parts[1]}, {parts[2]})"
        elif len(parts) == 2:
            return f"SUBSTRING({parts[0]}, {parts[1]})"
        return f"SUBSTRING({args})"
    
    def _translate_strip(self, args: str) -> str:
        return f"TRIM({args})"
    
    def _translate_compress(self, args: str) -> str:
        parts = [part.strip() for part in args.split(',')]
        if len(parts) >= 2:
            return f"REPLACE({parts[0]}, {parts[1]}, '')"
        return f"REPLACE({args}, ' ', '')"
    
    def _translate_intck(self, args: str) -> str:
        parts = [part.strip() for part in args.split(',')]
        if len(parts) >= 3:
            return f"DATEDIFF({parts[0]}, {parts[1]}, {parts[2]})"
        return f"DATEDIFF(day, {args})"
    
    def _translate_intnx(self, args: str) -> str:
        parts = [part.strip() for part in args.split(',')]
        if len(parts) >= 3:
            return f"DATEADD({parts[0]}, {parts[1]}, {parts[2]})"
        return f"DATEADD(day, {args})"
    
    def _translate_today(self, args: str) -> str:
        return "CURRENT_DATE"
    
    def _translate_year(self, args: str) -> str:
        return f"YEAR({args})"
    
    def _translate_month(self, args: str) -> str:
        return f"MONTH({args})"
    
    def _translate_day(self, args: str) -> str:
        return f"DAY({args})"
    
    def _translate_nmiss(self, args: str) -> str:
        return f"COUNT(CASE WHEN {args} IS NULL THEN 1 END)"
    
    def _translate_std(self, args: str) -> str:
        return f"STDDEV({args})"
    
    def _translate_var(self, args: str) -> str:
        return f"VARIANCE({args})"

class SASToSQLTranslator:
    def __init__(self):
        self.sas_sql_mapping = {
            'eq': '=', 'ne': '<>', 'gt': '>', 'lt': '<', 'ge': '>=', 'le': '<=',
            'and': 'AND', 'or': 'OR', 'not': 'NOT', 'in': 'IN'
        }
        self.function_translator = SASFunctionTranslator()
    
    def translate_data_step(self, data_step: Dict) -> str:
        try:
            table_name = data_step['table_name']
            operations = data_step['operations']
            source_tables = data_step['source_tables']
            has_datalines = data_step.get('has_datalines', False)
            
            if has_datalines:
                return self._translate_datalines_step(data_step)
            
            if not source_tables:
                return f"-- No source tables found for data step: {table_name}"
            
            if operations.get('merge'):
                return self._translate_merge_step(data_step)
            
            if operations.get('set'):
                return self._translate_set_step(data_step)
            
            select_clause = self._build_select_clause(operations)
            from_clause = self._build_from_clause(source_tables)
            where_clause = self._build_where_clause(operations)
            group_by_clause = self._build_group_by_clause(operations)
            calculated_fields = self._build_calculated_fields(operations)
            
            sql = f"SELECT {select_clause}"
            
            if calculated_fields:
                sql += f", {calculated_fields}"
            
            sql += f"\nFROM {from_clause}"
            
            if where_clause:
                sql += f"\nWHERE {where_clause}"
            if group_by_clause:
                sql += f"\nGROUP BY {group_by_clause}"
            
            return sql
        except Exception as e:
            return f"-- Error translating data step {data_step.get('table_name', 'unknown')}: {str(e)}"
    
    def _translate_merge_step(self, data_step: Dict) -> str:
        try:
            table_name = data_step['table_name']
            operations = data_step['operations']
            source_tables = data_step['source_tables']
            
            if not source_tables or len(source_tables) < 2:
                return f"-- MERGE requires at least 2 tables: {table_name}"
            
            by_vars = operations.get('by', [])
            if not by_vars:
                return f"-- MERGE requires BY statement: {table_name}"
            
            join_conditions = []
            for by_var in by_vars:
                join_conditions.append(f"a.{by_var} = b.{by_var}")
            join_condition = " AND ".join(join_conditions)
            
            where_conditions = []
            if "a and b" in data_step['content'].lower():
                where_conditions.append("a.acct_num IS NOT NULL AND b.acct_num IS NOT NULL")
            
            select_clause = self._build_select_clause(operations)
            if select_clause == "*":
                select_clause = "a.*, b.*"
            
            sql = f"SELECT {select_clause}\nFROM {source_tables[0]} a\nINNER JOIN {source_tables[1]} b ON {join_condition}"
            
            if where_conditions:
                sql += f"\nWHERE {' AND '.join(where_conditions)}"
            
            return sql
        except Exception as e:
            return f"-- Error translating merge step: {str(e)}"
    
    def _translate_set_step(self, data_step: Dict) -> str:
        try:
            table_name = data_step['table_name']
            operations = data_step['operations']
            source_tables = data_step['source_tables']
            
            if not source_tables:
                return f"-- No source tables found for SET statement: {table_name}"
            
            if len(source_tables) == 1:
                select_clause = self._build_select_clause(operations)
                where_clause = self._build_where_clause(operations)
                calculated_fields = self._build_calculated_fields(operations)
                
                sql = f"SELECT {select_clause}"
                if calculated_fields:
                    sql += f", {calculated_fields}"
                sql += f"\nFROM {source_tables[0]}"
                if where_clause:
                    sql += f"\nWHERE {where_clause}"
                return sql
            else:
                union_parts = []
                for table in source_tables:
                    union_parts.append(f"SELECT * FROM {table}")
                return "\nUNION ALL\n".join(union_parts)
        except Exception as e:
            return f"-- Error translating set step: {str(e)}"
    
    def _translate_datalines_step(self, data_step: Dict) -> str:
        try:
            table_name = data_step['table_name']
            operations = data_step['operations']
            columns = operations.get('input', [])
            if not columns:
                return f"-- No INPUT statement found for data step: {table_name}"
            column_defs = []
            for col in columns:
                column_defs.append(f"{col} VARCHAR(100)")
            create_sql = f"CREATE TABLE {table_name} (\n    " + ",\n    ".join(column_defs) + "\n)"
            return create_sql
        except Exception as e:
            return f"-- Error translating datalines step: {str(e)}"
    
    def _build_select_clause(self, operations: Dict) -> str:
        try:
            keep_cols = operations.get('keep', [])
            drop_cols = operations.get('drop', [])
            if keep_cols:
                return ", ".join(keep_cols)
            elif drop_cols:
                return "*  -- Note: DROP operation requires explicit column list"
            else:
                return "*"
        except:
            return "*"
    
    def _build_from_clause(self, source_tables: List[str]) -> str:
        try:
            if len(source_tables) == 1:
                return source_tables[0]
            else:
                return " CROSS JOIN ".join(source_tables)
        except:
            return "unknown_table"
    
    def _build_where_clause(self, operations: Dict) -> str:
        try:
            conditions = []
            where_conditions = operations.get('where', [])
            conditions.extend(where_conditions)
            if_conditions = operations.get('if', [])
            conditions.extend(if_conditions)
            
            if conditions:
                translated_conditions = []
                for condition in conditions:
                    # Remove any trailing semicolons and clean up the condition
                    condition = condition.rstrip(';').strip()
                    translated_condition = self._translate_condition(condition)
                    translated_conditions.append(translated_condition)
                return " AND ".join(translated_conditions)
            return ""
        except:
            return ""
    
    def _build_group_by_clause(self, operations: Dict) -> str:
        try:
            by_cols = operations.get('by', [])
            if by_cols:
                return ", ".join(by_cols)
            return ""
        except:
            return ""
    
    def _build_calculated_fields(self, operations: Dict) -> str:
        try:
            calculated_fields = operations.get('calculated_fields', [])
            if calculated_fields:
                fields = []
                for field in calculated_fields:
                    translated_expr = self._translate_condition(field['expression'])
                    fields.append(f"{translated_expr} AS {field['name']}")
                return ", ".join(fields)
            return ""
        except:
            return ""
    
    def _translate_condition(self, condition: str) -> str:
        try:
            # Clean up the condition first
            condition = condition.rstrip(';').strip()
            
            # Convert SAS date literals and other functions
            condition = self.function_translator.translate(condition)
            
            # Translate SAS operators to SQL
            for sas_op, sql_op in self.sas_sql_mapping.items():
                condition = re.sub(r'\b' + sas_op + r'\b', sql_op, condition, flags=re.IGNORECASE)
            
            return condition
        except:
            return condition
    
    def translate_proc_sql(self, proc_content: str) -> str:
        try:
            sql = proc_content
            # Remove SAS-specific clauses
            sql = re.sub(r'format\s*=\s*[^,\s]+\s*', '', sql, flags=re.IGNORECASE)
            sql = re.sub(r'outobs\s*=\s*\d+', '', sql, flags=re.IGNORECASE)
            
            # Convert SAS date literals first
            sql = self.function_translator.translate(sql)
            
            # Translate SAS operators to SQL
            for sas_op, sql_op in self.sas_sql_mapping.items():
                sql = re.sub(r'\b' + sas_op + r'\b', sql_op, sql, flags=re.IGNORECASE)
            
            # Remove PROC SQL and QUIT statements
            sql = re.sub(r'\bproc\s+sql\b', '', sql, flags=re.IGNORECASE)
            sql = re.sub(r'\bquit\b', '', sql, flags=re.IGNORECASE)
            
            # Handle macros
            sql = re.sub(r'%(\w+)\(', r'/* MACRO \1 CALL: ', sql)
            sql = re.sub(r'\)', r' */', sql)
            
            # Remove trailing semicolons
            sql = sql.rstrip(';').strip()
            
            return sql
        except Exception as e:
            return f"-- Error translating PROC SQL: {str(e)}"
    
    def translate_proc_print(self, proc_content: str) -> str:
        try:
            data_match = re.search(r'data\s*=\s*(\w+)', proc_content, re.IGNORECASE)
            var_match = re.search(r'var\s+([^;]+);', proc_content, re.IGNORECASE)
            where_match = re.search(r'where\s+([^;]+);', proc_content, re.IGNORECASE)
            
            if not data_match:
                return "-- No data source specified in PROC PRINT"
            
            input_table = data_match.group(1)
            columns = ", ".join([v.strip() for v in var_match.group(1).split()]) if var_match else "*"
            where_clause = f"WHERE {self.function_translator.translate(where_match.group(1).rstrip(';'))}" if where_match else ""
            
            sql = f"SELECT {columns}\nFROM {input_table}"
            if where_clause:
                sql += f"\n{where_clause}"
            return sql
        except Exception as e:
            return f"-- Error translating PROC PRINT: {str(e)}"

class SQLConsolidator:
    def __init__(self):
        self.cte_counter = 0
    
    def consolidate_queries(self, components: Dict, individual_queries: List[Dict]) -> str:
        try:
            # Build dependency graph
            dependency_graph = self._build_dependency_graph(components)
            
            # Get execution order (topological sort)
            execution_order = self._topological_sort(dependency_graph)
            
            cte_definitions = []
            final_queries = []
            
            # Process tables in dependency order - only create CTEs for intermediate tables
            for table_name in execution_order:
                # Skip creating CTEs for final output tables that are not used elsewhere
                if self._is_final_output_table(table_name, components, individual_queries):
                    continue
                    
                creating_query = self._find_creating_query(table_name, individual_queries)
                if creating_query:
                    cte_name = f"cte_{table_name}"
                    
                    # Get the SQL for this CTE
                    query_sql = creating_query['sql']
                    
                    # For data steps, we need to ensure all conditions are included
                    if creating_query['type'] == 'DATA_STEP':
                        if not query_sql.strip().upper().startswith('SELECT'):
                            # Handle CREATE TABLE statements
                            create_match = re.search(r'CREATE TABLE \w+ AS\s*(.*)', query_sql, re.DOTALL | re.IGNORECASE)
                            if create_match:
                                query_sql = create_match.group(1).strip()
                    
                    # Remove any trailing semicolons
                    query_sql = query_sql.rstrip(';').strip()
                    cte_def = f"{cte_name} AS (\n{self._indent_sql(query_sql)}\n)"
                    cte_definitions.append(cte_def)
                    
                    # Also create CTEs for PROC SQL that create tables (if they're intermediate)
                    if (creating_query['type'] == 'PROC_SQL' and 
                        creating_query.get('creates_table') and
                        not self._is_final_output_table(table_name, components, individual_queries)):
                        query_sql = creating_query['sql']
                        create_match = re.search(r'CREATE TABLE \w+ AS\s*(.*)', query_sql, re.DOTALL | re.IGNORECASE)
                        if create_match:
                            query_sql = create_match.group(1).strip()
                            query_sql = query_sql.rstrip(';').strip()
                            cte_def = f"{cte_name} AS (\n{self._indent_sql(query_sql)}\n)"
                            cte_definitions.append(cte_def)
            
            # Find the final query (usually the last PROC SQL that doesn't create a table)
            for query in reversed(individual_queries):
                if query['type'] == 'PROC_SQL' and not query.get('creates_table'):
                    final_query = query['sql']
                    
                    # Remove CREATE TABLE statement if present
                    final_query = re.sub(r'CREATE TABLE \w+ AS\s*', '', final_query, flags=re.IGNORECASE)
                    
                    # Replace table references with CTEs
                    for table_name in execution_order:
                        if not self._is_final_output_table(table_name, components, individual_queries):
                            cte_name = f"cte_{table_name}"
                            final_query = re.sub(rf'\b{re.escape(table_name)}\b', cte_name, final_query)
                    
                    # Remove any trailing semicolons
                    final_query = final_query.rstrip(';').strip()
                    final_queries.append(final_query)
                    break
            
            # If no final query found, use the last query
            if not final_queries and individual_queries:
                final_query = individual_queries[-1]['sql']
                # Remove CREATE TABLE statement if present
                final_query = re.sub(r'CREATE TABLE \w+ AS\s*', '', final_query, flags=re.IGNORECASE)
                
                for table_name in execution_order:
                    if not self._is_final_output_table(table_name, components, individual_queries):
                        cte_name = f"cte_{table_name}"
                        final_query = re.sub(rf'\b{re.escape(table_name)}\b', cte_name, final_query)
                
                # Remove any trailing semicolons
                final_query = final_query.rstrip(';').strip()
                final_queries.append(final_query)
            
            # Build the final SQL
            consolidated_sql = ""
            if cte_definitions:
                consolidated_sql = "WITH " + ",\n".join(cte_definitions) + "\n\n"
            if final_queries:
                consolidated_sql += final_queries[0]
            
            return consolidated_sql if consolidated_sql.strip() else "/* No queries to consolidate */"
            
        except Exception as e:
            import traceback
            return f"-- Error consolidating SQL: {str(e)}\n{traceback.format_exc()}"
    
    def _is_final_output_table(self, table_name: str, components: Dict, individual_queries: List[Dict]) -> bool:
        """Check if a table is a final output table that shouldn't be converted to CTE"""
        # Check if this table is used by any other table
        is_used = False
        for other_table, deps in components.get('table_dependencies', {}).items():
            if table_name in deps and other_table != table_name:
                is_used = True
                break
        
        # Check if this is the last created table (likely the final output)
        if not is_used:
            # Find the creating query
            creating_query = self._find_creating_query(table_name, individual_queries)
            if creating_query:
                # If this is a PROC SQL that creates a table and it's not used elsewhere,
                # it's likely the final output
                if creating_query['type'] == 'PROC_SQL' and creating_query.get('creates_table'):
                    return True
                # If this is the last data step and not used elsewhere, it's likely final output
                if (creating_query['type'] == 'DATA_STEP' and 
                    creating_query == individual_queries[-1]):
                    return True
        
        return False
    
    def _build_dependency_graph(self, components: Dict) -> Dict[str, List[str]]:
        graph = {}
        # Add all tables as nodes
        for table in components.get('tables', []):
            graph[table] = []
        
        # Add dependencies from data steps
        for data_step in components.get('data_steps', []):
            table_name = data_step['table_name']
            source_tables = data_step.get('source_tables', [])
            graph[table_name] = source_tables
        
        # Add dependencies from procedures
        for procedure in components.get('procedures', []):
            if procedure['type'] == 'SQL':
                # Extract dependencies from PROC SQL
                data_sources = procedure.get('data_sources', [])
                creates_table_match = re.search(r'create\s+table\s+(\w+)', procedure['content'], re.IGNORECASE)
                if creates_table_match:
                    table_name = creates_table_match.group(1)
                    if table_name not in graph:
                        graph[table_name] = []
                    graph[table_name].extend(data_sources)
        
        return graph
    
    def _topological_sort(self, graph: Dict[str, List[str]]) -> List[str]:
        visited = set()
        temp_visited = set()
        result = []
        
        def visit(node):
            if node in temp_visited:
                return
            if node not in visited:
                temp_visited.add(node)
                # Visit all dependencies first
                for neighbor in graph.get(node, []):
                    if neighbor in graph:  # Only visit nodes that are in our graph
                        visit(neighbor)
                temp_visited.remove(node)
                visited.add(node)
                result.append(node)
        
        # Visit all nodes
        for node in list(graph.keys()):
            if node not in visited:
                visit(node)
        
        return result
    
    def _find_creating_query(self, table_name: str, queries: List[Dict]) -> Optional[Dict]:
        for query in queries:
            if query['type'] == 'DATA_STEP' and query.get('table_name') == table_name:
                return query
            elif query['type'] == 'PROC_SQL' and query.get('creates_table') == table_name:
                return query
        return None
    
    def _indent_sql(self, sql: str, indent_level: int = 1) -> str:
        try:
            indent = "    " * indent_level
            lines = sql.split('\n')
            indented_lines = [indent + line if line.strip() else line for line in lines]
            return '\n'.join(indented_lines)
        except:
            return sql

class AICodeEnhancer:
    def __init__(self):
        self.optimization_rules = [
            self._optimize_joins, self._optimize_subqueries, self._add_index_hints,
            self._improve_readability, self._suggest_performance_improvements
        ]
    
    def enhance_sql(self, sql_code: str, context: Dict = None) -> str:
        enhanced_sql = sql_code
        for optimizer in self.optimization_rules:
            enhanced_sql = optimizer(enhanced_sql, context)
        return enhanced_sql
    
    def _optimize_joins(self, sql: str, context: Dict = None) -> str:
        return sql
    
    def _optimize_subqueries(self, sql: str, context: Dict = None) -> str:
        return sql
    
    def _add_index_hints(self, sql: str, context: Dict = None) -> str:
        return sql
    
    def _improve_readability(self, sql: str, context: Dict = None) -> str:
        try:
            # Remove extra whitespace and format SQL
            sql = re.sub(r'\s+', ' ', sql)
            sql = sqlparse.format(sql, reindent=True, keyword_case='upper')
            return sql
        except:
            return sql
    
    def _suggest_performance_improvements(self, sql: str, context: Dict = None) -> str:
        suggestions = []
        if "SELECT *" in sql.upper():
            suggestions.append("-- Consider specifying columns instead of using SELECT *")
        if "CROSS JOIN" in sql.upper():
            suggestions.append("-- CROSS JOIN can be expensive; ensure it's necessary")
        if len(suggestions) > 0:
            sql = "\n".join(suggestions) + "\n" + sql
        return sql

class SASProcessor:
    def __init__(self):
        self.analyzer = SASAnalyzer()
        self.translator = SASToSQLTranslator()
        self.consolidator = SQLConsolidator()
        self.enhancer = AICodeEnhancer()
    
    def process_sas_code(self, sas_code: str) -> Dict:
        try:
            components = self.analyzer.parse_sas_code(sas_code)
            individual_queries = []
            
            # Translate data steps
            for data_step in components['data_steps']:
                sql = self.translator.translate_data_step(data_step)
                individual_queries.append({
                    'type': 'DATA_STEP',
                    'table_name': data_step['table_name'],
                    'sql': sql,
                    'original_content': data_step['content']
                })
            
            # Translate procedures
            for procedure in components['procedures']:
                if procedure['type'] == 'SQL':
                    sql = self.translator.translate_proc_sql(procedure['content'])
                    creates_table_match = re.search(r'create\s+table\s+(\w+)', procedure['content'], re.IGNORECASE)
                    if creates_table_match:
                        individual_queries.append({
                            'type': 'PROC_SQL',
                            'creates_table': creates_table_match.group(1),
                            'sql': sql,
                            'original_content': procedure['content']
                        })
                    else:
                        individual_queries.append({
                            'type': 'PROC_SQL',
                            'sql': sql,
                            'original_content': procedure['content']
                        })
                elif procedure['type'] == 'PRINT':
                    sql = self.translator.translate_proc_print(procedure['content'])
                    individual_queries.append({
                        'type': 'PROC_PRINT',
                        'sql': sql,
                        'original_content': procedure['content']
                    })
            
            # Consolidate queries
            consolidated_sql = self.consolidator.consolidate_queries(components, individual_queries)
            
            # Enhance SQL
            enhanced_sql = self.enhancer.enhance_sql(consolidated_sql, components)
            
            return {
                'components': components,
                'individual_queries': individual_queries,
                'consolidated_sql': consolidated_sql,
                'enhanced_sql': enhanced_sql,
                'success': True
            }
            
        except Exception as e:
            import traceback
            return {
                'success': False,
                'error': str(e),
                'traceback': traceback.format_exc(),
                'components': {},
                'individual_queries': [],
                'consolidated_sql': '',
                'enhanced_sql': ''
            }

# Flask Application
app = Flask(__name__)

HTML_TEMPLATE = """
<!DOCTYPE html>
<html>
<head>
    <title>Enhanced SAS to SQL Converter</title>
    <style>
        :root {
            --primary-red: #d32f2f;
            --dark-red: #b71c1c;
            --light-red: #ff6659;
            --primary-blue: #1976d2;
            --dark-blue: #1565c0;
            --light-blue: #42a5f5;
            --white: #ffffff;
            --light-grey: #f8f9fa;
            --medium-grey: #e9ecef;
            --dark-grey: #495057;
            --text-dark: #212529;
            --success-green: #28a745;
            --warning-orange: #ffc107;
        }
        
        * {
            margin: 0;
            padding: 0;
            box-sizing: border-box;
        }
        
        body { 
            font-family: 'Inter', 'Segoe UI', system-ui, -apple-system, sans-serif; 
            background: linear-gradient(135deg, #667eea 0%, #764ba2 100%);
            min-height: 100vh;
            color: var(--text-dark);
            line-height: 1.6;
        }
        
        .app-container {
            max-width: 1400px; 
            margin: 0 auto;
            padding: 30px 20px;
        }
        
        .header {
            background: linear-gradient(135deg, var(--primary-blue) 0%, var(--dark-blue) 100%);
            color: var(--white);
            padding: 50px 40px;
            border-radius: 20px 20px 0 0;
            box-shadow: 0 10px 40px rgba(0,0,0,0.2);
            margin-bottom: 0;
            text-align: center;
            position: relative;
            overflow: hidden;
        }
        
        .header::before {
            content: '';
            position: absolute;
            top: 0;
            left: 0;
            right: 0;
            bottom: 0;
            background: url('data:image/svg+xml,<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 1000 100" fill="%23ffffff" opacity="0.1"><polygon points="0,0 1000,50 1000,100 0,100"/></svg>');
            background-size: cover;
        }
        
        .header h1 {
            font-size: 3.2rem;
            font-weight: 800;
            margin-bottom: 16px;
            display: flex;
            align-items: center;
            justify-content: center;
            gap: 20px;
            position: relative;
            text-shadow: 0 2px 10px rgba(0,0,0,0.3);
        }
        
        .header .subtitle {
            font-size: 1.3rem;
            opacity: 0.95;
            font-weight: 400;
            max-width: 800px;
            margin: 0 auto;
            line-height: 1.7;
            position: relative;
        }
        
        .main-content {
            display: grid;
            grid-template-columns: 1fr 1fr;
            gap: 0;
            background: var(--white);
            border-radius: 0 0 20px 20px;
            box-shadow: 0 20px 50px rgba(0,0,0,0.15);
            overflow: hidden;
            backdrop-filter: blur(10px);
        }
        
        .input-section, .output-section { 
            padding: 40px;
            min-height: 700px;
        }
        
        .input-section {
            background: var(--white);
            border-right: 3px solid var(--medium-grey);
            position: relative;
        }
        
        .input-section::after {
            content: '';
            position: absolute;
            right: -2px;
            top: 50%;
            transform: translateY(-50%);
            width: 4px;
            height: 80%;
            background: linear-gradient(to bottom, var(--primary-blue), var(--light-blue));
            border-radius: 2px;
        }
        
        .output-section {
            background: linear-gradient(135deg, var(--light-grey) 0%, var(--medium-grey) 100%);
            display: flex;
            flex-direction: column;
            position: relative;
        }
        
        .section-title {
            font-size: 1.7rem;
            font-weight: 700;
            color: var(--primary-blue);
            margin-bottom: 30px;
            padding-bottom: 18px;
            border-bottom: 3px solid var(--primary-blue);
            display: flex;
            align-items: center;
            gap: 15px;
            position: relative;
        }
        
        .section-title::before {
            content: '';
            width: 8px;
            height: 8px;
            background: var(--primary-blue);
            border-radius: 50%;
            display: inline-block;
        }
        
        .config-panel {
            background: linear-gradient(135deg, var(--light-grey) 0%, var(--medium-grey) 100%);
            padding: 30px;
            border-radius: 16px;
            margin-bottom: 35px;
            border-left: 6px solid var(--primary-blue);
            box-shadow: 0 8px 25px rgba(0,0,0,0.08);
            border: 1px solid rgba(255,255,255,0.2);
        }
        
        .config-row {
            display: flex;
            gap: 20px;
            margin-bottom: 25px;
            align-items: center;
        }
        
        .config-label {
            font-weight: 600;
            color: var(--dark-grey);
            min-width: 150px;
            font-size: 15px;
        }
        
        select, .file-input {
            flex: 1;
            padding: 14px 20px;
            border: 2px solid #e1e5e9;
            border-radius: 12px;
            background: var(--white);
            font-size: 15px;
            transition: all 0.3s ease;
            font-family: inherit;
            box-shadow: 0 2px 10px rgba(0,0,0,0.04);
        }
        
        select:focus, .file-input:focus {
            outline: none;
            border-color: var(--primary-blue);
            box-shadow: 0 0 0 4px rgba(25, 118, 210, 0.15);
            transform: translateY(-2px);
        }
        
        .file-upload-container {
            background: var(--white);
            border: 2px dashed #cbd5e0;
            border-radius: 12px;
            padding: 25px;
            text-align: center;
            margin-bottom: 25px;
            transition: all 0.3s ease;
            cursor: pointer;
        }
        
        .file-upload-container:hover {
            border-color: var(--primary-blue);
            background: rgba(25, 118, 210, 0.02);
        }
        
        .file-upload-container.dragover {
            border-color: var(--primary-blue);
            background: rgba(25, 118, 210, 0.05);
            transform: scale(1.02);
        }
        
        .upload-icon {
            font-size: 3rem;
            color: var(--primary-blue);
            margin-bottom: 15px;
        }
        
        .upload-text {
            font-weight: 600;
            color: var(--dark-grey);
            margin-bottom: 10px;
        }
        
        .upload-subtext {
            color: var(--dark-grey);
            font-size: 14px;
            opacity: 0.7;
        }
        
        .or-divider {
            text-align: center;
            margin: 25px 0;
            position: relative;
        }
        
        .or-divider::before {
            content: '';
            position: absolute;
            top: 50%;
            left: 0;
            right: 0;
            height: 1px;
            background: var(--medium-grey);
        }
        
        .or-text {
            background: var(--white);
            padding: 0 20px;
            color: var(--dark-grey);
            font-weight: 600;
            position: relative;
            display: inline-block;
        }
        
        .code-input-label {
            font-weight: 700;
            color: var(--primary-blue);
            margin-bottom: 15px;
            display: block;
            font-size: 1.1rem;
        }
        
        textarea { 
            width: 100%; 
            height: 350px; 
            padding: 25px; 
            border: 2px solid #e1e5e9; 
            border-radius: 16px; 
            font-family: 'Fira Code', 'Consolas', 'Monaco', monospace; 
            font-size: 14px;
            line-height: 1.6;
            background: var(--white);
            resize: vertical;
            transition: all 0.3s ease;
            box-shadow: 0 4px 15px rgba(0,0,0,0.05);
        }
        
        textarea:focus {
            outline: none;
            border-color: var(--primary-blue);
            box-shadow: 0 0 0 4px rgba(25, 118, 210, 0.15), 0 8px 25px rgba(0,0,0,0.1);
            transform: translateY(-2px);
        }
        
        .button-group {
            display: flex;
            gap: 15px;
            margin: 35px 0;
        }
        
        .btn {
            padding: 18px 35px; 
            border: none; 
            border-radius: 12px; 
            cursor: pointer; 
            font-size: 16px; 
            font-weight: 700;
            transition: all 0.3s ease;
            display: flex;
            align-items: center;
            gap: 12px;
            flex: 1;
            justify-content: center;
            font-family: inherit;
            text-transform: uppercase;
            letter-spacing: 0.5px;
            position: relative;
            overflow: hidden;
        }
        
        .btn::before {
            content: '';
            position: absolute;
            top: 0;
            left: -100%;
            width: 100%;
            height: 100%;
            background: linear-gradient(90deg, transparent, rgba(255,255,255,0.2), transparent);
            transition: left 0.5s;
        }
        
        .btn:hover::before {
            left: 100%;
        }
        
        .btn-primary {
            background: linear-gradient(135deg, var(--primary-blue) 0%, var(--dark-blue) 100%); 
            color: var(--white); 
            box-shadow: 0 8px 25px rgba(25, 118, 210, 0.4);
        }
        
        .btn-primary:hover { 
            transform: translateY(-3px);
            box-shadow: 0 12px 35px rgba(25, 118, 210, 0.5);
        }
        
        .btn-secondary {
            background: linear-gradient(135deg, var(--dark-grey) 0%, #343a40 100%);
            color: var(--white);
            box-shadow: 0 8px 25px rgba(73, 80, 87, 0.4);
        }
        
        .btn-secondary:hover {
            transform: translateY(-3px);
            box-shadow: 0 12px 35px rgba(73, 80, 87, 0.5);
        }
        
        .btn-download {
            background: linear-gradient(135deg, var(--success-green) 0%, #1e7e34 100%);
            color: var(--white);
            box-shadow: 0 8px 25px rgba(40, 167, 69, 0.4);
            margin-top: 20px;
        }
        
        .btn-download:hover {
            transform: translateY(-3px);
            box-shadow: 0 12px 35px rgba(40, 167, 69, 0.5);
        }
        
        .sql-output-container {
            flex: 1;
            display: flex;
            flex-direction: column;
        }
        
        .sql-code { 
            background: #1a1b26; 
            color: #c0caf5;
            padding: 30px; 
            border-radius: 16px; 
            font-family: 'Fira Code', 'Consolas', 'Monaco', monospace; 
            white-space: pre-wrap;
            font-size: 14px;
            line-height: 1.6;
            overflow-x: auto;
            border: 2px solid #2a2b3d;
            flex: 1;
            min-height: 450px;
            box-shadow: inset 0 2px 10px rgba(0,0,0,0.3);
        }
        
        .tabs { 
            display: flex; 
            margin-bottom: 0;
            background: var(--white);
            border-bottom: 3px solid var(--primary-blue);
            border-radius: 16px 16px 0 0;
            overflow: hidden;
            box-shadow: 0 4px 15px rgba(0,0,0,0.08);
        }
        
        .tab { 
            padding: 20px 30px; 
            cursor: pointer; 
            background: var(--light-grey);
            color: var(--dark-grey);
            font-weight: 600;
            border: none;
            flex: 1;
            text-align: center;
            transition: all 0.3s ease;
            font-size: 15px;
            position: relative;
            overflow: hidden;
        }
        
        .tab::after {
            content: '';
            position: absolute;
            bottom: 0;
            left: 50%;
            width: 0;
            height: 3px;
            background: var(--primary-blue);
            transition: all 0.3s ease;
            transform: translateX(-50%);
        }
        
        .tab.active { 
            background: var(--white); 
            color: var(--primary-blue);
            font-weight: 700;
        }
        
        .tab.active::after {
            width: 100%;
        }
        
        .tab:hover:not(.active) {
            background: var(--medium-grey);
            color: var(--primary-blue);
        }
        
        .tab-content { 
            display: none; 
            background: var(--white);
            padding: 0;
            border-radius: 0 0 16px 16px;
            flex: 1;
            overflow: auto;
            box-shadow: 0 8px 25px rgba(0,0,0,0.08);
        }
        
        .tab-content.active { 
            display: flex;
            flex-direction: column;
        }
        
        .summary-item {
            background: linear-gradient(135deg, var(--light-grey) 0%, var(--medium-grey) 100%);
            padding: 20px;
            margin: 15px 0;
            border-radius: 12px;
            border-left: 5px solid var(--primary-blue);
            display: flex;
            justify-content: space-between;
            align-items: center;
            box-shadow: 0 4px 15px rgba(0,0,0,0.05);
            transition: transform 0.3s ease;
        }
        
        .summary-item:hover {
            transform: translateX(5px);
        }
        
        .summary-label {
            font-weight: 600;
            color: var(--dark-grey);
            font-size: 15px;
        }
        
        .summary-value {
            font-weight: 800;
            color: var(--primary-blue);
            font-size: 16px;
            background: var(--white);
            padding: 8px 16px;
            border-radius: 8px;
            box-shadow: 0 2px 8px rgba(0,0,0,0.1);
        }
        
        .analysis-grid {
            display: grid;
            grid-template-columns: 1fr 1fr;
            gap: 15px;
            margin-top: 20px;
        }
        
        .download-section {
            margin-top: 25px;
            padding-top: 25px;
            border-top: 2px solid var(--medium-grey);
        }
        
        .status-indicator {
            display: inline-flex;
            align-items: center;
            gap: 8px;
            padding: 8px 16px;
            background: var(--success-green);
            color: white;
            border-radius: 20px;
            font-size: 14px;
            font-weight: 600;
            margin-left: 15px;
        }
        
        @media (max-width: 1024px) {
            .main-content {
                grid-template-columns: 1fr;
            }
            
            .input-section {
                border-right: none;
                border-bottom: 3px solid var(--medium-grey);
            }
            
            .input-section::after {
                display: none;
            }
        }
        
        /* Animation for conversion process */
        @keyframes pulse {
            0% { transform: scale(1); }
            50% { transform: scale(1.05); }
            100% { transform: scale(1); }
        }
        
        .converting {
            animation: pulse 1.5s ease-in-out infinite;
        }
    </style>
    <link href="https://fonts.googleapis.com/css2?family=Inter:wght@300;400;500;600;700;800&display=swap" rel="stylesheet">
    <link href="https://fonts.googleapis.com/css2?family=Fira+Code:wght@300;400;500;600&display=swap" rel="stylesheet">
</head>
<body>
    <div class="app-container">
        <div class="header">
            <h1>🔄 Enhanced SAS to SQL Converter</h1>
            <div class="subtitle">Convert your legacy SAS code to modern SQL with advanced macro expansion and intelligent JOIN detection</div>
        </div>
        
        <div class="main-content">
            <div class="input-section">
                <div class="section-title">SAS Input</div>
                
                <div class="config-panel">
                    <div class="config-row">
                        <div class="config-label">SQL Dialect:</div>
                        <select id="sqlDialect">
                            <option value="spark">Spark SQL</option>
                            <option value="oracle">Oracle</option>
                        </select>
                    </div>
                    
                    <div class="config-row">
                        <div class="config-label">Upload SAS File:</div>
                        <div class="file-upload-container" id="fileUploadContainer" onclick="document.getElementById('sasFileInput').click()">
                            <div class="upload-icon">📁</div>
                            <div class="upload-text">Click to browse or drag & drop SAS file</div>
                            <div class="upload-subtext">Supports .sas files up to 10MB</div>
                            <input type="file" id="sasFileInput" accept=".sas" style="display: none;" onchange="handleFileSelect(this.files)">
                        </div>
                    </div>
                </div>
                
                <div class="or-divider">
                    <span class="or-text">OR ENTER THE SAS CODE</span>
                </div>
                
                <form method="POST" id="conversionForm" enctype="multipart/form-data">
                    <label class="code-input-label">📝 Paste your SAS code below:</label>
                    <textarea name="sas_code" placeholder="/* Example SAS Code */
data derived1;
  set sales_data;
  where sales_date >= '01JAN2024'd;
  total_sale = quantity * price;
run;

data derived2;
  set customer_data;
  if region = 'North';
run;" id="sasCodeTextarea">{{ sas_code if sas_code }}</textarea>
                    
                    <div class="button-group">
                        <button type="submit" class="btn btn-primary" id="convertBtn">
                            <span>🚀 Convert to SQL</span>
                        </button>
                        <button type="button" class="btn btn-secondary" onclick="resetForm()">
                            <span>🔄 Reset</span>
                        </button>
                    </div>
                </form>
            </div>
            
            <div class="output-section">
                <div class="section-title">SQL Output 
                    {% if result and result.success %}
                    <span class="status-indicator">✅ Conversion Successful</span>
                    {% endif %}
                </div>
                
                {% if result %}
                <div class="sql-output-container">
                    <div class="tabs">
                        <div class="tab active" onclick="showTab('consolidated')">Consolidated SQL</div>
                        <div class="tab" onclick="showTab('individual')">Individual Queries</div>
                        <div class="tab" onclick="showTab('analysis')">Analysis</div>
                    </div>
                    
                    <div id="consolidated" class="tab-content active">
                        <div class="sql-code">{{ result.consolidated_sql }}</div>
                        <div class="download-section">
                            <button type="button" class="btn btn-download" onclick="downloadSQL()">
                                <span>📥 Download SQL as .txt</span>
                            </button>
                        </div>
                    </div>
                    
                    <div id="individual" class="tab-content">
                        {% for query in result.individual_queries %}
                        <div style="margin-bottom: 30px;">
                            <div style="background: linear-gradient(135deg, var(--primary-blue) 0%, var(--dark-blue) 100%); color: white; padding: 18px 25px; border-radius: 12px 12px 0 0; font-weight: 700; display: flex; align-items: center; gap: 10px;">
                                <span>🔹</span> {{ query.type }}
                            </div>
                            <div class="sql-code">{{ query.sql }}</div>
                        </div>
                        {% endfor %}
                    </div>
                    
                    <div id="analysis" class="tab-content">
                        <div style="padding: 25px;">
                            <div class="analysis-grid">
                                <div class="summary-item">
                                    <div class="summary-label">📊 Tables Found</div>
                                    <div class="summary-value">{{ result.components.tables | length }}</div>
                                </div>
                                <div class="summary-item">
                                    <div class="summary-label">⚡ Data Steps</div>
                                    <div class="summary-value">{{ result.components.data_steps | length }}</div>
                                </div>
                                <div class="summary-item">
                                    <div class="summary-label">🔧 Procedures</div>
                                    <div class="summary-value">{{ result.components.procedures | length }}</div>
                                </div>
                                <div class="summary-item">
                                    <div class="summary-label">📈 Variables</div>
                                    <div class="summary-value">{{ result.components.variables | length }}</div>
                                </div>
                            </div>
                            
                            {% if result.components.table_dependencies %}
                            <div style="margin-top: 35px;">
                                <h4 style="color: var(--primary-blue); margin-bottom: 20px; font-size: 1.3rem; display: flex; align-items: center; gap: 10px;">
                                    <span>🔗</span> Table Dependencies
                                </h4>
                                {% for table, deps in result.components.table_dependencies.items() %}
                                <div class="summary-item">
                                    <div class="summary-label">{{ table }}</div>
                                    <div class="summary-value">{{ deps | join(', ') }}</div>
                                </div>
                                {% endfor %}
                            </div>
                            {% endif %}
                        </div>
                    </div>
                </div>
                {% else %}
                <div class="sql-output-container">
                    <div class="sql-code" style="text-align: center; padding: 80px 20px; color: #888; display: flex; flex-direction: column; justify-content: center; align-items: center; background: linear-gradient(135deg, #1a1b26 0%, #2a2b3d 100%);">
                        <div style="font-size: 5rem; margin-bottom: 20px; opacity: 0.7;">⚡</div>
                        <div style="font-size: 1.5rem; font-weight: 600; margin-bottom: 15px; color: #c0caf5;">SQL Output Ready</div>
                        <div style="font-size: 1rem; opacity: 0.8; max-width: 400px; line-height: 1.6;">Enter SAS code and click "Convert to SQL" to see the magic happen! ✨</div>
                    </div>
                </div>
                {% endif %}
                
                {% if error %}
                <div class="result error" style="margin-top: 25px;">
                    <h4 style="color: var(--primary-red); margin-bottom: 15px; display: flex; align-items: center; gap: 10px;">❌ Conversion Error</h4>
                    <p style="background: #ffebee; padding: 15px; border-radius: 8px; border-left: 4px solid var(--primary-red);">{{ error }}</p>
                </div>
                {% endif %}
            </div>
        </div>
    </div>

    <script>
        function showTab(tabName) {
            // Hide all tab contents
            var tabContents = document.getElementsByClassName('tab-content');
            for (var i = 0; i < tabContents.length; i++) {
                tabContents[i].classList.remove('active');
            }
            
            // Remove active class from all tabs
            var tabs = document.getElementsByClassName('tab');
            for (var i = 0; i < tabs.length; i++) {
                tabs[i].classList.remove('active');
            }
            
            // Show selected tab
            document.getElementById(tabName).classList.add('active');
            event.currentTarget.classList.add('active');
        }
        
        function resetForm() {
            document.getElementById('sasCodeTextarea').value = '';
            document.getElementById('sasFileInput').value = '';
            document.getElementById('conversionForm').reset();
            document.getElementById('fileUploadContainer').innerHTML = `
                <div class="upload-icon">📁</div>
                <div class="upload-text">Click to browse or drag & drop SAS file</div>
                <div class="upload-subtext">Supports .sas files up to 10MB</div>
            `;
            
            // Clear any existing results
            var results = document.querySelector('.sql-output-container .sql-code');
            if (results && !results.innerHTML.includes('SQL Output Ready')) {
                results.innerHTML = `
                    <div style="text-align: center; padding: 80px 20px; color: #888; display: flex; flex-direction: column; justify-content: center; align-items: center;">
                        <div style="font-size: 5rem; margin-bottom: 20px; opacity: 0.7;">⚡</div>
                        <div style="font-size: 1.5rem; font-weight: 600; margin-bottom: 15px; color: #c0caf5;">SQL Output Ready</div>
                        <div style="font-size: 1rem; opacity: 0.8; max-width: 400px; line-height: 1.6;">Enter SAS code and click "Convert to SQL" to see the magic happen! ✨</div>
                    </div>
                `;
            }
            
            // Reset to first tab
            showTab('consolidated');
        }
        
        function downloadSQL() {
            const sqlContent = document.querySelector('#consolidated .sql-code').innerText;
            const blob = new Blob([sqlContent], { type: 'text/plain' });
            const url = URL.createObjectURL(blob);
            const a = document.createElement('a');
            a.href = url;
            a.download = 'converted_sql.txt';
            document.body.appendChild(a);
            a.click();
            document.body.removeChild(a);
            URL.revokeObjectURL(url);
        }
        
        function handleFileSelect(files) {
            if (files.length > 0) {
                const file = files[0];
                if (file.name.endsWith('.sas')) {
                    const reader = new FileReader();
                    reader.onload = function(e) {
                        document.getElementById('sasCodeTextarea').value = e.target.result;
                        document.getElementById('fileUploadContainer').innerHTML = `
                            <div class="upload-icon">✅</div>
                            <div class="upload-text" style="color: var(--success-green);">File loaded: ${file.name}</div>
                            <div class="upload-subtext">${(file.size / 1024).toFixed(2)} KB</div>
                        `;
                    };
                    reader.readAsText(file);
                } else {
                    alert('Please select a valid .sas file');
                    document.getElementById('sasFileInput').value = '';
                }
            }
        }
        
        // Drag and drop functionality
        const fileUploadContainer = document.getElementById('fileUploadContainer');
        
        fileUploadContainer.addEventListener('dragover', function(e) {
            e.preventDefault();
            this.classList.add('dragover');
        });
        
        fileUploadContainer.addEventListener('dragleave', function(e) {
            e.preventDefault();
            this.classList.remove('dragover');
        });
        
        fileUploadContainer.addEventListener('drop', function(e) {
            e.preventDefault();
            this.classList.remove('dragover');
            const files = e.dataTransfer.files;
            handleFileSelect(files);
        });
        
        // Add conversion animation
        document.getElementById('conversionForm').addEventListener('submit', function() {
            const convertBtn = document.getElementById('convertBtn');
            convertBtn.classList.add('converting');
            convertBtn.innerHTML = '<span>⏳ Converting...</span>';
            setTimeout(() => {
                convertBtn.classList.remove('converting');
                convertBtn.innerHTML = '<span>🚀 Convert to SQL</span>';
            }, 2000);
        });
    </script>
</body>
</html>
"""

@app.route('/', methods=['GET', 'POST'])
def index():
    if request.method == 'POST':
        sas_code = request.form.get('sas_code', '')
        
        # Handle file upload
        if 'sas_file' in request.files:
            file = request.files['sas_file']
            if file and file.filename.endswith('.sas'):
                sas_code = file.read().decode('utf-8')
        
        processor = SASProcessor()
        result = processor.process_sas_code(sas_code)
        
        if result['success']:
            return render_template_string(HTML_TEMPLATE, 
                                       sas_code=sas_code, 
                                       result=result,
                                       error=None)
        else:
            return render_template_string(HTML_TEMPLATE,
                                       sas_code=sas_code,
                                       result=None,
                                       error=result['error'])
    
    return render_template_string(HTML_TEMPLATE, 
                               sas_code=None, 
                               result=None,
                               error=None)

@app.route('/download')
def download_sql():
    """Download the SQL as a text file"""
    sql_content = request.args.get('sql', '')
    
    # Create a file-like object in memory
    file_like = io.BytesIO(sql_content.encode('utf-8'))
    
    return send_file(
        file_like,
        as_attachment=True,
        download_name='converted_sql.txt',
        mimetype='text/plain'
    )

if __name__ == '__main__':
    app.run(debug=True, host='0.0.0.0', port=5000)
