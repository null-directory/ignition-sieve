import re    # pattern matching!
import ast   # (safe!) arbitrary code execution
import shlex # shell lexer - for spliting things with quotes
from functools import wraps

def genNamedTuplefromPattern(pattern, name='MatchNames'):
	"""Summary: Generate a Named Tuple definition from a compiled regex pattern.
	  Each capture group in the named tuple is a field of the new named tuple.
	  
	Example:
	  [NamedTupleFromPattern(*m) for m in pattern.findall(someString)]
	  
	Returns:
	 - Named tuple definition
	"""
	return namedtuple(	name, 
						' '.join([	n 
									for n,_ 
									in sorted(	pattern.groupindex.items(), 
												key=lambda x: x[1] 
						)]))
						

def datasetToListDict(dataset):
	header = [str(name) for name in dataset.getColumnNames()]
	try:
		return [dict(zip(header, row)) for row in zip(*dataset.data)]
	except:
		return [dict(zip(header, row)) for row in zip(*dataset.delegateDataset.data)]

		
def datasetToDictList(dataset):
	header = [str(name) for name in dataset.getColumnNames()]
	return dict(zip( header, [dataset.getColumnAsList(i) for i in range(len(header))] ))

def gatherKeys(data):
	keys = set()
	for row in data:
		keys.update(row)
	return sorted(list(keys))

def listDictToDataset(data, keys=None):
	# gather the keys, in case there are voids in the data
	if not keys:
		keys = gatherKeys(data)
	
	columns = dict((key,[]) for key in keys)
	for row in data:
		for key in keys:
			columns[key].append( row.get(key, None) )

	aligned = zip(*[columns[key] for key in keys])
		
	return system.dataset.toDataSet(keys, aligned)
		
		
def continueVisiting(handled=False):
	"""because writing things is hard"""
	def followUp(function):
	
		@wraps(function)
		def visit(self, node):
			function(self, node)
			self.generic_visit(node, handled)
	
		return visit
	return followUp


class Validator(ast.NodeVisitor):
			
	TRUSTED_IMPORTS = set(['math', 'fnmatch', 're', 'collections'])
	TRUSTED_BUILTINS = set(['None','abs', 'all', 'any', 'bin', 'bool', 'bytearray', 'cmp', 'complex', 'dict', 
							'divmod', 'enumerate', 'filter', 'float', 'format', 'frozenset', 'hash', 
							'hex', 'int', 'iter', 'len', 'list', 'long', 'map', 'max', 'min', 'next', 
							'oct', 'pow', 'range', 'reduce', 'reversed', 'round', 'set', 'slice', 
							'sorted', 'str', 'sum', 'tuple', 'xrange', 'zip',
							
							'True', 'False' # turns out this has to be called out directly! It's a *name*...
							])
	
	
	def __init__(self, trustedScopes=set(), requiredImports=set(), debug=False):
		self._debug = debug
		self.indentLevel = 0
		self.disallowed = []
		self.currentAttribute = []
		self.requiredImports = set(self.TRUSTED_IMPORTS).union(requiredImports)		
		self.__trustedScopes__ = self.requiredImports.union(trustedScopes)
		
		self.LOCAL_VARIABLES = set()
		# At some point add a stack here for variables to mask more securely...
		
		# helpers for allowing special cases like local variables
		self.assignmentNodeChildren = None
		self.iterNodeChildren = None
		
		super(type(self),self).__init__()
	
	
	def nn(self,node):
		return type(node).__name__

	def _nnPrint(self, node, details='', columnPadding=28, indent='  '):
		formatString = '%s%%-%ds' % (indent*self.indentLevel, columnPadding - len(indent)*self.indentLevel)
		if self._debug:
			print formatString % self.nn(node), details
									
	def generic_visit(self, node, handled=False):
		if not handled:	self._nnPrint ( node , '...')
		self.indentLevel += 1
		super(type(self),self).generic_visit(node)
		
		if isinstance(node, (ast.For, ast.ListComp)):
			self.iterNodeChildren = None

		self.indentLevel -= 1
	
	def visit_Load(self, node): pass
	
	def visit_Lambda(self, node):
		self.disallowed.append(node)
	
	@continueVisiting(True)
	def visit_Assign(self, node):
		"""Allow an assignment to local scoped variables if NOT global."""
		self.assignmentNodeChildren = set(child for child in ast.iter_child_nodes(node))
	
	@continueVisiting(True)
	def visit_Attribute(self, node):
		self.currentAttribute.append(node.attr)
		self._nnPrint( node, '%s' % (node.attr) )
	

	
	def _visit_iter_node(self, node, allowedNodeTypes):
		self._nnPrint( node )
		self.iterNodeChildren = set(child 
									for child 
									in ast.iter_child_nodes(node) 
									if isinstance(child, allowedNodeTypes) )
	@continueVisiting(True)
	def visit_For(self, node):
		self._visit_iter_node(node, (ast.Name, ast.Tuple) )
		
	@continueVisiting(True)
	def visit_ListComp(self, node):
		self._visit_iter_node(node, (ast.Name, ast.Tuple, ast.comprehension) )
	
	def visit_iter_nested_node(self,node):
		self._nnPrint( node )
		if node in self.iterNodeChildren:
			self.iterNodeChildren.remove(node)
			self.iterNodeChildren.update(set(child 
										 for child 
										 in ast.iter_child_nodes(node) 
										 if isinstance(child, (ast.Name, ast.Tuple)) ))		
	
	@continueVisiting(True)	
	def visit_comprehension(self,node):
		self.visit_iter_nested_node(node)
		
	@continueVisiting(True)
	def visit_Tuple(self, node):	
		self.visit_iter_nested_node(node)							     
	
	
	@continueVisiting(True)
	def visit_Name(self, node):
		self.currentAttribute.append(node.id)
		fullyQualified = '.'.join(reversed(self.currentAttribute))
		self._nnPrint( node, '%s --> %s' % (node.id, fullyQualified) )
		
		if not self.checkScopeAllowed(reversed(self.currentAttribute)):	
			if '.' in fullyQualified \
				or fullyQualified in self.TRUSTED_BUILTINS:
				
				self.disallowed.append(fullyQualified)
				
		
			# allow assignments in iterators
			elif self.iterNodeChildren:
				if node in self.iterNodeChildren:
					self.iterNodeChildren.remove(node)
					
					# naive pass - just accept the name
					self.LOCAL_VARIABLES.add(node.id)
				
		
		
			# strictly allow assignments that are single-label			
			elif self.assignmentNodeChildren and node in self.assignmentNodeChildren \
				and	any([isinstance(child, ast.Store) for  child in ast.iter_child_nodes(node) ]) :
				
				self.LOCAL_VARIABLES.add(fullyQualified)
				
			else:
				self.disallowed.append(fullyQualified)
		else:
			rootObj = self.currentAttribute[-1]
			if rootObj in Validator.TRUSTED_IMPORTS:
				self.requiredImports.add(rootObj)
		
		# clear for the next
		self.currentAttribute = []
		self.assignmentNodeChildren = None

	def checkScopeAllowed(self, attributeList):
		fqn = []
		
		for name in attributeList:
			fqn.append(name)
			if '.'.join(fqn) in self.LOCAL_VARIABLES.union(self.__trustedScopes__):
				return True
		else:
			if len(fqn) == 1 and fqn[0] in self.LOCAL_VARIABLES.union(self.TRUSTED_BUILTINS):
				return True	
			return False

	@classmethod
	def validateScript(cls, script, expectedVariables):
		"""Use the Validator to ensure only (reasonably) trusted extensions are allowed."""
			
		code = compile(script, "<string>", "exec", ast.PyCF_ONLY_AST)
		
		validation = Validator(trustedScopes=expectedVariables)
		validation.visit(code)

		return validation



class Resolver(object):
	def __init__(self, script, parameters):
		self.script = script
		self.parameters = parameters
		self.scoped_references = ['d']
		
		self._resolveColumnReferences()
		self._resolveParameters()
		self._genFunction()
	
	def _resolveColumnReferences(self):
		
		def sanitizeColumnName(string):
			return re.sub('["\']', '', string)
			
		pattern = re.compile("""
		\{(?P<label>
			(?P<reference>[a-zA-Z _0-9]+?)           # Capture all ungreedy, in case a period is in the name.
			(?:\[(?P<anchor>[-0-9]+)\])? # Leave the option for referencing off anchors
			#(?:\.(?P<field>?????))  # Field is not implemented (working off the column's row value)
		)\}
		""", re.X + re.M)
				
		MatchNames = genNamedTuplefromPattern(pattern)
		matches = [MatchNames(*m) for m in pattern.findall(self.script)]
		if not matches:
			return self.script		
		
		for m in matches:
			if m.anchor:
				raise NotImplementedError('Slicing back to other anchors is not built yet. Pure PoC prep, sorry.')
			varname = sanitizeColumnName(m.reference)
			self.script = self.script.replace('{%s}' % m.label, 'd["%s"]' % (varname, m.reference))
			
	
#	def _resolveParameters(self):
#		
#		def sanitizeString(string):
#			return re.sub('[^\w]', '_', string)
#		
#		pattern = re.compile("""
#			(?P<label>
#				(?P<reference>\w+)   # Capture all ungreedy, in case a period is in the name.
#				(?:(?:\s*=\s*)       # key-value separator
#				(?P<value>[^,\n]+)   # Value 
#			))
#		""", re.X + re.M)
#		
#		MatchNames = genNamedTuplefromPattern(pattern)
#		
#		matches = [MatchNames(*m) for m in pattern.findall(self.parameters)]
#		
#		if not matches:
#			self.parameters={}
#		
#		parameters = {}
#		for m in matches:
#			varname = sanitizeString(m.reference)
#			try:
#				parameters[varname] = ast.literal_eval(m.value)
#			except ValueError:
#				parameters[varname] = str(m.value)
#						
#		# keeping the function paradigm for more reactive bindings later
#		self.parameters = dict([(p, lambda x=v:x) for p,v in parameters.items()])


	def _resolveParameters(self):
		"""Strictly named parameters are allowed here. 
		As a result, we can take it as given that there will be an '=' for each.
		
		We assume here that there are no '=' in the middle of strings or something like that, though.
		That'll either break the engine or submit a bogus value for that parameter.
		"""
		parameterString = self.parameters
		splitString = '='
		
		splitter = shlex.shlex(parameterString, posix=True)
		splitter.whitespace += ','
		splitter.whitespace_split = True
		varDict = {}
		
		varDecs = []
		tokenEntries = list(splitter)
		assignmentIndexes = [i 
							 for i,entry 
							 in enumerate(tokenEntries)
							 if '=' in entry] + [len(tokenEntries)]
		varDecs = [','.join(tokenEntries[assignmentIndexes[i]:assignmentIndexes[i+1]])
				   for i 
				   in range(len(assignmentIndexes)-1)]		
		
		for entry in varDecs:
			splitIX = entry.index(splitString)
			key = entry[:splitIX]
			try:
				value = ast.literal_eval( entry[splitIX+1:] )
			except Exception, err:
				value = entry[splitIX+1:]
			varDict[key] = value
		
		self.parameters = dict([(p, lambda x=v:x) for p,v in varDict.items()])


			
	def _genFunction(self):
		
		validation = Validator.validateScript(self.script, self.scoped_references + self.parameters.keys())
		if validation.disallowed:
			raise SyntaxError('The provided script failed validation on %s' % str(validation.disallowed))
		
		validatedImports = validation.requiredImports
		
		if not '\n' in self.script.strip() and not self.script.strip().startswith('return'):
			self.script = 'return ' + self.script.strip()
			
		# generate the function call
		# and wrap that call around it to give scope to the resolved variables
		#	The global state effectively closures the references variable.
		#	At run time, the comprehension resolves the actual current values
		#	and then applies them to the script.
		#	
		#	The validator returns the needed imports, if any.
		
		script = """
def generate_function():
	import %(imports)s
	def custom_script(%(default_references)s, %(parameters)s):
		%(script)s

	def resolved_parameters(%(default_references)s):
		custom_variables = dict([(k,f()) for k,f in references.items()])
		# Apply the resolved references to the function provided
		return custom_script(%(default_references)s,**custom_variables)
	
	return resolved_parameters
		""" % {'imports': ', '.join(validatedImports), 
			   'default_references': ', '.join(self.scoped_references),
			   'parameters': ', '.join(sorted(self.parameters)), 
			   'script': '\n\t\t'.join(self.script.splitlines()) 
			  }
		
		wrapped_code = compile(script,'<string>', 'exec')
	
		globals = dict(references=self.parameters)
		locals  = dict()
		exec wrapped_code in globals, locals
				
		self.function = locals['generate_function']() 


class Step(object):		
	def __init__(self, config, data):
		self.data = data
	
		self.code = config['code']
		self.parameters = config['variables']
		self.resultLabels = config['resultLabels'].split(',')
		self.operation = config['operation']
		self.varDict = self._resolveVariables()

		self.function = Resolver(self.code, self.parameters).function


	def _resolveVariables(self, parameterString='', splitString='='):
		if not parameterString:
			parameterString = self.parameters
			
		splitter = shlex.shlex(parameterString, posix=True)
		splitter.whitespace += ','
		splitter.whitespace_split = True
		varDict = {}
		
		varDecs = []
		tokenEntries = list(splitter)
		assignmentIndexes = [i 
							 for i,entry 
							 in enumerate(tokenEntries)
							 if '=' in entry] + [len(tokenEntries)]
		varDecs = [','.join(tokenEntries[assignmentIndexes[i]:assignmentIndexes[i+1]])
				   for i 
				   in range(len(assignmentIndexes)-1)]		
		
		for entry in varDecs:
			splitIX = entry.index(splitString)
			key = entry[:splitIX]
			try:
				value = ast.literal_eval( entry[splitIX+1:] )
			except Exception, err:
				value = entry[splitIX+1:]
			varDict[key] = value
		
		return varDict

	
	def applyStep(self):
		operationMapping = {'Row':              self.mapOntoRows
						,	'RowRemove':        self.removeRows
						,	'Bulk':             self.mapAcrossWindows
						,	'BulkColumn':       self.mapAcrossColumn
						,	'BulkRemove':       self.removeWindows
						,	'SplitIntoColumns': self.splitIntoColumns
						,	'FilterColumns':    self.filterColumns	
			}
		return operationMapping[self.operation]()


	def mapOntoRows(self):
		results = [None] * len(self.data)
		for i in range(len(self.data)):
			results[i] = self.function(self.data[i])
		
		self.mergeResults(results)
		return results

	def mapAcrossColumn(self, window=None):
		if window is None and 'columnName' in self.varDict:
			window = self.varDict['columnName']
		
		windowData = self._getWindowData(window)
		
		results = self.function(windowData)
		
		self.mergeResults(results)
		return results
					
	
	def mapAcrossWindows(self, windows=None, rank=False):
		"""If windows equals None, then the function is essentially applied to the whole dataset.
		If a columnName has been defined, then the results are filtered to it instead.
		"""
		if windows is None and 'columnName' in self.varDict:
			windows = self.varDict['columnName']
		
		windows = self._getWindowData(windows, rank)
		
		bulkWindows = self._sliceIntoWindows(windows, rank)
		
		windowResults = {}
		for label,windowData in bulkWindows.items():
			windowResults[label] = self.function(windowData)
		
		results = [windowResults[label] for label in windows]
			
		self.mergeResults(results)	
		return results
		

	def mergeResults(self, results):
		"""Results is the same length as the data, same width as resultLabels."""
		if not results: return
		
		for i in range(len(self.data)):			
			if isinstance(results[i], tuple) and len(results[i] > 1):
				for resultLabel, resultData in zip(self.resultLabels, results[i]):
					self.data[i][resultLabel] = resultData
			elif isinstance(results[i], dict):
				self.data[i] = dict(self.data[i].items() + results[i].items()) 
			else:
				self.data[i][self.resultLabels[0]] = results[i]		

	
	def removeRows(self):
		self.data = [ row
					  for row
					  in self.data
					  if self.function(row)]

	
	def filterColumns(self):
		columnList = set( ast.literal_eval( self.code ) )
		self.data = [dict((key,value) for key,value in row.items() if key in columnList)
					 for row
					 in self.data]
	
	
	def removeWindows(self):
		windows = self._getWindowData(windows, rank)
		
		bulkWindows = self._sliceIntoWindows(windows, rank)
		
		windowResults = {}
		for label,windowData in bulkWindows.items():
			windowResults[label] = self.function(windowData)	
		
		self.data = [row 
					 for row,label 
					 in zip(self.data, windows) 
					 if windowResults[label]]
			
			
	def splitIntoColumns(self):
		splitString = self.varDict['splitString']
	
		results = [{}] * len(self.data)
		
		for i in range(len(self.data)):
			results[i] = self._resolveVariables(self.function(self.data[i]), splitString)
		
		self.mergeResults(results)
		return results	
	
	
	def _getWindowData(self, windows=None, rank=False):
		if not windows: windows = [None]*len(self.data)
		
		if isinstance(windows, (str,unicode)):
			windows = [row.get(windows, None) for row in self.data]
			
		if rank:
			rank = 0
			lastLabel = None
			rankedWindows = []
			for label in windows:
				if label <> lastLabel:
					rank += 1
					lastLabel = label
				rankedWindows.append(rank)
			windows = rankedWindows		
		
		return windows

	def _sliceIntoWindows(self, windows=None, rank=False):
		windows = self._getWindowData(windows, rank)
		
		result = dict([(label, {}) for label in windows])
		
		for row,label in zip(self.data, windows):
			for key,value in row.items():
				try:
					result[label][key].append(value)
				except KeyError:
					result[label][key] = [value]	
					
		return result


