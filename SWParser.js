var ExExp = ExExp || (function () {
	'use strict';
	var rollOperator,
	parseExpression = function (s, until) {
		var untilCb = (typeof until === "function" ? until : function (tok) {
			return (tok == until);
		})
		// constants
		,
		ARG_COUNTS = {
			'abs': 1,
			'ceil': 1,
			'floor': 1,
			'round': 1,
			'max': [1],
			'min': [1]
		},
		BINARY_PRECEDENCE = {
			'?': 1,
			':': 2,
			'||': 3,
			'&&': 4,
			'|': 5,
			'^': 6,
			'&': 7,
			'=': 8,
			'==': 8,
			'!=': 8,
			'>=': 9,
			'>': 9,
			'<': 9,
			'<=': 9,
			'<<': 10,
			'>>': 10,
			'+': 11,
			'-': 11,
			'*': 12,
			'/': 12,
			'%': 12,
			'**': 14,
			't': 98,
			'd': 99
		},
		UNARY_PRECEDENCE = {
			'!': 13,
			'~': 13,
			'-': 13
		},
		CLOSERS = {
			'(': ")",
			'{': "}"
		}
		// local variables
		,
		operators = [{
			'precedence': 0
		}],
		operands = [],
		tableExp,
		m,
		err,
		operand;
		// helper functions
		function getToken(s) {
			var m;
			if (!s) {
				return s;
			}

			function retVal(tokType, matchObj) {
				return {
					'type': tokType,
					'text': matchObj[0],
					'match': matchObj
				};
			}
			m = s.match(/^\s+/);
			if (m) {
				return retVal("whitespace", m);
			}
			m = s.match(/^(abs|ceil|floor|round|max|min)[(]/);
			if (m) {
				return retVal("function", m);
			}
			m = s.match(/^[({]/);
			if (m) {
				return retVal("opengroup", m);
			}
			m = s.match(/^[)}]/);
			if (m) {
				return retVal("closegroup", m);
			}
			m = s.match(/^((\d+(\.\d+)?)|(\.\d+))/);
			if (m) {
				return retVal("number", m);
			}
			m = s.match(/^['"]/);
			if (m) {
				return retVal("quote", m);
			}
			m = s.match(/^((\|\|)|(&&)|(==)|(!=)|(>=)|(<=)|(<<)|(>>)|(\*\*)|[?:|\^&=><%!~])/);
			if (m) {
				return retVal("extoperator", m);
			}
			m = s.match(/^[\-+*\/td]/);
			if (m) {
				return retVal("baseoperator", m);
			}
			m = s.match(/^\[([^\]]+)\]/);
			if (m) {
				return retVal("label", m);
			}
			m = s.match(/^\$\{([^'"\($\}][^}]*)\}/);
			if (m) {
				return retVal("variable", m);
			}
			m = s.match(/^\$\{/);
			if (m) {
				return retVal("openvariable", m);
			}
			return {
				'type': "raw",
				'text': s.charAt(0)
			};
		}

		function popToken(state) {
			state.tok = getToken(state.s);
			if (state.tok) {
				state.s = state.s.substring(state.tok.text.length);
			}
			return state;
		}

		function popString(state, delim) {
			var i = -1,
			j = i,
			retval;
			// find first index of delim not preceded by an odd number of backslashes
			while (((i - j) & 1) === 0) {
				i = state.s.indexOf(delim, i + 1);
				if (i < 0) {
					return;
				}
				j = i - 1;
				while ((j >= 0) && (state.s.charAt(j) === '\\')) {
					j--;
				}
			}
			// unescape string to be returned
			function replaceEscapes(s) {
				return s.replace(/\\n/g, "\n").replace(/\\r/g, "\r").replace(/\\t/g, "\t").replace(/\\/g, "");
			}
			retval = state.s.substring(0, i).split("\\\\").map(replaceEscapes).join("\\");
			// point state delim, then pop off the delimiter token
			state.s = state.s.substring(i);
			popToken(state);
			return retval;
		}

		function popOperator() {
			var op = operators.pop(),
			right = operands.pop(),
			left,
			cond,
			datatype;
			if (op.unary) {
				operands.push({
					'type': (op.type === "baseoperator" ? "unop" : "unopex"),
					'datatype': right.datatype,
					'operator': op.text,
					'operand': right
				});
				return;
			}
			left = operands.pop();
			if (op.text !== ":") {
				if (op.text === "d" || op.text === "t") {
					datatype = "number";
				} else if (left.datatype === right.datatype) {
					datatype = left.datatype;
				} else if ((left.datatype === "string") || (right.datatype === "string")) {
					datatype = "string";
				}
				operands.push({
					'type': (op.type === "baseoperator" ? "binop" : "binopex"),
					'datatype': datatype,
					'operator': op.text,
					'left': left,
					'right': right,
					'mods': op.mods,
					'label': op.label
				});
				return;
			}
			op = operators.pop();
			if (op.text !== "?") {
				return "Error: Expected ? but got " + op.text;
			}
			cond = operands.pop();
			operands.push({
				'type': "cond",
				'cond': cond,
				'left': left,
				'right': right,
				'datatype': (left.datatype === right.datatype ? left.datatype : undefined)
			});
		}

		function pushOperator(op) {
			var err;
			op.precedence = (op.unary ? UNARY_PRECEDENCE[op.text] : BINARY_PRECEDENCE[op.text]) || 0;
			while (operators[operators.length - 1].precedence >= op.precedence) {
				err = popOperator();
				if (err) {
					return err;
				}
			}
			operators.push(op);
		}

		function argListUntil(tok) {
			return (tok === ',') || (tok === ')');
		}

		function parseHelper() {
			var err,
			func,
			argCounts,
			minArgs,
			maxArgs,
			str,
			args,
			argTree,
			opener,
			closer,
			operand,
			varExp;
			popToken(s);
			if (!s.tok) {
				return "Error: Unrecognized token: " + s.s.split(" ", 1)[0];
			}
			while (s.tok.type === "whitespace") {
				popToken(s);
				if (!s.tok) {
					return "Error: Unrecognized token: " + s.s.split(" ", 1)[0];
				}
			}
			switch (s.tok.type) {
				case "function":
					func = s.tok.match[1];
					argCounts = ARG_COUNTS[func];
					if (argCounts === undefined) {
						return "Error: Unrecognized function: " + func;
					}
					if (Array.isArray(argCounts)) {
						minArgs = argCounts[0];
						maxArgs = argCounts[1];
					} else {
						minArgs = argCounts;
						maxArgs = argCounts;
					}
					args = [];
					while ((s.tok) && (s.tok.text !== ')')) {
						argTree = parseExpression(s, argListUntil);
						if (typeof (argTree) === "string") {
							return argTree;
						} // error
						args.push(argTree);
						if (!s.tok) {
							return "Error: Unterminated function: " + func;
						}
						if (!argListUntil(s.tok.text)) {
							return "Error: Expected ',' or ')' to continue/close '" + func + "(', but got '" + s.tok.text + "'";
						}
					}
					if (minArgs < 0) {
						minArgs = args.length;
					}
					if (isNaN(maxArgs) || maxArgs < 0) {
						maxArgs = args.length;
					}
					if (args.length < minArgs) {
						return "Error: Function '" + func + "' requires at least " + minArgs + " argument(s)";
					}
					if (args.length > maxArgs) {
						return "Error: Function '" + func + "' requires at most " + maxArgs + " argument(s)";
					}
					operands.push({
						'type': "function",
						'datatype': "number",
						'function': func,
						'args': args
					});
					return;
				case "number":
					operands.push({
						'type': "number",
						'datatype': "number",
						'value': parseFloat(s.tok.text)
					});
					return;
				case "variable":
					operands.push({
						'type': "variable",
						'value': s.tok.match[1]
					});
					return;
				case "quote":
					str = popString(s, s.tok.text);
					if (typeof (str) !== "string") {
						return "Error: Unterminated string";
					}
					operands.push({
						'type': "string",
						'datatype': "string",
						'value': str
					});
					return;
				case "opengroup":
					opener = s.tok.text;
					closer = CLOSERS[opener];
					operand = parseExpression(s, closer);
					if (typeof (operand) === "string") {
						return operand;
					} // error
					operands.push(operand);
					if (s.tok.text !== closer) {
						return "Error: Expected '" + closer + "' to close '" + opener + "', but got '" + s.tok.text + "'";
					}
					return;
				case "openvariable":
					varExp = parseExpression(s, "}");
					if (typeof (varExp) === "string") {
						return varExp;
					} // error
					if (s.tok.text !== "}") {
						return "Error: Expected '}' to close '${', but got '" + s.tok.text + "'";
					}
					operands.push({
						'type': "variable",
						'value': varExp
					});
					return;
				case "extoperator":
				case "baseoperator":
					if (!UNARY_PRECEDENCE[s.tok.text]) {
						return "Error: " + s.tok.text + " is not a unary operator";
					}
					s.tok.unary = true;
					err = pushOperator(s.tok);
					if (err) {
						return err;
					}
					return parseHelper();
			}
			return "Error: Unrecognized token: " + s.tok.text + (s.tok.type === "raw" ? s.s.split(" ", 1)[0] : "");
		}
		// if we were given a string, construct a state object
		if (typeof (s) === "string") {
			s = {
				's': s
			};
		}
		// push operators and operands to their respective stacks, building sub-ASTs in the operand stack as needed
		err = parseHelper();
		if (err) {
			return err;
		}
		for (popToken(s) ;
		(s.tok) && (!untilCb(s.tok.text)) && ((until) || (s.tok.type !== "raw")) ; popToken(s)) {
			switch (s.tok.type) {
				case "extoperator":
				case "baseoperator":
					rollOperator = (s.tok.text === "d" ? s.tok : null);
					err = pushOperator(s.tok);
					if (err) {
						return err;
					}
					if ((rollOperator) && (s.s.charAt(0) === 'F')) {
						operands.push({
							'type': "rollspec",
							'value': "F"
						});
						s.s = s.s.substring(1);
					} else if (s.tok.text === "t") {
						if (s.s.charAt(0) !== '[') {
							return "Error: 't' operator requires '[table]' argument";
						}
						m = s.s.match(/^\[([^'"$(\]][^\]]*)\]/);
						if (m) {
							tableExp = m[1];
							s.s = s.s.substring(m[0].length);
						} else {
							s.s = s.s.substring(1);
							tableExp = parseExpression(s, "]");
							if (typeof (tableExp) === "string") {
								return tableExp;
							} // error
							if (s.tok.text !== "]") {
								return "Error: Expected ']' to close 't[', but got '" + s.tok.text + "'";
							}
						}
						operands.push({
							'type': "tablename",
							'value': tableExp
						});
					} else {
						err = parseHelper();
						if (err) {
							return err;
						}
					}
					if (rollOperator) {
						m = s.s.match(/^[acdfhkloprs0-9<=>!]+/);
						if (m) {
							rollOperator.mods = m[0];
							s.s = s.s.substring(m[0].length);
						}
					}
					break;
				case "label":
					if ((operators.length > 0) && (operators[operators.length - 1].text === "d")) {
						// set label on "d" operator instead of operand (e.g. "1d6[foo]" is "(1d6)[foo]", not "1d(6[foo])")
						operators[operators.length - 1].label = s.tok.match[1];
						break;
					}
					operand = operands.pop();
					if (operand) {
						operand.label = s.tok.match[1];
						operands.push(operand);
					}
					break;
			}
		}
		// no more input; collapse remaining operators and operands into a single AST
		while (operators.length > 1) {
			err = popOperator();
			if (err) {
				return err;
			}
		}
		return operands.pop();
	},
	write = function (s) {
		TAS.debug("EXEXP:" + s);
	},
	sendCommand = function (chunks, asts, evalResults, labels) {
		//infinite loop
		//TAS.debug("at sendCommand");
		//TAS.debug(chunks, asts, evalResults, labels);
		// constants
		var FUNCTION_FUNCTIONS = {
			'abs': Math.abs,
			'ceil': Math.ceil,
			'floor': Math.floor,
			'round': Math.round,
			'max': Math.max,
			'min': Math.min
		},
		BINARY_FUNCTIONS = {
			'||': function (x, y) {
				return x || y;
			},
			'&&': function (x, y) {
				return x && y;
			},
			'|': function (x, y) {
				return x | y;
			},
			'^': function (x, y) {
				return x ^ y;
			},
			'&': function (x, y) {
				return x & y;
			},
			'=': function (x, y) {
				return x == y;
			},
			'==': function (x, y) {
				return x == y;
			},
			'!=': function (x, y) {
				return x != y;
			},
			'>=': function (x, y) {
				return x >= y;
			},
			'>': function (x, y) {
				return x > y;
			},
			'<': function (x, y) {
				return x < y;
			},
			'<=': function (x, y) {
				return x <= y;
			},
			'<<': function (x, y) {
				return x << y;
			},
			'>>': function (x, y) {
				return x >> y;
			},
			'+': function (x, y) {
				return x + y;
			},
			'-': function (x, y) {
				return x - y;
			},
			'*': function (x, y) {
				return x * y;
			},
			'/': function (x, y) {
				return x / y;
			},
			'%': function (x, y) {
				return x % y;
			},
			'**': Math.pow,
			'd': function (x, y) {
				var retval = 0,
				i = 0;
				for (i = 0; i < x; i++) {
					retval += randomInteger(y);
				}
				return retval;
			}
		},
		UNARY_FUNCTIONS = {
			'!': function (x) {
				return !x;
			},
			'~': function (x) {
				return ~x;
			},
			'-': function (x) {
				return -x;
			}
		}
		// local variables
		,
		references = {},
		unevalRefs = [],
		evalReqs = [],
		i = 0,
		t,
		err,
		doSubstitution = false,
		label,
		newUneval = [],
		r,
		retval;
		// helper functions
		function lazyEval(t, labels, references, unevalRefs, evalReqs, force) {
			//alert(' at lazyEval, t: ' + t + ', t.type:'+t.type);
			var x,
			y,
			args = [],
			i = 0,
			forceSubtrees;
			if (t.label) {
				labels[t.label] = t;
			}
			switch (t.type) {
				case "number":
				case "rollspec":
					t.baseValid = true;
					return t;
				case "string":
					return t;
				case "tablename":
					if (typeof (t.value) !== "string") {
						x = lazyEval(t.value, labels, references, unevalRefs, evalReqs, true);
						if (typeof (x) === "string") {
							return x;
						} // error
						if (x.type === "number") {
							// number node; coerce to string
							x.value = String(x.value);
							x.type = "string";
						}
						if (x.type !== "string") {
							// unable to fully evaluate table name
							if (t.baseValid) {
								t.baseValid = false;
							}
							unevalRefs.push(t.value);
							return t;
						}
						// successfully evaluated table name
						t.value = x.value;
					}
					// if we got here, t.value is the name of a rollable table
					t.baseValid = true;
					return t;
				case "function":
					for (i = 0; i < t.args.length; i++) {
						x = lazyEval(t.args[i], labels, references, unevalRefs, evalReqs, true);
						if (typeof (x) === "string") {
							return x;
						} // error
						if (x.type === "string") {
							x.value = parseFloat(x.value);
							x.type = "number";
						}
						if (x.type !== "number") {
							// unable to fully evaluate argument
							if (t.baseValid) {
								t.baseValid = false;
							}
							return t;
						}
						args.push(x.value);
					}
					// successfully evaluated all arguments
					t.type = "number";
					t.datatype = "number";
					t.value = FUNCTION_FUNCTIONS[t["function"]].apply(args, args);
					for (i = 0; i < t.args.length; i++) {
						if (t.args[i].label) {
							labels[t.args[i].label] = t.args[i];
						}
					}
					delete t["function"];
					delete t.args;
					t.baseValid = true;
					return t;
				case "unop":
				case "unopex":
					force = force || (t.type !== "unop");
					x = lazyEval(t.operand, labels, references, unevalRefs, evalReqs, force);
					if (typeof (x) === "string") {
						return x;
					} // error
					if (force) {
						if (x.type !== "number") {
							// unable to fully evaluate operand
							if (t.baseValid) {
								t.baseValid = false;
							}
							return t;
						}
						// successfully evaluated operand
						t.type = "number";
						t.datatype = "number";
						t.value = UNARY_FUNCTIONS[t.operator](x.value);
						delete t.operator;
						if (t.operand.label) {
							labels[t.operand.label] = x;
						}
						delete t.operand;
						t.baseValid = true;
					} else {
						t.baseValid = x.baseValid;
					}
					return t;
				case "binop":
				case "binopex":
					force = force || (t.type !== "binop") || (t.left.datatype === "string") || (t.right.datatype === "string");
					forceSubtrees = force || (t.operator === "d") || (t.operator === "t");
					//TAS.debug('left is: ' + t.left + ', right is:' + t.right);
					x = lazyEval(t.left, labels, references, unevalRefs, evalReqs, forceSubtrees);
					y = lazyEval(t.right, labels, references, unevalRefs, evalReqs, forceSubtrees);
					//TAS.debug(x);
					//TAS.debug(y);
					force = true;
					/*********************didn't work until i commented out, now seems to have no effect ********************************/
					if (typeof x === "string") {
						//TAS.debug(x);
						return x;
					} // error
					if (typeof y === "string") {
						//TAS.debug(y);
						return y;
					} // error
					/****************************************************/
					if (force) {
						if ((x.type !== "number") && (x.type !== "string")) {
							// unable to fully evaluate left operand
							if (t.baseValid) {
								t.baseValid = false;
							}
							return t;
						}
						if ((y.type !== "number") && (y.type !== "string") && (y.type !== "rollspec") && (y.type !== "tablename")) {
							// unable to fully evaluate right operand
							if (t.baseValid) {
								t.baseValid = false;
							}
							return t;
						}
						if ((y.type === "rollspec") && (t.operator !== "d")) {
							return "Rollspec operand is only compatible with 'd' operator";
						}
						if ((t.operator === "t") && (y.type !== "tablename")) {
							return "'t' operator requires tablename operand";
						}
						// successfully evaluated both operands
						if ((t.operator === "t") || ((t.operator === "d") && (t.mods))) {
							// operator is rollable table or is roll with mods; must submit to base system for evaluation
							evalReqs.push(t);
							return t;
						}
						//TAS.debug('about to call binary');
						t.value = BINARY_FUNCTIONS[t.operator](x.value, y.value);
						delete t.operator;
						if (t.left.label) {
							labels[t.left.label] = x;
						}
						delete t.left;
						if (t.right.label) {
							labels[t.right.label] = y;
						}
						delete t.right;
						t.type = (typeof (t.value) === "string" ? "string" : "number");
						t.datatype = t.type;
						t.baseValid = (t.datatype === "number");
					} else if ((x.datatype === "number") && (y.datatype === "number")) {
						t.datatype = "number";
						t.baseValid = true;
					}
					return t;
				case "cond":
					x = lazyEval(t.cond, labels, references, unevalRefs, evalReqs, true);
					if (typeof (x) === "string") {
						return x;
					} // error
					if ((x.type !== "number") && (x.type !== "string")) {
						// unable to fully evaluate condition
						t.baseValid = false;
						return t;
					}
					// successfully evaluated condition; replace t with t.left or t.right as appropriate
					y = (x.value ? t.left : t.right);
					if (t.cond.label) {
						labels[t.cond.label] = x;
					}
					delete t.cond;
					delete t.left;
					delete t.right;
					_.each(y, function (k) {
						t[k] = y[k];
					});
					return lazyEval(t, labels, references, unevalRefs, evalReqs, force);
				case "variable":
					if (typeof (t.value) !== "string") {
						x = lazyEval(t.value, labels, references, unevalRefs, evalReqs, true);
						if (typeof (x) === "string") {
							return x;
						} // error
						if (x.type === "number") {
							// number node; coerce to string
							x.value = String(x.value);
							x.type = "string";
						}
						if (x.type !== "string") {
							// unable to fully evaluate variable name
							if (t.baseValid) {
								t.baseValid = false;
							}
							unevalRefs.push(t.value);
							return t;
						}
						// successfully evaluated variable name
						t.value = x.value;
					}
					// if we got here, t.value is the name of a variable
					if ((labels[t.value]) && ((labels[t.value].type === "string") || (labels[t.value].type === "number"))) {
						// variable exists and has been fully evaluated
						t.type = labels[t.value].type;
						t.datatype = labels[t.value].datatype;
						t.baseValid = labels[t.value].baseValid;
						t.value = labels[t.value].value;
					} else {
						// variable not yet defined or not yet fully evaluated
						if (!references[t.value]) {
							references[t.value] = [];
						}
						references[t.value].push(t);
						if (t.baseValid) {
							t.baseValid = false;
						}
					}
					return t;
				default:
					return "Unknown node type: " + t.type;
			}
		}

		function hasUnevaluatedLabels(t) {
			var i = 0;
			// base types: fully evaluated
			if ((t.type === "number") || (t.type === "string") || (t.type === "rollspec")) {
				return false;
			}
			// if we got here, node is unevaluated
			if (t.label) {
				return true;
			}
			// node has no label; check children
			switch (t.type) {
				case "function":
					for (i = 0; i < t.args.length; i++) {
						if (hasUnevaluatedLabels(t.args[i])) {
							return true;
						}
					}
					return false;
				case "tablename":
				case "variable":
					if (typeof (t.value) === "string") {
						return false;
					}
					return hasUnevaluatedLabels(t.value);
				case "unop":
				case "unopex":
					return hasUnevaluatedLabels(t.operand);
				case "cond":
					if (hasUnevaluatedLabels(t.cond)) {
						return true;
					}
					//don't fall through
					if (hasUnevaluatedLabels(t.left)) {
						return true;
					}
					return hasUnevaluatedLabels(t.right);
				case "binop":
				case "binopex":
					if (hasUnevaluatedLabels(t.left)) {
						return true;
					}
					return hasUnevaluatedLabels(t.right);
			}
		}

		function flattenAST(t) {
			var retval;
			switch (t.type) {
				case "number":
				case "rollspec":
					retval = t.value || 0;
					break;
				case "tablename":
					retval = "[" + t.value + "]";
					break;
				case "unop":
					retval = "(" + t.operator + flattenAST(t.operand) + ")";
					break;
				case "binop":
					retval = "(" + flattenAST(t.left) + t.operator + flattenAST(t.right) + (t.mods || "") + ")";
					if ((t.label) && (t.operator === "d")) {
						retval += "[" + t.label + "]";
					}
					break;
				default:
					return "Unknown node type: " + t.type;
			}
			return retval;
		}

		function astToCmd(t) {
			if (t.type === "string") {
				return t.value;
			}
			var retval = flattenAST(t);
			return retval;
		}

		function reportError(err) {
			ExExp.write("Error: " + err);
			return "";
		}
		//BEGIN
		// substitute in results of base evaluation
		for (i = 0; i < evalResults.length; i++) {
			t = evalResults[i][0];
			delete t.operator;
			delete t.left;
			delete t.right;
			t.type = "number";
			t.datatype = "number";
			t.value = evalResults[i][1];
			t.baseValid = true;
		}
		// traverse ASTs, collapsing as much as possible
		for (i = 0; i < asts.length; i++) {
			if (asts[i].baseValid) {
				continue;
			} // can be handled by base expression evaluator
			if ((asts[i].type === "string") || (asts[i].type === "number")) {
				continue;
			} // tree is fully evaluated
			err = lazyEval(asts[i], labels, references, unevalRefs, evalReqs, false);
			if (typeof (err) === "string") {
				return reportError(err);
			}
		}
		// do variable substitution; repeat until we don't make any more progress
		doSubstitution = true;
		while (doSubstitution) {
			doSubstitution = false;
			// substitute in values for variables for which we already have names
			for (label in references) {
				if (references.hasOwnProperty(label)) {
					if (!labels[label]) {
						return reportError("Variable '" + label + "' not defined");
					}
					if ((labels[label].type !== "string") && (labels[label].type !== "number")) {
						// variable exists but not yet evaluated; try to evaluate
						err = lazyEval(labels[label], labels, references, unevalRefs, evalReqs, true);
						if (typeof (err) === "string") {
							return reportError(err);
						}
					} else if ((labels[label].type === "string") || (labels[label].type === "number")) {
						// variable fully evaluated; substitute it in
						for (i = 0; i < references[label].length; i++) {
							references[label][i].type = labels[label].type;
							references[label][i].datatype = labels[label].datatype;
							references[label][i].value = labels[label].value;
							references[label][i].baseValid = labels[label].baseValid;
						}
						delete references[label];
						doSubstitution = true;
					}
				}
			}
			// try to get names for variables and tables with unevaluated names
			while (unevalRefs.length > 0) {
				r = lazyEval(unevalRefs.shift(), labels, references, unevalRefs, evalReqs, true);
				if (typeof (r) === "string") {
					return reportError(err);
				}
				if ((r.type === "string") || (r.type === "number")) {
					doSubstitution = true;
				} else {
					newUneval.push(r);
				}
			}
			unevalRefs = newUneval;
		}
		// flatten fully evaluated ASTs into strings and splice into chunks
		for (i = asts.length - 1; i >= 0; i--) {
			if ((!asts[i].baseValid) && (asts[i].type !== "number") && (asts[i].type !== "string")) {
				continue;
			}
			if ((unevalRefs.length > 0) & (hasUnevaluatedLabels(asts[i]))) {
				continue;
			}
			chunks.splice(i, 2, (chunks[i] || "") + astToCmd(asts.splice(i, 1)[0]) + (chunks[i + 1] || ""));
		}
		if (evalReqs.length > 0) {
			TAS.error("Cannot evaluate");
			return "";
		}
		if (asts.length > 0) {
			// need to finish evaluating some ASTs; recurse directly
			//TAS.debug("sendCommand (recurse), asts.length=" + asts.length + ", asts[0].baseValid=" + asts[0].baseValid + ", asts[0].type=" + asts[0].type);
			if (!(asts.length === 1 && asts[0].type === "binop")) {
				// HACK! minus (probably) in front; no math needed
				return sendCommand(chunks, asts, [], labels);
			}
		}
		// if we got here, we're done evaluating everything; submit results
		retval = chunks.join("");
		return retval;
	},
	handleExpression = function (msg) {
		//replace spaces. replace "-" in front with "0-", replace "(-" with "(0-"
		//also replace leading + with '', and replace (+  with (0+
		var chunks = [],
		asts = [],
		cmd,
		state,
		ast;
		msg = msg.replace(/\s/g, '').replace(/^-/, '0-').replace(/\(-/g, '(0-').replace(/^\+/, '').replace(/\(\+/g, '(0+');
		cmd = msg;
		state = {
			's': cmd
		};
		//TAS.debug(msg);
		ast = parseExpression(state, null);
		//TAS.debug(ast);
		if (typeof (ast) === "string") {
			ExExp.write("could not parse" + msg);
			return "";
		}
		asts.push(ast);
		state.s = (state.tok) ? (state.tok.text + state.s) : state.s;
		//  ((state.tok || {'text': ""}).text || "") + state.s;
		chunks.push(state.s);
		return sendCommand(chunks, asts, [], {});
	};
	return {
		write: write,
		handleExpression: handleExpression
	};
}());
var SWUtils = SWUtils || (function () {
	'use strict';
	/* for interaction with ExExp, and some basic utils that have nothing to do with Pathfinder rules. */
	/** Determines if string can be evaluated to a number
	* ensures:  no macro calls, dropdowns, or keep highest/lowest more than 1
	* allows: floor, abs, kh1, kl1,  ceil, round, max, min
	*@param {string} preeval string to examine
	*@returns {bool} true if string will evaluate to a number.
	*/
	var validNumericStr = function (preeval) {
		var anyIllegal = preeval.match(/\||\?|&|\{|\}|k[h,l][^1]/);
		if (anyIllegal) {
			return false;
		}
		anyIllegal = preeval.replace(/floor|ceil|round|abs|max|min|kh1|kl1/g, '');
		anyIllegal = anyIllegal.match(/[a-zA-Z]/);
		if (anyIllegal) {
			return false;
		}
		return true;
	},
	/** searches a string for @{attribute} and replaces those with their values, passes result to the callback
	* if error then passes null
	* @param {string} stringToSearch = string containing one or more @{fieldname}
	* @param {function(string)} callback when done passes resultant string to callback
	*/
	findAndReplaceFields = function (stringToSearch, callback) {
		var fieldnames ;
		if (typeof callback !== "function") {
			return;
		}
		if (!stringToSearch) {
			callback(null);
			return;
		}
		try {
			stringToSearch = stringToSearch.split("selected|").join("");
			stringToSearch = stringToSearch.split("target|").join("");
			fieldnames = stringToSearch.match(/\@\{[^}]+\}/g);
			if (!fieldnames) {
				callback(stringToSearch);
				return;
			}
			fieldnames=fieldnames.sort();
			fieldnames = _.uniq(fieldnames,true);
			fieldnames = _.map(fieldnames,function(field){
				return field.slice(2,-1);
			});
			getAttrs(fieldnames, function (values) {
				var evalstr = stringToSearch, innermatches=null,initialsplit;
				try {
					_.each(fieldnames,function(field){
						//evalstr = evalstr.replace(  new RegExp(escapeForRegExp('@{'+field+'}'),'g'), values[field]);
						initialsplit = evalstr.split('@{'+field+'}');
						evalstr = initialsplit.join(values[field]);
					});
					innermatches=evalstr.match(/\@\{[^}]+\}/g);
				} catch (err2) {
					TAS.error("findAndReplaceFields", err2);
					evalstr = null;
				} finally {
					if (innermatches) {
						findAndReplaceFields(evalstr,callback);
					} else {
						callback(evalstr);
					}
				}
			});
		} catch (err) {
			TAS.error("findAndReplaceFields", err);
			callback(null);
		}
	},
	/** Replaces kl1 and kh1 with min and max
	* example: replaces {x,y}kh1 with min(x,y)
	* @param {string} str the string to search
	* @returns {string} the resultant string after performing the replace
	*/
	convertKL1KH1toMinMax = function (str) {
		var matches;
		//TAS.debug("at convertKL1KH1toMinMax for "+str) ;
		if (str) {
			matches = str.match(/(\{[^}]+\})(kh1|kl1)(?!.*\1)/g);
			//TAS.debug("matches are:",matches);
			if (matches && matches.length > 0) {
				str = _.reduce(matches, function (memo, match) {
					var isMin = /kl1$/.test(match),
					isMax = /kh1$/.test(match),
					newFunc = isMin ? "min" : (isMax ? "max" : ""),
					newMatch = match.slice(1, match.length - 4),
					replaceStr = newFunc + "(" + newMatch + ")";
					return memo.replace(match, replaceStr);
				}, str);
			}
		}
		return str;
	},
	/** Reads in the string, evaluates it to a single number, passes that number to a callback
	* calls callback with: the number, 0 (if exprStr empty), or null if an error is encountered
	*@param {string} exprStr A string containing a mathematical expression, possibly containing references to fields such as @{myfield}
	*@param {function(Number)} callback a function taking one parameter - could be int or float
	*/
	evaluateExpression = function (exprStr, callback) {
		var bmatches1 = 0, bmatches2 = 0, pmatches1 = 0, pmatches2 = 0, smatches1 = 0, smatches2 = 0;
		if (typeof callback !== "function") {
			return;
		}
		if (exprStr === "" || exprStr === null || exprStr === undefined) {
			callback(0);
			return;
		}
		//verify that same number of parenthesis exists
		bmatches1 = (exprStr.match(/\(/g) || []).length;
		bmatches2 = (exprStr.match(/\)/g) || []).length;
		pmatches1 = (exprStr.match(/\{/g) || []).length;
		pmatches2 = (exprStr.match(/\}/g) || []).length;
		smatches1 = (exprStr.match(/\[/g) || []).length;
		smatches2 = (exprStr.match(/\]/g) || []).length;
		if (bmatches1 !== bmatches2 || pmatches1 !== pmatches2 || smatches1 !== smatches2) {
			TAS.warn("evaluateExpression: Mismatched brackets, cannot evaluate:" + exprStr);
			callback(null);
			return;
		}

		findAndReplaceFields(exprStr, function (replacedStr) {
			var evaluated,
			newexprStr;
			//TAS.debug("search and replace of " + exprStr + " resulted in " + replacedStr);
			if (replacedStr === null || replacedStr === undefined) {
				callback(null);
				return;
			}
			try {
				replacedStr = replacedStr.replace(/\s+/g, '').replace(/\[\[/g, "(").replace(/\]\]/g, ")").replace(/\[/g, "(").replace(/\]/g, ")");
				newexprStr = convertKL1KH1toMinMax(replacedStr);
				//TAS.debug("replacedStr is now "+newexprStr);
				if (newexprStr !== replacedStr) {
					replacedStr = newexprStr;
				}
				if (!isNaN(Number(replacedStr)) && isFinite(replacedStr)) {
					evaluated = parseFloat(replacedStr);
					if (!isNaN(evaluated)) {
						callback(evaluated);
						return;
					}
				}
				if (typeof replacedStr !== "undefined" && replacedStr !== null && validNumericStr(replacedStr)) {
					evaluated = ExExp.handleExpression(replacedStr);
					if (!isNaN(evaluated)) {
						callback(evaluated);
					} else {
						TAS.warn("cannot evaluate this to number: " + exprStr +" came back with " + replacedStr);
						callback(null);
					}
				} else {
					TAS.warn("cannot evaluate this to number: " + exprStr+" came back with " + replacedStr);
					callback(null);
				}
			} catch (err3) {
				TAS.error("error trying to convert to number:" + err3);
				callback(null);
			}
		});
	},
	/** evaluateAndSetNumber
	 * Examines the string in readField, and tests to see if it is a number
	 * if it's a number immediately write it to writeField.
	 * if not, then replace any @{field} references with numbers, and then evaluate it
	 * as a mathematical expression till we find a number.
	 *
	 * note this is NOT recursive, you can't point one field of
	 *
	 * @param {string} readField= field to read containing string to parse
	 * @param {string} writeField= field to write to
	 * @param {number} defaultVal= optional, default to set if we cannot evaluate the field. If not supplied assume 0
	 * @param {function} callback - function(newval, oldval, ischanged)
	 * @param {bool} silently if true set new val with {silent:true}
	 * @param {bool} dontSetErrorFlag if true and we could not evaluate, then set attribute named writeField+"_error" to 1
	 * @param {function} errcallback  call if there was an error parsing string function(newval, oldval, ischanged)
	 */
	evaluateAndSetNumber = function (readField, writeField, defaultVal, callback, silently, errcallback) {
		var 
		done = function (a, b, c,currError) {
			var donesetter={};
			if (currError){
				donesetter[writeField+'_error']=0;
				setAttrs(donesetter,{silent:true});
			}
			if (typeof callback === "function") {
				callback(a, b, c);
			}
		},
		errordone = function(a,b,c,currError){
			var donesetter={};
			//TAS.debug("leaving set of "+ writeField+" with old:"+b+", new:"+c+" is changed:"+ c+" and curreerror:"+currError);
			if (!currError){
				donesetter[writeField+'_error']=1;
				setAttrs(donesetter,{silent:true});				
			}
			if (typeof errcallback === "function") {
				errcallback(a, b, c);
			} else if (typeof callback === "function") {
				callback(a, b, c);
			}
		};
		getAttrs([readField, writeField, writeField+"_error"], function (values) {
			var setter = {},
			params = {},
			trueDefault=0, 
			currVal=0,
			isError=0,
			currError=0,
			isChanged=false,
			value=0;	
			try {
				if (silently){params.silent=true;}
				currError= parseInt(values[writeField+"_error"],10)||0;
				trueDefault = defaultVal || 0;
				currVal = parseInt(values[writeField], 10);
				value = Number(values[readField]);
				//check for blank
				if (typeof values[readField] === "undefined" || !values[readField] || values[readField]===null || values[readField]==="" ) {
					//if value of readField is blank then set to defaultval.
					value = trueDefault;
					if (currVal !== value || isNaN(currVal)) {
						setter[writeField] = value;
						setAttrs(setter, params, function () {
							done(value, currVal, true,currError);
						});
					} else {
						done(value, currVal, false,currError);
					}
				} else if (!isNaN(value)) {
					//check for number
					if (currVal !== value) {
						setter[writeField] = value;
						setAttrs(setter, params, function () {
							done(value, currVal, true);
						});
					} else {
						done(value, currVal, false,currError);
					}
				} else {
					//pass to evaluateExpression 
					evaluateExpression(values[readField], function (value2) {
						try {
							if (value2 === null || value2===undefined || isNaN(value2)) {
								isError=1;
								value2=trueDefault;
								//TAS.debug("setting "+ writeField+" to " +value2);
							}
							if (isNaN(currVal) || currVal !== value2) {
								setter[writeField] = value2;
							} 
							if (_.size(setter)>0){
								isChanged=true;
							}
						} catch (err2) {
							TAS.error("SWUtils.evaluateAndSetNumber error after call to evaluateExpression ", err2);
							isError=1;
						} finally {
							setAttrs(setter, params, function () {
								if (!isError){
									done(value2, currVal, isChanged,currError);
								} else {
									errordone(value2,currVal,isChanged,currError);
								}
							});

						}
					});
				}
			} catch (err) {
				TAS.error("SWUtils.evaluateAndSetNumber", err);
				setter[writeField+'_error']=1;
				setAttrs(setter,{silent:true},function(){errordone(value, currVal, false,currError);});
			}
		});
	},
	/** Reads dropdown value, determines attribute referenced, gets that attribute value, passes it to callback.
	* similar to evaluateAndSetNumber but uses a synchronus function to perform search and replace, and assumes the string is only one value not an expression.
	* necessary because some dropdowns have other text in the dropdowns, so we can't use the dropdown value exactly as is.
	* called by setDropdownValue
	* @param {string} readField the attribute name of dropdown we are looking at
	* @param {function} synchrousFindAttributeFunc reads in the value of the dropdown field, and returns the exact name of the attribute to look up (since some dropdowns have other text in value)
	* @param {function(int)} callback pass the value the dropdown selection represents
	*   exceptions: if readField is not found pass in "", if readField is 0 or starts with 0 pass in 0.
	*/
	getDropdownValue = function (readField, synchrousFindAttributeFunc, callback) {
		if (!readField || (callback && typeof callback !== "function") || typeof synchrousFindAttributeFunc !== "function") {
			return;
		}
		getAttrs([readField], function (values) {
			var fieldToFind = values[readField],
			foundField = "";
			if (typeof fieldToFind === "undefined" || fieldToFind === null) {
				callback("");
			} else if (fieldToFind === "0" || fieldToFind === 0 || fieldToFind.indexOf("0") === 0) {
				//select = none
				callback(0);
			} else {
				foundField = synchrousFindAttributeFunc(fieldToFind);
				getAttrs([foundField], function (v) {
					var valueOf = parseInt(v[foundField], 10) || 0;
					callback(valueOf, foundField);
				});
			}
		});
	},
	/** Looks at a dropdown value, and sets writeField(s) with the number to which selected option refers.
	* calls getDropdownValue
	* @param {string} readField the dropdown field
	* @param {string_or_Array} writeFields Field(s) to write the value to
	* @param {function} synchrousFindAttributeFunc takes value of @readField and says what the lookup field is.
	* @param {function(int)} callback (optional) if we need to update the field, call this function
	*         with the value we set as the only parameter.
	* @param {bool} silently if true call setAttrs with {silent:true}
	*/
	setDropdownValue = function (readField, writeFields, synchrousFindAttributeFunc, callback, silently) {
		var done = function (newval, currval, changed) {
			if (typeof callback === "function") {
				callback(newval, currval, changed);
			}
		};
		SWUtils.getDropdownValue(readField, synchrousFindAttributeFunc, function (valueOf) {
			var params = {};
			if (silently) {params.silent=true;}
			if (Array.isArray(writeFields) && writeFields.length === 1) {
				writeFields = writeFields[0];
			}
			if (typeof writeFields === "string") {
				getAttrs([writeFields], function (v) {
					var currValue = parseInt(v[writeFields], 10),
					setter = {};
					//TAS.debug("setDropdownValue, readField:" + readField + ", currValue:" + currValue + ", newValue:" + valueOf);
					if (currValue !== valueOf || isNaN(currValue)) {
						setter[writeFields] = valueOf;
						setAttrs(setter, params, function () {
							done(valueOf, currValue, true);
						});
					} else {
						done(valueOf, currValue, false);
					}
				});
			} else if (Array.isArray(writeFields)) {
				getAttrs(writeFields, function (v) {
					var i = 0,
					setter = {};
					for (i = 0; i < writeFields.length; i++) {
						if (parseInt(v[writeFields[i]], 10) !== valueOf) {
							setter[writeFields[i]] = valueOf;
						}
					}
					if (_.size(setter) > 0) {
						setAttrs(setter, params, function () {
							done(valueOf, 0, true);
						});
					} else {
						done(valueOf, 0, false);
					}
				});
			}
		});
	},
	/** getRowTotal return newvalue, currentvalue, allvalues in callback. Summed up floats and round total to int. 
	* THIS IS PROBABLY SLOWER THAN DOING IT YOURSELF, just wrote to make things simpler.
	* @param {Array} fields array of field names to be added up, EXCEPT the first field which is ignored (at index 0) which is the total current value
	* @param {number} bonus a number that is added to the other fields.
	* @param {Array} penalties array of fieldnames whose values are to be subtracted from the total
	* @param {boolean} totalIsFloat true if we should not round the total to int.
	* @param {function(number,number)} callback call this with: new total, current total
	* @param {function} errorCallback call if error attempting to add.
	*/
	getRowTotal = function (fields, bonus, penalties, totalIsFloat, callback, errorCallback) {
		var readFields;
		if (typeof callback !== "function" || typeof errorCallback !== "function") {
			return;
		}
		try {
			if (!fields || (!Array.isArray(fields)) || fields.length === 0) {
				return;
			}
			if (penalties && Array.isArray(penalties) && penalties.length > 0) {
				readFields = fields.concat(penalties);
			} else {
				readFields = fields;
			}
		} catch (err2) {
			TAS.error("SWUtils.getRowTotal catastrophic error: ", err2);
			errorCallback();
			return;
		}
		getAttrs(readFields, function (v) {
			var currValue = totalIsFloat ? parseFloat(v[fields[0]]) : parseInt(v[fields[0]], 10),
			newValue = 0,
			penalty = 0,
			i; //, setter = {}
			try {
				//remember start at 1
				for (i = 1; i < fields.length; i++) {
					newValue += parseFloat(v[fields[i]]) || 0;
				}
				if (bonus && !isNaN(parseInt(bonus, 10))) {
					newValue += parseFloat(bonus);
				}
				if (penalties) {
					for (i = 0; i < penalties.length; i++) {
						penalty += parseFloat(v[penalties[i]]) || 0;
					}
					newValue -= penalty;
				}
				if (!totalIsFloat) {
					newValue = Math.floor(newValue);
				}
				callback(newValue, currValue);
			} catch (err) {
				TAS.error("SWUtils.getRowTotal", err);
				errorCallback();
			}
		});
	},
	/** Adds up numbers and puts it in the first field of the fields array.
	* All numbers are added up as FLOATS, and then FLOOR is used to round the sum down
	* @param {Array} fields array of field names to be added up, EXCEPT the first field. fields[0] MUST be the total field
	* @param {number} bonus a number that is added to the other fields.
	* @param {Array} penalties array of fieldnames whose values are to be subtracted from the total
	* @param {boolean} totalIsFloat true if we should not round the total to int.
	* @param {function(number,number)} callback optional call this with two values: the new total, old total
	* @param {bool} silently if true call setAttrs with {silent:true}
	*/
	updateRowTotal = function (fields, bonus, penalties, totalIsFloat, callback, silently) {
		var done = function () {
			if (typeof callback === "function") {
				callback();
			}
		};
		getRowTotal(fields, bonus, penalties, totalIsFloat, function (newValue, currValue) {
			var setter = {},
			params = {};
			try {
				if (newValue !== currValue) {
					setter[fields[0]] = newValue;
				}
			} catch (err) {
				TAS.error("PFUtilsAsync.updateRowTotal", err);
			} finally {
				if (_.size(setter) > 0) {
					if (silently) {
						params.silent=true;
					}
					setAttrs(setter, params, done);
				} else {
					done();
				}
			}
		}, done);
	},
	/** Escapes special chars for regex
	*@param {string} str the string to examine
	*@param {boolean} escapeSpaces if we should replace any space with \s* (caller can use it for matching purposes)
	*@returns {string} resultant string after search and replace
	*/
	escapeForRegExp = function (str, escapeSpaces) {
		var regexEscapes = /[\-\[\]\/\{\}\(\)\*\+\?\.\\\^\$\|\~\!\@\#]/g,
		tempstr ='';
		if (str) {
			tempstr = str.replace(regexEscapes, "\\$&");
			if (escapeSpaces){
				//replace space plus multiple spaces with non escaped 0 or * space.
				tempstr = tempstr.replace(/\t+|\s+/g,'\\s*');
			}
		}
		return tempstr;
	},
	/** Escapes special chars for macros - to create sub queries - this is not used currently
	*@param {string} str the string to examine
	*@returns {string} resultant string after search and replace
	*/
	escapeForMacroCall = function (str) {
		var macroCallEscapes = [ [/\{\{/g, '&#123;&#123;'],
			[/\}\}/g, '&#125;&#125;'],
			[/\(/g, '&#40;'],
			[/\)/g, '&#41;'],
			[/\,/g, '&#44;'],
			[/\?/g, '&#63;'],
			[/'/g, '&#39;'],
			[/"/g, '&#34;'],
			[/\=/g, '&#61;'] ];
		if (str) {
			return _.reduce(macroCallEscapes, function (currStr, pair) {
				return currStr.replace(pair[0], pair[1]);
			}, str);
		}
		return "";
	},
	/** Escapes '{{' for passing to a rolltemplate
	*@param {string} str the string to examine
	*@returns {string} resultant string after search and replace
	*/
	escapeForRollTemplate = function (str) {
		if (!str){return str;}
		return str.replace(/\{\{/g, '&#123;&#123;');
	},
	/** escapes string so it can be used in the name section of another link button
	*if it finds [name](link) in a string it will remove the [ and ] and the (link)
	* replaces [ and ] with escaped versions everywhere else.
	*@param {string] str the string we want to use inside a link button
	*@returns {string} safe to use new name for button
	*/
	escapeForChatLinkButton = function(str){
		var markdownLinkreg=/^([^\[]*?)\[([^\]]*?)\]\(([^\)]*?)\)(.*)$/,
			retstr="", matches;
		if (!str){return str;}
		matches = markdownLinkreg.exec(str);
		if(matches){
			if (matches[1]){
				retstr+=matches[1];
			}
			if(matches[2]){
				retstr += matches[2];
			}
			if (matches[4]){
				retstr += matches[4];
			}
		} else {
			retstr = str;
		}
		retstr = retstr.replace(/\[/g,'&#91;').replace(/\]/g,'&#93;');
		return retstr;
	},
	/** returns id portion of a source Attribute or repeating row attribute name
	* @param {string} sourceAttribute from eventInfo object
	* @returns {string} the id portion of string, or blank.
	*/
	getRowId = function (sourceAttribute) {
		if (!sourceAttribute) { return ""; }
		var strs = sourceAttribute.split('_');
		if (strs && _.size(strs) >= 4) {
			return strs[2];
		}
		return "";
	},
	getAttributeName = function (source) {
		if (!source) { return ""; }
		var itemId = getRowId(source), attrib = "";
		if (itemId) {
			attrib = source.substring(source.indexOf(itemId) + itemId.length + 1, source.length);
		}
		return attrib;
	},
	/** getRepeatingIDStr - if id is not empty, then returns the ID with an underscore on the right. else returns empty string
	* this is used so the same function can be written for loops from getIDs or direct from the event with no ID
	*@param {string} id the id of the row or blank
	*@returns {string} id_  or blank
	*/
	getRepeatingIDStr = function (id) {
		var idStr = "";
		if (!(id === null || id === undefined)) {
			idStr = id + "_";
		}
		return idStr;
	},
	/** Append values of multiple arrays of strings together to return one NEW array of strings that is the cartesian product.
	* @example cartesianAppend(["a","b"],["c","d"], ["e","f"]);
	* // returns ["ace","acf","ade","adf","bce","bcf","bde","bdf"]
	* @example cartesianAppend(["pre_"] , ["a","b","c"], ["_post"] );
	* //returns ["pre_a_post","pre_b_post","pre_c_post"]
	* @param {Array} [...] Arrays of strings
	* @returns {Array} of all values in other arrays
	*/
	cartesianAppend = function () {
		return _.reduce(arguments, function (a, b) {
			return _.flatten(_.map(a, function (x) {
				return _.map(b, function (y) {
					return String(x) + String(y);
				});
			}), true);
		}, [[]]);
	},
	/** Concatenates cartesian product of all arrays together returns one flattened NEW array.
	* @param {Array} [...] Arrays
	* @returns {Array} cartesian product of all arrays (concatenated nothing else)
	*/
	cartesianProduct = function () {
		return _.reduce(arguments, function (a, b) {
			return _.flatten(_.map(a, function (x) {
				return _.map(b, function (y) {
					return x.concat([y]);
				});
			}), true);
		}, [[]]);
	},
	/** trimBoth removes spaces at beginning and end of string, or of each string in an array.
	* performs a deep match, so if array is of arrays, will call trim on every string. 
	* if object is not an array or string, just return object.
	* therefore, non immutable objects are not cloned and array will contain links to them.
	*@param {Array or string} val string or array of strings
	*@returns {Array or string} same object type as passed in 
	*/
	trimBoth = function(val){
		if (Array.isArray(val)){
			return _.map(val,trimBoth);
		}
		if (typeof val === 'string') {
			return val.replace(/^\s*|\s*$/g,'');
		}
		return val;
	}
	;
	return {
		cartesianAppend: cartesianAppend,
		cartesianProduct: cartesianProduct,
		convertKL1KH1toMinMax: convertKL1KH1toMinMax,
		escapeForRegExp: escapeForRegExp,
		escapeForRollTemplate: escapeForRollTemplate,
		searchAndReplaceFields: findAndReplaceFields,
		findAndReplaceFields: findAndReplaceFields,
		evaluateExpression: evaluateExpression,
		getRowId: getRowId,
		getAttributeName: getAttributeName,
		evaluateAndSetNumber: evaluateAndSetNumber,
		escapeForChatLinkButton: escapeForChatLinkButton,
		getDropdownValue: getDropdownValue,
		setDropdownValue: setDropdownValue,
		getRowTotal: getRowTotal,
		updateRowTotal: updateRowTotal,
		getRepeatingIDStr: getRepeatingIDStr,
		validNumericStr: validNumericStr,
		trimBoth: trimBoth
	};
}());
