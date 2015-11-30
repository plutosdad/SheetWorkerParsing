
var ExExp = (function(){

    parseExpression = function (s, until) {
        //alert('parsing: ' + s);
        //alert('until is ' + typeof until);
        var untilCb = (typeof (until) == typeof (function () {}) ? until : function (tok) {
            return (tok == until);
        });

        // constants
        var ARG_COUNTS = {
            'abs': 1
            , 'ceil': 1
            , 'floor': 1
            , 'round': 1
            , 'max': [1]
            , 'min': [1]
        };
        var BINARY_PRECEDENCE = {
            '?': 1
            , ':': 2
            , '||': 3
            , '&&': 4
            , '|': 5
            , '^': 6
            , '&': 7
            , '=': 8
            , '==': 8
            , '!=': 8
            , '>=': 9
            , '>': 9
            , '<': 9
            , '<=': 9
            , '<<': 10
            , '>>': 10
            , '+': 11
            , '-': 11
            , '*': 12
            , '/': 12
            , '%': 12
            , '**': 14
            , 't': 98
            , 'd': 99
        };
        var UNARY_PRECEDENCE = {
            '!': 13
            , '~': 13
            , '-': 13
        };
        var CLOSERS = {
            '(': ")"
            , '{': "}"
        };

        // local variables
        var operators = [{
                'precedence': 0
            }]
            , operands = [];

        // helper functions
        function getToken(s) {
            if (!s) {
                return s;
            }

            var m;

            function retVal(tokType, matchObj) {
                return {
                    'type': tokType
                    , 'text': matchObj[0]
                    , 'match': matchObj
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
            m = s.match(/^((\|\|)|(&&)|(==)|(!=)|(>=)|(<=)|(<<)|(>>)|(\*\*)|[?:|^&=><%!~])/);
            if (m) {
                return retVal("extoperator", m);
            }
            m = s.match(/^[-+*/td]/);
            if (m) {
                return retVal("baseoperator", m);
            }
            m = s.match(/^\[([^\]]+)\]/);
            if (m) {
                return retVal("label", m);
            }
            m = s.match(/^\${([^'"($}][^}]*)}/);
            if (m) {
                return retVal("variable", m);
            }
            m = s.match(/^\${/);
            if (m) {
                return retVal("openvariable", m);
            }

            return {
                'type': "raw"
                , 'text': s.charAt(0)
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
            var i = -1
                , j = i;
            // find first index of delim not preceeded by an odd number of backslashes
            while (((i - j) & 1) == 0) {
                i = state.s.indexOf(delim, i + 1);
                if (i < 0) {
                    return;
                }
                j = i - 1;
                while ((j >= 0) && (state.s.charAt(j) == '\\')) {
                    j--;
                }
            }
            // unescape string to be returned
            function replaceEscapes(s) {
                return s.replace(/\\n/g, "\n")
                    .replace(/\\r/g, "\r")
                    .replace(/\\t/g, "\t")
                    .replace(/\\/g, "");
            }
            var retval = state.s.substring(0, i)
                .split("\\\\")
                .map(replaceEscapes)
                .join("\\");
            // point state delim, then pop off the delimiter token
            state.s = state.s.substring(i);
            popToken(state);
            return retval;
        }

        function popOperator() {
            var op = operators.pop();
            var right = operands.pop();
            if (op.unary) {
                operands.push({
                    'type': (op.type == "baseoperator" ? "unop" : "unopex")
                    , 'datatype': right.datatype
                    , 'operator': op.text
                    , 'operand': right
                });
                return;
            }
            var left = operands.pop();
            if (op.text != ":") {
                var datatype;
                if ((op.text == "d") || (op.text == "t")) {
                    datatype = "number";
                } else if (left.datatype == right.datatype) {
                    datatype = left.datatype;
                } else if ((left.datatype == "string") || (right.datatype == "string")) {
                    datatype = "string";
                }
                operands.push({
                    'type': (op.type == "baseoperator" ? "binop" : "binopex")
                    , 'datatype': datatype
                    , 'operator': op.text
                    , 'left': left
                    , 'right': right
                    , 'mods': op.mods
                    , 'label': op.label
                });
                return;
            }
            op = operators.pop();
            if (op.text != "?") {
                return "Error: Expected ? but got " + op.text;
            }
            var cond = operands.pop();
            operands.push({
                'type': "cond"
                , 'cond': cond
                , 'left': left
                , 'right': right
                , 'datatype': (left.datatype == right.datatype ? left.datatype : undefined)
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
            return (tok == ',') || (tok == ')');
        }

        function parseHelper() {
            var err;

            popToken(s);
            if (!s.tok) {
                return "Error: Unrecognized token: " + s.s.split(" ", 1)[0];
            }
            while (s.tok.type == "whitespace") {
                popToken(s);
                if (!s.tok) {
                    return "Error: Unrecognized token: " + s.s.split(" ", 1)[0];
                }
            }
            switch (s.tok.type) {
            case "function":
                var func = s.tok.match[1];
                var argCounts = ARG_COUNTS[func]
                    , minArgs, maxArgs;
                if (typeof (argCounts) == typeof (0)) {
                    minArgs = argCounts;
                    maxArgs = argCounts;
                } else if (typeof (argCounts) == typeof ([])) {
                    minArgs = argCounts[0];
                    maxArgs = argCounts[1];
                } else {
                    return "Error: Unrecognized function: " + func;
                }
                var args = [];
                while ((s.tok) && (s.tok.text != ')')) {
                    var argTree = parseExpression(s, argListUntil);
                    if (typeof (argTree) == typeof ("")) {
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
                if ((typeof (minArgs) != typeof (0)) || (minArgs < 0)) {
                    minArgs = args.length;
                }
                if ((typeof (maxArgs) != typeof (0)) || (maxArgs < 0)) {
                    maxArgs = args.length;
                }
                if (args.length < minArgs) {
                    return "Error: Function '" + func + "' requires at least " + minArgs + " argument(s)";
                }
                if (args.length > maxArgs) {
                    return "Error: Function '" + func + "' requires at most " + maxArgs + " argument(s)";
                }
                operands.push({
                    'type': "function"
                    , 'datatype': "number"
                    , 'function': func
                    , 'args': args
                });
                return;
            case "number":
                operands.push({
                    'type': "number"
                    , 'datatype': "number"
                    , 'value': parseFloat(s.tok.text)
                });
                return;
            case "variable":
                operands.push({
                    'type': "variable"
                    , 'value': s.tok.match[1]
                });
                return;
            case "quote":
                var str = popString(s, s.tok.text);
                if (typeof (str) != typeof ("")) {
                    return "Error: Unterminated string";
                }
                operands.push({
                    'type': "string"
                    , 'datatype': "string"
                    , 'value': str
                });
                return;
            case "opengroup":
                var opener = s.tok.text
                    , closer = CLOSERS[opener];
                var operand = parseExpression(s, closer);
                if (typeof (operand) == typeof ("")) {
                    return operand;
                } // error
                operands.push(operand);
                if (s.tok.text != closer) {
                    return "Error: Expected '" + closer + "' to close '" + opener + "', but got '" + s.tok.text + "'";
                }
                return;
            case "openvariable":
                var varExp = parseExpression(s, "}");
                if (typeof (varExp) == typeof ("")) {
                    return varExp;
                } // error
                if (s.tok.text != "}") {
                    return "Error: Expected '}' to close '${', but got '" + s.tok.text + "'";
                }
                operands.push({
                    'type': "variable"
                    , 'value': varExp
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
            return "Error: Unrecognized token: " + s.tok.text + (s.tok.type == "raw" ? s.s.split(" ", 1)[0] : "");
        }

        // if we were given a string, construct a state object
        if (typeof (s) == typeof ("")) {
            s = {
                's': s
            };
        }

        // push operators and operands to their respective stacks, building sub-ASTs in the operand stack as needed
        var err = parseHelper();
        if (err) {
            return err;
        }
        for (popToken(s);
            (s.tok) && (!untilCb(s.tok.text)) && ((until) || (s.tok.type != "raw")); popToken(s)) {
            switch (s.tok.type) {
            case "extoperator":
            case "baseoperator":
                rollOperator = (s.tok.text == "d" ? s.tok : null);
                err = pushOperator(s.tok);
                if (err) {
                    return err;
                }
                if ((rollOperator) && (s.s.charAt(0) == 'F')) {
                    operands.push({
                        'type': "rollspec"
                        , 'value': "F"
                    })
                    s.s = s.s.substring(1);
                } else if (s.tok.text == "t") {
                    if (s.s.charAt(0) != '[') {
                        return "Error: 't' operator requires '[table]' argument";
                    }
                    var m = s.s.match(/^\[([^'"$(\]][^\]]*)\]/);
                    var tableExp;
                    if (m) {
                        tableExp = m[1];
                        s.s = s.s.substring(m[0].length);
                    } else {
                        s.s = s.s.substring(1);
                        tableExp = parseExpression(s, "]");
                        if (typeof (tableExp) == typeof ("")) {
                            return tableExp;
                        } // error
                        if (s.tok.text != "]") {
                            return "Error: Expected ']' to close 't[', but got '" + s.tok.text + "'";
                        }
                    }
                    operands.push({
                        'type': "tablename"
                        , 'value': tableExp
                    });
                } else {
                    err = parseHelper();
                    if (err) {
                        return err;
                    }
                }
                if (rollOperator) {
                    var m = s.s.match(/^[acdfhkloprs0-9<=>!]+/);
                    if (m) {
                        rollOperator.mods = m[0];
                        s.s = s.s.substring(m[0].length)
                    }
                }
                break;
            case "label":
                if ((operators.length > 0) && (operators[operators.length - 1].text == "d")) {
                    // set label on "d" operator instead of operand (e.g. "1d6[foo]" is "(1d6)[foo]", not "1d(6[foo])")
                    operators[operators.length - 1].label = s.tok.match[1];
                    break;
                }
                var operand = operands.pop();
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

    write= function (s) {
    	console.log("EXEXP:"+s);
    },


    sendCommand= function (chunks, asts, evalResults, labels) {
        // constants
        var FUNCTION_FUNCTIONS = {
            'abs': Math.abs
            , 'ceil': Math.ceil
            , 'floor': Math.floor
            , 'round': Math.round
            , 'max': Math.max
            , 'min': Math.min
        };
        var BINARY_FUNCTIONS = {
            '||': function (x, y) {
                return x || y;
            }
            , '&&': function (x, y) {
                return x && y;
            }
            , '|': function (x, y) {
                return x | y;
            }
            , '^': function (x, y) {
                return x ^ y;
            }
            , '&': function (x, y) {
                return x & y;
            }
            , '=': function (x, y) {
                return x == y;
            }
            , '==': function (x, y) {
                return x == y;
            }
            , '!=': function (x, y) {
                return x != y;
            }
            , '>=': function (x, y) {
                return x >= y;
            }
            , '>': function (x, y) {
                return x > y;
            }
            , '<': function (x, y) {
                return x < y;
            }
            , '<=': function (x, y) {
                return x <= y;
            }
            , '<<': function (x, y) {
                return x << y;
            }
            , '>>': function (x, y) {
                return x >> y;
            }
            , '+': function (x, y) {
                return x + y;
            }
            , '-': function (x, y) {
                return x - y;
            }
            , '*': function (x, y) {
                return x * y;
            }
            , '/': function (x, y) {
                return x / y;
            }
            , '%': function (x, y) {
                return x % y;
            }
            , '**': Math.pow
            , 'd': function (x, y) {
                var retval = 0;
                for (var i = 0; i < x; i++) {
                    retval += randomInteger(y);
                }
                return retval;
            }
        };
        var UNARY_FUNCTIONS = {
            '!': function (x) {
                return !x;
            }
            , '~': function (x) {
                return ~x;
            }
            , '-': function (x) {
                return -x;
            }
        };


        // local variables
        var references = {}
            , unevalRefs = []
            , evalReqs = [];

        // helper functions
        function lazyEval(t, labels, references, unevalRefs, evalReqs, force) {
            //alert(' at lazyEval, t: ' + t + ', t.type:'+t.type);
            var x, y;

            if (t.label) {
                labels[t.label] = t;
            }

            switch (t.type) {
            case "number":
            case "rollspec":
                t.baseValid = true;
                // fall through
            case "string":
                return t;
            case "tablename":
                if (typeof (t.value) != typeof ("")) {
                    x = lazyEval(t.value, labels, references, unevalRefs, evalReqs, true);
                    if (typeof (x) == typeof ("")) {
                        return x;
                    } // error
                    if (x.type == "number") {
                        // number node; coerce to string
                        x.value = "" + x.value;
                        x.type = "string"
                    }
                    if (x.type != "string") {
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
                var args = [];
                for (var i = 0; i < t.args.length; i++) {
                    x = lazyEval(t.args[i], labels, references, unevalRefs, evalReqs, true);
                    if (typeof (x) == typeof ("")) {
                        return x;
                    } // error
                    if (x.type == "string") {
                        x.value = parseFloat(x.value);
                        x.type = "number";
                    }
                    if (x.type != "number") {
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
                t.value = FUNCTION_FUNCTIONS[t.function].apply(args, args);
                for (var i = 0; i < t.args.length; i++) {
                    if (t.args[i].label) {
                        labels[t.args[i].label] = t.args[i];
                    }
                }
                delete t.function;
                delete t.args;
                t.baseValid = true;
                return t;
            case "unop":
            case "unopex":
                force = force || (t.type != "unop");
                x = lazyEval(t.operand, labels, references, unevalRefs, evalReqs, force);
                if (typeof (x) == typeof ("")) {
                    return x;
                } // error
                if (force) {
                    if (x.type != "number") {
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
                force = force || (t.type != "binop") || (t.left.datatype == "string") || (t.right.datatype == "string");
                var forceSubtrees = force || (t.operator == "d") || (t.operator == "t");
                 //alert('left is: ' + t.left + ', right is:' + t.right);
                x = lazyEval(t.left, labels, references, unevalRefs, evalReqs, forceSubtrees);
                y = lazyEval(t.right, labels, references, unevalRefs, evalReqs, forceSubtrees);
                    //alert('typeof left:' + typeof x + ', typeof right:' + typeof y);
                    force = true;
               // if (typeof (x) == typeof ("")) {
               //     return x;
               // } // error
                //if (typeof (y) == typeof ("")) {
                //    return y;
               // } // error
                if (force) {
                    if ((x.type != "number") && (x.type != "string")) {
                        // unable to fully evaluate left operand
                        if (t.baseValid) {
                            t.baseValid = false;
                        }
                        return t;
                    }
                    if ((y.type != "number") && (y.type != "string") && (y.type != "rollspec") && (y.type != "tablename")) {
                        // unable to fully evaluate right operand
                        if (t.baseValid) {
                            t.baseValid = false;
                        }
                        return t;
                    }
                    if ((y.type == "rollspec") && (t.operator != "d")) {
                        return "Rollspec operand is only compatible with 'd' operator";
                    }
                    if ((t.operator == "t") && (y.type != "tablename")) {
                        return "'t' operator requires tablename operand";
                    }
                    // successfully evaluated both operands
                    if ((t.operator == "t") || ((t.operator == "d") && (t.mods))) {
                        // operator is rollable table or is roll with mods; must submit to base system for evaluation
                        evalReqs.push(t);
                        return t;
                    }
                    //alert('about to call binary');
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
                    t.type = (typeof (t.value) == typeof ("") ? "string" : "number");
                    t.datatype = t.type;
                    t.baseValid = (t.datatype == "number");
                } else if ((x.datatype == "number") && (y.datatype == "number")) {
                    t.datatype = "number";
                    t.baseValid = true;
                }
                return t;
            case "cond":
                x = lazyEval(t.cond, labels, references, unevalRefs, evalReqs, true);
                if (typeof (x) == typeof ("")) {
                    return x;
                } // error
                if ((x.type != "number") && (x.type != "string")) {
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
                for (var k in y) {
                    t[k] = y[k];
                }
                return lazyEval(t, labels, references, unevalRefs, evalReqs, force);
            case "variable":
                if (typeof (t.value) != typeof ("")) {
                    x = lazyEval(t.value, labels, references, unevalRefs, evalReqs, true);
                    if (typeof (x) == typeof ("")) {
                        return x;
                    } // error
                    if (x.type == "number") {
                        // number node; coerce to string
                        x.value = "" + x.value;
                        x.type = "string"
                    }
                    if (x.type != "string") {
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
                if ((labels[t.value]) && ((labels[t.value].type == "string") || (labels[t.value].type == "number"))) {
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
            // base types: fully evaluated
            if ((t.type == "number") || (t.type == "string") || (t.type == "rollspec")) {
                return false;
            }

            // if we got here, node is unevaluated
            if (t.label) {
                return true;
            }

            // node has no label; check children
            switch (t.type) {
            case "function":
                for (var i = 0; i < t.args.length; i++) {
                    if (hasUnevaluatedLabels(t.args[i])) {
                        return true;
                    }
                }
                return false;
            case "tablename":
            case "variable":
                if (typeof (t.value) == typeof ("")) {
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
                // fall through
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
                retval = t.value | 0;
                break;
            case "tablename":
                retval = "[" + t.value + "]";
                break;
            case "unop":
                retval = "(" + t.operator + flattenAST(t.operand) + ")";
                break;
            case "binop":
                retval = "(" + flattenAST(t.left) + t.operator + flattenAST(t.right) + (t.mods || "") + ")";
                if ((t.label) && (t.operator == "d")) {
                    retval += "[" + t.label + "]";
                }
                break;
            default:
                return "Unknown node type: " + t.type;
            }

            return retval;
        }

        function astToCmd(t) {
            if (t.type == "string") {
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
        for (var i = 0; i < evalResults.length; i++) {
            var t = evalResults[i][0];
            delete t.operator;
            delete t.left;
            delete t.right;
            t.type = "number";
            t.datatype = "number";
            t.value = evalResults[i][1];
            t.baseValid = true;
        }

        // traverse ASTs, collapsing as much as possible
        for (var i = 0; i < asts.length; i++) {
            if (asts[i].baseValid) {
                continue;
            } // can be handled by base expression evaluator
            if ((asts[i].type == "string") || (asts[i].type == "number")) {
                continue;
            } // tree is fully evaluated
            var err = lazyEval(asts[i], labels, references, unevalRefs, evalReqs, false);
            if (typeof (err) == typeof ("")) {
                return reportError(err);
            }
        }

        // do variable substitution; repeat until we don't make any more progress
        var doSubstitution = true;
        while (doSubstitution) {
            doSubstitution = false;
            // substitute in values for variables for which we already have names
            for (var label in references) {
                if (!labels[label]) {
                    return reportError("Variable '" + label + "' not defined");
                }
                if ((labels[label].type != "string") && (labels[label].type != "number")) {
                    // variable exists but not yet evaluated; try to evaluate
                    var err = lazyEval(labels[label], labels, references, unevalRefs, evalReqs, true);
                    if (typeof (err) == typeof ("")) {
                        return reportError(err);
                    }
                }
                if ((labels[label].type == "string") || (labels[label].type == "number")) {
                    // variable fully evaluated; substitute it in
                    for (var i = 0; i < references[label].length; i++) {
                        references[label][i].type = labels[label].type;
                        references[label][i].datatype = labels[label].datatype;
                        references[label][i].value = labels[label].value;
                        references[label][i].baseValid = labels[label].baseValid;
                    }
                    delete references[label];
                    doSubstitution = true;
                }
            }
            // try to get names for variables and tables with unevaluated names
            var newUneval = [];
            while (unevalRefs.length > 0) {
                var r = lazyEval(unevalRefs.shift(), labels, references, unevalRefs, evalReqs, true);
                if (typeof (r) == typeof ("")) {
                    return reportError(err);
                }
                if ((r.type == "string") || (r.type == "number")) {
                    doSubstitution = true;
                } else {
                    newUneval.push(r);
                }
            }
            unevalRefs = newUneval;
        }

        // flatten fully evaluated ASTs into strings and splice into chunks
        for (var i = asts.length - 1; i >= 0; i--) {
            if ((!asts[i].baseValid) && (asts[i].type != "number") && (asts[i].type != "string")) {
                continue;
            }
            if ((unevalRefs.length > 0) & (hasUnevaluatedLabels(asts[i]))) {
                continue;
            }
            chunks.splice(i, 2, (chunks[i] || "") + astToCmd(asts.splice(i, 1)[0]) + (chunks[i + 1] || ""));
        }

        if (evalReqs.length > 0) {
			Console.log("Cannot evalutate");
			return ;
        }
        if (asts.length > 0) {
            // need to finish evaluating some ASTs; recurse directly
            return ExExp.sendCommand(chunks, asts, [], labels)
        }
        // if we got here, we're done evaluating everything; submit results via sendChat
		var retval=chunks.join("");
      
        return retval;
    },

  
    handleExpression= function ( msg) {
        var chunks = []
            , asts = []
            , cmd = msg.replace(/^\s+/, "");
        var state = {
            's': cmd
        };
		var ast = ExExp.parseExpression(state, null);
		if (typeof (ast) == typeof ("")) {
			ExExp.write("could not parse"+msg);
			return "";
		}
		asts.push(ast);
		state.s =  (state.tok)?(state.tok.text+state.s):state.s;
          //  ((state.tok || {'text': ""}).text || "") + state.s;
        chunks.push(state.s);
        return ExExp.sendCommand(chunks, asts, [], {});
    };

	
    return {
		parseExpression:parseExpression,
		write:write,
		sendCommand:sendCommand,
		handleExpression:handleExpression
    };
}());


var SWUtils = SWUtils || (function() {	
	
	//no macro calls, dropdowns, or keep  highest/lowest more than 1
	//currently support floor, abs, kh1, kl1 , also extended: ceil, round, max, min
	var validNumericStr = function(preeval) {
		var anyillegal=preeval.match(/\||\?|&|\{|\}|k[h,l][^1]/);
		if (!(anyillegal==undefined) && anyillegal.length>0) {
			return false;
		}
		
		var r2=preeval.replace(/floor|ceil|round|abs|max|min|kh1|kl1/g,'');
		anyillegal = r2.match(/[a-zA-Z]/);
		if (!(anyillegal==undefined) && anyillegal.length>0) {
			return false;
		}
		return true;
	},
	
	/* searchAndReplaceFields
	 * Examines a string for instances of @{fieldname}, and then searches the sheet for those values 
	 * then replaces the intances in the string with the values of those fields.
	 * Because it is a search and replace, if there are no @{fieldname} values, then it will return the same string back.
	 * If there is an error, it will return an empty string "".
	 *
	 * @fromfield = string containing one or more @{fieldname}
	 * @callback = method accepting 1 parameter , this parameter will be the result of the search and replace in the fromfield.
	 * @evalToNumber = true if call validNumericStr 
	 * the end result should be evaluable to a number (not a macro string that is sent to chat)
	 *   e.g.: replaces  [[ and ]] with ( and ) , ensures only kl1 or kh1 (not kh2 or more etc),
	 *         no strings except valid functions like floor, ceil, etc, according to validNumericStr
	 */
	searchAndReplaceFields = function(fromfield, evalToNumber, callback ) {
		if (typeof callback !== "function") {
			return;
		}
		if (! fromfield ) {
			callback("");
			return;
		}
		try {
			var i,numfields,fieldnames=[],matches = [];
			if (evalToNumber) {
				fromfield = fromfield.replace("selected|","").replace("target|","");
			}
			matches = fromfield.match(/(@\{([^}]+)\})(?!.*\1)/g);
			if (typeof matches == "undefined" || matches==null) {
				callback (fromfield);
				return;
			}
			numfields=matches.length;

			fieldnames=[numfields];
			for (i=0;i<numfields;i++) {
				fieldnames[i]=matches[i].replace("@{","").replace("}","");
			}
			getAttrs(fieldnames,function(values){
				var evalstr=fromfield;
				try {
					var replacements=[numfields];
					for (i=0;i<numfields;i++){
						replacements[i]=values[fieldnames[i]];
					}
					for (i=0;i<numfields;i++){
						evalstr = evalstr.replace(matches[i],replacements[i]);
					}
					if (evalToNumber) {
						evalstr=evalstr.replace(/\s+/g,'').replace(/\[\[/g,"(").replace(/\]\]/g,")");
						if (! validNumericStr(evalstr) ) {
							evalstr="";
							console.log("ERROR: cannot evaluate this to number: " + fromfield);
						}
					}
				} catch (err) {
					console.log("ERROR:" + err);
					evalstr="";
				} finally {
					callback ( evalstr);
				}
			});
		} catch (err){
			console.log("ERROR: " + err);
			callback (fromfield);
		} 
	},

	/* evaluateExpression
	*  reads in the string, evalutates it until we find a number, then passes that numbe to the callback.
	*  @exprStr= A string containing a mathematical expression, possibly containing references to fields such as @{myfield}
	*  @callback = a function taking one parameter, either a number or empty string . 
	*/
	evaluateExpression = function(exprStr,callback) {
		if (typeof callback !== "function" ) {
			return;
		}
		if (! exprStr) {
			callback("");
		}
		searchAndReplaceFields(exprStr, true, function(replacedStr) {
			//console.log("we received "+replacedStr+" back");
			var evaluated, setter={};
			if (typeof replacedStr != "undefined" && replacedStr != null ) {
				evaluated = ExExp.handleExpression(replacedStr);
				callback( evaluated);
			} else {
				callback("");
			}
		});	
	},


	/* evaluateAndSet
	 * Searches the readField for any instances of @{field} and replaces them with a value
	 * then writes the resulting string to the writeField. 
	 * 
	 * @readField = the field that contains the string to evaluate, like a field containing a macro
	 * @writeField = the field to write the evaluated value of readField to
	*/
	evaluateAndSetString = function (readField,writeField,evalToNumber) {
		if (typeof writeField === "undefined" || writeField == null || 
			typeof readField === "undefined" || readField == null) {
			return;
		}
		getAttrs([readField], evalToNumber,function(values) {
			searchAndReplaceFields(values[readField], function(valueOf) {
				if (typeof valueOf != "undefined" && valueOf != null && valueOf.length > 0) {
					var setter = {};
					setter[writeField]=valueOf;
					setAttrs(setter);
				}
			});
		});
	},
	


	/* evaluateToNumberAndSet
	* Examines the string in readField, and tests to see if it is a number
	* if it's a number immediately write it to writeField.
	* if not, then replace any @{field} references with numbers, and then evaluate it 
	* as a mathematical expression till we find a number.
	*
	* note this is NOT recursive, you can't point one field of 
    *
	* @readField = field to read containing string to parse
	* @writeField = field to write to
	* @defaultVal= optional, default to set if we cannot evaluate the field. If none set to 0.
	* 
	*/
	evaluateAndSetNumber = function(readField,writeField,defaultVal){
		getAttrs([readField,writeField], function (values){ 
			var o = {};
			var value = 0;
			var currVal= parseFloat(values[writeField],10)||0;
			value = parseFloat(values[readField]);//cannot do "||0" since 0 is valid but falsy
			if (isNaN(value) || typeof(value) === "undefined") {
				SWUtils.evaluateExpression(values[readField],function(value){
					//should be same, but sometimes not!? check both
					if ( isNaN(value) || typeof(value) === "undefined" ) {value=defaultVal||0;}
					if (currVal!==value) {
						o[writeField]=value;
						setAttrs(o);					
					}
				});
			} else {
				if (currVal!==value) {
					o[writeField]=value;
					setAttrs(o);
				}				
			}
		});		
	};

	
	
    return {
		validNumericStr:validNumericStr,
		searchAndReplaceFields:searchAndReplaceFields,
		evaluateExpression:evaluateExpression,
		evaluateAndSetString:evaluateAndSetString,
		evaluateAndSetNumber:evaluateAndSetNumber
    };
}());
	
	