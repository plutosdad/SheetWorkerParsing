# SheetWorkerParsing
Parsing and search and replace for Roll 20 SheetWorkers

To use:
Copy the contents of SWParser.js to the end of your character sheet html
Pick an attribute/field that you want the user to be able to enter macro text into.
Pick an antribute/field to write the resultant value to after evaluating.

Then create an on("change") event handler for the field that will be edited:

on("change:field1",function() {
	SWUtils.evaluateAndSetNumber("field1","field2");
});

You can use just about anything you can use in a macro, except for kh1 and kl1, 
instead use min() and max(). And the min and max come before the parenthesis, not after brackets.

To use in your own code to get a number, you can call the following functions:

SWUtils.evaluateAndSetNumber
this function reads in a field that contains a macro, and writes to another field.

SWUtils.evaluateExpression
This will read a string and replace any attribute references such as @{fieldname} 
This function is asynchronous due to its nature and the second parameter is a callback
to a function that takes a number as its first parameter. Note that if the function
cannot be evaluated to a number then it will return an error or the original string 
depending on what problems were encountered.
SWUtils.evaluateExpression(stringToParse, function(value) {
  if (isNaN(parseFloat(value))) {
    //we have a problem
  } else {
    //use value in your calculations.
  }
});

ExExp.handleExpression
This function is synchronous, it will evaluate an exression of numbers and math functions 
and return a result.
var result = ExExp.handleExpression(stringToParse);


