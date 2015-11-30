# SheetWorkerParsing
Parsing and search and replace for Roll 20 SheetWorkers.
This has functions to take "macro" field in a character sheet, lookup any references, then evaluate the macro and possibly set the value to a another field on a sheet.
I edited the Extended Expressions API script by Manveti (link below)

#Known Issues
Cannot handle keep highest or keep lowest (kl1,kh1), you must replace those with "max" or "min" BEFORE the parenthesis, not after. (note, if you are evaluating to a single number, then only kl1 or kh1 is valid anyway)

#Example
The example.html has the full code, but if you have the following fields <br/>
Input fields (number):<br/>
&lt;input title=&quot;@{one}&quot; type=&quot;number&quot; name=&quot;attr_one&quot;  /&gt;<br/>
&lt;input title=&quot;@{two}&quot; type=&quot;number&quot; name=&quot;attr_two&quot;  /&gt;<br/>
&lt;input title=&quot;@{three}&quot; type=&quot;number&quot; name=&quot;attr_three&quot; /&gt;<br/>
Equation field (text):<br/>
&lt;input  title=&quot;@{eq}&quot; type=&quot;text&quot; name=&quot;attr_eq&quot;  /&gt;<br/>
Result field (number):<br/>
&lt;input title=&quot;@{resultval}&quot; type=&quot;number&quot; name=&quot;attr_resultval&quot; /&gt;<br/>

Then you can make sure the result field is updated whenever the equation is changed using the following:
on("change:eq",function() {
	SWUtils.evaluateAndSetNumber("eq","resultval");
})  ;

Note: you do NOT have to also watch the @{one} @{two} or @{three} fields as well. If those are updated, Roll20 will trigger an update on the @{eq} field, and the eventhandler will be called!
    
#Acknowledgements
Thanks to user <a href="https://app.roll20.net/users/503018/manveti">manveti</a> for his awesome Extended Expressions rules engine api that you can find here: <a href="https://wiki.roll20.net/Script:Extended_Expressions">wiki page</a> , <a href="https://github.com/Roll20/roll20-api-scripts/tree/master/ExtendedExpressions">gitHub</a>  The real power in evaluating fields is due to Manveti. Most of my contribution is getting ExtendedExpressions to work in the SheetWorker context, and then adding the replacement of field values functionality. The version here is still in a module called ExExp, but I introduce a 3rd way to use it, rather than "inline" or "roll", so that it will work with the sheetworkers.
