@ rule32 @
expression e;
identifier fun;
@@

-fun(e);
+fun(e, e);



@ rule13 @
expression e;
identifier fun;
@@

-fun(e);
+fun(e, e);


@ rule1 @
expression e;
identifier fun;
@@

-fun(e);
+fun(e, e);

@ rule2 depends on !rule1 && ( ruleh3     |f| rule32) @
@@

-gh();