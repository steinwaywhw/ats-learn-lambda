


datasort typ = 
| BaseType 
| ArrowType of (typ, typ)

datasort term = 
| FVarTerm of int 
| BVarTerm of int 
| AbsTerm  of term 
| AppTerm  of (term, term)



absprop snorm (term)

dataprop red (term, typ) = 
| {t:term}   RedBase (t, BaseType ()) of (snorm t)
| {t,u:term} RedArrow (t, ArrowType (t1, t2)) of (red (AppTerm (t, u)))