#define ATS_DYNLOADFLAG 0
#include "share/atspre_staload.hats"
#include "atsparcc.hats"
#include "atsutils.hats"

staload "sexp.sats"
staload _ = "sexp.dats"

staload "list.sats"
staload "simple.sats"


#define :: ListCons 
#define nil ListNil 

#define INT 0
#define BOOL 1
#define UNIT 2

(******************************)

implement show_any<tvar> (t) = 
	case+ t of 
	| VarName x  => show x 
	| VarIndex x => show x

implement show_any<ttype> (t) = 
	case+ t of 
	| STBase t => 
		(ifcase 
		| t = INT  => show "int"
		| t = BOOL => show "bool"
		| t = UNIT => show "unit")
	| STFun (a, b) => ignoret (show a; show "->"; show b)


implement show_any<term> (term) = 
	case+ term of 
	| TMVar v         => (show "TMVar("; show v; show ")")
	| TMLam (v, x, t) => (show "TMLam("; show v; show ":"; show x; show "."; show t; show ")")
	| TMApp (t1, t2)  => (show "TMApp("; show t1; show "("; show t2; show "))")
	| TMInt x         => (show "TMInt("; show x;  show ")")
	| TMBool x        => (show "TMBool("; show x; show ")")
	| TMUnit _        => (show "TMUnit()")

(******************************)

implement order_compare<tvar> (a, b) = 
	case+ (a, b) of 
	| (VarName x, VarName y)   => order_compare<string> (x, y)
	| (VarIndex x, VarIndex y) => order_compare<int> ($UNSAFE.cast{int} x, $UNSAFE.cast{int} y)
	| (_, _)                   => ($UNSAFE.cast{int} a) - ($UNSAFE.cast{int} b) // address


implement order_compare<ttype> (a, b) = 
	case+ (a, b) of 
	| (STBase a, STBase b)             => a - b 
	| (STFun (a1, a2), STFun (b1, b2)) => 
		let 
			val x = cmp (a1, b1)
		in
			if x = 0 then cmp (a2, b2) else x
		end
	| (_, _) => ($UNSAFE.cast{int} a) - ($UNSAFE.cast{int} b)
 
implement order_compare<term> (a, b) = 
	case+ (a, b) of 
	| (TMVar a, TMVar b)                     => cmp (a, b)
	| (TMLam (a, va, ta), TMLam (b, vb, tb)) => if cmp (a, b) != 0 then cmp (a, b) else
												if cmp (va, vb) != 0 then cmp (va, vb) else cmp (ta, tb)
	| (TMApp (ta1, ta2), TMApp (tb1, tb2))   => if cmp (ta1, tb1) != 0 then cmp (ta1, tb2) else cmp (ta2, tb2)
	| (TMInt a, TMInt b)                     => a - b
	| (TMBool a, TMBool b)                   => cmp (a, b)
	| (TMUnit _, TMUnit _)                   => 0
	| (_, _)                                 => ($UNSAFE.cast{int} a) - ($UNSAFE.cast{int} b) // address

(******************************)


implement parse_simple_term (sexp) = let 

	fun parse_simple_type (sexp: sexp): ttype = 
		case+ sexp of
		| SSymbol s when s = "int" => STBase INT
		| SSymbol s when s = "bool" => STBase BOOL 
		| SSymbol s when s = "unit" => STBase UNIT
		| SList (SSymbol "->" :: x :: y :: nil ()) => STFun (parse_simple_type x, parse_simple_type y)
		| _ => $raise LamParsingException "parse_simple_type"

	fun parse_simple_lam (sexp: sexp): term = 
		case+ sexp of 
		| SList (
			SSymbol k 
			:: SList (SSymbol v :: t :: nil ()) 
			:: b 
			:: nil ()) when k = "lam" => TMLam (VarName v, parse_simple_type t, parse_simple_term b)
		| _ =>> $raise LamParsingException ("parse_simple_lam")

	fun parse_simple_var (sexp: sexp): term = 
		case+ sexp of 
		| SSymbol s                   => if s = "()" then TMUnit () else TMVar (VarName s)
		| SInt s                      => TMInt s
		| SBool s                     => TMBool s
		| SString s                   => TMVar (VarName s)
		| SList (SSymbol s :: nil ()) => TMVar (VarName s)
		| SList _                     => $raise LamParsingException ("parse_simple_var") 

	fun parse_simple_app (sexp: sexp): term = 
		case+ sexp of 
		| SList (a :: b :: nil ()) => TMApp (parse_simple_term a, parse_simple_term b)
		| _ =>> $raise LamParsingException ("parse_simple_app")
in 
	case+ sexp of 
	| SList (SSymbol "lam" :: _)      =>  parse_simple_lam sexp 
	| SList (xs) when list_len xs > 1 =>> parse_simple_app sexp 
	| _                               =>> parse_simple_var sexp
end


implement term_type_check (t) = let 
	
	exception TypeError of string 

	fun check (t: term, ctx: map (term, ttype), t: ttype): bool = 


	fun type_of (t: term, ctx: map (term, ttype)): ttype = 
		case+ t of 
		| TMVar x => (case+ find (map, x) of 
					 | Just t    => t
					 | Nothing _ => $raise TypeError ("variable not defined"))
		| TMInt _ => STBase INT 
		| TMBool _ => STBase BOOL 
		| TMUnit _ => STBase UNIT 
		| TMLam (x, t, b) => check (b, insert (ctx, x, t), )
	
in 
end 