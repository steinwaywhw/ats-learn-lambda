#include "share/atspre_staload.hats"
#include "atsparcc.hats"
#include "atsutils.hats"

staload "stream.sats"
staload "list.sats"
staload "maybe.sats"
staload "string.sats"
staload "set.sats"


extern fun file_get_stream (string): stream char 
extern fun test_untyped (): void 
extern fun test_simple (): void
extern fun test_infer (): void

(******************************)

implement file_get_stream (path) = sm where {
	staload "libc/SATS/stdio.sats"

	fun tostream (file: FILEref): stream char = let
		val c = int2char0 (fgetc file)
	in 
		if feof file = 0
		then $delay StreamCons (c, tostream file)
		else $delay StreamNil () where {
			val _ = fclose_exn file
		} 
	end

	val file = fopen_ref_exn (path, file_mode_r)
	val sm = tostream file
}

(******************************)

(*local 
	staload "untyped.sats"
	staload "sexp.sats"
	staload _ = "untyped.dats"
	staload _ = "sexp.dats"
in 

implement test_untyped () = {

	fun term_from_string (str: string): term = let 
		assume output_t = sexp 

		val t = list_foldr<char,stream char> (string_explode str, $delay StreamNil (), lam (x, xs) => $delay StreamCons (x, xs))
		val t = parser_apply (parser_sexp_sexp (), $UNSAFE.cast{input_t} t, lam (x, input) => x)
	in 
		try 
			parse_term t
		with 
			~LamParsingException x => (println! x; $raise LamParsingException x)
	end

	#define :: ListCons
	#define nil ListNil

	val K = term_from_string ("(lam x (lam y (x)))")
	val S = term_from_string ("(lam x (lam y (lam z ((x z) (y z)))))")
	val I = term_from_string ("(lam x (x))")
//	val K = term_alpha K 
//	val S = term_alpha S 
//	val I = term_alpha I 

//	val _ = show (aterm_subterm (term_alpha (TMApp (TMApp (S, K), I)), 0 :: 0 :: 0 :: 0 :: 0 :: nil ()))
//	val _ = show (aterm_subterm (term_alpha S, 0 :: 0 :: nil ()))

//	val _ = aterm_residual (term_alpha (TMApp (TMApp (S, K), I)), 0 :: 0 :: 0 :: 0 :: 0 :: nil (), 0 :: nil ())

//(
//	(
//		\.\.(0 1) 
//		(
//			(
//				\.\.(0 1) 
//				(\.0 a)
//			) 
//			\.0
//		)
//	) 
//	\.0
//)

	val M = term_from_string ("(((lam x (lam y (y x))) (((((lam x (lam y (y x))) (((lam x (x)) a)))) (lam x (x))))) (lam x (x)))")

	implement {} show_begin () = show "\n"
	implement {} show_end () = show "\n"

	fun mk (p: path): set path = set_insert (set_make (), p)

	val _ = show (aterm_beta_redexes (term_alpha M))
	val _ = show () 
	val _ = cterm_church_rosser (aterm_colorize (term_alpha M), mk (0::1::0::nil()), mk (0::1::0::1::nil()))

//	val _ = aterm_residual (term_alpha M, 0 :: 1 :: 0 :: nil (), 0 :: 1 :: 0 :: nil ())

//	val _ = show I 
//	val _ = show (aterm_bnorm I)
//	val _ = show (aterm_bnorm (ATApp (ATApp (S, K), K)))

//	val t = term_from_string ("((lam u (lam v (u x))) y)")
//	val f = term_subterm (t, 0 :: nil ())
//	val a = term_subterm (t, 1 :: nil ())

//	val _ = show (term_alpha f)
//	val _ = show ()
//	val _ = show (term_alpha a)
//	val _ = show ()

//	val _ = show (aterm_bnorm (term_alpha t))

//	val _ = show ()
//	val omega = term_from_string "(lam x (x x))"
//	val _ = show (term_alpha omega)
//	val _ = show ()
//	val oo = TMApp (omega, omega)
//	val- Just oo1 = aterm_breduce_leftmost (term_alpha oo)
//	val- Just oo2 = aterm_breduce_leftmost oo1

//	val _ = show oo2

}

end*)

(******************************)

//local
//	staload "simple.sats"
//	staload "sexp.sats"
//	staload _ = "simple.dats"
//	staload _ = "sexp.dats"
//in 

//implement test_simple () = {
//	fun term_from_string (str: string): term = let 
//		assume output_t = sexp 

//		val t = list_foldr<char,stream char> (string_explode str, $delay StreamNil (), lam (x, xs) => $delay StreamCons (x, xs))
//		val t = parser_apply (parser_sexp_sexp (), $UNSAFE.cast{input_t} t, lam (x, input) => x)
//		val _ = show t
//	in 
//		try 
//			parse_simple_term t
//		with 
//			~LamParsingException x => (println! x; $raise LamParsingException x)
//	end


//	val x = term_from_string ("(lam (x int) (add x))")
//	val _ = show x
//}

//end


(******************************)

local 
	staload "infer.sats"
	staload "sexp.sats"
	staload _ = "infer.dats"
	staload _ = "sexp.dats"
in 

implement test_infer () = {
	fun term_from_string (str: string): term = let 
		assume output_t = sexp 

		val t = list_foldr<char,stream char> (string_explode str, $delay StreamNil (), lam (x, xs) => $delay StreamCons (x, xs))
		val t = parser_apply (parser_sexp_sexp (), $UNSAFE.cast{input_t} t, lam (x, input) => x)
	in 
		try 
			parse_term t
		with 
			~LamParsingException x => (println! x; $raise LamParsingException x)
	end

	#define :: ListCons
	#define nil ListNil

	val add = term_from_string "(let ((add (lam (x y) (+ x y)))) (add 3 4))"
	val _ = show (term_alpha add)
}

end

implement main0 () = {
	val _ = test_infer ()
}




