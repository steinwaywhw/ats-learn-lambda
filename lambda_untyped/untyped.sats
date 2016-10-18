staload "parser.sats"

typedef nat = intGte 0

datatype tvar = 
| VarName  of string
| VarIndex of int 

datatype term = 
| TMVar of tvar 
| TMLam of (tvar, term)
| TMApp of (term, term)

datatype aterm = 
| ATVar of tvar 
| ATLam of (aterm)
| ATApp of (aterm, aterm)

datatype cterm = 
| CTVar of (tvar)
| CTLam of (cterm)
| CTApp of (cterm, cterm, int)

exception LamParsingException of string

staload "sexp.sats"

fun parse_term (sexp): term 

staload "list.sats"
staload "set.sats"
staload "stream.sats"
staload "maybe.sats"

typedef path = list int 
exception PathException of ()

fun term_size (term): nat 
fun term_paths (term): set path
fun term_subterm (term, path): term 
fun term_freevars (term): set tvar 

fun term_alpha (term): aterm 

fun aterm_subterm (aterm, path): aterm 
fun aterm_shift (aterm, int): aterm 
fun aterm_subst (aterm, aterm): aterm 
fun aterm_beta_reduce (aterm, path): maybe aterm 
fun aterm_beta_redexes (aterm): set path 

//fun aterm_residual (aterm, path, path): set path 

fun aterm_colorize (aterm): cterm 

fun cterm_mark (cterm, path, int): cterm 
fun cterm_markall (cterm, set path, int): cterm 
fun cterm_shift (cterm, int): cterm 
fun cterm_subst (cterm, cterm): cterm 
//fun cterm_beta_reduce (cterm, path): maybe cterm 

fun cterm_develop (cterm, int): cterm 
fun cterm_church_rosser (cterm, set path, set path): (set path, set path)

staload "maybe.sats"

fun aterm_breduce_leftmost (aterm): maybe aterm 
fun aterm_bnorm (aterm): aterm 


