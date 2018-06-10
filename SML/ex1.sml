val seconds = 60;

val minuts = 60;

val hours = 24;

val secs_in_hours = seconds * hours;

val pi = 3.14159;

fun area r = pi * r * r;

fun square x : real = x * x;

fun title name = "The Duke of " ^ name;

(* fun digit i = chr (i + ord #"0"); *)

fun digit i =
    if (i < 0) orelse (i > 9) then
	 NONE
    else SOME (String.sub("0123456789", i));

fun isLower c = #"a" <= c andalso c <= #"z";

type king =
     { name : string,
       born : int,
       crowned : int,
       died : int };

val henryV =
    { name = "Henry V",
      born = 1387,
      crowned = 1413,
      died = 1422 };

val henryVI =
    { name = "Henry VI",
      born = 1421,
      crowned = 1422,
      died = 1471 };

val dog =
    { name = "Tuzik",
      born = 2014 }
	
fun lifetime ({born, died, ...} : king) = died - born;

infix xor;
fun (p xor q) = (p orelse q) andalso not (p andalso q);

infix 6 plus;
fun (a plus b) = "(" ^ a ^ " + " ^ b ^ ")";
(*
> "3" plus "2" plus "1";
val it = "((3 + 2) + 1)": string
*)

