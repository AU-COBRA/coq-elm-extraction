From Coq Require Import Ascii.
From Coq Require Import List.
From Coq Require Import NArith.
From Coq Require Import String.

Import ListNotations.
Local Open Scope string.

Local Open Scope positive.

Definition Nlog2up_nat (n : N) : nat :=
  match n with
  | N0 => 1
  | Npos p => Pos.size_nat p
  end.

Local Open Scope N.
Definition string_of_N (n : N) : string :=
  (fix f n num acc :=
     let (q, r) := N.div_eucl num 10 in
     let char :=
         match r with
         | 0 => "0"
         | 1 => "1"
         | 2 => "2"
         | 3 => "3"
         | 4 => "4"
         | 5 => "5"
         | 6 => "6"
         | 7 => "7"
         | 8 => "8"
         | 9 => "9"
         | _ => "x" (* unreachable *)
         end%char in
     let acc := String char acc in
     if q =? 0 then
       acc
     else
       match n with
       | 0%nat => "" (* unreachable *)
       | S n => f n q acc
       end) (Nlog2up_nat n) n EmptyString.

Definition string_of_nat (n : nat) : string :=
  string_of_N (N.of_nat n).

Definition replace_char (orig : ascii) (new : ascii) : string -> string :=
  fix f s :=
    match s with
    | EmptyString => EmptyString
    | String c s => if (c =? orig)%char then
                      String new (f s)
                    else
                      String c (f s)
    end.

Definition remove_char (c : ascii) : string -> string :=
  fix f s :=
    match s with
    | EmptyString => EmptyString
    | String c' s => if (c' =? c)%char then
                       f s
                     else
                       String c' (f s)
    end.

Local Open Scope char.

Fixpoint substring_from (from : nat) (s : string) : string :=
  match from, s with
  | 0%nat, _ => s
  | S n, String _ s => substring_from n s
  | S n, EmptyString => EmptyString
  end.

Fixpoint substring_count (count : nat) (s : string) : string :=
  match count, s with
  | 0%nat, _ => EmptyString
  | S n, String c s => String c (substring_count n s)
  | S n, EmptyString => EmptyString
  end.

Local Open Scope N.

Definition is_letter (c : ascii) : bool :=
  let n := N_of_ascii c in
  (65 (* A *) <=? n) && (n <=? 90 (* Z *)) ||
  (97 (* a *) <=? n) && (n <=? 122 (* z *))%bool%N.

Definition char_to_upper (c : ascii) : ascii :=
  if is_letter c then
    match c with
    | Ascii b0 b1 b2 b3 b4 b5 b6 b7 =>
      Ascii b0 b1 b2 b3 b4 false b6 b7
    end
  else
    c.

Definition char_to_lower (c : ascii) : ascii :=
  if is_letter c then
    match c with
    | Ascii b0 b1 b2 b3 b4 b5 b6 b7 =>
      Ascii b0 b1 b2 b3 b4 true b6 b7
    end
  else
    c.

Definition capitalize (s : string) : string :=
  match s with
  | EmptyString => EmptyString
  | String c s => String (char_to_upper c) s
  end.

Definition uncapitalize (s : string) : string :=
  match s with
  | EmptyString => EmptyString
  | String c s => String (char_to_lower c) s
  end.

Definition lines (l : list string) :=
  String.concat (String (ascii_of_nat 10) "") l.

Notation "<$ x ; y ; .. ; z $>" :=
  (lines (List.cons x (List.cons y .. (List.cons z List.nil) ..))) : string_scope.
