From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib.Strings Require Import Byte.
From MetaRocq.Utils Require Import bytestring.

Import String.
Import ListNotations.
Local Open Scope bs_scope.
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
         | 0 => String "0"
         | 1 => String "1"
         | 2 => String "2"
         | 3 => String "3"
         | 4 => String "4"
         | 5 => String "5"
         | 6 => String "6"
         | 7 => String "7"
         | 8 => String "8"
         | 9 => String "9"
         | _ => String "x" (* unreachable *)
         end in
     let acc := char acc in
     if q =? 0 then
       acc
     else
       match n with
       | 0%nat => "" (* unreachable *)
       | S n => f n q acc
       end) (Nlog2up_nat n) n EmptyString.

Definition string_of_nat (n : nat) : string :=
  string_of_N (N.of_nat n).

Definition replace_char (orig : byte) (new : byte) : string -> string :=
  fix f s :=
    match s with
    | EmptyString => EmptyString
    | String c s => if (c =? orig)%byte then
                      String new (f s)
                    else
                      String c (f s)
    end.

Definition remove_char (c : byte) : string -> string :=
  fix f s :=
    match s with
    | EmptyString => EmptyString
    | String c' s => if (c' =? c)%byte then
                       f s
                     else
                       String c' (f s)
    end.

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

Definition is_letter (c : byte) : bool :=
  let n := to_N c in
  (65 (* A *) <=? n) && (n <=? 90 (* Z *)) ||
  (97 (* a *) <=? n) && (n <=? 122 (* z *))%bool%N.

Definition char_to_upper (c : byte) : byte :=
  if is_letter c then
    let '(b0, (b1, (b2, (b3, (b4, (b5, (b6, b7))))))) := Byte.to_bits c in
    Byte.of_bits (b0, (b1, (b2, (b3, (b4, (false, (b6, b7)))))))
  else
    c.

Definition char_to_lower (c : byte) : byte :=
  if is_letter c then
    let '(b0, (b1, (b2, (b3, (b4, (b5, (b6, b7))))))) := Byte.to_bits c in
    Byte.of_bits (b0, (b1, (b2, (b3, (b4, (true, (b6, b7)))))))
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
  String.concat (String x0a "") l.

Notation "<$ x ; y ; .. ; z $>" :=
  (lines (List.cons x (List.cons y .. (List.cons z List.nil) ..))) : bs_scope.
