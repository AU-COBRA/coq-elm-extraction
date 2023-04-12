From Coq Require Import String.
From MetaCoq.Erasure.Typed Require Import ResultMonad.
From MetaCoq.Template Require Import Ast.
From MetaCoq.Template Require Import LiftSubst.
From MetaCoq.Template Require Import AstUtils.
From MetaCoq.Template Require Import Loader.
From MetaCoq.Template Require Import TemplateMonad.
From MetaCoq.Template Require Import Typing.
From MetaCoq.Utils Require Import utils.
From MetaCoq.Erasure Require EAst.
From MetaCoq.SafeChecker Require Import PCUICSafeChecker.
From MetaCoq.SafeChecker Require Import PCUICWfEnvImpl.

Import PCUICErrors.
Import MCMonadNotation.

(** Extracts a constant name, inductive name or returns None *)
Definition to_kername (t : Ast.term) : option kername :=
  match t with
  | Ast.tConst c _ => Some c
  | Ast.tInd c _ => Some c.(inductive_mind)
  | _ => None
  end.

Notation "<%% t %%>" :=
  (ltac:(let p y :=
             let e := eval cbv in (to_kername y) in
             match e with
             | @Some _ ?kn => exact kn
             | _ => fail "not a name"
             end in quote_term t p)).

Definition to_globref (t : Ast.term) : option global_reference :=
  match t with
  | Ast.tConst kn _ => Some (ConstRef kn)
  | Ast.tInd ind _ => Some (IndRef ind)
  | Ast.tConstruct ind c _ => Some (ConstructRef ind c)
  | _ => None
  end.

Notation "<! t !>" :=
  (ltac:(let p y :=
             let e := eval cbv in (to_globref y) in
             match e with
             | @Some _ (ConstRef ?kn) => exact (kn : kername)
             | @Some _ (IndRef ?ind) => exact (ind : inductive)
             | @Some _ (ConstructRef ?ind ?c) => exact ((ind, c) : kername * nat)
             | _ => fail "not a globref"
             end in quote_term t p)).

Definition result_of_typing_result
           {A}
           (Σ : PCUICAst.PCUICEnvironment.global_env_ext)
           (tr : typing_result A) : result A string :=
  match tr with
  | Checked a => Ok a
  | TypeError err => Err (string_of_type_error Σ err)
  end.

Open Scope bs.

Definition string_of_env_error Σ e :=
  match e with
  | IllFormedDecl s e =>
    "IllFormedDecl " ++ s ++ "\nType error: " ++ string_of_type_error Σ e
  | AlreadyDeclared s => "Alreadydeclared " ++ s
  end.

Definition result_of_option {A} (o : option A) (err : string) : result A string :=
  match o with
  | Some a => Ok a
  | None => Err err
  end.

Definition to_string_name (t : Ast.term) : string :=
  match to_kername t with
  | Some kn => string_of_kername kn
  | None => "Not a constant or inductive"
  end.

Definition extract_def_name {A : Type} (a : A) : TemplateMonad kername :=
  a <- tmEval cbn a;;
  quoted <- tmQuote a;;
  let (head, args) := decompose_app quoted in
  match head with
  | tConst name _ => ret name
  | _ => tmFail ("Expected constant at head, got " ++ string_of_term head)
  end.

Definition extract_def_name_exists {A : Type} (a : A) : TemplateMonad kername :=
  a <- tmEval cbn a;;
  quoted <- tmQuote a;;
  let (head, args) := decompose_app quoted in
  match head with
  | tConstruct ind _ _ =>
    if eq_kername ind.(inductive_mind)
                        <%% sigT %%>
    then match nth_error args 3 with
         | Some (tConst name _) => ret name
         | Some t => tmFail ("Expected constant at second component, got " ++ string_of_term t)
         | None => tmFail ("existT: Expected 4 arguments, found less")
         end
    else tmFail ("Expected constructor existT at head, got " ++ string_of_term head)
  | _ => tmFail ("Expected constructor at head, got " ++ string_of_term head)
  end.

Definition remap (kn : kername) (new_name : String.string) : kername * String.string :=
  (kn, new_name).

(* TODO: port the pretty-printers to use bytestring and use MetaCoq's MCString utils *)

Definition parens (top : bool) (s : String.string) : String.string :=
  if top then s else "(" ++ s ++ ")".

Definition nl : String.string := String (Ascii.ascii_of_nat 10) EmptyString.
