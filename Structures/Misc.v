From mathcomp.ssreflect
Require Import ssreflect ssrbool ssrnat eqtype ssrfun seq path choice fintype.
Require Import Eqdep.
From fcsl
Require Import pred prelude ordtype pcm finmap unionmap heap.
From Toychain
Require Import SeqFacts Chains.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Require Import String.

Record Address: Type := mkAddr {
    ip:string;
    port:nat
}.
Search "eqType".
Definition addr_eq (a b: Address) := (string_dec (ip a) (ip b)) && (port a==port b).
Lemma eq_addrP : Equality.axiom addr_eq. Admitted.
Canonical addr_eqMixin:= Eval hnf in EqMixin eq_addrP.

Canonical AddrEqType := Eval hnf in EqType Address addr_eqMixin.

Axiom AddrChoiceMixin : Choice.mixin_of AddrEqType.

Canonical Addr_ChoiceType := Eval hnf in ChoiceType Address AddrChoiceMixin.

Axiom AddrCountMixin : Finite.mixin_of AddrEqType.

Canonical Addr_CountType := Eval hnf in CountType Address AddrCountMixin.

Axiom AddrFinMixin : Finite.mixin_of Addr_CountType.
Canonical AddrFinType := Eval hnf in FinType Address AddrCountMixin.

Record Transaction:Type := mkTx {
    src:Address;
    dst:Address;
    val:nat;
}.


Definition trans_eq (a b:Transaction):= ((src a) == (src b)) && ((dst a) == (dst b)) && ((val a) == (val b)).
Lemma eq_transP : Equality.axiom trans_eq.
Admitted.

Canonical Trans_eqMixin := Eval hnf in EqMixin eq_transP.
Canonical Trans_eqType := Eval hnf in EqType Transaction Trans_eqMixin.