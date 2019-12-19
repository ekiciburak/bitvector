From BV Require Import BVList InvCond.
Require Import List Bool NArith Psatz ZArith Nnat.

Include RAW2BITVECTOR(RAWBITVECTOR_LIST).


Ltac downcast :=
  repeat
    match goal with
      | [ |- forall n : N, _]           => intro n
      | [ |- forall s : bitvector _, _] => intro s
      | [ |- _ -> _ ]                   => intro
      | [ |- _ <-> _ ]                  => split; intro
      | [ s: bitvector _ |- _ ]         => destruct s as (s, ?H); cbn in *
      | [ H: _ /\ _ |- _ ]              => destruct H as (?H, ?H)
      | [ H: exists s, _ |- _ ]         => destruct H as (?s, ?H) 
      | [ H: bv_eq _ _ = true  |- _ ]   => unfold bv_eq in H;
                                           rewrite RAWBITVECTOR_LIST.bv_eq_reflect in H
      (** bv_neg *)
      | [ |- context[exists (a: bitvector ?n), 
             bv_eq (bv_neg a) 
                   {| bv := ?t; wf := ?Ht |} = true] ] =>
                  unfold bv_eq;
                  destruct (bvneg_eq n t Ht) as (?Hx1, ?Hx2);
                  cbn in *
        | [ |- context [bv_eq (bv_neg _) 
                              {| bv := ?t; wf := ?Ht |} = true] ] =>
                  unfold bv_eq;
                  rewrite RAWBITVECTOR_LIST.bv_eq_reflect;
                  destruct (bvneg_eq _ t Ht) as (?Hx1, ?Hx2)

      (** bv_not *)
      | [ |- context[exists (a: bitvector ?n), 
             bv_eq (bv_not a) 
                   {| bv := ?t; wf := ?Ht |} = true] ] =>
                  unfold bv_eq;
                  destruct (bvnot_eq n t Ht) as (?Hx1, ?Hx2);
                  cbn in *
        | [ |- context [bv_eq (bv_not _) 
                              {| bv := ?t; wf := ?Ht |} = true] ] =>
                  unfold bv_eq;
                  rewrite RAWBITVECTOR_LIST.bv_eq_reflect;
                  destruct (bvnot_eq _ t Ht) as (?Hx1, ?Hx2)

      (** bv_and *)
      | [ |- context[exists (a: bitvector ?n), 
             bv_eq (bv_and a {| bv := ?s; wf := ?Hs |}) 
                   {| bv := ?t; wf := ?Ht |} = true] ] =>
                  unfold bv_eq;
                  destruct (bvand_eq n s t Hs Ht) as (?Hx1, ?Hx2);
                  cbn in *
        | [ |- context [bv_eq (bv_and _ {| bv := ?s; wf := ?Hs |}) 
                              {| bv := ?t; wf := ?Ht |} = true] ] =>
                  unfold bv_eq;
                  rewrite RAWBITVECTOR_LIST.bv_eq_reflect;
                  destruct (bvand_eq _ s t Hs Ht) as (?Hx1, ?Hx2)

      (** bv_or *)
      | [ |- context[exists (a: bitvector ?n), 
             bv_eq (bv_or a {| bv := ?s; wf := ?Hs |}) 
                   {| bv := ?t; wf := ?Ht |} = true] ] =>
                  unfold bv_eq;
                  destruct (bvor_eq n s t Hs Ht) as (?Hx1, ?Hx2);
                  cbn in *
        | [ |- context [bv_eq (bv_or _ {| bv := ?s; wf := ?Hs |}) 
                              {| bv := ?t; wf := ?Ht |} = true] ] =>
                  unfold bv_eq;
                  rewrite RAWBITVECTOR_LIST.bv_eq_reflect;
                  destruct (bvor_eq _ s t Hs Ht) as (?Hx1, ?Hx2)

      (** bv_shl *)
      | [ |- context[exists (a: bitvector ?n), 
             bv_eq (bv_shl a {| bv := ?s; wf := ?Hs |}) 
                   {| bv := ?t; wf := ?Ht |} = true] ] =>
                  unfold bv_eq;
                  destruct (bvshl_eq n s t Hs Ht) as (?Hx1, ?Hx2);
                  cbn in *
        | [ |- context [bv_eq (bv_shl _ {| bv := ?s; wf := ?Hs |}) 
                              {| bv := ?t; wf := ?Ht |} = true] ] =>
                  unfold bv_eq;
                  rewrite RAWBITVECTOR_LIST.bv_eq_reflect;
                  destruct (bvshl_eq _ s t Hs Ht) as (?Hx1, ?Hx2)

      (** bv_shl ltr <> *)
      | [ |- context[exists (a: bitvector ?n), 
             bv_eq (bv_shl a {| bv := ?s; wf := ?Hs |}) 
                   {| bv := ?t; wf := ?Ht |} = false] ]  =>
                  let Hx1 := fresh "Hx1" in
                  specialize (bvshl_neq n s t Hs Ht); intro Hx1;
                  unfold bv_ult, bv_ashr_a, bv_eq in *;
                  rewrite Hs, Ht in Hx1

      (** bv_shl rtl <> *)
      | [ H: bv_eq (bv_shl _ {| bv := ?s; wf := ?Hs |}) 
                   {| bv := ?t; wf := ?Ht |} = false |- _ ] =>
                  let Hx1 := fresh "Hx1" in
                  specialize (bvshl_neq _ s t Hs Ht); intro Hx1;
                  unfold bv_ult, bv_ashr_a, bv_eq in *;
                  rewrite Hs, Ht in Hx1

      (** bv_ugt *)
       | [ |- context[exists (a: bitvector ?n), 
             bv_ugt (bv_shl a {| bv := ?s; wf := ?Hs |}) 
                   {| bv := ?t; wf := ?Ht |} = true] ] =>
                  destruct (bvshl_ugt n s t Hs Ht) as (?Hx1, ?Hx2);
                  unfold bv_ult, bv_shl;
                  cbn in *; 
                  rewrite Hs in Hx1

         | [ |- context [bv_ult {| bv := ?t; wf := ?Ht |} 
                        (bv_shl (bv_not (zeros ?n)) {| bv := ?s; wf := ?Hs |}) = true] ] =>
                  destruct (bvshl_ugt n s t Hs Ht) as (?Hx1, ?Hx2);
                  unfold bv_ult, bv_shl;
                  cbn in *; 
                  rewrite Hs in Hx2

      (** bv_uge *)
       | [ |- context[exists (a: bitvector ?n), 
             bv_uge (bv_shl a {| bv := ?s; wf := ?Hs |}) 
                   {| bv := ?t; wf := ?Ht |} = true] ] =>
                  destruct (bvshl_uge n s t Hs Ht) as (?Hx1, ?Hx2);
                  unfold bv_uge, bv_shl;
                  cbn in *; 
                  rewrite Hs in Hx1

         | [ |- context [bv_uge (bv_shl (bv_not (zeros ?n)) {| bv := ?s; wf := ?Hs |}) 
                                {| bv := ?t; wf := ?Ht |} = true] ] =>
                  destruct (bvshl_uge n s t Hs Ht) as (?Hx1, ?Hx2);
                  unfold bv_uge, bv_shl;
                  cbn in *; 
                  rewrite Hs in Hx2

      (** bv_shl2 *)
      | [ |- context[exists (a: bitvector ?n), 
             bv_eq (bv_shl {| bv := ?s; wf := ?Hs |} a) 
                   {| bv := ?t; wf := ?Ht |} = true] ] =>
                  unfold bv_eq;
                  destruct (bvshl_eq2 n s t Hs Ht) as (?Hx1, ?Hx2);
                  rewrite Hs in Hx1;
                  cbn in * 
      | [ |- context[exists i : nat, bv_eq (bv_shl {| bv := ?s; wf := ?Hs |} (nat2bv i ?n))
                                          {| bv := ?t; wf := ?Ht |} = true]  ] => 
                  unfold bv_eq;
                  destruct (bvshl_eq2 _ s t Hs Ht) as (?Hx1, ?Hx2);
                  rewrite Hs in Hx1;
                  cbn in * 

      (** bv_shr *)
      | [ |- context[exists (a: bitvector ?n), 
             bv_eq (bv_shr a {| bv := ?s; wf := ?Hs |}) 
                   {| bv := ?t; wf := ?Ht |} = true] ] =>
                  unfold bv_eq;
                  destruct (bvshr_eq n s t Hs Ht) as (?Hx1, ?Hx2);
                  cbn in *
        | [ |- context [bv_eq (bv_shr _ {| bv := ?s; wf := ?Hs |}) 
                              {| bv := ?t; wf := ?Ht |} = true] ] =>
                  unfold bv_eq;
                  rewrite RAWBITVECTOR_LIST.bv_eq_reflect;
                  destruct (bvshr_eq _ s t Hs Ht) as (?Hx1, ?Hx2)

      (** bv_ult *)
       | [ |- context[exists (a: bitvector ?n), 
             bv_ugt (bv_shr a {| bv := ?s; wf := ?Hs |}) 
                   {| bv := ?t; wf := ?Ht |} = true] ] =>
                  unfold bv_ugt;
                  let Hx1 := fresh in
                  specialize (bvshr_ugt_ltr n s t Hs Ht); intro Hx1

      (** bv_shr2 *)
      | [ |- context[exists (a: bitvector ?n), 
             bv_eq (bv_shr {| bv := ?s; wf := ?Hs |} a) 
                   {| bv := ?t; wf := ?Ht |} = true] ] =>
                  unfold bv_eq;
                  destruct (bvshr_eq2 n s t Hs Ht) as (?Hx1, ?Hx2);
                  rewrite Hs in Hx1;
                  cbn in * 
      | [ |- context[exists i : nat, bv_eq (bv_shr {| bv := ?s; wf := ?Hs |} (nat2bv i ?n))
                                          {| bv := ?t; wf := ?Ht |} = true]  ] => 
                  unfold bv_eq;
                  destruct (bvshr_eq2 _ s t Hs Ht) as (?Hx1, ?Hx2);
                  rewrite Hs in Hx1;
                  cbn in * 

      (** bv_ashr_a *)
      | [ |- context[exists (a: bitvector ?n), 
             bv_eq (bv_ashr_a a {| bv := ?s; wf := ?Hs |}) 
                   {| bv := ?t; wf := ?Ht |} = true] ] =>
                   unfold bv_eq in *;
                  destruct (bvashr_eq n s t Hs Ht) as (?Hx1, ?Hx2);
                  cbn in *
      
      (** bv_ashr *)
      | [ |- context[exists (a: bitvector ?n), 
             bv_eq (bv_ashr {| bv := ?s; wf := ?Hs |} a) 
                   {| bv := ?t; wf := ?Ht |} = true] ] =>
                   unfold bv_eq in *;
                   destruct (bvashr_eq2 n s t Hs Ht) as (?Hx1, ?Hx2);
                   cbn in *
      | [ |- context[exists i : nat, bv_eq (bv_ashr {| bv := ?s; wf := ?Hs |} (nat2bv i ?n))
                                          {| bv := ?t; wf := ?Ht |} = true]  ] => 
                  unfold bv_eq;
                  destruct (bvashr_eq2 _ s t Hs Ht) as (?Hx1, ?Hx2);
                  rewrite Hs in Hx1;
                  cbn in * 


      | _ => fail "no such non-dep proof found"
      end.

Ltac match_hyp h :=
  let rec hlp :=
    match goal with
      | [ h: (?A /\ ?B) -> _ |- _ ] => assert (HA: A /\ B); easy || hlp
      | [ H: _ |- _ ] => specialize (h H) || (revert H; hlp; intro H)
      | [ H: _ |- _] => apply h in H || (revert H; hlp; intro H)
      | _ => fail "no such specialization possible"
    end 
  in hlp.


Ltac exist_hyp :=
  let rec hlp :=
    match goal with
      | [H: RAWBITVECTOR_LIST.bitvector |- exists (a: RAWBITVECTOR_LIST.bitvector), _  ] => 
               try (exists H; easy) || (clear H; hlp)
      | [H: RAWBITVECTOR_LIST.size _ = _ |- exists (_ : bitvector _), _  ] => 
               (try (exists (MkBitvector H); easy)) || 
               (try (exists (MkBitvector H); now rewrite RAWBITVECTOR_LIST.bv_eq_reflect)) ||
               (clear H; hlp)
      | [H:  exists x : RAWBITVECTOR_LIST.bitvector, _ /\ _ |- exists (_ : bitvector _), _  ] => 
               destruct H as (x, (?HL, ?HR)); hlp
      | [H:  exists i : nat, _ |- exists (_ : nat), _  ] => 
               try (destruct H as (i, H); exists i;
                    rewrite RAWBITVECTOR_LIST.bv_eq_reflect; subst;
                    easy) || (clear H; hlp)
      | _ => fail "no such specialization possible"
    end 
  in hlp.

Theorem bvashr_eq2_tac: forall (n : N), forall (s t : bitvector n), 
  iff
    (exists (i : nat), bv_eq (bv_ashr s (nat2bv i n)) t = true)
    (exists (x : bitvector n), bv_eq (bv_ashr s x) t = true).
Proof. downcast.
       - assert ((exists i : nat, RAWBITVECTOR_LIST.bv_ashr s 
                 (RAWBITVECTOR_LIST.nat2bv i (RAWBITVECTOR_LIST.size s)) = t)).
         { exists i. rewrite H1. easy. }
         match_hyp Hx1.
         exist_hyp.
       - assert (exists x : RAWBITVECTOR_LIST.bitvector, RAWBITVECTOR_LIST.size x = n /\ 
                                                         RAWBITVECTOR_LIST.bv_ashr s x = t).
         { exists x. easy.  }
         match_hyp Hx2.
         exist_hyp.
Qed.

Theorem bvashr_eq_tac: forall (n : N), forall (s t : bitvector n),
   iff
    (((bv_ult s (nat2bv (N.to_nat n) n) = true) 
      ->  bv_eq (bv_ashr_a (bv_shl t s) s) t = true)
                        /\
     ((bv_ult s (nat2bv (N.to_nat n) n) = false) 
      ->  bv_eq t (bv_not (zeros n)) = true \/ (bv_eq t (zeros n) = true)))
    (exists (x : bitvector n), (bv_eq (bv_ashr_a x s) t = true)).
Proof. downcast.
       - unfold bv_ult, bv_ashr_a, nat2bv, bv_not, bv_eq, bv, wf in *. cbn in *.
         rewrite !RAWBITVECTOR_LIST.bv_eq_reflect in H.
         rewrite H0, H1 in *.
         rewrite !RAWBITVECTOR_LIST.bv_eq_reflect in H2.
         unfold RAWBITVECTOR_LIST.bv_not, RAWBITVECTOR_LIST.bits in Hx1.
         match_hyp Hx1.
         exist_hyp.
      - destruct (bvashr_eq n s t H1 H0) as (Hx1, Hx2).
        unfold bv_ult, bv_ashr_a, nat2bv, bv_not, bv_eq, bv, wf in *. cbn in *.
        rewrite H1, H0 in Hx2.
        rewrite !RAWBITVECTOR_LIST.bv_eq_reflect.
        apply Hx2.
        exist_hyp.
Qed.

Theorem bvshr_eq2_tac: forall (n : N), forall (s t : bitvector n), 
  iff 
    (exists (i : nat), bv_eq (bv_shr s (nat2bv i n)) t = true)
    (exists (x : bitvector n), bv_eq (bv_shr s x) t = true).
Proof. downcast.
       - assert (exists i, RAWBITVECTOR_LIST.bv_shr s (RAWBITVECTOR_LIST.nat2bv i n) = t).
         { exists i. easy. }
         match_hyp Hx1.
         exist_hyp.
       - assert ((exists x : RAWBITVECTOR_LIST.bitvector,
          RAWBITVECTOR_LIST.size x = n /\ RAWBITVECTOR_LIST.bv_shr s x = t)).
         { exists x. easy. }
         match_hyp Hx2.
         exist_hyp.
Qed.

(* (t <u (~s >> s)) => (exists x, (x >> s) >u t) *)
Theorem bvshr_ugt_ltr_tac: forall (n : N), forall (s t : bitvector n), 
    (bv_ult t (bv_shr (bv_not s) s) = true) -> 
    (exists (x : bitvector n), bv_ugt (bv_shr x s) t = true).
Proof. downcast.
       match_hyp H2. exist_hyp.
Qed.

(*--------------------Logical right shift 1--------------------*)
(* (t << s) >> s = t <=> (exists x, x >> s = t) *)
Theorem bvshr_eq_tac: forall (n : N), forall (s t : bitvector n), 
  iff 
    (bv_eq (bv_shr (bv_shl t s) s) t = true)
    (exists (x : bitvector n), bv_eq (bv_shr x s) t = true).
Proof. downcast.
       - match_hyp Hx1. exist_hyp.
       - apply Hx2. exist_hyp.
Qed.

(* (exists i, s << i = t) <=> (exists x, s << x = t) *)
Theorem bvshl_eq2_tac: forall (n : N), forall (s t : bitvector n), 
  iff
    (exists (i : nat), bv_eq (bv_shl s (nat2bv i n)) t = true)
    (exists (x : bitvector n), bv_eq (bv_shl s x) t = true).
Proof. downcast.
       - assert (exists i, RAWBITVECTOR_LIST.bv_shl s (RAWBITVECTOR_LIST.nat2bv i n) = t).
         { exists i. easy. }
         match_hyp Hx1.
         exist_hyp.
       - assert ((exists x : RAWBITVECTOR_LIST.bitvector,
          RAWBITVECTOR_LIST.size x = n /\ RAWBITVECTOR_LIST.bv_shl s x = t)).
          { exists x. easy. }
         match_hyp Hx2.
         exist_hyp.
Qed.

(* ~0 << s >=u t <=> x << s >= t *)
Theorem bvshl_uge_tac : forall (n : N), forall (s t : bitvector n), iff
    (bv_uge (bv_shl (bv_not (zeros n)) s) t = true)
    (exists (x : bitvector n), (bv_uge (bv_shl x s) t = true)).
Proof. downcast.
       - match_hyp Hx1. exist_hyp.
       - apply Hx2. exist_hyp.
Qed.

(* (t <u (~0 << s)) <=> (exists x, x << s >u t) *)
Theorem bvshl_ugt_tac : forall (n : N), forall (s t : bitvector n),
  iff
    (bv_ult t (bv_shl (bv_not (zeros n)) s) = true)
    (exists (x : bitvector n), (bv_ugt (bv_shl x s) t = true)).
Proof. downcast.
       - match_hyp Hx1. exist_hyp.
       - apply Hx2. exist_hyp.
Qed.

Theorem bvshl_neq_tac: forall (n : N), forall (s t : bitvector n), 
    (exists (x : bitvector n), bv_eq (bv_shl x s) t = false) <->
    bv_eq t (zeros n) = false \/ 
    bv_ult s (nat2bv (N.to_nat n) n) = true.
Proof. downcast.
       - apply Hx1. exist_hyp.
       - match_hyp Hx1. exist_hyp.
Qed.

Theorem bvand_eq_tac: forall (n : N), forall (s t : bitvector n), 
  iff 
    (bv_eq (bv_and t s) t = true)
    (exists (x : bitvector n), bv_eq (bv_and x s) t = true).
Proof. downcast.
       - match_hyp Hx1. exist_hyp.
       - apply Hx2. exist_hyp.
Qed.

Theorem bvor_eq_tac: forall (n : N), forall (s t : bitvector n), 
   iff 
    (bv_eq (bv_or t s) t = true)
    (exists (x : bitvector n), bv_eq (bv_or x s) t = true).
Proof. downcast.
       - match_hyp Hx1. exist_hyp.
       - apply Hx2. exist_hyp.
Qed.

Theorem bvshl_eq_tac: forall (n : N), forall (s t : bitvector n),
    iff
     (bv_eq (bv_shl (bv_shr t s) s) t = true)
     (exists (x : bitvector n), bv_eq (bv_shl x s) t = true).
Proof. downcast.
       - match_hyp Hx1. exist_hyp.
       - apply Hx2. exist_hyp.
Qed.

Theorem bvneg_eq_tac: forall (n : N), forall (t : bitvector n),
  iff 
    True 
    (exists (x : bitvector n), bv_eq (bv_neg x) t = true).
Proof. downcast.
       - match_hyp Hx1. exist_hyp.
       - easy.
Qed.

Theorem bvnot_eq_tac: forall (n : N), forall (t : bitvector n),
  iff
    True
    (exists (x : bitvector n), bv_eq (bv_not x) t = true).
Proof. downcast.
       - match_hyp Hx1. exist_hyp.
       - easy.
Qed. 

(*------------------------------Neg------------------------------*)
(* -x = t <=> True *)

Theorem bvneg_eq : forall (n : N), forall (t : bitvector n),
  iff 
    True 
    (exists (x : bitvector n), bv_eq (bv_neg x) t = true).
Proof.
  intros n t. unfold bv_eq, bv_neg in *.  cbn in *. split.
  + intros H. destruct t as (t, Ht).
    specialize (bvneg_eq n t Ht); intros.
    destruct H0 as (Hltr, Hrtl).
    specialize (@Hltr H). destruct Hltr as (x, (Hx, Hltr)). 
    exists (@MkBitvector n x Hx). 
    now rewrite RAWBITVECTOR_LIST.bv_eq_reflect. 
  + easy. 
Qed.

(*------------------------------------------------------------*)


(*------------------------------Not------------------------------*)
(* ~x - t <=> True *)
Theorem bvnot_eq : forall (n : N), forall (t : bitvector n),
  iff
    True
    (exists (x : bitvector n), bv_eq (bv_not x) t = true).
Proof.
  intros n t. unfold bv_eq, bv_not in *. cbn in *. split. 
  + intros H. destruct t as (t, Ht).
    specialize (bvnot_eq n t Ht); intros.
    destruct H0 as (Hltr, Hrtl). specialize (@Hltr H).
    destruct Hltr as (x, (Hx, Hltr)).
    exists (@MkBitvector n x Hx).
    now rewrite RAWBITVECTOR_LIST.bv_eq_reflect.
  + easy.
Qed.

(*------------------------------------------------------------*)

(*------------------------------And------------------------------*)
(* t & s = t <=> (exists x, x & s = t) *)
Theorem bvand_eq : forall (n : N), forall (s t : bitvector n), 
  iff 
    (bv_eq (bv_and t s) t = true)
    (exists (x : bitvector n), bv_eq (bv_and x s) t = true).
Proof. intros.
       destruct s as (s, Hs).
       destruct t as (t, Ht).
       unfold bv_and, bv_eq, bv in *.
       specialize (bvand_eq n s t Hs Ht); intros.
       destruct H as (H, Ha).
       split; intros.
       + rewrite RAWBITVECTOR_LIST.bv_eq_reflect in H0.
         specialize (H H0). 
         destruct H as (x, (Hx, p)).
         exists (@MkBitvector n x Hx).
         now rewrite RAWBITVECTOR_LIST.bv_eq_reflect.
       + rewrite RAWBITVECTOR_LIST.bv_eq_reflect. apply Ha.
         destruct H0 as ((x, Hx), p).
         rewrite RAWBITVECTOR_LIST.bv_eq_reflect in p.
         exists x. split; easy.
Qed.

(*------------------------------------------------------------*)


(*------------------------------Or------------------------------*)
(* t & s = t <=> (exists x, x | s = t) *)
Theorem bvor_eq : forall (n : N), forall (s t : bitvector n), 
   iff 
    (bv_eq (bv_or t s) t = true)
    (exists (x : bitvector n), bv_eq (bv_or x s) t = true).
Proof. intros.
       destruct s as (s, Hs).
       destruct t as (t, Ht).
       unfold bv_or, bv_eq, bv in *. cbn.
       specialize (bvor_eq n s t Hs Ht); intros.
       destruct H as (Ha, H).
       split; intros.
       + rewrite RAWBITVECTOR_LIST.bv_eq_reflect in H0.
         specialize (Ha H0). 
         destruct Ha as (x, (Hx, p)).
         exists (@MkBitvector n x Hx).
         now rewrite RAWBITVECTOR_LIST.bv_eq_reflect.
       + rewrite RAWBITVECTOR_LIST.bv_eq_reflect. apply H.
         destruct H0 as ((x, Hx), p).
         rewrite RAWBITVECTOR_LIST.bv_eq_reflect in p.
         exists x. split; easy.
Qed.

(*------------------------------------------------------------*)


(*--------------------Logical left shift 1--------------------*)
(* (t >> s) << s = t <=> (exists x, x << s = t) *)
Theorem bvshl_eq : forall (n : N), forall (s t : bitvector n),
    iff
     (bv_eq (bv_shl (bv_shr t s) s) t = true)
     (exists (x : bitvector n), bv_eq (bv_shl x s) t = true).
Proof. intros.
       destruct s as (s, Hs).
       destruct t as (t, Ht).
       unfold bv_shl, bv_eq, bv in *. cbn.
       specialize (bvshl_eq n s t Hs Ht); intros.
       destruct H as (Ha, H).
       split; intros.
       + rewrite RAWBITVECTOR_LIST.bv_eq_reflect in H0.
         specialize (Ha H0).
         destruct Ha as (x, (Hx, p)).
         exists (@MkBitvector n x Hx).
         now rewrite RAWBITVECTOR_LIST.bv_eq_reflect.
       + rewrite RAWBITVECTOR_LIST.bv_eq_reflect. apply H.
         destruct H0 as ((x, Hx), p).
         rewrite RAWBITVECTOR_LIST.bv_eq_reflect in p.
         exists x. split; easy.
Qed.


(* t != 0 or s <u size(s) <=> (exists x, x << s != t) *)
Theorem bvshl_neq_ltr: forall (n : N), forall (s t : bitvector n), 
    bv_eq t (zeros n) = false \/ 
     bv_ult s (nat2bv (N.to_nat n) n) = true ->
    (exists (x : bitvector n), bv_eq (bv_shl x s) t = false).
Proof. intros.
       destruct s as (s, Hs).
       destruct t as (t, Ht).
       unfold bv_ult, bv_ashr_a, bv_eq, bv in *. cbn in *.
       specialize (bvshl_neq_ltr n s t Hs Ht); intros.
       rewrite Ht, Hs in H0. specialize (@H0 H).
       destruct H0 as (x, (Hx, H0)). now exists (@MkBitvector n x Hx). 
Qed.

Theorem bvshl_neq_rtl: forall (n : N), forall (s t : bitvector n), 
    (exists (x : bitvector n), bv_eq (bv_shl x s) t = false) ->
    bv_eq t (zeros n) = false \/ 
    bv_ult s (nat2bv (N.to_nat n) n) = true.
Proof. intros.
       destruct s as (s, Hs).
       destruct t as (t, Ht).
       unfold bv_ult, bv_ashr_a, bv_eq, bv in *. cbn in *.
       specialize (bvshl_neq_rtl n s t Hs Ht); intros.
       rewrite Hs, Ht in H0. apply H0.
       destruct H as ((x, Hx), p).
       exists (@MkBitvector n x Hx). cbn in *.
       split. easy. apply p.
Qed.

Theorem bvshl_neq: forall (n : N), forall (s t : bitvector n), 
  iff
    (bv_eq t (zeros n) = false \/ 
     bv_ult s (nat2bv (N.to_nat n) n) = true)
    (exists (x : bitvector n), bv_eq (bv_shl x s) t = false).
Proof.
  intros. split.
  + apply bvshl_neq_ltr.
  + apply bvshl_neq_rtl.
Qed.

(* (t <u (~0 << s)) <=> (exists x, x << s >u t) *)
Theorem bvshl_ugt : forall (n : N), forall (s t : bitvector n),
  iff
    (bv_ult t (bv_shl (bv_not (zeros n)) s) = true)
    (exists (x : bitvector n), (bv_ugt (bv_shl x s) t = true)).
Proof. intros. 
        split; intros;
        destruct s as (s, Hs);
        destruct t as (t, Ht);
        unfold bv_ult, bv_ugt, bv_shl, zeros, bv_not, bits, bv in *;
        cbn in *;
        specialize (bvshl_ugt n s t Hs Ht); intros;
        unfold RAWBITVECTOR_LIST.bv_not, RAWBITVECTOR_LIST.bits in *;
        destruct H0 as (H0a, H0b).
        - rewrite Hs in H0a.
          specialize (H0a H).
          destruct H0a as (x, (Hx, p)).
          now exists (@MkBitvector n x Hx).
        - rewrite Hs in H0b.
          apply H0b.
          destruct H as ((x, Hx), p).
          exists x. split; easy.
Qed.

(* ~0 << s >=u t <=> x << s >= t *)
Theorem bvshl_uge : forall (n : N), forall (s t : bitvector n), iff
    (bv_uge (bv_shl (bv_not (zeros n)) s) t = true)
    (exists (x : bitvector n), (bv_uge (bv_shl x s) t = true)).
Proof. intros. destruct s as (s, Hs).
       destruct t as (t, Ht).
       unfold bv_uge, bv_shl, zeros, bv_not, bits, bv in *.
       specialize (bvshl_uge n s t Hs Ht); intros.
       destruct H as (Hltr, Hrtl).
       split; intros.
       - rewrite Hs in Hltr. specialize (@Hltr H). destruct Hltr as (x, (Hx, Hltr)).
         exists (@MkBitvector n x Hx). apply Hltr.
       - destruct H as ((x, Hx), H). rewrite Hs in Hrtl. 
         apply Hrtl. exists x. now split. 
Qed.

(*------------------------------------------------------------*)



(*--------------------Logical left shift 2--------------------*)
(* (exists i, s << i = t) <=> (exists x, s << x = t) *)
Theorem bvshl_eq2 : forall (n : N), forall (s t : bitvector n), 
  iff
    (exists (i : nat), bv_eq (bv_shl s (nat2bv i n)) t = true)
    (exists (x : bitvector n), bv_eq (bv_shl s x) t = true).
Proof. intros.
        destruct s as (s, Hs).
        destruct t as (t, Ht).
        unfold bv_shl, nat2bv, bv_eq, bv in *. cbn in *.
        specialize (InvCond.bvshl_eq2 n s t Hs Ht); intros.
        split; intros.
        - destruct H as (H, Ha).
          rewrite Hs in H.
          destruct H0 as (i, H0).
          rewrite RAWBITVECTOR_LIST.bv_eq_reflect in H0.
          assert (exists i, RAWBITVECTOR_LIST.bv_shl s (RAWBITVECTOR_LIST.nat2bv i n) = t).
          { exists i. easy. }
          specialize (H H1).
          destruct H as (x, (Hx, p)).
          exists (@MkBitvector n x Hx).
          now rewrite RAWBITVECTOR_LIST.bv_eq_reflect.
        - destruct H as (H, Ha).
          destruct H0 as ((x, Hx), H0).
          assert ((exists x : RAWBITVECTOR_LIST.bitvector,
          RAWBITVECTOR_LIST.size x = n /\ RAWBITVECTOR_LIST.bv_shl s x = t)).
          { exists x. rewrite RAWBITVECTOR_LIST.bv_eq_reflect in H0.
            easy. }
          specialize (Ha H1).
          destruct Ha as (i, Hi).
          exists i.
          rewrite RAWBITVECTOR_LIST.bv_eq_reflect.
          now rewrite Hs in Hi.
Qed.

(*------------------------------------------------------------*)


(*--------------------Logical right shift 1--------------------*)
(* (t << s) >> s = t <=> (exists x, x >> s = t) *)
Theorem bvshr_eq : forall (n : N), forall (s t : bitvector n), 
  iff 
    (bv_eq (bv_shr (bv_shl t s) s) t = true)
    (exists (x : bitvector n), bv_eq (bv_shr x s) t = true).
Proof. intros.
        destruct s as (s, Hs).
        destruct t as (t, Ht).
        unfold bv_eq, bv_shr, bv_shl, bv in *. cbn in *.
        specialize (InvCond.bvshr_eq n s t Hs Ht); intros.
        destruct H as (H, Ha).
        split; intros.
        - rewrite RAWBITVECTOR_LIST.bv_eq_reflect in H0.
          specialize (H H0).
          destruct H as (x, (Hx, p)).
          exists (@MkBitvector n x Hx).
          now rewrite RAWBITVECTOR_LIST.bv_eq_reflect.
        - rewrite RAWBITVECTOR_LIST.bv_eq_reflect.
          apply Ha.
          destruct H0 as ((x, Hx), H0).
          rewrite RAWBITVECTOR_LIST.bv_eq_reflect in H0.
          exists x; easy.
Qed.


(* (t <u (~s >> s)) => (exists x, (x >> s) >u t) *)
Theorem bvshr_ugt_ltr : forall (n : N), forall (s t : bitvector n), 
    (bv_ult t (bv_shr (bv_not s) s) = true) -> 
    (exists (x : bitvector n), bv_ugt (bv_shr x s) t = true).
Proof. intros.
       destruct s as (s, Hs).
       destruct t as (t, Ht).
       unfold bv_ugt, bv_ult, bv_shr, bv in *. cbn in *.
       specialize (bvshr_ugt_ltr n s t Hs Ht); intros.
       unfold RAWBITVECTOR_LIST.bv_not, RAWBITVECTOR_LIST.bits in *.
       rewrite RAWBITVECTOR_LIST.bv_shr_eq in H, H0.
       specialize (H0 H).
       destruct H0 as (x, (Hx, p)).
       rewrite RAWBITVECTOR_LIST.bv_shr_eq in p.
       exists (@MkBitvector n x Hx).
       now rewrite RAWBITVECTOR_LIST.bv_shr_eq.
Qed.

(*------------------------------------------------------------*)


(*--------------------Logical right shift 2--------------------*)
(* (exists x, s >> x = t) <=> (exists i, s >> i = t) *)
Theorem bvshr_eq2 : forall (n : N), forall (s t : bitvector n), 
  iff 
    (exists (i : nat), bv_eq (bv_shr s (nat2bv i n)) t = true)
    (exists (x : bitvector n), bv_eq (bv_shr s x) t = true).
Proof. intros.
        destruct s as (s, Hs).
        destruct t as (t, Ht).
        unfold bv_eq, bv_shr, nat2bv, bv in *. cbn in *.
        specialize (bvshr_eq2 n s t Hs Ht); intros.
        destruct H as (Ha, H).
        split;intros.
        - destruct H0 as (i, H0).
          rewrite RAWBITVECTOR_LIST.bv_eq_reflect in H0.
          assert (exists i, RAWBITVECTOR_LIST.bv_shr s (RAWBITVECTOR_LIST.nat2bv i n) = t).
          { exists i. easy. }
          rewrite <- Hs in H1.
          specialize (Ha H1).
          destruct Ha as (x, (Hx, p)).
          exists (@MkBitvector n x Hx).
          now rewrite RAWBITVECTOR_LIST.bv_eq_reflect.
        - destruct H0 as ((x, Hx), p).
          rewrite RAWBITVECTOR_LIST.bv_eq_reflect in p.
          assert ((exists x : RAWBITVECTOR_LIST.bitvector, 
              RAWBITVECTOR_LIST.size x = n /\ 
              RAWBITVECTOR_LIST.bv_shr s x = t)).
          { exists x. easy. }
          specialize (H H0).
          destruct H as (i, H).
          exists i. 
          now rewrite RAWBITVECTOR_LIST.bv_eq_reflect, <- Hs.
Qed.

(*------------------------------------------------------------*)


(*--------------------Arithmetic right shift 1--------------------*)
Theorem bvashr_eq : forall (n : N), forall (s t : bitvector n),
   iff
    (((bv_ult s (nat2bv (N.to_nat n) n) = true) 
      ->  bv_eq (bv_ashr_a (bv_shl t s) s) t = true)
                        /\
     ((bv_ult s (nat2bv (N.to_nat n) n) = false) 
      ->  bv_eq t (bv_not (zeros n)) = true \/ (bv_eq t (zeros n) = true)))
    (exists (x : bitvector n), (bv_eq (bv_ashr_a x s) t = true)).
Proof. intros.
       destruct s as (s, Hs).
       destruct t as (t, Ht).
       unfold bv_ult, bv_ashr_a, nat2bv, bv_not, bv_eq, bv, wf. cbn in *.
       rewrite !RAWBITVECTOR_LIST.bv_eq_reflect.
       specialize (InvCond.bvashr_eq n s t Hs Ht); intros.
       rewrite Hs, Ht in H. split; intros.
       + apply H in H0.
         destruct H0 as (x, (Hx, p)).
         exists (@MkBitvector n x Hx).
         now rewrite RAWBITVECTOR_LIST.bv_eq_reflect.
       + apply H.
         destruct H0 as ((x, Hx), p).
         exists x. split. easy.
         now rewrite RAWBITVECTOR_LIST.bv_eq_reflect in p.
Qed.

(*------------------------------------------------------------*)


(*--------------------Arithmetic right shift 2--------------------*)
(* (exists i, s >>a i = t) <=> (exists x, s >>a x = t) *)
Theorem bvashr_eq2 : forall (n : N), forall (s t : bitvector n), 
  iff
    (exists (i : nat), bv_eq (bv_ashr s (nat2bv i n)) t = true)
    (exists (x : bitvector n), bv_eq (bv_ashr s x) t = true).
Proof. intros.
        destruct s as (s, Hs).
        destruct t as (t, Ht).
        unfold bv_eq, bv_ashr, bv.  cbn.
        specialize (InvCond.bvashr_eq2 n s t Hs Ht); intros.
        split;intros.
        destruct H as (Ha, H).
        - destruct H0 as (i, H0).
          rewrite RAWBITVECTOR_LIST.bv_eq_reflect, <- Hs in H0.
          assert (exists i : nat, RAWBITVECTOR_LIST.bv_ashr s 
             (RAWBITVECTOR_LIST.nat2bv i (RAWBITVECTOR_LIST.size s)) = t).
          { exists i. easy. }
          specialize (Ha H1).
          destruct Ha as (x, (Hx, p)).
          exists (@MkBitvector n x Hx).
          now rewrite RAWBITVECTOR_LIST.bv_eq_reflect.
        - destruct H0 as ((x, Hx), p).
          rewrite RAWBITVECTOR_LIST.bv_eq_reflect in p.
          assert (exists x : RAWBITVECTOR_LIST.bitvector,
            RAWBITVECTOR_LIST.size x = n /\ 
            RAWBITVECTOR_LIST.bv_ashr s x = t).
          { exists x. easy. }
          apply H in H0.
          destruct H0 as (i, H0).
          exists i.
          now rewrite RAWBITVECTOR_LIST.bv_eq_reflect, <- Hs.
Qed.


(* ((s <u t \/ s >=s 0) /\ t != 0) <=> (exists x, (s >>a x) <u t) *)
Theorem bvashr_ult2_ltr : forall (n : N), forall (s t : bitvector n),
     (((bv_ult s t = true) \/ (bv_slt s (zeros n)) = false) /\
     (bv_eq t (zeros n)) = false) ->
     (exists (x : bitvector n), (bv_ult (bv_ashr_a s x) t = true)).
Proof. intros. 
        destruct H as (H1, H2).
        destruct s as (s, Hs).
        destruct t as (t, Ht).
        unfold bv_ult, bv_slt, bv_ashr_a, bv_eq, bv in *. cbn in *.
        specialize (InvCond.bvashr_ult2_ltr n s t Hs Ht); intros.
        rewrite Hs, Ht in H.
        assert ((RAWBITVECTOR_LIST.bv_ult s t = true \/
                 RAWBITVECTOR_LIST.bv_slt s (RAWBITVECTOR_LIST.zeros n) = false) /\
                 RAWBITVECTOR_LIST.bv_eq t (RAWBITVECTOR_LIST.zeros n) = false). 
        split; easy.
        specialize (H H0).
        destruct H as (x, (Hx, p)).
        exists (@MkBitvector n x Hx). easy.
Qed.

Theorem bvashr_ult2_rtl : forall (n : N), forall (s t : bitvector n),
    (exists (x : bitvector n), (bv_ult (bv_ashr_a s x) t = true)) ->
    (((bv_ult s t = true) \/ (bv_slt s (zeros n)) = false) /\ 
    (bv_eq t (zeros n)) = false).
Proof. intros n s t H. 
        destruct H as ((x, Hx), H).
        destruct s as (s, Hs).
        destruct t as (t, Ht).
        unfold bv_ult, bv_slt, bv_ashr_a, bv_eq, bv in *. cbn in *.
        specialize (InvCond.bvashr_ult2_rtl n s t Hs Ht); intro STIC.
        rewrite Hs, Ht in STIC. apply STIC.
        now exists x.
Qed.

Theorem bvashr_ult2 : forall (n : N), forall (s t : bitvector n), iff
     (((bv_ult s t = true) \/ (bv_slt s (zeros n)) = false) /\
     (bv_eq t (zeros n)) = false)
     (exists (x : bitvector n), (bv_ult (bv_ashr_a s x) t = true)).
Proof. split.
      + apply bvashr_ult2_ltr.
      + apply bvashr_ult2_rtl.
Qed.


(* ((s <s (s >> !t)) \/ (t <u s)) <=> (exists x, (s >>a x) >u t) *)
Theorem bvashr_ugt2_ltr: forall (n : N), forall (s t : bitvector n),
    ((bv_slt s (bv_shr s (bv_not t)) = true) \/ (bv_ult t s = true)) ->
    (exists (x : bitvector n), (bv_ugt (bv_ashr_a s x) t = true)).
Proof. intros. 
        destruct s as (s, Hs).
        destruct t as (t, Ht).
        unfold bv_ugt, bv_ult, bv_slt, bv_ashr_a, bv in *. cbn in *.
        specialize (bvashr_ugt2_ltr n s t Hs Ht); intros.
        unfold RAWBITVECTOR_LIST.bv_not, RAWBITVECTOR_LIST.bits in H0.
        rewrite <- RAWBITVECTOR_LIST.bv_shr_eq in H0.
        specialize (H0 H).
        destruct H0 as (x, (Hx, p)).
        exists (@MkBitvector n x Hx). easy.
Qed.

Theorem bvashr_ugt2_rtl: forall (n : N), forall (s t : bitvector n),
    (exists (x : bitvector n), (bv_ugt (bv_ashr_a s x) t = true)) ->
    ((bv_slt s (bv_shr s (bv_not t)) = true) \/ (bv_ult t s = true)).
Proof. intros n s t H.
        destruct H as ((x, Hx), H).
        destruct s as (s, Hs).
        destruct t as (t, Ht).
        unfold bv_ugt, bv_ult, bv_slt, bv_ashr_a, bv in *. cbn in *.
        specialize (InvCond.bvashr_ugt2_rtl n s t Hs Ht); intro STIC.
        rewrite <- RAWBITVECTOR_LIST.bv_shr_eq in STIC.
        apply STIC.
        now exists x.
Qed.

Theorem bvashr_ugt2: forall (n : N), forall (s t : bitvector n), iff
    ((bv_slt s (bv_shr s (bv_not t)) = true) \/ (bv_ult t s = true))
    (exists (x : bitvector n), (bv_ugt (bv_ashr_a s x) t = true)).
Proof. split.
      + apply bvashr_ugt2_ltr.
      + apply bvashr_ugt2_rtl.
Qed.


(* (s <u min(s) \/ t >= s) <=> s >>a x <= t *)
Theorem bvashr_ule2 : forall (n : N), forall (s t : bitvector n),
  iff
    ((bv_ult s (signed_min n) = true) \/ (bv_uge t s = true))
    (exists (x : bitvector n), bv_ule (bv_ashr s x) t = true).
Proof.
  intros n s t. destruct s as (s, Hs). destruct t as (t, Ht).
    unfold bv_ult, bv_uge, bv_ule, bv_ashr, signed_min in *.
    cbn in *. pose proof (@bvashr_ule2 n s t Hs Ht). 
    destruct H as (ltr, rtl). split.
  + intros H. specialize (@ltr H). destruct ltr as (x, (Hx, ltr)).
    exists (@MkBitvector n x Hx). easy.
  + intros H. destruct H as ((x, Hx), H). apply rtl. now exists x. 
Qed.


(* s >=u ~s \/ s >= t <=> s >>a x >= t *)  
Theorem bvashr_uge2 : forall (n : N), forall (s t : bitvector n),
  iff
    ((bv_uge s (bv_not s) = true) \/ (bv_uge s t = true))
    (exists (x : bitvector n), (bv_uge (bv_ashr_a s x) t = true)).
Proof.
  intros n s t. destruct s as (s, Hs). destruct t as (t, Ht).
    unfold bv_ult, bv_uge, bv_ule, bv_ashr, signed_min in *.
    cbn in *. pose proof (@bvashr_uge2 n s t Hs Ht). 
    destruct H as (ltr, rtl). split.
  + intros H. specialize (@ltr H). destruct ltr as (x, (Hx, ltr)).
    exists (@MkBitvector n x Hx). easy.
  + intros H. destruct H as ((x, Hx), H). apply rtl. now exists x. 
Qed.

(*------------------------------------------------------------*)


(*--------------------------Addition--------------------------*)
Theorem bvadd_dep: forall (n : N), forall (s t : bitvector n),
    iff 
    True
    (exists (x : bitvector n), bv_eq (bv_add x s) t = true).
Proof. intros n s t.
        split; intro A.
        - exists (bv_subt' t s).
          now rewrite bv_add_subst_opp.
        - easy.
Qed.

(*------------------------------------------------------------*)