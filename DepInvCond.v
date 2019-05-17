From BV Require Import BVList InvCond.
Require Import List Bool NArith Psatz (*Int63*) ZArith Nnat.

Include RAW2BITVECTOR(RAWBITVECTOR_LIST).

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

(* (exists x, x << s != t) => t != 0 or s <u size(s) *)
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
(*------------------------------------------------------------*)



(*--------------------Logical left shift 2--------------------*)
(* (exists i, s << i = t) <=> (exists x, s << x = t) *)
Theorem bvshl_eq2 : forall (n : N), forall (s t : bitvector n), 
  iff
    (exists (i : nat), 
      ((bv_shl s (nat2bv i n)) = t))
    (exists (x : bitvector n), (bv_shl s x = t)).
Proof. intros.
        destruct s as (s, Hs).
        destruct t as (t, Ht).
        unfold bv_shl, nat2bv, bv in *. cbn in *.
        specialize (InvCond.bvshl_eq2 n s t Hs Ht); intros.
        destruct H as (H, Ha).
        split; intros.
        + destruct H0 as (i, H0). exists (nat2bv i n). apply H0.
        + destruct H0 as (x, H0). exists (bv2nat_a x).
          (*unfold bv2nat_a, nat2bv. apply H0.*)
Admitted.
(*------------------------------------------------------------*)


(*--------------------Logical right shift 1--------------------*)
(* (t << s) >> s = t <=> (exists x, x >> s = t) *)
Theorem bvshr_eq : forall (n : N), forall (s t : bitvector n), 
  iff 
    (bv_shr (bv_shl t s) s = t)
    (exists (x : bitvector n), bv_shr x s = t).
Proof. intros.
        destruct s as (s, Hs).
        destruct t as (t, Ht).
        unfold bv_shr, bv_shl, bv, wf in *. cbn in *.
        specialize (InvCond.bvshr_eq n s t Hs Ht); intros.
        destruct H as (H, Ha).
        split; intros.
        + 
Admitted.

(* (t <u (~s >> s)) <=> (exists x, (x >> s) >u t) *)
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
Theorem bvshr_ugt_rtl : forall (n : N), forall (s t : bitvector n), 
    (exists (x : bitvector n), bv_ugt (bv_shr x s) t = true) ->
    (bv_ult t (bv_shr (bv_not s) s) = true).
Proof. intros.
        destruct s as (s, Hs).
        destruct t as (t, Ht).
        destruct H as ((x, Hx), H).
        unfold bv_ugt, bv_ult, bv_shr_a, bv in *. cbn in *.
        specialize (bvshr_ugt_rtl n s t Hs Ht); intros.
        rewrite RAWBITVECTOR_LIST.bv_shr_eq in *.
        apply H0. exists x. split. apply Hx.
        now rewrite RAWBITVECTOR_LIST.bv_shr_eq.
Qed.
Theorem bvshr_ugt : forall (n : N), forall (s t : bitvector n), iff
    (bv_ult t (bv_shr (bv_not s) s) = true)
    (exists (x : bitvector n), bv_ugt (bv_shr x s) t = true).
Proof. split.
        + apply bvshr_ugt_ltr.
        + apply bvshr_ugt_rtl.
Qed.
(*------------------------------------------------------------*)


(*--------------------Logical right shift 2--------------------*)
(* (exists x, s >> x = t) <=> (exists i, s >> i = t) *)
Theorem bvshr_eq2 : forall (n : N), forall (s t : bitvector n), 
  iff 
    (exists (i : nat), 
      ((bv_shr s (nat2bv i n)) = t))
    (exists (x : bitvector n), bv_shr s x = t).
Proof. intros.
        destruct s as (s, Hs).
        destruct t as (t, Ht).
        unfold bv_shr, nat2bv, bv in *. cbn.
        specialize (bvshr_eq2 n s t Hs Ht); intros.
        destruct H as (Ha, H).
        split;intros.
        + destruct H0 as (i, H0). exists (nat2bv i n). apply H0.
        + destruct H0 as (x, H0). exists (bv2nat_a x). 
Admitted.
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
    (exists (i : nat), 
      ((bv_ashr s (nat2bv i n)) = t))
    (exists (x : bitvector n), (bv_ashr s x = t)).
Proof. intros.
        destruct s as (s, Hs).
        destruct t as (t, Ht).
        unfold bv_ashr, bv, wf. cbn.
        specialize (InvCond.bvashr_eq2 n s t Hs Ht); intros.
        split;intros.
        + destruct H0 as (i, H0).
          exists (nat2bv i n). apply H0.
        + destruct H as (H, Ha). destruct H0 as (x, H0). 
          exists (bv2nat_a x). 
Admitted.

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
    ((bv_slt s (bv_shr_a s (bv_not t)) = true) \/ (bv_ult t s = true)) ->
    (exists (x : bitvector n), (bv_ugt (bv_ashr_a s x) t = true)).
Proof. intros. 
        destruct s as (s, Hs).
        destruct t as (t, Ht).
        unfold bv_ugt, bv_ult, bv_slt, bv_ashr_a, bv in *. cbn in *.
        specialize (bvashr_ugt2_ltr n s t Hs Ht); intros.
        unfold RAWBITVECTOR_LIST.bv_not, RAWBITVECTOR_LIST.bits in H0.
        specialize (H0 H).
        destruct H0 as (x, (Hx, p)).
        exists (@MkBitvector n x Hx). easy.
Qed.
Theorem bvashr_ugt2_rtl: forall (n : N), forall (s t : bitvector n),
    (exists (x : bitvector n), (bv_ugt (bv_ashr_a s x) t = true)) ->
    ((bv_slt s (bv_shr_a s (bv_not t)) = true) \/ (bv_ult t s = true)).
Proof. intros. 
        destruct H as (x, H).
        destruct s as (s, Hs).
        destruct t as (t, Ht).
        destruct x as (x, Hx).
        unfold bv_ugt, bv_ult, bv_slt, bv_ashr_a, bv in *. cbn in *.
        specialize (InvCond.bvashr_ugt2_rtl n s t Hs Ht); intro IC.
        apply IC.
        now exists x.
Qed.
Theorem bvashr_ugt2: forall (n : N), forall (s t : bitvector n), iff
    ((bv_slt s (bv_shr_a s (bv_not t)) = true) \/ (bv_ult t s = true))
    (exists (x : bitvector n), (bv_ugt (bv_ashr_a s x) t = true)).
Proof. split.
      + apply bvashr_ugt2_ltr.
      + apply bvashr_ugt2_rtl.
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