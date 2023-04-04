From BV Require Import BVList InvCond.
Require Import List Bool NArith Psatz ZArith Nnat.

Import RAWBITVECTOR_LIST.

Require Import List Bool NArith Psatz (*Int63*) ZArith Nnat.


Import ListNotations.

Lemma rev_skipn : forall (b : bitvector) (n : nat), 
  (n < length b)%nat -> rev (skipn n b) = firstn (length b - n) (rev b).
Proof.
  induction b.
  + intros n len. now contradict len.
  + intros n len. induction n.
    - rewrite skip0. rewrite Nat.sub_0_r. rewrite <- rev_length. 
      rewrite firstn_all. easy.
    - simpl. simpl in len. apply lt_S_n in len. specialize (@IHb n len).
      rewrite IHb. case n in *.
      * rewrite Nat.sub_0_r. rewrite <- rev_length. rewrite firstn_all.
        rewrite firstn_app. rewrite firstn_all. rewrite Nat.sub_diag.
        rewrite firstn_O. rewrite app_nil_r. easy.
      * apply Nat.lt_le_incl in len. 
        assert (gt0 : (0 < S n)%nat).
        { case n.
          + apply Nat.lt_0_1.
          + intros n0. apply (@Nat.lt_0_succ (S n0)). }
        pose proof (@firstn_removelast bool (length b - S n) (rev b ++ [a])).
        assert (length (rev b ++ [a]) = S (length (rev b))).
        { induction (rev b).
          + easy.
          + rewrite app_length. assert (length [a] = 1)%nat by easy.
            rewrite H0. rewrite Nat.add_1_r. easy. }
        pose proof (@Nat.sub_lt (length b) (S n) len gt0).
        rewrite <- rev_length in H1 at 2. apply Nat.lt_lt_succ_r in H1.
        rewrite <- H0 in H1. specialize (@H H1).
        rewrite <- H. rewrite removelast_app. simpl. rewrite app_nil_r. easy.
        easy.
Qed.


Lemma firstn_succ_mlf : forall (s : bitvector) (n : nat),
  firstn (S n) s = mk_list_false (S n) -> 
  firstn  n s = mk_list_false n.
Proof.
  induction s.
  + intros n H1st. easy.
  + Reconstr.scrush.
Qed.

Theorem size_len_eq : forall (x y : bitvector), size x = size y <-> 
  length x = length y.
Proof.
  intros x y. split.
  + intros H. unfold size in H. now apply Nat2N.inj in H.
  + intros H. unfold size. rewrite H. apply eq_refl.
Qed.

Fixpoint list2NR (a: list bool) (n: nat) :=
  match a with
    | []      => n
    | x :: xs => if x then list2NR xs (2 * n + 1) else list2NR xs (2 * n)
  end.

Lemma true_list2NR:
  forall (s: bitvector),
  list2NR (true :: s) 0 = list2NR s 1.
Proof. simpl. easy. Qed.

Lemma rl_fact2: forall (s: bitvector) (a: bool),
  s <> nil ->
  removelast (a :: s) = a :: removelast s.
Proof. intro s.
       induction s as [ | x xs IHs] using rev_ind.
       - simpl. easy.
       - intros a H. simpl.  
         case_eq (xs ++ [x]); intros.
         + subst. easy.
         + easy.
Qed.

Lemma list2NR_eqT:
  forall(s: bitvector) n,
  list2NR (s ++ [true]) n = S (2 * list2NR s n).
Proof. intro s.
       induction s; intros.
       - simpl. lia.
       - simpl in *.
         rewrite <- !plus_n_O in *.
         case_eq a; intros.
         + rewrite IHs. lia.
         + rewrite IHs. lia.
Qed.

Lemma list2NR_eqF:
  forall(s: bitvector) n,
  list2NR (s ++ [false]) n = (2 * list2NR s n).
Proof. intro s.
       induction s; intros.
       - simpl. lia.
       - simpl in *.
         rewrite <- !plus_n_O in *.
         case_eq a; intros.
         + rewrite IHs. lia.
         + rewrite IHs. lia.
Qed.

Lemma list2NR_eq:
  forall(s: bitvector),
  list2NR s 0 = N.to_nat (list2N (rev s)).
Proof. intros s.
       induction s using rev_ind; intros.
       - simpl. easy.
       - simpl.
         Search rev.
         rewrite rev_app_distr.
         simpl.
         case_eq x; intros.
         + rewrite N2Nat.inj_succ_double.
           rewrite <- IHs.
           rewrite list2NR_eqT.
           easy.
         + rewrite N2Nat.inj_double.
           rewrite <- IHs.
           rewrite list2NR_eqF.
           easy.
Qed.


Lemma list2NR_eq2:
  forall(s: bitvector),
  list2NR (rev s) 0 = N.to_nat (list2N s).
Proof. intros s.
       induction s; intros.
       - simpl. easy.
       - simpl.
         case_eq a; intros.
         + rewrite N2Nat.inj_succ_double.
           rewrite <- IHs.
           rewrite list2NR_eqT.
           easy.
         + rewrite N2Nat.inj_double.
           rewrite <- IHs.
           rewrite list2NR_eqF.
           easy.
Qed.


Lemma app_false: forall (s : bitvector),
  list2N s = list2N (s ++ [false]).
Proof. intro s.
       induction s as [ | x xs IHs].
       - simpl. easy.
       - simpl. case_eq x; intros.
         + rewrite IHs. easy.
         + rewrite IHs. easy.
Qed.

Compute list2NR [true; false; true] 3.
Compute 2 * (list2NR [true; false; true] 2) + 1.
Compute list2NR [false; true; true] (list2NR [false; true; true] 0).
Compute list2NR [true; false; true; false] 0.
Compute list2NR [true; false; true; false; true] 0.
Compute firstn 50 [true; false; true; false; true].
Compute list2N (rev [false; false; true; true; true; false; true]).

Definition s1 := [false; false; true; true; false; true; true; false].
Definition s2 := [true; false; true].
Definition n := 5.
Compute
list2NR (s1 ++ s2) n = list2NR s1 (list2NR s2 n + 1).
Compute
list2NR ([true] ++ s1) n = list2NR [true] (list2NR s1 n).
Compute list2NR (s1 ++ [true]) 7 = S (2 * list2NR s1 7).
Compute (list2NR s1 0).

Lemma lengthS: 
  forall (s: bitvector) x, length (s ++ [x]) = S (length s).
Proof. intro s.
       induction s; intros.
       - simpl. easy.
       - simpl. rewrite IHs. easy.
Qed.

Lemma firstN_app: forall m (s: bitvector) x,
  length s >= m -> 
  firstn m s = firstn m (s ++ [x]).
Proof. intro m.
       induction m; intros.
       - simpl. easy.
       - simpl. case_eq s; intros.
         + subst. easy.
         + simpl. rewrite <- IHm.
           easy. subst. simpl in *. lia.
Qed.

Compute firstn 2 (mk_list_false 3).
Compute mk_list_false 0.

Lemma firstN_app15:
 forall m s,
  firstn (S m) s = mk_list_false (S m) ->
  firstn m s = mk_list_false m.
Proof. intros m.
       induction m; intros.
       - simpl. easy.
       - simpl.
         case_eq s; intros.
         + subst. easy.
         + subst.
           rewrite firstn_cons in H.
           assert(mk_list_false (S (S m)) = false :: mk_list_false (S m)).
           { simpl. easy. }
           rewrite H0 in H.
           assert (b = false).
           { inversion H. easy. }
           subst.
           f_equal.
           apply IHm.
           inversion H.
           easy.
Qed.

Lemma firstN_app2:
  forall m k s, 
  m >= k ->
  firstn m s = mk_list_false m -> 
  firstn (m - k) s = mk_list_false (m - k).
Proof. intro m.
       induction m; intros.
       - simpl. easy.
       - simpl. case_eq k; intros.
         + simpl. easy.
         + apply IHm. lia.
           apply firstN_app15.
           easy.
Qed.

Lemma mklf:
forall (xs: bitvector),
mk_list_false (length xs) ++ [false] = false :: mk_list_false (length xs).
Proof. intro s.
       induction s; intros.
       - simpl. easy.
       - simpl. rewrite IHs. easy.
Qed.

Lemma first_bits_zeroA : forall (s : bitvector), 
  (length s >= (list2NR s 0)) ->
  firstn (length s - (list2NR s 0)) s = mk_list_false (length s - (list2NR s 0)).
Proof. intros s H.
       induction s as [ | x xs IHs] using (rev_ind).
       - simpl. easy.
       - simpl in *.
         case_eq x; intros.
         + subst.
           rewrite list2NR_eqT in *.
           simpl.
           rewrite <- !plus_n_O in *.
           rewrite lengthS in *.
           simpl in *.
           rewrite <- !plus_n_O in *.
           simpl in *.
           rewrite <- firstN_app.
           specialize (firstN_app2 (length xs - list2NR xs 0)
                                   (list2NR xs 0) xs); intro HH.
           rewrite Nat.sub_add_distr.
           apply HH.
           lia.
           apply IHs. lia.
           lia.
         + subst.
           rewrite list2NR_eqF in *.
           simpl.
           rewrite <- !plus_n_O in *.
           rewrite lengthS in *.
           case_eq (list2NR xs 0); intros.
           * subst.
             rewrite plus_O_n.
             rewrite H0 in *.
             rewrite <- minus_n_O in *.
             assert(S (length xs) = length(xs ++ [false])).
             { rewrite app_length. simpl. lia. }
             rewrite H1 at 1.
             rewrite firstn_all.
             simpl. rewrite <- IHs.
             rewrite firstn_all.
             rewrite firstn_all in IHs.
             rewrite IHs.
             induction xs; intros.
             ++ simpl. easy.
             ++ simpl. rewrite mklf. easy.
             ++ lia.
             ++ lia.
           * rewrite H0 in *.
             simpl.
             rewrite <- firstN_app.
             assert((length xs - (n0 + S n0)) = ((length xs - S n0) - n0)).
             { simpl. lia. }
             rewrite H1.
             specialize (firstN_app2 (length xs - S n0) (n0) xs); intro HH.
             apply HH.
             lia.
             apply IHs.
             lia. lia.
Qed.

Lemma first_bits_zero : forall (s : bitvector), 
  (N.to_nat (list2N s) < length s)%nat ->
  firstn (length s - N.to_nat (list2N s)) (rev s) = mk_list_false (length s - N.to_nat (list2N s)).
Proof. intros s H.
       rewrite <- list2NR_eq2.
       specialize(first_bits_zeroA (rev s)); intro HH.
       rewrite rev_length in HH.
       rewrite HH. easy.
       rewrite <- list2NR_eq2 in H.
       lia.
Qed.

Require Import Coq.Reals.ArithProp.

Lemma first_bits_ule : forall (x s : bitvector), size x = size s -> 
  (N.to_nat (list2N s) < length s)%nat -> 
  ule_list_big_endian 
    (firstn (length s - N.to_nat (list2N s)) x)
    (firstn (length s - N.to_nat (list2N s)) (bv_not (rev s))) = true.
 Proof.
  intros x s Hsize Hlt. pose proof (@first_bits_zero s Hlt) as Hzero.
  unfold bv_not, bits. rewrite firstn_map. rewrite Hzero.
  pose proof bv_not_false_true as negb_mlf. 
  unfold bv_not, bits in negb_mlf. rewrite negb_mlf.
  assert (len_firstn : length (firstn (length s - N.to_nat (list2N s)) x) = 
          (length s - N.to_nat (list2N s))%nat).
  { pose proof (@firstn_length_le bool x (length s - N.to_nat (list2N s))).
    pose proof Hsize as Hlen. apply size_len_eq in Hlen. rewrite Hlen in H.
    apply Nat.lt_le_incl in Hlt.
    apply le_minusni_n in Hlt.
    apply H in Hlt. apply Hlt. }
  rewrite <- len_firstn at 2. apply ule_list_big_endian_1.
Qed. 


(* (exists x, (x >> s) >u t) => (t <u (~s >> s)) *)
Theorem bvshr_ugt_rtl : forall (n : N), forall (s t : bitvector), 
  (size s) = n -> (size t) = n ->
    (exists (x : bitvector), (size x = n) /\ bv_ugt (bv_shr x s) t = true)
          ->
    (bv_ult t (bv_shr (bv_not s) s) = true).
Proof.
  intros n s t Hs Ht H. destruct H as (x, (Hx, H)).
  apply bv_ugt_bv_ult in H. rewrite bv_shr_eq in *.
  unfold bv_ult in *. rewrite Ht in *. 
  unfold ult_list in *. rewrite <- (@bv_shr_a_size n x s Hx Hs) in H. 
  rewrite <- (@bv_shr_a_size n (bv_not s) s 
                (@bv_not_size n s Hs) Hs). 
  rewrite N.eqb_refl in *.
  unfold bv_shr_a in *. rewrite Hs, Hx in *. rewrite (@bv_not_size n s Hs).
  rewrite N.eqb_refl in *. unfold shr_n_bits_a in *.
  pose proof rev_skipn. pose proof Hx as Hx2. 
  pose proof (@bv_not_size n s Hs) as Hnots. pose proof Hs as Hs2. 
  unfold size in Hx2, Hnots, Hs2. apply N2Nat.inj_iff in Hx2. 
  apply N2Nat.inj_iff in Hnots. apply N2Nat.inj_iff in Hs2. 
  rewrite Nat2N.id in Hx2, Hnots, Hs2.
  case_eq (list2nat_be_a s <? length x); intros case.
  + pose proof (@bv_not_size n s Hs) as len. pose proof Hx as Hxlen.
    unfold size in len, Hxlen. apply N2Nat.inj_iff in len. 
    apply N2Nat.inj_iff in Hxlen. rewrite Nat2N.id in len, Hxlen.
    rewrite len. rewrite <- Hxlen. rewrite case in *. 
    rewrite rev_app_distr in *. rewrite rev_mk_list_false in *.
    apply Nat.ltb_lt in case.
    rewrite (@rev_skipn x (list2nat_be_a s) case) in H.
    pose proof rev_skipn. rewrite Hx2 in case. rewrite <- Hnots in case.
    rewrite (@rev_skipn (bv_not s) (list2nat_be_a s) case).
    rewrite Hnots. rewrite <- Hx2. rewrite Hnots in case.
    rewrite <- Hs2 in case. unfold list2nat_be_a in case.
    assert (ule_list_big_endian 
              (mk_list_false (list2nat_be_a s) ++
                firstn (length x - list2nat_be_a s) (rev x))
              (mk_list_false (list2nat_be_a s) ++
                firstn (length x - list2nat_be_a s) (rev (bv_not s))) = true) as ult.
    { apply (@app_ule_list_big_endian 
              (firstn (length x - list2nat_be_a s) (rev x)) 
              (firstn (length x - list2nat_be_a s) (rev (bv_not s)))
              (mk_list_false (list2nat_be_a s))). 
      unfold list2nat_be_a. rewrite rev_bvnot. rewrite Hx2. rewrite <- Hs2.
      apply first_bits_ule. unfold size. rewrite rev_length.
      rewrite Hx2, Hs2. easy. apply case. }
    apply (@ult_ule_list_big_endian_trans 
            (rev t) 
            (mk_list_false (list2nat_be_a s) ++
              firstn (length x - list2nat_be_a s) (rev x))
            (mk_list_false (list2nat_be_a s) ++
              firstn (length x - list2nat_be_a s) (rev (bv_not s)))
            H ult).
  + rewrite case in *. rewrite Hnots. rewrite <- Hx2. rewrite case.
    apply H.
Qed.
