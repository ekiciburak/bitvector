We are trying to return to and solve our challenge problem.
The invertibility condition is for right shift and unsigned greater than on bit-vectors:
`(exists x, (x >> s) >u t) <=> (t <u (~s >> s))`,
and the challenging case is in the left-to-right direction of the equivalence:
`(exists x, (x >> s) >u t) => (t <u (~s >> s))`.
In my multiple approaches to prove this implication, it seems like I have diverged down multiple paths.
Broadly, there are the old and new attempts. Note that the labels `ltr` and `rtl` were inverted, so the 
same goal is called `bvshr_ugt_rtl` in the old attempt and `bvshr_ugt_ltr` in the new attempt. 
Either way, the Coq goal is:
```
forall (n : N), forall (s t : bitvector), 
  (size s) = n -> (size t) = n ->
    (exists (x : bitvector), (size x = n) /\ bv_ugt (bv_shr x s) t = true)
          ->
    (bv_ult t (bv_shr (bv_not s) s) = true).
```

# Old Attempt
- Introduce premises, and skolemize existential premise.
- Simplify/unfold definitions. Importantly, replace `bv_shr` by alternative definition `bv_shr_a` which uses `skipn`.
- Use `rev_skipn` that proves
  ```
  rev_skipn: forall (b : bitvector) (n : nat), 
  (n < length b)%nat -> rev (skipn n b) = firstn (length b - n) (rev b).
  ```
  and simplify/unfold further.
- Case split on `toNat(s) < length(x)`
  1. If yes, 
    + Further simplify the context and goal, until we can use `rev_skipn` to replace
      the `skipn` in the goal with `firstn`.
    + Locally prove 
      ```
      [00..0] ++ firstn (length(x) - toNat(s)) (rev x)
                          <=u
      [00..0] ++ firstn (length(x) - toNat(s)) (rev (~s))
      ```
      which essentially reduces to `first_bits_ule` which proves the same thing as above with the `[00..0]` removed.
      ```
      firstn (length(x) - toNat(s)) (rev x)
                       <=u
      firstn (length(x) - toNat(s)) (rev (~s))
      ```
      which, in turn, reduces to `first_bits_zero`:
      ```
      toNat(s) < length(s) -> firstn (length(s) - toNat(s)) (rev s) = [00..0]
      ```
      and this is what we are trying to prove using 4 different approaches:
      1. induction on `length(s) - toNat(s)`; 
      2. induction on `length(s)` followed by 
      case splitting on `toNat(s)`, 
      3. induction on `length(s)` followed by 
      case splitting on `toNat(s)`, 
      4. induction on `toNat(s)` followed by 
      case splitting on `length(s)` 
      
      Approach 4 seems most promising (in terms
      of results) where for the induction on `toNat(s)`, I am able to prove both
      cases of the inductive case and the first case of the base case, and am
      only failing on the second case of the base case to prove 
      `length s = S n -> firstn (S n) (rev s) = mk_list_false (S n)` but this
      should be easy in theory, since in the base case `length(s) = 0`, but 
      Coq is not allowing me to retain this fact and use it in the proof.
  2. If no, then it is trivial to prove `t <u (~s >> s)`.


# New Attempt
There seems to be two approaches here.
## The `toNat` Approach
- Introduce premises, and skolemize existential premise.
- We don't rewrite `bv_shr` in terms of `bv_shr_a` simply because the 
  lemma here is already stated in terms of `bv_shr_a`.
- Change the `<u` in premise and conclusion to `<` over naturals.
- Then we do a lot of shit but essentially this reduces to 
  `skipn_bvnot`:
  ```
  forall (b : bitvector), toNat(b) < length (b) -> 
  skipn toNat(b) ~b = mk_list_true (length (b) - toNat(b)).
  ```
  which is essentially the same thing as `first_bits_zero` above
  with the direction and polarity of the BV reversed. But we 
  further reduce this to align the polarity in `skipn_b_zeros`:
  ```
  forall (b : bitvector), toNat(b) < length (b) -> 
  skipn toNat(b) b = mk_list_false (length (b) - toNat(b)).
  ```

## The Old Approach
- Introduce premises, and skolemize existential premise.
- Simplify/unfold definitions. Importantly, replace `bv_shr` by alternative definition `bv_shr_a` which uses `skipn`.
- Reduce proof to `ule_shr_shrnot`:
  ```
  forall (a b : bitvector), toNat(b) < length(b) ->
    (a >> b) <u (~b >> b).
  ```