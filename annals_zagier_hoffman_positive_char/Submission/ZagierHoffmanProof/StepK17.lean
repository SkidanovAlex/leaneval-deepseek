import Submission.ZagierHoffmanProof.StepK16

set_option autoImplicit false
set_option maxHeartbeats 8000000

open Polynomial
open scoped BigOperators

/-!
# Step K17: the complete-homogeneous tower and its Frobenius difference (KEY lemma)

For `q = |F|` and natural numbers `a, r, m`, `hh a r m ∈ F[X]` is the complete
homogeneous polynomial of degree `m` in the `r` variables
`X^{q^a}, …, X^{q^{a+r-1}}` (start index `a`; recursive split by the last variable,
structural recursion on `r`).  The Frobenius shift is clean:
`(hh a r m)^q = hh (a+1) r m` (`hh_frob`), and the last-variable recursion is `hh_rec`.
The ★ tower identity (`hh_key`, PLAN SESSION 151) is

    hh a r m − hh (a+1) r m = (X^{q^a} − X^{q^{a+r}}) · hh a (r+1) (m−1)   (m ≥ 1),

proven by induction on `r` with an inner induction on `m` (base: telescoping
`hh_key_degone`; step: outer KEY at level `r`, inner KEY at level `m−1`, both
`hh_rec` expansions).  With `a = 0` and `hh_frob` this is the Session-151 form
(`tower_identity`):

    h_m(X,…,X^{q^{r-1}}) − h_m(X,…,X^{q^{r-1}})^q = (X − X^{q^r})·h_{m−1}(X,…,X^{q^r}).

This is the engine of the uniform `EvalStep d` reduction for every `d` (the per-stage
coefficient collapse of `U_d`; the full reduction is the next milestone).  All lemmas
here are sorry-free.
-/

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]




/-- Complete homogeneous polynomial of degree `m` in the `r` variables
`X^{q^a}, …, X^{q^{a+r-1}}` (`q = |F|`), as an element of `F[X]`:

    hh a 0 m = if m = 0 then 1 else 0        (no variables)
    hh a (r+1) m = Σ_{i=0}^{m} (X^{q^{a+r}})^i · hh a r (m − i)   (split by last variable)

Structural recursion on `r`.  Frobenius shifts the start: `(hh a r m)^q = hh (a+1) r m`. -/
noncomputable def hh (a : ℕ) : ℕ → ℕ → F[X]
  | 0, m => if m = 0 then 1 else 0
  | r + 1, m => ∑ i ∈ Finset.range (m + 1), (X ^ ((Nat.card F) ^ (a + r))) ^ i * hh a r (m - i)

/-- `hh a r 0 = 1`. -/
lemma hh_zero (a r : ℕ) : hh F a r 0 = 1 := by
  induction r with
  | zero => simp [hh]
  | succ r ih => rw [hh]; simp [ih]

/-- `hh a 0 (m+1) = 0`. -/
lemma hh_empty (a m : ℕ) : hh F a 0 (m + 1) = 0 := by
  simp [hh]

/-- `hh a 1 m = X^{q^a·m}` (one variable). -/
lemma hh_one (a m : ℕ) : hh F a 1 m = (X ^ ((Nat.card F) ^ a)) ^ m := by
  classical
  induction m with
  | zero =>
      rw [hh]
      simp [hh_zero F a 0]
  | succ m ih =>
      rw [hh]
      have hzero : (∑ i ∈ Finset.range (m + 1),
          (X ^ ((Nat.card F) ^ (a + 0))) ^ i * hh F a 0 (m + 1 - i)) = 0 := by
        apply Finset.sum_eq_zero
        intro i hi
        have hi' : i < m + 1 := Finset.mem_range.mp hi
        have hmk : m + 1 - i = (m - i) + 1 := by omega
        rw [hmk]
        rw [hh_empty F a (m - i)]
        simp
      rw [Finset.sum_range_succ]
      rw [hzero]
      simp [hh]

/-- recursion by the last variable:
`hh a (r+1) (m+1) = hh a r (m+1) + X^{q^{a+r}}·hh a (r+1) m`. -/
lemma hh_rec (a r m : ℕ) :
    hh F a (r + 1) (m + 1) = hh F a r (m + 1) + X ^ ((Nat.card F) ^ (a + r)) * hh F a (r + 1) m := by
  classical
  calc
    hh F a (r + 1) (m + 1)
        = (∑ i ∈ Finset.range (m + 1), (X ^ ((Nat.card F) ^ (a + r))) ^ (i + 1) * hh F a r (m + 1 - (i + 1)))
            + hh F a r (m + 1) := by
          rw [hh, Finset.sum_range_succ']
          simp
    _ = X ^ ((Nat.card F) ^ (a + r)) * hh F a (r + 1) m + hh F a r (m + 1) := by
          have hfac : (∑ i ∈ Finset.range (m + 1),
              (X ^ ((Nat.card F) ^ (a + r))) ^ (i + 1) * hh F a r (m + 1 - (i + 1))) =
              X ^ ((Nat.card F) ^ (a + r)) * hh F a (r + 1) m := by
            calc
              (∑ i ∈ Finset.range (m + 1),
                  (X ^ ((Nat.card F) ^ (a + r))) ^ (i + 1) * hh F a r (m + 1 - (i + 1)))
                  = ∑ i ∈ Finset.range (m + 1),
                      (X ^ ((Nat.card F) ^ (a + r))) * ((X ^ ((Nat.card F) ^ (a + r))) ^ i * hh F a r (m - i)) := by
                    apply Finset.sum_congr rfl
                    intro i hi
                    have hi' : i < m + 1 := Finset.mem_range.mp hi
                    have hmm : m + 1 - (i + 1) = m - i := by omega
                    rw [pow_succ', hmm, ← mul_assoc]
              _ = (X ^ ((Nat.card F) ^ (a + r))) * (∑ i ∈ Finset.range (m + 1),
                      (X ^ ((Nat.card F) ^ (a + r))) ^ i * hh F a r (m - i)) := by
                    rw [← Finset.mul_sum]
              _ = (X ^ ((Nat.card F) ^ (a + r))) * hh F a (r + 1) m := by
                    rw [hh]
          rw [hfac]
    _ = hh F a r (m + 1) + X ^ ((Nat.card F) ^ (a + r)) * hh F a (r + 1) m := by
          ring

/-- Frobenius shifts the start index: `(hh a r m)^q = hh (a+1) r m`, `q = |F|`. -/
lemma hh_frob (a r m : ℕ) :
    (hh F a r m) ^ (Nat.card F) = hh F (a + 1) r m := by
  classical
  induction r generalizing m with
  | zero =>
      by_cases hm : m = 0
      · subst m
        simp [hh]
      · have hm' : m = (m - 1) + 1 := by omega
        have hne : Nat.card F ≠ 0 := by
          have hq' : 2 ≤ Nat.card F := card_ge_two F
          omega
        rw [hm']
        simp [hh, zero_pow hne]
  | succ r ih =>
      let A : F[X] := X ^ ((Nat.card F) ^ (a + r))
      letI : Fintype F := Fintype.ofFinite F
      haveI : CharP F (ringChar F) := ringChar.charP F
      rcases FiniteField.card (K := F) (p := ringChar F) with ⟨n, hprime, hcard⟩
      haveI : Fact (Nat.Prime (ringChar F)) := ⟨hprime⟩
      have hcard' : Nat.card F = (ringChar F) ^ (n : ℕ) := by
        rw [← Fintype.card_eq_nat_card]
        exact hcard
      haveI : CharP (F[X]) (ringChar F) := by
        refine charP_of_injective_algebraMap (R := F) (A := F[X]) ?_ (ringChar F)
        intro a b h
        exact Polynomial.C_injective h
      have hpowsum :
          (∑ i ∈ Finset.range (m + 1), A ^ i * hh F a r (m - i)) ^ (Nat.card F)
            = ∑ i ∈ Finset.range (m + 1), (A ^ i * hh F a r (m - i)) ^ (Nat.card F) := by
        have hf := sum_pow_char_pow' (p := ringChar F) (n := (n : ℕ)) (R := F[X])
          (s := (Finset.range (m + 1) : Finset ℕ))
          (f := fun i : ℕ => A ^ i * hh F a r (m - i))
        rw [← hcard'] at hf
        exact hf
      have hAq : A ^ (Nat.card F) = X ^ ((Nat.card F) ^ (a + r + 1)) := by
        dsimp [A]
        calc
          (X ^ ((Nat.card F) ^ (a + r)) : F[X]) ^ (Nat.card F)
              = X ^ (((Nat.card F) ^ (a + r)) * (Nat.card F)) := (pow_mul X ((Nat.card F) ^ (a + r)) (Nat.card F)).symm
          _ = X ^ ((Nat.card F) ^ (a + r + 1)) := by
                congr 1
      have hper (i : ℕ) (hi : i ∈ Finset.range (m + 1)) :
          (A ^ i * hh F a r (m - i)) ^ (Nat.card F) =
            (X ^ ((Nat.card F) ^ (a + r + 1))) ^ i * hh F (a + 1) r (m - i) := by
        have h1 : (A ^ i) ^ (Nat.card F) = (A ^ (Nat.card F)) ^ i := by
          calc
            (A ^ i) ^ (Nat.card F) = A ^ (i * Nat.card F) := (pow_mul A i (Nat.card F)).symm
            _ = A ^ ((Nat.card F) * i) := by congr 1; exact Nat.mul_comm i (Nat.card F)
            _ = (A ^ (Nat.card F)) ^ i := pow_mul A (Nat.card F) i
        calc
          (A ^ i * hh F a r (m - i)) ^ (Nat.card F)
              = (A ^ i) ^ (Nat.card F) * (hh F a r (m - i)) ^ (Nat.card F) := by rw [mul_pow]
          _ = (A ^ (Nat.card F)) ^ i * (hh F a r (m - i)) ^ (Nat.card F) := by rw [h1]
          _ = (A ^ (Nat.card F)) ^ i * hh F (a + 1) r (m - i) := by rw [ih (m - i)]
          _ = (X ^ ((Nat.card F) ^ (a + r + 1))) ^ i * hh F (a + 1) r (m - i) := by rw [hAq]
      calc
        (hh F a (r + 1) m) ^ (Nat.card F)
            = (∑ i ∈ Finset.range (m + 1), A ^ i * hh F a r (m - i)) ^ (Nat.card F) := by
              rw [hh]
        _ = ∑ i ∈ Finset.range (m + 1), (A ^ i * hh F a r (m - i)) ^ (Nat.card F) := hpowsum
        _ = ∑ i ∈ Finset.range (m + 1),
              (X ^ ((Nat.card F) ^ (a + r + 1))) ^ i * hh F (a + 1) r (m - i) := by
              apply Finset.sum_congr rfl
              intro i hi
              exact hper i hi
        _ = hh F (a + 1) (r + 1) m := by
              rw [hh]
              apply Finset.sum_congr rfl
              intro i hi
              have hE : (Nat.card F) ^ (a + r + 1) = (Nat.card F) ^ ((a + 1) + r) := by
                congr 1
                omega
              rw [hE]


/-- degree-one tower difference telescopes: `hh a r 1 − hh (a+1) r 1 = X^{q^a} − X^{q^{a+r}}`. -/
lemma hh_key_degone (a r : ℕ) :
    hh F a r 1 - hh F (a + 1) r 1 = X ^ ((Nat.card F) ^ a) - X ^ ((Nat.card F) ^ (a + r)) := by
  classical
  induction r with
  | zero =>
      simp [hh, hh_empty F a 0, hh_empty F (a + 1) 0]
  | succ r ih =>
      have hE : (Nat.card F) ^ ((a + 1) + r) = (Nat.card F) ^ (a + (r + 1)) := by
        congr 1
        omega
      calc
        hh F a (r + 1) 1 - hh F (a + 1) (r + 1) 1
            = (hh F a r 1 + X ^ ((Nat.card F) ^ (a + r))) - (hh F (a + 1) r 1 + X ^ ((Nat.card F) ^ ((a + 1) + r))) := by
              rw [hh_rec F a r 0, hh_rec F (a + 1) r 0]
              simp [hh_zero F a (r + 1), hh_zero F (a + 1) (r + 1)]
        _ = (hh F a r 1 + X ^ ((Nat.card F) ^ (a + r))) - (hh F (a + 1) r 1 + X ^ ((Nat.card F) ^ (a + (r + 1)))) := by
              rw [hE]
        _ = (X ^ ((Nat.card F) ^ a) - X ^ ((Nat.card F) ^ (a + r))) + X ^ ((Nat.card F) ^ (a + r)) - X ^ ((Nat.card F) ^ (a + (r + 1))) := by
              have hL : hh F a r 1 + X ^ ((Nat.card F) ^ (a + r)) - (hh F (a + 1) r 1 + X ^ ((Nat.card F) ^ (a + (r + 1)))) =
                  (hh F a r 1 - hh F (a + 1) r 1) + X ^ ((Nat.card F) ^ (a + r)) - X ^ ((Nat.card F) ^ (a + (r + 1))) := by ring
              rw [hL, ih]
        _ = X ^ ((Nat.card F) ^ a) - X ^ ((Nat.card F) ^ (a + (r + 1))) := by
              ring


/-- ★ THE TOWER IDENTITY: `hh a r m − hh (a+1) r m = (X^{q^a} − X^{q^{a+r}})·hh a (r+1) (m−1)`
for `m ≥ 1`.  Equivalently (with `a = 0`, via `hh_frob`):
`h_m(X,…,X^{q^{r-1}}) − h_m(X,…,X^{q^{r-1}})^q = (X − X^{q^r})·h_{m−1}(X,…,X^{q^r})`. -/
lemma hh_key (a r : ℕ) : ∀ (m : ℕ), 1 ≤ m →
    hh F a r m - hh F (a + 1) r m =
      (X ^ ((Nat.card F) ^ a) - X ^ ((Nat.card F) ^ (a + r))) * hh F a (r + 1) (m - 1) := by
  classical
  induction r with
  | zero =>
      intro m hm
      have hm' : m = (m - 1) + 1 := by omega
      rw [hm']
      simp [hh]
  | succ r ihr =>
      intro m hm
      induction m with
      | zero => omega
      | succ m' ih' =>
          by_cases hm' : m' = 0
          · -- KEY(a, r+1, 1)
            subst m'
            calc
              hh F a (r + 1) 1 - hh F (a + 1) (r + 1) 1
                  = X ^ ((Nat.card F) ^ a) - X ^ ((Nat.card F) ^ (a + (r + 1))) := hh_key_degone F a (r + 1)
              _ = (X ^ ((Nat.card F) ^ a) - X ^ ((Nat.card F) ^ (a + (r + 1)))) * 1 := by ring
              _ = (X ^ ((Nat.card F) ^ a) - X ^ ((Nat.card F) ^ (a + (r + 1)))) * hh F a (r + 2) 0 := by
                    rw [hh_zero F a (r + 2)]
          · -- KEY(a, r+1, m'+1), with m' ≥ 1
            have hm'1 : 1 ≤ m' := by omega
            have hout := ihr (m' + 1) (by omega)
            have hin := ih' hm'1
            have hE1 : (Nat.card F) ^ ((a + 1) + r) = (Nat.card F) ^ (a + (r + 1)) := by
              congr 1
              omega
            have hout' : hh F a r (m' + 1) - hh F (a + 1) r (m' + 1) =
                (X ^ ((Nat.card F) ^ a) - X ^ ((Nat.card F) ^ (a + r))) * hh F a (r + 1) m' := by
              have hsub : (m' + 1) - 1 = m' := by omega
              rw [hsub] at hout
              exact hout
            calc
              hh F a (r + 1) (m' + 1) - hh F (a + 1) (r + 1) (m' + 1)
                  = (hh F a r (m' + 1) + X ^ ((Nat.card F) ^ (a + r)) * hh F a (r + 1) m') -
                      (hh F (a + 1) r (m' + 1) + X ^ ((Nat.card F) ^ ((a + 1) + r)) * hh F (a + 1) (r + 1) m') := by
                    rw [hh_rec F a r m', hh_rec F (a + 1) r m']
              _ = (hh F a r (m' + 1) - hh F (a + 1) r (m' + 1)) +
                      X ^ ((Nat.card F) ^ (a + r)) * hh F a (r + 1) m' -
                      X ^ ((Nat.card F) ^ ((a + 1) + r)) * hh F (a + 1) (r + 1) m' := by
                    ring
              _ = (X ^ ((Nat.card F) ^ a) - X ^ ((Nat.card F) ^ (a + r))) * hh F a (r + 1) m' +
                      X ^ ((Nat.card F) ^ (a + r)) * hh F a (r + 1) m' -
                      X ^ ((Nat.card F) ^ ((a + 1) + r)) * hh F (a + 1) (r + 1) m' := by
                    rw [hout']
              _ = X ^ ((Nat.card F) ^ a) * hh F a (r + 1) m' -
                      X ^ ((Nat.card F) ^ ((a + 1) + r)) * hh F (a + 1) (r + 1) m' := by
                    ring
              _ = X ^ ((Nat.card F) ^ a) * hh F a (r + 1) m' -
                      X ^ ((Nat.card F) ^ (a + (r + 1))) * hh F (a + 1) (r + 1) m' := by
                    rw [hE1]
              _ = (X ^ ((Nat.card F) ^ a) - X ^ ((Nat.card F) ^ (a + (r + 1)))) * hh F a (r + 2) m' := by
                    have hsub : hh F (a + 1) (r + 1) m' =
                        hh F a (r + 1) m' -
                          (X ^ ((Nat.card F) ^ a) - X ^ ((Nat.card F) ^ (a + (r + 1)))) * hh F a (r + 2) (m' - 1) := by
                      rw [← hin]
                      ring
                    rw [hsub]
                    have hr1 : hh F a (r + 2) m' =
                        hh F a (r + 1) m' + X ^ ((Nat.card F) ^ (a + (r + 1))) * hh F a (r + 2) (m' - 1) := by
                      have hr := hh_rec F a (r + 1) (m' - 1)
                      have hsub2 : (m' - 1) + 1 = m' := by omega
                      have hsub3 : r + 1 + 1 = r + 2 := by omega
                      rw [hsub3, hsub2] at hr
                      exact hr
                    rw [hr1]
                    ring


/-- THE SESSION-151 FORM of the tower identity (a = 0, via `hh_frob`):
`h_m(X,…,X^{q^{r-1}}) − h_m(X,…,X^{q^{r-1}})^q = (X − X^{q^r})·h_{m−1}(X,…,X^{q^r})`. -/
lemma tower_identity (r m : ℕ) (hm : 1 ≤ m) :
    hh F 0 r m - (hh F 0 r m) ^ (Nat.card F) =
      (X - X ^ ((Nat.card F) ^ r)) * hh F 0 (r + 1) (m - 1) := by
  classical
  have hk := hh_key F 0 r m hm
  -- hk : hh 0 r m − hh 1 r m = (X^{q^0} − X^{q^r})·hh 0 (r+1)(m−1)
  have hf := hh_frob F 0 r m
  -- hf : (hh 0 r m)^q = hh 1 r m
  calc
    hh F 0 r m - (hh F 0 r m) ^ (Nat.card F)
        = hh F 0 r m - hh F (0 + 1) r m := by
          rw [hf]
    _ = (X ^ ((Nat.card F) ^ 0) - X ^ ((Nat.card F) ^ (0 + r))) * hh F 0 (r + 1) (m - 1) := hk
    _ = (X - X ^ ((Nat.card F) ^ r)) * hh F 0 (r + 1) (m - 1) := by
          congr 2
          · rw [pow_zero]
            simp
          · rw [zero_add]


end ZagierHoffmanPositiveChar
