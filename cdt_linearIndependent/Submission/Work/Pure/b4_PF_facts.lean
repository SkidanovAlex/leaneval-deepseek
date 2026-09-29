import Mathlib
import Submission.Work.Pure.b4_defs
import Submission.Work.Pure.b4_PF_aux
import Submission.Work.Pure.b4_PF_vanishing
import Submission.Work.Pure.b4_PF_D

/-!
# The descent facts for the pure function `B₄` (`Work.Pure.b4_PF_facts`)

Calegari–Dimitrov–Tang, arXiv:2408.15403, §"Pure functions".  With
`φ = sympPhi = x/(x−1)`, `y = sympY = x·φ`, the symmetrized powers
`Pₙ(y) = xⁿ + φⁿ` (`Submission.CDT.sympP`) and the descent
`Θ = (x−φ)(Li₂(x) − Li₂(φ))` (`Work.Pure.b4Theta`) written as the weight sum
`b4F = Σ_{k≥1} k⁻²·(P_{k+1} − y·P_{k−1})` (`Work.Pure.b4F`), this module proves

* `(b4P j).subst sympY = sympP j` : the recurrence `b4P` computes `Pⱼ`;
* `b4Q k` has integer coefficients;
* `coeff n (b4Q k) = 0` for `2n ≤ k` (the valuation bound `X^{⌊k/2⌋+1} ∣ b4Q k`);
* `b4F.subst sympY = b4Theta` : the descent of `B₄` is `Θ`.

The last identity is proved coefficientwise: for fixed `n` both sides reduce to the
*finite* double sum `Σ_{k ≤ n} k⁻²·coeff n ((x−φ)(x^{k+1} − φ^{k+1}))`, the truncation
being justified by the valuation bound (for `b4F.subst sympY`) and by the vanishing of
`coeff q (φ^m)` for `m > q` (for `b4Theta`).
-/

namespace Work.Pure

open PowerSeries
open Submission.CDT
open scoped BigOperators

noncomputable section

/-! ## Substitution facts -/

/-- the coefficient of `X · f` (the underlying variable is `y` in `b4_defs`) -/
private lemma coeff_X_mul_b4 (m : ℕ) (f : PowerSeries ℚ) :
    PowerSeries.coeff m (X * f) = if 1 ≤ m then PowerSeries.coeff (m - 1) f else 0 := by
  simpa using PowerSeries.coeff_X_pow_mul' f 1 m

/-- `coeff n (f * g)` as a sum over `p + q = n` (`p ≤ n`). -/
private lemma coeff_mul_range (n : ℕ) (f g : PowerSeries ℚ) :
    PowerSeries.coeff n (f * g) =
      ∑ p ∈ Finset.range (n + 1), PowerSeries.coeff p f * PowerSeries.coeff (n - p) g := by
  rw [PowerSeries.coeff_mul]
  exact Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun a b => PowerSeries.coeff a f * PowerSeries.coeff b g) n

/-- `x^m − φ^m` has valuation `m`. -/
private lemma coeff_Xpow_sub (q m : ℕ) (h : q < m) :
    PowerSeries.coeff q ((X : PowerSeries ℚ) ^ m - sympPhi ^ m) = 0 := by
  rw [map_sub, PowerSeries.coeff_X_pow, if_neg (by omega), coeff_pow_lt_one coeff_sympPhi_zero h,
    sub_zero]

/-- step (1): `b4P j` is the polynomial `Pⱼ`, read in the symmetrization coordinate. -/
private lemma b4P_subst_sympY : ∀ j : ℕ, (b4P j).subst sympY = sympP j := by
  apply Nat.twoStepInduction
  · rw [b4P_zero, sympP_zero]
    rw [show (2 : PowerSeries ℚ) = PowerSeries.C (2:ℚ) from rfl, PowerSeries.subst_C]
    rfl
  · rw [b4P_one, sympP_one]
    exact PowerSeries.subst_X sympY_hasSubst
  · intro n ih1 ih2
    rw [b4P_succ_succ, sympP_succ_succ]
    rw [PowerSeries.subst_sub sympY_hasSubst, PowerSeries.subst_mul sympY_hasSubst,
      PowerSeries.subst_mul sympY_hasSubst, PowerSeries.subst_X sympY_hasSubst, ih1, ih2]

/-- `P_{k+2} − y·P_k = (x − φ)(x^{k+1} − φ^{k+1})`. -/
private lemma sympP_sub (k : ℕ) :
    sympP (k+2) - sympY * sympP k = (X - sympPhi) * (X^(k+1) - sympPhi^(k+1)) := by
  simp only [sympP, sympY]
  ring

/-- the descent of `b4Q`: `(Q_{k+1})∘y = (x − φ)(x^{k+1} − φ^{k+1})`. -/
private lemma b4Q_subst_sympY (k : ℕ) :
    (b4Q (k+1)).subst sympY = (X - sympPhi) * (X^(k+1) - sympPhi^(k+1)) := by
  have hk : k + 1 - 1 = k := by omega
  rw [b4Q]
  rw [PowerSeries.subst_sub sympY_hasSubst, PowerSeries.subst_mul sympY_hasSubst,
    PowerSeries.subst_X sympY_hasSubst, hk, b4P_subst_sympY (k+1+1), b4P_subst_sympY k]
  exact sympP_sub k

/-! ## Integrality -/

private lemma intSeries_const_int (z : ℤ) : IntSeries (PowerSeries.C (z : ℚ)) := by
  intro n
  rw [PowerSeries.coeff_C]
  by_cases h : n = 0
  · subst h; exact ⟨z, by simp⟩
  · exact ⟨0, by simp [h]⟩

private lemma b4P_intSeries (n : ℕ) : IntSeries (b4P n) := by
  induction n using Nat.twoStepInduction with
  | zero => rw [b4P_zero]; exact intSeries_const_int 2
  | one => rw [b4P_one]; exact intSeries_X
  | more n ih1 ih2 =>
      rw [b4P_succ_succ]
      exact intSeries_sub (intSeries_mul intSeries_X ih2) (intSeries_mul intSeries_X ih1)

private lemma b4Q_intSeries (k : ℕ) : IntSeries (b4Q k) := by
  rw [b4Q]
  exact intSeries_sub (b4P_intSeries (k+1)) (intSeries_mul intSeries_X (b4P_intSeries (k-1)))

/-! ## The valuation bound -/

/-- step (3): `coeff n (b4Q k) = 0` for `2n ≤ k`, from the vanishing of `b4P` below
degree `⌈·/2⌉` (`Work.Pure.b4_PF_vanishing`). -/
private lemma b4Q_vanishing (n k : ℕ) (h : 2 * n ≤ k) :
    PowerSeries.coeff n (b4Q k) = 0 := by
  rw [b4Q]
  rw [map_sub, b4_PF_vanishing (k + 1) n (by omega), coeff_X_mul_b4]
  by_cases hn : 1 ≤ n
  · rw [if_pos hn, b4_PF_vanishing (k - 1) (n - 1) (by omega)]
    simp
  · rw [if_neg hn]; simp

/-! ## The descent `b4F.subst sympY = b4Theta` -/

/-- `coeff r b4F` with the summation cut at any `n ≥ 2r` (the discarded summands
vanish by the valuation bound). -/
private lemma coeff_b4F_range (r n : ℕ) (h : 2 * r ≤ n) :
    PowerSeries.coeff r b4F =
      ∑ k ∈ Finset.range (n+1), b4wt k * PowerSeries.coeff r (b4Q (k+1)) := by
  rw [coeff_b4F]
  simp only [b4wt_eq]
  refine Finset.sum_subset ?_ ?_
  · intro x hx
    simp only [Finset.mem_range] at hx ⊢
    omega
  · intro x hx hx2
    simp only [Finset.mem_range] at hx hx2
    rw [b4Q_vanishing r (x+1) (by omega), mul_zero]

/-- the coefficients of `b4F.subst sympY` are the finite weight sums of
`coeff n ((x−φ)(x^{k+1}−φ^{k+1}))`. -/
private lemma coeff_subst_b4F (n : ℕ) :
    PowerSeries.coeff n (b4F.subst sympY) =
      ∑ k ∈ Finset.range (n+1),
        b4wt k * PowerSeries.coeff n ((X - sympPhi) * (X^(k+1) - sympPhi^(k+1))) := by
  rw [coeff_subst_range₂ b4F coeff_sympY_zero coeff_sympY_one n]
  calc ∑ r ∈ Finset.range (n/2+1), PowerSeries.coeff r b4F * PowerSeries.coeff n (sympY ^ r)
      = ∑ r ∈ Finset.range (n/2+1),
          (∑ k ∈ Finset.range (n+1), b4wt k * PowerSeries.coeff r (b4Q (k+1)))
            * PowerSeries.coeff n (sympY ^ r) := by
        apply Finset.sum_congr rfl
        intro r hr
        have hr' : 2 * r ≤ n := by
          simp only [Finset.mem_range] at hr
          omega
        rw [coeff_b4F_range r n hr']
    _ = ∑ r ∈ Finset.range (n/2+1), ∑ k ∈ Finset.range (n+1),
          (b4wt k * PowerSeries.coeff r (b4Q (k+1))) * PowerSeries.coeff n (sympY ^ r) := by
        apply Finset.sum_congr rfl
        intro r hr
        rw [Finset.sum_mul]
    _ = ∑ k ∈ Finset.range (n+1), ∑ r ∈ Finset.range (n/2+1),
          (b4wt k * PowerSeries.coeff r (b4Q (k+1))) * PowerSeries.coeff n (sympY ^ r) :=
        Finset.sum_comm
    _ = ∑ k ∈ Finset.range (n+1), b4wt k *
          (∑ r ∈ Finset.range (n/2+1),
            PowerSeries.coeff r (b4Q (k+1)) * PowerSeries.coeff n (sympY ^ r)) := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro r hr
        ring
    _ = ∑ k ∈ Finset.range (n+1), b4wt k * PowerSeries.coeff n ((b4Q (k+1)).subst sympY) := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [← coeff_subst_range₂ (b4Q (k+1)) coeff_sympY_zero coeff_sympY_one n]
    _ = ∑ k ∈ Finset.range (n+1),
          b4wt k * PowerSeries.coeff n ((X - sympPhi) * (X^(k+1) - sympPhi^(k+1))) := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [b4Q_subst_sympY k]

/-- the coefficients of `b4Ds` with the summation cut at any `n ≥ q`. -/
private lemma coeff_b4Ds_range (n q : ℕ) (h : q ≤ n) :
    PowerSeries.coeff q b4Ds =
      ∑ k ∈ Finset.range (n+1), b4wt k * PowerSeries.coeff q (X^(k+1) - sympPhi^(k+1)) := by
  rw [coeff_b4Ds]
  refine Finset.sum_subset ?_ ?_
  · intro x hx
    simp only [Finset.mem_range] at hx ⊢
    omega
  · intro x hx hx2
    simp only [Finset.mem_range] at hx hx2
    rw [coeff_Xpow_sub q (x+1) (by omega), mul_zero]

/-- the coefficients of `b4Theta` are the same finite weight sums.  Uses the
identification `b4Li2 − b4Li2.subst sympPhi = b4Ds`
(`Work.Pure.b4_PF_D`). -/
private lemma coeff_b4Theta_eq (n : ℕ) :
    PowerSeries.coeff n b4Theta =
      ∑ k ∈ Finset.range (n+1),
        b4wt k * PowerSeries.coeff n ((X - sympPhi) * (X^(k+1) - sympPhi^(k+1))) := by
  have hθ : b4Theta = (X - sympPhi) * b4Ds := by
    rw [b4Theta, b4_PF_D]
  rw [hθ, coeff_mul_range]
  calc ∑ p ∈ Finset.range (n+1), PowerSeries.coeff p (X - sympPhi) * PowerSeries.coeff (n - p) b4Ds
      = ∑ p ∈ Finset.range (n+1), PowerSeries.coeff p (X - sympPhi) *
          (∑ k ∈ Finset.range (n+1),
            b4wt k * PowerSeries.coeff (n-p) (X^(k+1) - sympPhi^(k+1))) := by
        apply Finset.sum_congr rfl
        intro p hp
        rw [coeff_b4Ds_range n (n-p) (by omega)]
    _ = ∑ p ∈ Finset.range (n+1), ∑ k ∈ Finset.range (n+1),
          PowerSeries.coeff p (X - sympPhi) *
            (b4wt k * PowerSeries.coeff (n-p) (X^(k+1) - sympPhi^(k+1))) := by
        apply Finset.sum_congr rfl
        intro p hp
        rw [Finset.mul_sum]
    _ = ∑ k ∈ Finset.range (n+1), ∑ p ∈ Finset.range (n+1),
          PowerSeries.coeff p (X - sympPhi) *
            (b4wt k * PowerSeries.coeff (n-p) (X^(k+1) - sympPhi^(k+1))) :=
        Finset.sum_comm
    _ = ∑ k ∈ Finset.range (n+1), b4wt k *
          (∑ p ∈ Finset.range (n+1),
            PowerSeries.coeff p (X - sympPhi) *
              PowerSeries.coeff (n-p) (X^(k+1) - sympPhi^(k+1))) := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro p hp
        ring
    _ = ∑ k ∈ Finset.range (n+1),
          b4wt k * PowerSeries.coeff n ((X - sympPhi) * (X^(k+1) - sympPhi^(k+1))) := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [← coeff_mul_range n (X - sympPhi) (X^(k+1) - sympPhi^(k+1))]

/-! ## Assembly -/

/-- Route. (1) `b4P` is defined by `P₀ = 2`, `P₁ = X`, `P_{n+2} = X·P_{n+1} - X·P_n`, exactly the
recurrence satisfied by `sympP n = Xⁿ + φⁿ` (`Submission.CDT.sympP_zero/one/succ_succ`), so
`(b4P j).subst sympY = sympP j` follows by double induction (use `PowerSeries.subst_mul`,
`subst_sub`, `subst_X`, `subst_C`).
(2) `b4P n` has integer coefficients (induction: `2`, `X`, and multiplication/subtraction by `X`),
so `b4Q k = b4P(k+1) - X·b4P(k-1)` has integer coefficients.
(3) The valuation bound: `b4P n` is divisible by `X^{⌈n/2⌉}` (induction), so
`b4Q k` is divisible by `X^{⌊k/2⌋+1}`, giving `2*n ≤ k → coeff n (b4Q k) = 0`.
(4) `b4F.subst sympY = b4Theta`: by `Submission.CDT.coeff_subst_range` (both sides have zero
constant term; `sympY` has valuation 2), the coefficients of `b4F.subst sympY` are finite sums;
using (1) one has
`(b4F.subst sympY) = Σ_{k≥1} k⁻²·((sympP (k+1)) - sympY·sympP (k-1))`, and
`sympP (k+1) - sympY·sympP (k-1) = (X-φ)(X^k - φ^k)`, so the sum is
`(X-φ)·Σ_k (X^k-φ^k)/k² = (X-φ)(b4Li2 - b4Li2.subst sympPhi) = b4Theta` (finite coefficientwise
sums: for fixed `n` only `k ≤ 2n+1` contribute; interchange the finite sums). -/
theorem b4_PF_facts :
    (∀ j : ℕ, (Work.Pure.b4P j).subst Submission.CDT.sympY = Submission.CDT.sympP j) ∧
    (∀ n k : ℕ, ∃ z : ℤ, PowerSeries.coeff n (Work.Pure.b4Q k) = (z : ℚ)) ∧
    (∀ n k : ℕ, 2 * n ≤ k → PowerSeries.coeff n (Work.Pure.b4Q k) = 0) ∧
    (Work.Pure.b4F.subst Submission.CDT.sympY = Work.Pure.b4Theta) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact b4P_subst_sympY
  · intro n k
    obtain ⟨z, hz⟩ := b4Q_intSeries k n
    exact ⟨z, hz.symm⟩
  · intro n k h
    exact b4Q_vanishing n k h
  · apply PowerSeries.ext
    intro n
    rw [coeff_subst_b4F n, coeff_b4Theta_eq n]

end

end Work.Pure
