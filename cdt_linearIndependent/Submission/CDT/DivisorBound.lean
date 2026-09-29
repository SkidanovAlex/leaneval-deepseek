import Submission.CDT.FrobeniusGeneric
import Submission.Commons.Algebra.Polynomial.dvd_of_forall_rootMultiplicity_le

/-!
# The divisor bound for `b3`

Combining the five local bounds

* `ord_0 b3 ≥ 2`, `ord_4 b3 ≥ 2`, `ord_{−1/72} b3 ≥ 1`,
* `ord_β b3 ≥ −1` at every root `β` of the cubic `cub`,
* `ord_α b3 ≥ 0` wherever `Δ₁(α) ≠ 0` (the generic bound),

one gets `cub·b3 = y²(y−4)²(y + 1/72)·Q` with `Q` a polynomial: multiplying by
`cub` kills all poles (the `−1` at the roots of the cubic being exactly
compensated by the simple roots of `cub`), and the remaining statements are
vanishing orders of a polynomial.
-/

open Classical

noncomputable section

namespace Submission.CDT

open Polynomial

namespace FrobeniusApply

open Submission.CDT.Elim14C
open Submission.CDT.ElimOpC

set_option maxHeartbeats 800000

lemma cub_ne_zero : cub ≠ 0 := by
  intro h
  have := cub_eval_zero_pt
  rw [h] at this
  simp at this

lemma ordAt_cub_eq_zero (α : ℂ) (h : cub.eval α ≠ 0) : ordAt α (am cub) = 0 := by
  rw [ordAt_algebraMap]
  have : Polynomial.rootMultiplicity α cub = 0 := by
    rw [Polynomial.rootMultiplicity_eq_zero]
    intro hr
    exact h hr
  rw [this]
  simp

/-- **The divisor bound.**  Under the five local order bounds, `cub·b3` is a
polynomial divisible by `y²(y−4)²(y + 1/72)`. -/
theorem divisor_bound (b3 : RF) (hb : b3 ≠ 0)
    (h0 : (2 : ℤ) ≤ ordAt (0 : ℂ) b3) (h4 : (2 : ℤ) ≤ ordAt (4 : ℂ) b3)
    (ha : (1 : ℤ) ≤ ordAt a72 b3)
    (hcub : ∀ α : ℂ, cub.eval α = 0 → (-1 : ℤ) ≤ ordAt α b3)
    (hgen : ∀ α : ℂ, D1.eval α ≠ 0 → (0 : ℤ) ≤ ordAt α b3) :
    ∃ Q : Polynomial ℂ, am cub * b3 = am ((Polynomial.X - Polynomial.C (0 : ℂ)) ^ 2
      * (Polynomial.X - Polynomial.C (4 : ℂ)) ^ 2 * (Polynomial.X - Polynomial.C a72) * Q) := by
  have hcub0 : cub ≠ 0 := cub_ne_zero
  have hcubne : am cub ≠ 0 := RatFunc.algebraMap_ne_zero hcub0
  -- Step A: `cub·b3` has nonnegative order everywhere
  have hF : ∀ α : ℂ, (0 : ℤ) ≤ ordAt α (am cub * b3) := by
    intro α
    have hmul := ordAt_mul α hcubne hb
    by_cases hcα : cub.eval α = 0
    · have h1 : (1 : ℤ) ≤ ordAt α (am cub) := by
        rw [ordAt_algebraMap]
        have hpos : 0 < Polynomial.rootMultiplicity α cub :=
          (Polynomial.rootMultiplicity_pos hcub0).mpr hcα
        omega
      rw [hmul]
      have := hcub α hcα
      omega
    · have h0c := ordAt_cub_eq_zero α hcα
      rw [hmul, h0c, zero_add]
      by_cases hD : D1.eval α = 0
      · have hw : w.eval α = 0 := by
          have hprod : w.eval α * cub.eval α = 0 := by
            rw [← Polynomial.eval_mul, ← D1_factor]
            exact hD
          rcases mul_eq_zero.mp hprod with h | h
          · exact h
          · exact absurd h hcα
        rw [w_eval_eq] at hw
        rcases mul_eq_zero.mp hw with h1 | h3
        · rcases mul_eq_zero.mp h1 with h2 | h4'
          · rw [h2]; omega
          · have hα : α = 4 := sub_eq_zero.mp h4'
            rw [hα]; omega
        · have hα : α = a72 := by
            have h72 : (72 : ℂ) * α = -1 := by linear_combination h3
            have h' : α = -1 / 72 := by
              rw [eq_div_iff (by norm_num : (72 : ℂ) ≠ 0), mul_comm]
              exact h72
            rw [h']; unfold a72; norm_num
          rw [hα]; omega
      · exact hgen α hD
  -- Step B: `cub·b3` is a polynomial
  have hdvd : (am cub * b3).denom ∣ (am cub * b3).num := by
    refine Commons.Algebra.Polynomial.dvd_of_forall_rootMultiplicity_le
      (RatFunc.denom_ne_zero _) (fun α => ?_)
    have h := hF α
    simp only [ordAt] at h
    omega
  obtain ⟨Q, hQ⟩ := hdvd
  have hQne : Q ≠ 0 := by
    intro h0Q
    rw [h0Q, mul_zero] at hQ
    exact RatFunc.num_ne_zero (mul_ne_zero hcubne hb) hQ
  have hnumden : am cub * b3 = am Q := by
    conv_lhs => rw [← RatFunc.num_div_denom (am cub * b3)]
    rw [hQ, map_mul, mul_div_cancel_left₀ _ (RatFunc.algebraMap_ne_zero (RatFunc.denom_ne_zero _))]
  -- Step C: the vanishing orders of `Q`
  have hrm0 : (2 : ℤ) ≤ (Polynomial.rootMultiplicity (0 : ℂ) Q : ℤ) := by
    have h : (2 : ℤ) ≤ ordAt (0 : ℂ) (am Q) := by
      rw [← hnumden]
      rw [ordAt_mul (0 : ℂ) hcubne hb,
        ordAt_cub_eq_zero (0 : ℂ) (by rw [cub_eval_zero_pt]; norm_num), zero_add]
      exact h0
    rwa [ordAt_algebraMap] at h
  have hrm4 : (2 : ℤ) ≤ (Polynomial.rootMultiplicity (4 : ℂ) Q : ℤ) := by
    have h : (2 : ℤ) ≤ ordAt (4 : ℂ) (am Q) := by
      rw [← hnumden]
      rw [ordAt_mul (4 : ℂ) hcubne hb,
        ordAt_cub_eq_zero (4 : ℂ) (by rw [cub_eval_four]; norm_num), zero_add]
      exact h4
    rwa [ordAt_algebraMap] at h
  have hrma : (1 : ℤ) ≤ (Polynomial.rootMultiplicity a72 Q : ℤ) := by
    have h : (1 : ℤ) ≤ ordAt a72 (am Q) := by
      rw [← hnumden]
      rw [ordAt_mul a72 hcubne hb,
        ordAt_cub_eq_zero a72 (by rw [cub_eval_a72]; norm_num), zero_add]
      exact ha
    rwa [ordAt_algebraMap] at h
  have hdvd0 : (Polynomial.X - Polynomial.C (0 : ℂ)) ^ 2 ∣ Q := by
    refine (Polynomial.le_rootMultiplicity_iff hQne).mp ?_
    exact_mod_cast hrm0
  have hdvd4 : (Polynomial.X - Polynomial.C (4 : ℂ)) ^ 2 ∣ Q := by
    refine (Polynomial.le_rootMultiplicity_iff hQne).mp ?_
    exact_mod_cast hrm4
  have hdvda : (Polynomial.X - Polynomial.C a72) ^ 1 ∣ Q := by
    refine (Polynomial.le_rootMultiplicity_iff hQne).mp ?_
    exact_mod_cast hrma
  -- the three linear factors are pairwise coprime
  have hc04 : IsCoprime (Polynomial.X - Polynomial.C (0 : ℂ)) (Polynomial.X - Polynomial.C (4 : ℂ)) :=
    Polynomial.isCoprime_X_sub_C_of_isUnit_sub (by
      rw [isUnit_iff_ne_zero]; norm_num)
  have hc0a : IsCoprime (Polynomial.X - Polynomial.C (0 : ℂ)) (Polynomial.X - Polynomial.C a72) :=
    Polynomial.isCoprime_X_sub_C_of_isUnit_sub (by
      rw [isUnit_iff_ne_zero]; unfold a72; norm_num)
  have hc4a : IsCoprime (Polynomial.X - Polynomial.C (4 : ℂ)) (Polynomial.X - Polynomial.C a72) :=
    Polynomial.isCoprime_X_sub_C_of_isUnit_sub (by
      rw [isUnit_iff_ne_zero]; unfold a72; norm_num)
  have hc04pow : IsCoprime ((Polynomial.X - Polynomial.C (0 : ℂ)) ^ 2)
      ((Polynomial.X - Polynomial.C (4 : ℂ)) ^ 2) := hc04.pow (m := 2) (n := 2)
  have hprod14 : ((Polynomial.X - Polynomial.C (0 : ℂ)) ^ 2
      * (Polynomial.X - Polynomial.C (4 : ℂ)) ^ 2) ∣ Q :=
    IsCoprime.mul_dvd hc04pow hdvd0 hdvd4
  have h14a : IsCoprime ((Polynomial.X - Polynomial.C (0 : ℂ)) ^ 2
      * (Polynomial.X - Polynomial.C (4 : ℂ)) ^ 2) (Polynomial.X - Polynomial.C a72) :=
    IsCoprime.mul_left (hc0a.pow_left (m := 2)) (hc4a.pow_left (m := 2))
  have hdvda' : (Polynomial.X - Polynomial.C a72) ∣ Q := by
    simpa using hdvda
  have hdvdprod : ((Polynomial.X - Polynomial.C (0 : ℂ)) ^ 2
      * (Polynomial.X - Polynomial.C (4 : ℂ)) ^ 2) * (Polynomial.X - Polynomial.C a72) ∣ Q :=
    IsCoprime.mul_dvd h14a hprod14 hdvda'
  obtain ⟨Q', hQ'⟩ := hdvdprod
  exact ⟨Q', by rw [hnumden, hQ']⟩

end FrobeniusApply

end Submission.CDT
