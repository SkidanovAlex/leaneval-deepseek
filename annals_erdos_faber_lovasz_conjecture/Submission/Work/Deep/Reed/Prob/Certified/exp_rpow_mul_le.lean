import Mathlib.Analysis.MeanInequalities
import Submission.Work.Deep.Reed.Prob.Expectation

/-!
# Weighted Hölder (`Lyapunov`) inequality for expectations

For a finite probability space `ν` and non-negative random variables `u`, `v`,
and an exponent `lam ∈ [0,1]`,

`ν.exp (u^lam * v^(1-lam)) ≤ (ν.exp u)^lam * (ν.exp v)^(1-lam)`,

which is the two-function case of Hölder's inequality, equivalently the
log-convexity of the moment curve.  The proof is the classical one: apply the
weighted arithmetic–geometric mean inequality pointwise after normalising
`u` and `v` by their expectations.
-/

set_option autoImplicit false

open scoped BigOperators

namespace Work.Deep.Reed.Prob.Certified

/-- **Weighted AM–GM** (Young's inequality): for `s, t ≥ 0` and `lam ∈ [0,1]`,
the weighted geometric mean is at most the weighted arithmetic mean. -/
private theorem rpow_mul_le_add {s t lam : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t)
    (h0 : 0 ≤ lam) (h1 : lam ≤ 1) :
    s ^ lam * t ^ (1 - lam) ≤ lam * s + (1 - lam) * t := by
  have hAM := Real.geom_mean_le_arith_mean_weighted (Finset.univ : Finset (Fin 2))
    (w := ![lam, 1 - lam]) (z := ![s, t])
    (by intro i _; fin_cases i <;> simp [h0, sub_nonneg.mpr h1])
    (by simp [Fin.sum_univ_two])
    (by intro i _; fin_cases i <;> simp [hs, ht])
  simpa [Fin.prod_univ_two, Fin.sum_univ_two] using hAM

/-- **Hölder's inequality for expectations**: the expectation of the weighted
geometric mean of two non-negative random variables is at most the weighted
geometric mean of their expectations. -/
theorem exp_rpow_mul_le {Ω : Type*} [Fintype Ω] (ν : Work.Deep.Reed.FinProb Ω) {u v : Ω → ℝ}
    (hu : ∀ ω, 0 ≤ u ω) (hv : ∀ ω, 0 ≤ v ω) {lam : ℝ} (h0 : 0 ≤ lam) (h1 : lam ≤ 1) :
    ν.exp (fun ω => u ω ^ lam * v ω ^ (1 - lam))
      ≤ (ν.exp u) ^ lam * (ν.exp v) ^ (1 - lam) := by
  classical
  -- the two endpoint exponents give an equality
  rcases eq_or_ne lam 0 with rfl | hl0
  · simp [Real.rpow_zero, Real.rpow_one]
  rcases eq_or_ne lam 1 with rfl | hl1
  · simp [Real.rpow_zero, Real.rpow_one]
  have hlampos : 0 < lam := lt_of_le_of_ne h0 (Ne.symm hl0)
  have hlamlt1 : lam < 1 := lt_of_le_of_ne h1 hl1
  have h1mpos : 0 < 1 - lam := sub_pos.mpr hlamlt1
  have hEu : 0 ≤ ν.exp u := ν.exp_nonneg hu
  have hEv : 0 ≤ ν.exp v := ν.exp_nonneg hv
  -- if `ν.exp u = 0` then `u` vanishes on the support of `ν`, so both sides vanish
  have hkeyU : ν.exp u = 0 → ν.exp (fun ω => u ω ^ lam * v ω ^ (1 - lam)) = 0 := by
    intro hA
    have hsum : ∑ ω, ν.wt ω * u ω = 0 := by
      have h := hA; rwa [Work.Deep.Reed.FinProb.exp] at h
    rw [Work.Deep.Reed.FinProb.exp]
    refine Finset.sum_eq_zero fun ω _ => ?_
    have hwu : ν.wt ω * u ω = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (f := fun ω => ν.wt ω * u ω)
        (fun ω _ => mul_nonneg (ν.wt_nonneg ω) (hu ω))).mp hsum ω (Finset.mem_univ ω)
    rcases eq_or_lt_of_le (ν.wt_nonneg ω) with hw | hw
    · rw [← hw, zero_mul]
    · have hu0 : u ω = 0 := by
        rcases eq_or_lt_of_le (hu ω) with h | h
        · exact h.symm
        · have hpos : 0 < ν.wt ω * u ω := mul_pos hw h
          rw [hwu] at hpos
          exact absurd hpos (lt_irrefl 0)
      rw [hu0, Real.zero_rpow hl0, zero_mul, mul_zero]
  -- symmetrically for `ν.exp v = 0`
  have hkeyV : ν.exp v = 0 → ν.exp (fun ω => u ω ^ lam * v ω ^ (1 - lam)) = 0 := by
    intro hB
    have hsum : ∑ ω, ν.wt ω * v ω = 0 := by
      have h := hB; rwa [Work.Deep.Reed.FinProb.exp] at h
    rw [Work.Deep.Reed.FinProb.exp]
    refine Finset.sum_eq_zero fun ω _ => ?_
    have hwv : ν.wt ω * v ω = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (f := fun ω => ν.wt ω * v ω)
        (fun ω _ => mul_nonneg (ν.wt_nonneg ω) (hv ω))).mp hsum ω (Finset.mem_univ ω)
    rcases eq_or_lt_of_le (ν.wt_nonneg ω) with hw | hw
    · rw [← hw, zero_mul]
    · have hv0 : v ω = 0 := by
        rcases eq_or_lt_of_le (hv ω) with h | h
        · exact h.symm
        · have hpos : 0 < ν.wt ω * v ω := mul_pos hw h
          rw [hwv] at hpos
          exact absurd hpos (lt_irrefl 0)
      rw [hv0, Real.zero_rpow h1mpos.ne', mul_zero, mul_zero]
  rcases eq_or_ne (ν.exp u) 0 with hA | hA
  · rw [hkeyU hA, hA, Real.zero_rpow hl0, zero_mul]
  rcases eq_or_ne (ν.exp v) 0 with hB | hB
  · rw [hkeyV hB, hB, Real.zero_rpow h1mpos.ne', mul_zero]
  have hApos : 0 < ν.exp u := lt_of_le_of_ne hEu (Ne.symm hA)
  have hBpos : 0 < ν.exp v := lt_of_le_of_ne hEv (Ne.symm hB)
  -- after normalising, the expectation of the geometric mean is at most `1`
  have hnorm : ν.exp (fun ω => (u ω / ν.exp u) ^ lam * (v ω / ν.exp v) ^ (1 - lam)) ≤ 1 := by
    have hpt : ∀ ω, (u ω / ν.exp u) ^ lam * (v ω / ν.exp v) ^ (1 - lam)
        ≤ lam * (u ω / ν.exp u) + (1 - lam) * (v ω / ν.exp v) :=
      fun ω => rpow_mul_le_add (div_nonneg (hu ω) hApos.le) (div_nonneg (hv ω) hBpos.le) h0 h1
    have hexpu : ν.exp (fun ω => u ω / ν.exp u) = 1 := by
      have h : (fun ω => u ω / ν.exp u) = (fun ω => (ν.exp u)⁻¹ * u ω) := by
        funext ω; rw [div_eq_inv_mul]
      rw [h, ν.exp_mul_left, inv_mul_cancel₀ hA]
    have hexpv : ν.exp (fun ω => v ω / ν.exp v) = 1 := by
      have h : (fun ω => v ω / ν.exp v) = (fun ω => (ν.exp v)⁻¹ * v ω) := by
        funext ω; rw [div_eq_inv_mul]
      rw [h, ν.exp_mul_left, inv_mul_cancel₀ hB]
    calc ν.exp (fun ω => (u ω / ν.exp u) ^ lam * (v ω / ν.exp v) ^ (1 - lam))
        ≤ ν.exp (fun ω => lam * (u ω / ν.exp u) + (1 - lam) * (v ω / ν.exp v)) :=
          ν.exp_mono hpt
      _ = lam * ν.exp (fun ω => u ω / ν.exp u) + (1 - lam) * ν.exp (fun ω => v ω / ν.exp v) := by
          rw [ν.exp_add, ν.exp_mul_left, ν.exp_mul_left]
      _ = 1 := by rw [hexpu, hexpv]; ring
  -- factor the normalisation out of the expectation
  have hmain : ν.exp (fun ω => u ω ^ lam * v ω ^ (1 - lam))
      = (ν.exp u) ^ lam * (ν.exp v) ^ (1 - lam)
        * ν.exp (fun ω => (u ω / ν.exp u) ^ lam * (v ω / ν.exp v) ^ (1 - lam)) := by
    have hfun : (fun ω => u ω ^ lam * v ω ^ (1 - lam))
        = (fun ω => ((ν.exp u) ^ lam * (ν.exp v) ^ (1 - lam))
            * ((u ω / ν.exp u) ^ lam * (v ω / ν.exp v) ^ (1 - lam))) := by
      funext ω
      have hu' : u ω ^ lam = (ν.exp u) ^ lam * (u ω / ν.exp u) ^ lam := by
        rw [← Real.mul_rpow hApos.le (div_nonneg (hu ω) hApos.le), mul_div_cancel₀ (u ω) hA]
      have hv' : v ω ^ (1 - lam) = (ν.exp v) ^ (1 - lam) * (v ω / ν.exp v) ^ (1 - lam) := by
        rw [← Real.mul_rpow hBpos.le (div_nonneg (hv ω) hBpos.le), mul_div_cancel₀ (v ω) hB]
      rw [hu', hv']; ring
    rw [hfun, ν.exp_mul_left]
  rw [hmain]
  calc (ν.exp u) ^ lam * (ν.exp v) ^ (1 - lam)
        * ν.exp (fun ω => (u ω / ν.exp u) ^ lam * (v ω / ν.exp v) ^ (1 - lam))
      ≤ (ν.exp u) ^ lam * (ν.exp v) ^ (1 - lam) * 1 :=
        mul_le_mul_of_nonneg_left hnorm
          (mul_nonneg (Real.rpow_nonneg hApos.le lam) (Real.rpow_nonneg hBpos.le (1 - lam)))
    _ = (ν.exp u) ^ lam * (ν.exp v) ^ (1 - lam) := mul_one _

end Work.Deep.Reed.Prob.Certified
