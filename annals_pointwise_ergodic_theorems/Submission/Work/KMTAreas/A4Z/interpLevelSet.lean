/-
# Interpolation of an `ℓ^∞ -> ℓ²` and an `ℓ^p -> ℓ²` bound (two-endpoint truncation)

If `T` is linear on bounded functions and satisfies

* `‖T g‖_{ℓ²} ≤ A` for every `1`-bounded `g` supported in `[-N₀,N₀]` (an `ℓ^∞ -> ℓ²` endpoint),
* `‖T g‖_{ℓ²} ≤ B ‖g‖_{ℓ^p}` for every bounded `g` (an `ℓ^p -> ℓ²` endpoint, `1 < p < 2`),

then `T` maps `ℓ²` into `ℓ²` with the interpolated constant `2 A^{1-p/2} B^{p/2}`.  This is the
truncation/layer-cake argument: for `λ = t‖f‖_{ℓ²}` with `t = (B/A)^{p/2}` one splits
`f = f 1_{|f| ≤ λ} + f 1_{|f| > λ}`, applies the two endpoints to the two pieces and uses the
elementary level-set bound `‖f 1_{|f| > λ}‖_{ℓ^p} ≤ λ^{1-2/p}‖f‖_{ℓ²}^{2/p}`
(`eLpNorm_levelSetHigh_le`, delegated).

The `2` in the constant is slack: both terms of the split are equal to `A^{1-p/2}B^{p/2}‖f‖_{ℓ²}`.

## Main result

* `Work.KMTAreas.A4Z.eLpNorm_two_le_of_interp_levelSet`
-/
import Mathlib
import Submission.Work.KMTAreas.A4Z.eLpNorm_levelSetHigh_le
import Submission.Work.KMTAreas.A5.Basic

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open Work.Analysis.InverseTheory
open Work.KMTAreas.A5 (BoundedZ boundedZ_of_bound boundedZ_add boundedZ_smul boundedZ_sub boundedZ_zero)

namespace Work.KMTAreas.A4Z


/-- **Two-endpoint interpolation by truncation.** -/
theorem eLpNorm_two_le_of_interp_levelSet (N₀ : ℕ) (T : (ℤ → ℂ) → (ℤ → ℂ))
    (hadd : ∀ f g : ℤ → ℂ, BoundedZ f → BoundedZ g → T (f + g) = T f + T g)
    (hsmul : ∀ (c : ℂ) (f : ℤ → ℂ), BoundedZ f → T (c • f) = c • T f)
    {p A B : ℝ} (hp1 : 1 < p) (hp2 : p < 2) (hA : 0 < A) (hB : 0 < B)
    (h1 : ∀ g : ℤ → ℂ, SupportIn g N₀ → (∀ x : ℤ, ‖g x‖ ≤ 1) →
      eLpNorm (T g) 2 Measure.count ≤ ENNReal.ofReal A)
    (h2 : ∀ g : ℤ → ℂ, BoundedZ g →
      eLpNorm (T g) 2 Measure.count
        ≤ ENNReal.ofReal B * eLpNorm g (ENNReal.ofReal p) Measure.count)
    {f : ℤ → ℂ} (hf : MemLp f 2 Measure.count) (hbdd : BoundedZ f) (hfsupp : SupportIn f N₀) :
    eLpNorm (T f) 2 Measure.count
      ≤ ENNReal.ofReal (2 * A ^ (1 - p / 2) * B ^ (p / 2)) * eLpNorm f 2 Measure.count := by
  classical
  have hT0 : T (0 : ℤ → ℂ) = 0 := by
    have h1' : T (0 : ℤ → ℂ) = T 0 + T 0 := by
      simpa using hadd 0 0 boundedZ_zero boundedZ_zero
    funext x
    have hx : T (0 : ℤ → ℂ) x + 0 = T (0 : ℤ → ℂ) x + T (0 : ℤ → ℂ) x := by
      rw [add_zero]
      exact congrFun h1' x
    exact (add_left_cancel hx).symm
  by_cases hE0 : eLpNorm f 2 Measure.count = 0
  · have hfzero : f = 0 := by
      funext x
      have hdirac : Measure.dirac x ≤ (Measure.count : Measure ℤ) := by
        rw [Measure.count]
        exact Measure.le_sum Measure.dirac x
      have hle : ‖f x‖ₑ ≤ eLpNorm f 2 Measure.count := by
        rw [← eLpNorm_dirac f x (by norm_num : (2 : ℝ≥0∞) ≠ 0)]
        exact eLpNorm_mono_measure f hdirac
      have h0 : ‖f x‖ₑ = 0 := le_antisymm (by simpa [hE0] using hle) bot_le
      exact enorm_eq_zero.mp h0
    rw [hfzero, hT0]
    simp
  · set E : ℝ := (eLpNorm f 2 Measure.count).toReal with hEdef
    have hElt : eLpNorm f 2 Measure.count < ⊤ := MeasureTheory.MemLp.eLpNorm_lt_top hf
    have hEpos : 0 < E := ENNReal.toReal_pos hE0 hElt.ne
    have hEeq : eLpNorm f 2 Measure.count = ENNReal.ofReal E := by
      rw [hEdef, ENNReal.ofReal_toReal hElt.ne]
    set t : ℝ := (B / A) ^ (p / 2) with htdef
    have htpos : 0 < t := Real.rpow_pos_of_pos (div_pos hB hA) _
    set lam : ℝ := t * E with hlamdef
    have hlamp : 0 < lam := mul_pos htpos hEpos
    set s : ℂ := ((lam⁻¹ : ℝ) : ℂ) with hs
    set flo : ℤ → ℂ := fun x => if ‖f x‖ ≤ lam then f x else 0 with hflodef
    set fhi : ℤ → ℂ := fun x => if lam < ‖f x‖ then f x else 0 with hfhiedef
    have hsplit : flo + fhi = f := by
      funext x
      simp only [Pi.add_apply, hflodef, hfhiedef]
      by_cases h : ‖f x‖ ≤ lam
      · rw [if_pos h, if_neg (not_lt.mpr h), add_zero]
      · rw [if_neg h, if_pos (not_le.mp h), zero_add]
    have hflobdd : BoundedZ flo := boundedZ_of_bound (C := lam) fun x => by
      simp only [hflodef]
      split_ifs with h
      · exact h
      · simpa using hlamp.le
    have hfhibdd : BoundedZ fhi := by
      have hsub : fhi = f - flo := by
        funext x
        simp only [hfhiedef, hflodef, Pi.sub_apply]
        by_cases h : ‖f x‖ ≤ lam
        · rw [if_neg (not_lt.mpr h), if_pos h, sub_self]
        · rw [if_pos (not_le.mp h), if_neg h, sub_zero]
      rw [hsub]
      exact boundedZ_sub hbdd hflobdd
    have hflosupp : SupportIn flo N₀ := by
      intro x hx
      simp only [hflodef]
      split_ifs with h
      · exact hfsupp x hx
      · rfl
    -- the `ℓ^∞` bound for the low part
    have hs1 : (lam : ℂ) * s = 1 := by
      rw [hs, ← Complex.ofReal_mul, mul_inv_cancel₀ (ne_of_gt hlamp), Complex.ofReal_one]
    have hb1 : eLpNorm (T flo) 2 Measure.count ≤ ENNReal.ofReal lam * ENNReal.ofReal A := by
      have hscale : eLpNorm (T (s • flo)) 2 Measure.count ≤ ENNReal.ofReal A := by
        refine h1 (s • flo) (SupportIn.smul s hflosupp) fun x => ?_
        rw [Pi.smul_apply, norm_smul]
        have hx1 : ‖flo x‖ ≤ lam := by
          simp only [hflodef]
          split_ifs with h
          · exact h
          · simpa using hlamp.le
        have hnorm : ‖s‖ = lam⁻¹ := by
          rw [hs, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        rw [hnorm]
        calc lam⁻¹ * ‖flo x‖ ≤ lam⁻¹ * lam := mul_le_mul_of_nonneg_left hx1 (by positivity)
          _ = 1 := inv_mul_cancel₀ (ne_of_gt hlamp)
      have hT : T flo = (lam : ℂ) • T (s • flo) := by
        have h1' : flo = (lam : ℂ) • (s • flo) := by
          rw [smul_smul, hs1, one_smul]
        exact (congrArg T h1').trans (hsmul (lam : ℂ) (s • flo) (boundedZ_smul s hflobdd))
      calc eLpNorm (T flo) 2 Measure.count
          = ‖(lam : ℂ)‖ₑ * eLpNorm (T (s • flo)) 2 Measure.count := by
            rw [hT, eLpNorm_const_smul]
        _ = ENNReal.ofReal lam * eLpNorm (T (s • flo)) 2 Measure.count := by
            have hnorm : ‖(lam : ℂ)‖ₑ = ENNReal.ofReal lam := by
              rw [← ofReal_norm, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hlamp.le]
            rw [hnorm]
        _ ≤ ENNReal.ofReal lam * ENNReal.ofReal A :=
            mul_le_mul_of_nonneg_left hscale (by positivity)
    -- the `ℓ^p` bound for the high part
    have hb2 : eLpNorm (T fhi) 2 Measure.count
        ≤ ENNReal.ofReal B * ENNReal.ofReal (lam ^ (1 - 2 / p) * E ^ (2 / p)) := by
      refine (h2 fhi hfhibdd).trans ?_
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      have hL := eLpNorm_levelSetHigh_le hf (lt_trans zero_lt_one hp1) hp2 hlamp
      rw [← hEdef] at hL
      simpa only [hfhiedef] using hL
    have htri : eLpNorm (T f) 2 Measure.count
        ≤ eLpNorm (T flo) 2 Measure.count + eLpNorm (T fhi) 2 Measure.count := by
      rw [← hsplit, hadd flo fhi hflobdd hfhibdd]
      exact eLpNorm_add_le (by norm_num)
    -- the real arithmetic
    have hAne : A ≠ 0 := ne_of_gt hA
    have hBne : B ≠ 0 := ne_of_gt hB
    have hq0 : (0 : ℝ) ≤ B / A := div_nonneg hB.le hA.le
    have hqp : 0 < B / A := div_pos hB hA
    have hAA : A ^ (1 - p / 2) = A / A ^ (p / 2) := by
      rw [Real.rpow_sub hA, Real.rpow_one]
    have hAt : A * t = A ^ (1 - p / 2) * B ^ (p / 2) := by
      rw [hAA, htdef, Real.div_rpow hB.le hA.le]
      field_simp
    have hexp : (p / 2) * (1 - 2 / p) = p / 2 - 1 := by
      field_simp
    have hBt : B * t ^ (1 - 2 / p) = A ^ (1 - p / 2) * B ^ (p / 2) := by
      have ht2 : t ^ (1 - 2 / p) = (B / A) ^ (p / 2) * (A / B) := by
        have hsum : p / 2 - 1 = p / 2 + (-1 : ℝ) := by ring
        rw [htdef, ← Real.rpow_mul hq0, hexp, hsum, Real.rpow_add hqp, Real.rpow_neg hq0 1,
          Real.rpow_one, inv_div]
      rw [ht2, ← hAt, htdef]
      field_simp
    have hEpow : E ^ (1 - 2 / p) * E ^ (2 / p) = E := by
      rw [← Real.rpow_add hEpos, show 1 - 2 / p + 2 / p = 1 by ring, Real.rpow_one]
    have hlamrpow : lam ^ (1 - 2 / p) = t ^ (1 - 2 / p) * E ^ (1 - 2 / p) := by
      rw [hlamdef, Real.mul_rpow htpos.le hEpos.le]
    have hident : lam * A + B * (lam ^ (1 - 2 / p) * E ^ (2 / p))
        = 2 * A ^ (1 - p / 2) * B ^ (p / 2) * E := by
      calc lam * A + B * (lam ^ (1 - 2 / p) * E ^ (2 / p))
          = (t * E) * A + B * ((t ^ (1 - 2 / p) * E ^ (1 - 2 / p)) * E ^ (2 / p)) := by
            rw [hlamdef, hlamrpow]
        _ = E * (A * t) + (B * t ^ (1 - 2 / p)) * (E ^ (1 - 2 / p) * E ^ (2 / p)) := by ring
        _ = E * (A ^ (1 - p / 2) * B ^ (p / 2))
              + (A ^ (1 - p / 2) * B ^ (p / 2)) * E := by rw [hAt, hBt, hEpow]
        _ = 2 * A ^ (1 - p / 2) * B ^ (p / 2) * E := by ring
    calc eLpNorm (T f) 2 Measure.count
        ≤ eLpNorm (T flo) 2 Measure.count + eLpNorm (T fhi) 2 Measure.count := htri
      _ ≤ ENNReal.ofReal lam * ENNReal.ofReal A
            + ENNReal.ofReal B * ENNReal.ofReal (lam ^ (1 - 2 / p) * E ^ (2 / p)) :=
          add_le_add hb1 hb2
      _ = ENNReal.ofReal (lam * A + B * (lam ^ (1 - 2 / p) * E ^ (2 / p))) := by
          rw [← ENNReal.ofReal_mul hlamp.le, ← ENNReal.ofReal_mul hB.le, ← ENNReal.ofReal_add]
          · positivity
          · positivity
      _ = ENNReal.ofReal (2 * A ^ (1 - p / 2) * B ^ (p / 2) * E) := by rw [hident]
      _ = ENNReal.ofReal (2 * A ^ (1 - p / 2) * B ^ (p / 2)) * eLpNorm f 2 Measure.count := by
          rw [ENNReal.ofReal_mul (by positivity), ← hEeq]

end Work.KMTAreas.A4Z
