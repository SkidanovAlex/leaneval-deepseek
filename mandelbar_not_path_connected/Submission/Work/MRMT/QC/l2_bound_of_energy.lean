import Mathlib
import Submission.Work.MRMT.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.MRMT.QC

open MeasureTheory Filter

/-- Cauchy–Schwarz / Hölder with conjugate exponents `2, 2` for nonnegative `L²` functions:
the integral of the product is bounded by the product of the `L²` norms. -/
private lemma l2_mul_integral_le {f g : ℂ → ℝ}
    (hf : MemLp f 2 (volume : Measure ℂ)) (hg : MemLp g 2 (volume : Measure ℂ))
    (hf0 : 0 ≤ᵐ[(volume : Measure ℂ)] f) (hg0 : 0 ≤ᵐ[(volume : Measure ℂ)] g) :
    ∫ z, f z * g z ≤ Real.sqrt (∫ z, f z ^ 2) * Real.sqrt (∫ z, g z ^ 2) := by
  have hpq : (2 : ℝ).HolderConjugate 2 := Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := (volume : Measure ℂ)) hpq hf0 hg0
    (by simpa using hf) (by simpa using hg)
  rw [show (∫ z, f z ^ (2 : ℝ)) = ∫ z, f z ^ 2 from by
        apply integral_congr_ae; filter_upwards with z; exact Real.rpow_natCast (f z) 2,
      show (∫ z, g z ^ (2 : ℝ)) = ∫ z, g z ^ 2 from by
        apply integral_congr_ae; filter_upwards with z; exact Real.rpow_natCast (g z) 2] at h
  rwa [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow] at h

/-- The elementary real inequality underlying the energy bound: if
`A ≤ k * A + √B * √A` with `k < 1` then `A ≤ B / (1 - k)²`. -/
private lemma real_key {A B k : ℝ} (hk1 : k < 1) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (h : A ≤ k * A + Real.sqrt B * Real.sqrt A) : A ≤ B / (1 - k) ^ 2 := by
  have h1 : (1 - k) * A ≤ Real.sqrt B * Real.sqrt A := by linarith
  by_cases hs : Real.sqrt A = 0
  · have hA_eq : A = 0 := by
      have hh := Real.sq_sqrt hA; rw [hs] at hh; simpa using hh.symm
    rw [hA_eq]; exact div_nonneg hB (sq_nonneg _)
  · have hs' : 0 < Real.sqrt A := lt_of_le_of_ne' (Real.sqrt_nonneg A) hs
    have h2 : (1 - k) * Real.sqrt A ≤ Real.sqrt B := by
      have hsq : Real.sqrt A * Real.sqrt A = A := by
        rw [show Real.sqrt A * Real.sqrt A = (Real.sqrt A) ^ 2 by ring, Real.sq_sqrt hA]
      have hmul : Real.sqrt A * ((1 - k) * Real.sqrt A) ≤ Real.sqrt A * Real.sqrt B := by
        calc Real.sqrt A * ((1 - k) * Real.sqrt A)
            = (1 - k) * (Real.sqrt A * Real.sqrt A) := by ring
          _ = (1 - k) * A := by rw [hsq]
          _ ≤ Real.sqrt B * Real.sqrt A := h1
          _ = Real.sqrt A * Real.sqrt B := by ring
      exact le_of_mul_le_mul_left hmul hs'
    have h3 : ((1 - k) * Real.sqrt A) ^ 2 ≤ (Real.sqrt B) ^ 2 :=
      pow_le_pow_left₀ (by nlinarith [hs', hk1]) h2 2
    rw [mul_pow, Real.sq_sqrt hB, Real.sq_sqrt hA] at h3
    rw [le_div_iff₀ (by nlinarith [hk1])]
    nlinarith [h3]

theorem l2_bound_of_energy {p q : ℂ → ℂ} {e : ℂ → ℝ} {k : ℝ} (hk0 : 0 ≤ k) (hk1 : k < 1)
    (hpm : MeasureTheory.MemLp p 2 (MeasureTheory.volume : MeasureTheory.Measure ℂ))
    (hqm : MeasureTheory.MemLp q 2 (MeasureTheory.volume : MeasureTheory.Measure ℂ))
    (hem : MeasureTheory.MemLp e 2 (MeasureTheory.volume : MeasureTheory.Measure ℂ))
    (he : ∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure ℂ), 0 ≤ e z)
    (henergy : ∫ z, ‖p z‖ ^ 2 = ∫ z, ‖q z‖ ^ 2)
    (hbd : ∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure ℂ), ‖q z‖ ≤ k * ‖p z‖ + e z) :
    ∫ z, ‖p z‖ ^ 2 ≤ (∫ z, (e z) ^ 2) / (1 - k) ^ 2 := by
  have hpmn : MemLp (fun z => ‖p z‖) 2 (volume : Measure ℂ) := hpm.norm
  have hqmn : MemLp (fun z => ‖q z‖) 2 (volume : Measure ℂ) := hqm.norm
  have hg2 : Integrable (fun z => ‖q z‖ ^ 2) (volume : Measure ℂ) := hqmn.integrable_sq
  have hfg : Integrable (fun z => ‖p z‖ * ‖q z‖) (volume : Measure ℂ) :=
    MemLp.integrable_mul hpmn hqmn
  have heg : Integrable (fun z => e z * ‖q z‖) (volume : Measure ℂ) :=
    MemLp.integrable_mul hem hqmn
  have hle : (fun z => ‖q z‖ ^ 2) ≤ᵐ[(volume : Measure ℂ)]
      (fun z => k * (‖p z‖ * ‖q z‖) + e z * ‖q z‖) := by
    filter_upwards [hbd] with z hz
    have hg0 : 0 ≤ ‖q z‖ := norm_nonneg _
    calc ‖q z‖ ^ 2 = ‖q z‖ * ‖q z‖ := by ring
      _ ≤ (k * ‖p z‖ + e z) * ‖q z‖ := mul_le_mul_of_nonneg_right hz hg0
      _ = k * (‖p z‖ * ‖q z‖) + e z * ‖q z‖ := by ring
  have hsumint : Integrable (fun z => k * (‖p z‖ * ‖q z‖) + e z * ‖q z‖) (volume : Measure ℂ) :=
    (hfg.const_mul k).add heg
  have hmain : ∫ z, ‖q z‖ ^ 2 ≤ k * (∫ z, ‖p z‖ * ‖q z‖) + ∫ z, e z * ‖q z‖ := by
    have h := integral_mono_ae hg2 hsumint hle
    rwa [integral_add (hfg.const_mul k) heg, integral_const_mul k (fun z => ‖p z‖ * ‖q z‖)] at h
  have hCS1 : ∫ z, ‖p z‖ * ‖q z‖ ≤ Real.sqrt (∫ z, ‖p z‖ ^ 2) * Real.sqrt (∫ z, ‖q z‖ ^ 2) :=
    l2_mul_integral_le hpmn hqmn (Eventually.of_forall fun z => norm_nonneg _)
      (Eventually.of_forall fun z => norm_nonneg _)
  have hCS2 : ∫ z, e z * ‖q z‖ ≤ Real.sqrt (∫ z, e z ^ 2) * Real.sqrt (∫ z, ‖q z‖ ^ 2) :=
    l2_mul_integral_le hem hqmn he (Eventually.of_forall fun z => norm_nonneg _)
  have hA0 : 0 ≤ ∫ z, ‖p z‖ ^ 2 := integral_nonneg (fun z => by positivity)
  have hB0 : 0 ≤ ∫ z, e z ^ 2 := integral_nonneg (fun z => by positivity)
  have hkey : ∫ z, ‖p z‖ ^ 2 ≤ k * (∫ z, ‖p z‖ ^ 2)
      + Real.sqrt (∫ z, e z ^ 2) * Real.sqrt (∫ z, ‖p z‖ ^ 2) := by
    rw [← henergy] at hmain hCS1 hCS2
    calc ∫ z, ‖p z‖ ^ 2
        ≤ k * (∫ z, ‖p z‖ * ‖q z‖) + ∫ z, e z * ‖q z‖ := hmain
      _ ≤ k * (Real.sqrt (∫ z, ‖p z‖ ^ 2) * Real.sqrt (∫ z, ‖p z‖ ^ 2))
            + Real.sqrt (∫ z, e z ^ 2) * Real.sqrt (∫ z, ‖p z‖ ^ 2) :=
            add_le_add (mul_le_mul_of_nonneg_left hCS1 hk0) hCS2
      _ = k * (∫ z, ‖p z‖ ^ 2)
            + Real.sqrt (∫ z, e z ^ 2) * Real.sqrt (∫ z, ‖p z‖ ^ 2) := by
            rw [show Real.sqrt (∫ z, ‖p z‖ ^ 2) * Real.sqrt (∫ z, ‖p z‖ ^ 2)
                  = (Real.sqrt (∫ z, ‖p z‖ ^ 2)) ^ 2 by ring, Real.sq_sqrt hA0]
  exact real_key hk1 hA0 hB0 hkey

end Work.MRMT.QC
