import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

open MeasureTheory intervalIntegral Filter Set
open scoped Interval Topology ComplexConjugate

namespace Commons.Analysis.Complex

noncomputable section

/-! # Crossing the branch cut of the principal logarithm

For a continuous curve `u ↦ φ u + i u` that crosses the negative real axis at `u = 0`
(where `φ 0 < 0`), the integral of `(φ' + i) / (φ + i u)` over `[a, b]` (`a < 0 < b`)
equals the principal-logarithm difference plus `-2πi`, the jump of the argument. -/

/-- The curve `u ↦ φ u + i u` associated with `φ`. -/
def ccZ (φ : ℝ → ℝ) (u : ℝ) : ℂ := (φ u : ℂ) + (u : ℂ) * Complex.I

lemma ccZ_im (φ : ℝ → ℝ) (u : ℝ) : (ccZ φ u).im = u := by
  simp [ccZ]

lemma ccZ_re (φ : ℝ → ℝ) (u : ℝ) : (ccZ φ u).re = φ u := by
  simp [ccZ]

lemma ccZ_mem_slitPlane {φ : ℝ → ℝ} {u : ℝ} (hu : u ≠ 0) : ccZ φ u ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  exact Or.inr (by rw [ccZ_im]; exact hu)

lemma integral_curve_cross {a b : ℝ} (ha : a < 0) (hb : 0 < b) (φ φ' : ℝ → ℝ)
    (hcont : ContinuousOn φ (Set.Icc a b))
    (hderiv : ∀ u ∈ Set.Ioo a b, u ≠ 0 → HasDerivAt φ (φ' u) u)
    (hφ0 : φ 0 < 0)
    (hintL : IntervalIntegrable
      (fun u : ℝ => ((φ' u : ℂ) + Complex.I) / ((φ u : ℂ) + (u : ℂ) * Complex.I)) volume a 0)
    (hintR : IntervalIntegrable
      (fun u : ℝ => ((φ' u : ℂ) + Complex.I) / ((φ u : ℂ) + (u : ℂ) * Complex.I)) volume 0 b) :
    (∫ u in a..b, ((φ' u : ℂ) + Complex.I) / ((φ u : ℂ) + (u : ℂ) * Complex.I))
      = Complex.log ((φ b : ℂ) + (b : ℂ) * Complex.I)
        - Complex.log ((φ a : ℂ) + (a : ℂ) * Complex.I) - 2 * (Real.pi : ℂ) * Complex.I := by
  change (∫ u in a..b, ((φ' u : ℂ) + Complex.I) / ccZ φ u)
      = Complex.log (ccZ φ b) - Complex.log (ccZ φ a) - 2 * (Real.pi : ℂ) * Complex.I
  have hab : a < b := ha.trans hb
  have hintL' : IntervalIntegrable (fun u : ℝ => ((φ' u : ℂ) + Complex.I) / ccZ φ u)
      volume a 0 := by simpa only [ccZ] using hintL
  have hintR' : IntervalIntegrable (fun u : ℝ => ((φ' u : ℂ) + Complex.I) / ccZ φ u)
      volume 0 b := by simpa only [ccZ] using hintR
  -- continuity of the curve on the closed interval
  have hcontZ : ContinuousOn (ccZ φ) (Set.Icc a b) := by
    unfold ccZ
    exact (Complex.continuous_ofReal.comp_continuousOn hcont).add
      ((Complex.continuous_ofReal.mul continuous_const).continuousOn)
  -- ambient continuity at the crossing point
  have hIcc_nhds : Set.Icc a b ∈ 𝓝 (0 : ℝ) :=
    Filter.mem_of_superset (Ioo_mem_nhds ha hb) Set.Ioo_subset_Icc_self
  have hca0 : ContinuousAt (ccZ φ) 0 := hcontZ.continuousAt hIcc_nhds
  have hZre0 : (ccZ φ 0).re < 0 := by rw [ccZ_re]; exact hφ0
  have hZim0 : (ccZ φ 0).im = 0 := ccZ_im φ 0
  -- the one-sided limits of `log ∘ ccZ` at `0`
  have hlim0R : Tendsto (fun u : ℝ => Complex.log (ccZ φ u)) (𝓝[>] (0 : ℝ))
      (𝓝 ((Real.log ‖ccZ φ 0‖ : ℂ) + (Real.pi : ℂ) * Complex.I)) := by
    have hlog := Complex.tendsto_log_nhdsWithin_im_nonneg_of_re_neg_of_im_zero
      (z := ccZ φ 0) hZre0 hZim0
    have h1 : Tendsto (ccZ φ) (𝓝[>] (0 : ℝ)) (𝓝 (ccZ φ 0)) :=
      hca0.tendsto.mono_left inf_le_left
    have h2 : Tendsto (ccZ φ) (𝓝[>] (0 : ℝ)) (𝓟 {z : ℂ | 0 ≤ z.im}) := by
      rw [tendsto_principal]
      filter_upwards [self_mem_nhdsWithin] with u hu
      rw [ccZ_im]; exact le_of_lt hu
    exact hlog.comp ((h1.inf h2).mono_left (le_inf le_rfl le_rfl))
  have hlim0L : Tendsto (fun u : ℝ => Complex.log (ccZ φ u)) (𝓝[<] (0 : ℝ))
      (𝓝 ((Real.log ‖ccZ φ 0‖ : ℂ) - (Real.pi : ℂ) * Complex.I)) := by
    have hlog := Complex.tendsto_log_nhdsWithin_im_neg_of_re_neg_of_im_zero
      (z := ccZ φ 0) hZre0 hZim0
    have h1 : Tendsto (ccZ φ) (𝓝[<] (0 : ℝ)) (𝓝 (ccZ φ 0)) :=
      hca0.tendsto.mono_left inf_le_left
    have h2 : Tendsto (ccZ φ) (𝓝[<] (0 : ℝ)) (𝓟 {z : ℂ | z.im < 0}) := by
      rw [tendsto_principal]
      filter_upwards [self_mem_nhdsWithin] with u hu
      rw [ccZ_im]; exact hu
    exact hlog.comp ((h1.inf h2).mono_left (le_inf le_rfl le_rfl))
  -- the limits at the honest endpoints
  have hlima : Tendsto (fun u : ℝ => Complex.log (ccZ φ u)) (𝓝[>] a)
      (𝓝 (Complex.log (ccZ φ a))) := by
    have h : Tendsto (ccZ φ) (𝓝[Set.Ioo a b] a) (𝓝 (ccZ φ a)) :=
      (hcontZ.continuousWithinAt (Set.left_mem_Icc.mpr hab.le)).mono Set.Ioo_subset_Icc_self
    rw [nhdsWithin_Ioo_eq_nhdsGT hab] at h
    exact h.clog (ccZ_mem_slitPlane (ne_of_lt ha))
  have hlimb : Tendsto (fun u : ℝ => Complex.log (ccZ φ u)) (𝓝[<] b)
      (𝓝 (Complex.log (ccZ φ b))) := by
    have h : Tendsto (ccZ φ) (𝓝[Set.Ioo a b] b) (𝓝 (ccZ φ b)) :=
      (hcontZ.continuousWithinAt (Set.right_mem_Icc.mpr hab.le)).mono Set.Ioo_subset_Icc_self
    rw [nhdsWithin_Ioo_eq_nhdsLT hab] at h
    exact h.clog (ccZ_mem_slitPlane (ne_of_gt hb))
  -- differentiability of the curve
  have hderivZ : ∀ u ∈ Set.Ioo a b, u ≠ 0 →
      HasDerivAt (ccZ φ) ((φ' u : ℂ) + Complex.I) u := by
    intro u hu hu0
    have h1 : HasDerivAt (fun u : ℝ => (φ u : ℂ)) (φ' u : ℂ) u :=
      (hderiv u hu hu0).ofReal_comp
    have h2 : HasDerivAt (fun u : ℝ => (u : ℂ) * Complex.I) Complex.I u := by
      simpa using ((hasDerivAt_id u).ofReal_comp).mul_const Complex.I
    exact h1.add h2
  have hlogderiv : ∀ u ∈ Set.Ioo a b, u ≠ 0 →
      HasDerivAt (fun u : ℝ => Complex.log (ccZ φ u))
        (((φ' u : ℂ) + Complex.I) / ccZ φ u) u :=
    fun u hu hu0 => (hderivZ u hu hu0).clog_real (ccZ_mem_slitPlane hu0)
  -- the two halves
  have hright := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto
      (f := fun u : ℝ => Complex.log (ccZ φ u))
      (f' := fun u : ℝ => ((φ' u : ℂ) + Complex.I) / ccZ φ u)
      (a := (0 : ℝ)) (b := b) hb
      (fun u hu => hlogderiv u ⟨ha.trans hu.1, hu.2⟩ (ne_of_gt hu.1))
      hintR' hlim0R hlimb
  have hleft := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto
      (f := fun u : ℝ => Complex.log (ccZ φ u))
      (f' := fun u : ℝ => ((φ' u : ℂ) + Complex.I) / ccZ φ u)
      (a := a) (b := (0 : ℝ)) ha
      (fun u hu => hlogderiv u ⟨hu.1, hu.2.trans hb⟩ (ne_of_lt hu.2))
      hintL' hlima hlim0L
  rw [← intervalIntegral.integral_add_adjacent_intervals hintL' hintR', hleft, hright]
  ring

end

end Commons.Analysis.Complex