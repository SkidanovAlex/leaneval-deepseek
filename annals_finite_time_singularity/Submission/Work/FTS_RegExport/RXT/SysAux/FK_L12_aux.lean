import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS_RegExport.RXT.C2Radial
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.Spaces.aesm_slice_of_continuousOn_Qd
import Submission.Work.Spaces.uncurry_partial_c1
import Submission.Work.FTS_RegExport.RXT.hasDerivAt_integral_Itheta_of_bound
import Submission.Work.FTS_RegExport.RXT.continuousAt_integral_Itheta_of_bound
import Submission.Work.FTS_RegExport.RXT.SysAux.abs_setIntegral_Itheta_mul_K_le
import Submission.Work.FTS_RegExport.RXT.SysAux.DzIter_two_pt_open

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_RegExport.RXT.SysAux

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-! ## Auxiliary lemmas in this file

The single target is `FK_L12_slice_facts` below.  Everything between here and it is a helper. -/

/-! ### The weight `z^{3/2}/(1+z)²` and its elementary properties -/

/-- The radial weight `L12Wt z = z^{3/2}/(1+z)²`. -/
def L12Wt (z : ℝ) : ℝ := z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2

lemma L12Wt_pos {z : ℝ} (hz : 0 < z) : 0 < L12Wt z :=
  div_pos (Real.rpow_pos_of_pos hz _) (by positivity)

lemma L12Wt_nonneg {z : ℝ} (hz : 0 < z) : 0 ≤ L12Wt z := (L12Wt_pos hz).le

/-- `L12Wt z / z = √z/(1+z)²`. -/
lemma L12Wt_div_eq {z : ℝ} (hz : 0 < z) : L12Wt z / z = Real.sqrt z / (1 + z) ^ 2 := by
  have h : z ^ ((3 : ℝ) / 2) = Real.sqrt z * z := by
    rw [Real.sqrt_eq_rpow, show ((3 : ℝ) / 2) = (1 : ℝ) / 2 + 1 by norm_num,
      Real.rpow_add hz, Real.rpow_one]
  rw [L12Wt, h]
  field_simp

/-- `L12Wt z / z² = z^{-1/2}/(1+z)²`. -/
lemma L12Wt_div_sq_eq {z : ℝ} (hz : 0 < z) :
    L12Wt z / z ^ 2 = z ^ (-(1 : ℝ) / 2) / (1 + z) ^ 2 := by
  have h : z ^ ((3 : ℝ) / 2) = z ^ (-(1 : ℝ) / 2) * z ^ 2 := by
    rw [show ((3 : ℝ) / 2) = -(1 : ℝ) / 2 + 2 by norm_num, Real.rpow_add hz, Real.rpow_two]
  rw [L12Wt, h]
  field_simp

/-- `L12Wt z ≤ 1` for `z > 0`. -/
lemma L12Wt_le_one {z : ℝ} (hz : 0 < z) : L12Wt z ≤ 1 := by
  rw [L12Wt, div_le_one (by positivity : (0 : ℝ) < (1 + z) ^ 2)]
  by_cases h1 : z ≤ 1
  · exact le_trans (Real.rpow_le_one hz.le h1 (by norm_num)) (by nlinarith)
  · have h2 : z ^ ((3 : ℝ) / 2) ≤ z ^ (2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (le_of_lt (lt_of_not_ge h1)) (by norm_num)
    rw [Real.rpow_two] at h2
    nlinarith

/-- `L12Wt z ≤ z^{3/2}` for `z > 0`. -/
lemma L12Wt_le_rpow {z : ℝ} (hz : 0 < z) : L12Wt z ≤ z ^ ((3 : ℝ) / 2) := by
  rw [L12Wt, div_le_iff₀ (by positivity : (0 : ℝ) < (1 + z) ^ 2)]
  exact le_mul_of_one_le_right (Real.rpow_nonneg hz.le _) (by nlinarith)

/-- `L12Wt z / z ≤ 1` for `z > 0`. -/
lemma L12Wt_div_le_one {z : ℝ} (hz : 0 < z) : L12Wt z / z ≤ 1 := by
  rw [L12Wt_div_eq hz, div_le_one (by positivity : (0 : ℝ) < (1 + z) ^ 2)]
  by_cases h1 : z ≤ 1
  · have h : Real.sqrt z ≤ 1 := Real.sqrt_le_one.mpr h1
    nlinarith
  · have h2 : Real.sqrt z ≤ 1 + z := by
      rw [Real.sqrt_le_iff]
      exact ⟨by positivity, by nlinarith⟩
    nlinarith

/-- `L12Wt w / w² ≤ (z/2)^{-1/2}` for `w ≥ z/2 > 0`. -/
lemma L12Wt_div_sq_le {z w : ℝ} (hz : 0 < z) (hw : z / 2 ≤ w) :
    L12Wt w / w ^ 2 ≤ (z / 2) ^ (-(1 : ℝ) / 2) := by
  have hw0 : 0 < w := lt_of_lt_of_le (by linarith) hw
  rw [L12Wt_div_sq_eq hw0]
  have h1 : w ^ (-(1 : ℝ) / 2) / (1 + w) ^ 2 ≤ w ^ (-(1 : ℝ) / 2) / 1 :=
    div_le_div_of_nonneg_left (Real.rpow_nonneg hw0.le _) one_pos (by nlinarith)
  rw [div_one] at h1
  exact h1.trans (Real.rpow_le_rpow_of_nonpos (by linarith : (0 : ℝ) < z / 2) hw (by norm_num))

/-! ### Elementary measure facts on the angular interval -/

/-- The measure attached to `Iθ = [0,π/2]` is the one of the open interval `(0,π/2)`. -/
lemma volume_restrict_Iθ_eq :
    (volume.restrict Work.Spaces.Iθ : Measure ℝ) = volume.restrict (Set.Ioo 0 (Real.pi / 2)) := by
  rw [Work.Spaces.Iθ]
  exact (Measure.restrict_congr_set MeasureTheory.Ioo_ae_eq_Icc).symm

private lemma measurableSet_Iθ : MeasurableSet Work.Spaces.Iθ := by
  rw [Work.Spaces.Iθ]; exact measurableSet_Icc

/-- Almost every `θ ∈ Iθ` lies in the open interval. -/
lemma ae_mem_Ioo_of_mem_Iθ :
    ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ), θ ∈ Set.Ioo 0 (Real.pi / 2) := by
  rw [volume_restrict_Iθ_eq]
  exact ae_restrict_mem measurableSet_Ioo

private lemma integrable_const_Ioo (c : ℝ) :
    Integrable (fun _ : ℝ => c) (volume.restrict (Set.Ioo 0 (Real.pi / 2))) := by
  refine MeasureTheory.integrable_const_iff.mpr (Or.inr ?_)
  exact MeasureTheory.isFiniteMeasure_restrict.mpr
    (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top)

/-- `deriv` of two functions that agree on an open set. -/
lemma deriv_congr_of_isOpen {f g : ℝ → ℝ} {s : Set ℝ} (hs : IsOpen s)
    (h : Set.EqOn f g s) : Set.EqOn (deriv f) (deriv g) s :=
  fun z hz => Filter.EventuallyEq.deriv_eq
    (Filter.Eventually.mono (hs.mem_nhds hz) fun w hw => h hw)

/-! ### Delegated elementary facts (proved in sibling files of this directory) -/

lemma sqrt_div_sq_integrableOn_aux :
    IntegrableOn (fun r : ℝ => Real.sqrt r / (1 + r) ^ 2) (Set.Ioi 0) := by
  have hfcont : ContinuousOn (fun s : ℝ => Real.sqrt s / (1 + s) ^ 2) (Set.Ioi 0) := by
    refine ContinuousOn.div Real.continuous_sqrt.continuousOn
      ((continuous_const.add continuous_id).continuousOn.pow 2) (fun s hs => ?_)
    have h0 : (0 : ℝ) < s := hs
    positivity
  have h1 : IntegrableOn (fun s : ℝ => Real.sqrt s / (1 + s) ^ 2) (Set.Ioc 0 1) := by
    refine Integrable.mono'
      (MeasureTheory.integrableOn_const (s := Set.Ioc (0 : ℝ) 1) (C := (1 : ℝ))
        (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top))
      ((hfcont.mono (fun s hs => hs.1)).aestronglyMeasurable measurableSet_Ioc) ?_
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioc (fun s hs => ?_)
    have hs0 : (0 : ℝ) < s := hs.1
    have hpos : (0 : ℝ) < (1 + s) ^ 2 := by positivity
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    refine (div_le_one hpos).mpr ?_
    have h3 : Real.sqrt s ≤ 1 + s := by
      rw [Real.sqrt_le_iff]
      exact ⟨by positivity, by nlinarith⟩
    nlinarith [h3, hs0]
  have h2 : IntegrableOn (fun s : ℝ => Real.sqrt s / (1 + s) ^ 2) (Set.Ioi 1) := by
    have hle : ∀ s ∈ Set.Ioi (1 : ℝ),
        Real.sqrt s / (1 + s) ^ 2 ≤ s ^ (-(3 / 2 : ℝ)) := by
      intro s hs
      have hs0 : (0 : ℝ) < s := lt_trans (by norm_num) hs
      have hstep : Real.sqrt s / (1 + s) ^ 2 ≤ Real.sqrt s / s ^ 2 :=
        div_le_div_of_nonneg_left (Real.sqrt_nonneg s) (by positivity) (by nlinarith)
      have heq : Real.sqrt s / s ^ 2 = s ^ (-(3 / 2 : ℝ)) := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast s 2, ← Real.rpow_sub hs0]
        norm_num
      linarith [hstep, heq.le]
    refine Integrable.mono'
      ((integrableOn_Ioi_rpow_iff (s := -(3 / 2 : ℝ)) (t := (1 : ℝ)) (by norm_num)).mpr
        (by norm_num))
      ((hfcont.mono (fun s hs => lt_trans (by norm_num) hs)).aestronglyMeasurable
        measurableSet_Ioi) ?_
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi (fun s hs => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact hle s hs
  have hunion : Set.Ioc (0 : ℝ) 1 ∪ Set.Ioi (1 : ℝ) = Set.Ioi (0 : ℝ) := by
    ext x
    simp only [Set.mem_union, Set.mem_Ioc, Set.mem_Ioi]
    constructor
    · rintro (⟨h0, _⟩ | h1) <;> linarith
    · intro hx
      by_cases h : x ≤ 1
      · exact Or.inl ⟨hx, h⟩
      · exact Or.inr (lt_of_not_ge h)
  rw [← hunion]
  exact h1.union h2

lemma abs_setIntegral_Itheta_mul_K_le_aux {G : ℝ → ℝ} {c : ℝ} (hc : 0 ≤ c)
    (hmeas : AEStronglyMeasurable G (volume.restrict Work.Spaces.Iθ))
    (hb : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ), |G θ| ≤ c) :
    |∫ θ in Work.Spaces.Iθ, G θ * Work.Spaces.K θ| ≤ c * 3 * (Real.pi / 2) :=
  abs_setIntegral_Itheta_mul_K_le hc hmeas hb

lemma abs_setIntegral_Ioi_le_of_integral_zero_aux {g : ℝ → ℝ} {B z : ℝ}
    (hB : 0 ≤ B) (hz : 0 < z) (hint : IntegrableOn g (Set.Ioi 0))
    (hbd : ∀ r : ℝ, 0 < r → |g r| ≤ B * (Real.sqrt r / (1 + r) ^ 2))
    (h0 : ∫ r in Set.Ioi 0, g r = 0) :
    |∫ r in Set.Ioi z, g r| ≤ B * z ^ ((3 : ℝ) / 2) := by
  have hintz : IntegrableOn g (Set.Ioi z) := hint.mono_set (Set.Ioi_subset_Ioi hz.le)
  have hadd : (∫ r in (0 : ℝ)..z, g r) + (∫ r in Set.Ioi z, g r) = ∫ r in Set.Ioi 0, g r :=
    intervalIntegral.integral_interval_add_Ioi (a := (0 : ℝ)) (b := z) (μ := volume) hint hintz
  have hEq : ∫ r in Set.Ioi z, g r = -∫ r in (0 : ℝ)..z, g r := by linarith
  rw [hEq, abs_neg, intervalIntegral.integral_of_le hz.le]
  -- the integrand is dominated by the constant `B * √z` on `(0,z]`
  have hnorm : IntegrableOn (fun r : ℝ => ‖g r‖) (Set.Ioi 0) := hint.norm
  have hdomN : IntegrableOn (fun r : ℝ => ‖g r‖) (Set.Ioc 0 z) :=
    hnorm.mono_set (fun r hr => hr.1)
  have hdom : IntegrableOn (fun r : ℝ => |g r|) (Set.Ioc 0 z) := by
    simpa only [Real.norm_eq_abs] using hdomN
  have hconst : IntegrableOn (fun _ : ℝ => B * Real.sqrt z) (Set.Ioc 0 z) :=
    MeasureTheory.integrableOn_const (s := Set.Ioc (0 : ℝ) z) (C := B * Real.sqrt z)
      (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
  have hbound_ae : ∀ᵐ r ∂(volume.restrict (Set.Ioc 0 z)), |g r| ≤ B * Real.sqrt z := by
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioc (fun r hr => ?_)
    have hr0 : 0 < r := hr.1
    have h1 : |g r| ≤ B * (Real.sqrt r / (1 + r) ^ 2) := hbd r hr0
    have h2 : Real.sqrt r / (1 + r) ^ 2 ≤ Real.sqrt z := by
      have hden : (1 : ℝ) ≤ (1 + r) ^ 2 := by nlinarith [hr0.le]
      have hs : Real.sqrt r ≤ Real.sqrt z := Real.sqrt_le_sqrt hr.2
      calc Real.sqrt r / (1 + r) ^ 2 ≤ Real.sqrt r / 1 :=
            div_le_div_of_nonneg_left (Real.sqrt_nonneg r) one_pos hden
        _ = Real.sqrt r := div_one _
        _ ≤ Real.sqrt z := hs
    exact le_trans h1 (mul_le_mul_of_nonneg_left h2 hB)
  have hsz : Real.sqrt z * z = z ^ ((3 : ℝ) / 2) := by
    rw [Real.sqrt_eq_rpow, show ((3 : ℝ) / 2) = (1 : ℝ) / 2 + 1 by norm_num,
      Real.rpow_add hz, Real.rpow_one]
  calc |∫ r in Set.Ioc (0 : ℝ) z, g r| ≤ ∫ r in Set.Ioc (0 : ℝ) z, |g r| :=
        MeasureTheory.abs_integral_le_integral_abs
    _ ≤ ∫ r in Set.Ioc (0 : ℝ) z, B * Real.sqrt z :=
        MeasureTheory.integral_mono_ae hdom hconst hbound_ae
    _ = ∫ r in (0 : ℝ)..z, B * Real.sqrt z := by
        rw [intervalIntegral.integral_of_le hz.le]
    _ = B * Real.sqrt z * z := by
        rw [intervalIntegral.integral_const]
        simp only [sub_zero, smul_eq_mul]
        ring
    _ = B * z ^ ((3 : ℝ) / 2) := by rw [← hsz]; ring

lemma DzIter_two_pt_open_aux {h : ℝ → ℝ → ℝ}
    (hsmooth : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), ContDiffOn ℝ 2 (fun z => h z θ) (Set.Ioi 0))
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    Work.Spaces.DzIter 2 h z θ = z * Work.Spaces.pzIter 1 h z θ
      + z ^ 2 * Work.Spaces.pzIter 2 h z θ :=
  DzIter_two_pt_open hsmooth hz hθ

/-! ### Differentiation under the angular integral sign -/

/-- **Differentiation under the angular integral sign.**  `G` is `C²` on the open quadrant with a
uniform bound `C₀` on `G` and a uniform bound `C₁` on `∂_z G` on the half-neighbourhood
`(z₀/2, 2z₀)` of `z₀`. -/
lemma param_hasDerivAt {G : ℝ → ℝ → ℝ} {φ : ℝ → ℝ} {C₀ C₁ z₀ : ℝ}
    (hC₁ : 0 ≤ C₁) (hz₀ : 0 < z₀) (hφ : ContinuousOn φ Work.Spaces.Iθ)
    (hG2 : ContDiffOn ℝ 2 (Function.uncurry G) Work.FTS.EllipticEst.Q0)
    (hbd0 : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → |G z θ| ≤ C₀)
    (hbd1 : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      z₀ / 2 ≤ z → z ≤ 2 * z₀ → |Work.Spaces.pz G z θ| ≤ C₁) :
    HasDerivAt (fun z => ∫ θ in Work.Spaces.Iθ, G z θ * φ θ)
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.pz G z₀ θ * φ θ) z₀ := by
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (by simpa [Work.Spaces.Iθ] using hφ)
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hM 0 ⟨le_refl 0, by linarith [Real.pi_pos]⟩)
  have hφ' : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), |φ θ| ≤ M := fun θ hθ => by
    simpa [Real.norm_eq_abs] using hM θ ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  have hsub : Set.Ioo (0 : ℝ) (Real.pi / 2) ⊆ Work.Spaces.Iθ :=
    fun θ hθ => ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  have hGcont : ContinuousOn (Function.uncurry G) Work.FTS.EllipticEst.Q0 := hG2.continuousOn
  have hpz1 : ContDiffOn ℝ 1 (Function.uncurry (Work.Spaces.pz G)) Work.FTS.EllipticEst.Q0 :=
    (Work.Spaces.uncurry_partial_c1 Work.FTS.EllipticEst.isOpen_Q0 hG2).1
  have hsliceG : ∀ z : ℝ, 0 < z →
      ContinuousOn (fun θ : ℝ => G z θ) (Set.Ioo 0 (Real.pi / 2)) :=
    fun z hz => hGcont.comp ((continuous_const.prodMk continuous_id).continuousOn)
      (fun θ hθ => ⟨hz, hθ⟩)
  have hslicePz : ∀ z : ℝ, 0 < z →
      ContinuousOn (fun θ : ℝ => Work.Spaces.pz G z θ) (Set.Ioo 0 (Real.pi / 2)) :=
    fun z hz => hpz1.continuousOn.comp ((continuous_const.prodMk continuous_id).continuousOn)
      (fun θ hθ => ⟨hz, hθ⟩)
  have hderiv : ∀ᵐ θ ∂(volume.restrict (Set.Ioo 0 (Real.pi / 2))),
      ∀ z ∈ Set.Ioo (z₀ / 2) (2 * z₀),
        HasDerivAt (fun z' => G z' θ * φ θ) (Work.Spaces.pz G z θ * φ θ) z := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with θ hθ z hz
    have hzp : 0 < z := lt_trans (by linarith) hz.1
    have hmem : (z, θ) ∈ Work.FTS.EllipticEst.Q0 := ⟨hzp, hθ⟩
    have hd : DifferentiableAt ℝ (Function.uncurry G) (z, θ) :=
      (hG2.differentiableOn (by norm_num)).differentiableAt
        (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds hmem)
    exact (Work.Spaces.differentiableAt_curry_left hd).hasDerivAt.mul_const (φ θ)
  have hG_meas : ∀ᶠ z in 𝓝 z₀,
      AEStronglyMeasurable (fun θ => G z θ * φ θ) (volume.restrict (Set.Ioo 0 (Real.pi / 2))) := by
    filter_upwards [isOpen_Ioo.mem_nhds (show z₀ ∈ Set.Ioo (z₀ / 2) (2 * z₀) by
      constructor <;> linarith)] with z hz
    exact ((hsliceG z (lt_trans (by linarith) hz.1)).mul (hφ.mono hsub)).aestronglyMeasurable
      measurableSet_Ioo
  have hG_int : Integrable (fun θ => G z₀ θ * φ θ)
      (volume.restrict (Set.Ioo 0 (Real.pi / 2))) := by
    refine Integrable.mono' (integrable_const_Ioo (C₀ * M)) ?_ ?_
    · exact ((hsliceG z₀ hz₀).mul (hφ.mono hsub)).aestronglyMeasurable measurableSet_Ioo
    · filter_upwards [ae_restrict_mem measurableSet_Ioo] with θ hθ
      have hbθ : |G z₀ θ| ≤ C₀ := hbd0 z₀ θ hz₀ hθ.1 hθ.2
      have hb : |G z₀ θ * φ θ| ≤ C₀ * M := by
        rw [abs_mul]
        exact mul_le_mul hbθ (hφ' θ hθ) (abs_nonneg _) (le_trans (abs_nonneg _) hbθ)
      simpa [Real.norm_eq_abs] using hb
  have hG'_meas : AEStronglyMeasurable (fun θ => Work.Spaces.pz G z₀ θ * φ θ)
      (volume.restrict (Set.Ioo 0 (Real.pi / 2))) :=
    ((hslicePz z₀ hz₀).mul (hφ.mono hsub)).aestronglyMeasurable measurableSet_Ioo
  have hbound : ∀ᵐ θ ∂(volume.restrict (Set.Ioo 0 (Real.pi / 2))),
      ∀ z ∈ Set.Ioo (z₀ / 2) (2 * z₀), ‖Work.Spaces.pz G z θ‖ ≤ C₁ := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with θ hθ z hz
    rw [Real.norm_eq_abs]
    exact hbd1 z θ (lt_trans (by linarith) hz.1) hθ.1 hθ.2 hz.1.le hz.2.le
  have hmain := hasDerivAt_integral_Itheta_of_bound (G := G) (G' := Work.Spaces.pz G)
    (φ := φ) (z₀ := z₀) (K := C₁) hz₀ hC₁ hφ hG_meas hG_int hG'_meas hbound hderiv
  rw [← volume_restrict_Iθ_eq] at hmain
  exact hmain

/-- `∂_z G` is `C²` on the open quadrant as soon as `G` is `C³` there (one order is lost, as for
`Work.Spaces.uncurry_partial_c1`). -/
lemma contDiffOn_two_uncurry_pz {G : ℝ → ℝ → ℝ}
    (h : ContDiffOn ℝ 3 (Function.uncurry G) Work.FTS.EllipticEst.Q0) :
    ContDiffOn ℝ 2 (Function.uncurry (Work.Spaces.pz G)) Work.FTS.EllipticEst.Q0 := by
  have hV := Work.FTS.EllipticEst.isOpen_Q0
  have hdiff : ∀ p ∈ Work.FTS.EllipticEst.Q0,
      DifferentiableAt ℝ (Function.uncurry G) p := fun p hp =>
    (h.differentiableOn (n := (3 : WithTop ℕ∞)) (by norm_num)).differentiableAt
      (hV.mem_nhds hp)
  have hfd : ContDiffOn ℝ 2 (fun p : ℝ × ℝ => fderiv ℝ (Function.uncurry G) p)
      Work.FTS.EllipticEst.Q0 := by
    have h' := h.fderivWithin (m := (2 : WithTop ℕ∞)) hV.uniqueDiffOn (by norm_num)
    refine h'.congr ?_
    intro p hp
    rw [fderivWithin_of_isOpen hV hp]
  have hcomp : ContDiffOn ℝ 2 (fun p : ℝ × ℝ => (fderiv ℝ (Function.uncurry G) p) (1, 0))
      Work.FTS.EllipticEst.Q0 := by
    simpa using hfd.clm_apply contDiffOn_const
  refine hcomp.congr ?_
  intro p hp
  exact Work.Spaces.pz_eq_fderiv (hdiff p hp)

end

end Work.FTS_RegExport.RXT.SysAux
