/-
# `HardyBasic` — the `L¹`/`L²` bookkeeping for `HardyHyp` of the interior class

Auxiliary estimates for `Work.FTS.CoercivityFix.Coer1T.hardyHyp_of_coerAdm`: the pointwise
bound on the `L₁₂`-density in terms of the radial `ℋ⁴`-energy density `B4`, the
integrability of the angular slice `θ ↦ K(θ) f z θ / z`, of the comparison integrals
`(∫_θ f²)/z^{2j}` (`intB` of `HardyHyp`) and the `z`-estimates for the zero mode
`L12f f` near `0` and near `∞` used for `intA`, `bd0` and `bdTop`.
-/
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.Vocab
import Submission.Work.Coercivity.Defs
import Submission.Work.Coercivity.Basic
import Submission.Work.Coercivity.L12dens_sq_slice
import Submission.Work.Coercivity.integral_Itheta_K
import Submission.Work.Coercivity.HkIntegrand_le_succ
import Submission.Work.FTS.H2.L12densIntegrable
import Submission.Work.FTS.H2.L12ZeroQ
import Submission.Work.FM.Core
import Submission.Work.FM.Core2
import Submission.Work.FTS.CoercivityFix.Coer1T.Hardy.Ioi_tail_sq_integrable
import Submission.Work.FTS.CoercivityFix.Coer1T.Hardy.Ioc_prim_sq_integrable

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.CoercivityFix.Coer1T

theorem HkMem_four_of_five (α : ℝ) {f : ℝ → ℝ → ℝ} (hsm : Work.FTS.LocData.SmoothQuad f)
    (h : Work.Spaces.HkMem α 5 f) : Work.Spaces.HkMem α 4 f := by
  have hmono : ∀ z θ, Work.Spaces.HkIntegrand α 4 f z θ ≤ Work.Spaces.HkIntegrand α 5 f z θ :=
    fun z θ => Work.Coercivity.HkIntegrand_le_succ α 4 f z θ
  have hcont : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α 4 f p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
    Work.FTS.LocData.continuousOn_HkIntegrand_smoothQuad α 4 f hsm
  have haesmJoint : AEStronglyMeasurable
      (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α 4 f p.1 p.2)
      ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) :=
    Work.Spaces.aesm_of_continuousOn_Qd _ hcont
  constructor
  · intro z hz
    have hz' : (0 : ℝ) ≤ z := hz
    rcases eq_or_lt_of_le hz' with h0 | hpos
    · subst h0
      refine IntegrableOn.congr_fun integrableOn_zero (fun θ _ => ?_) measurableSet_Icc
      simp [Work.Spaces.HkIntegrand, Work.Spaces.w, Work.Spaces.Wt]
    · have haesm : AEStronglyMeasurable (fun θ => Work.Spaces.HkIntegrand α 4 f z θ)
          (volume.restrict Work.Spaces.Iθ) :=
        Work.Spaces.aesm_slice_of_continuousOn_Qd _ hcont hpos
      exact (h.1 z hz).mono' haesm (Filter.Eventually.of_forall fun θ => by
        rw [Real.norm_of_nonneg (Work.Spaces.HkIntegrand_nonneg α 4 f z θ)]
        exact hmono z θ)
  · have haesm : AEStronglyMeasurable
        (fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f z θ)
        (volume.restrict Work.Spaces.Iz) := haesmJoint.integral_prod_right'
    refine h.2.mono' haesm ?_
    filter_upwards [self_mem_ae_restrict measurableSet_Ici] with z hz
    rw [Real.norm_of_nonneg (integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α 4 f z θ)]
    exact integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun θ => Work.Spaces.HkIntegrand_nonneg α 4 f z θ)
      (h.1 z hz) (Filter.Eventually.of_forall fun θ => hmono z θ)

/-- The radial `ℋ⁴`-energy density `B α f s = ∫_θ HkIntegrand α 4 f s θ`. -/
def B4 (α : ℝ) (f : ℝ → ℝ → ℝ) (s : ℝ) : ℝ :=
  ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f s θ

theorem B4_nonneg (α : ℝ) (f : ℝ → ℝ → ℝ) (s : ℝ) : 0 ≤ B4 α f s :=
  integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α 4 f s θ

theorem B4_integrableOn (α : ℝ) (f : ℝ → ℝ → ℝ) (hmem : Work.Spaces.HkMem α 4 f) :
    MeasureTheory.IntegrableOn (B4 α f) (Set.Ioi (0 : ℝ)) :=
  hmem.2.mono_set Set.Ioi_subset_Ici_self

/-- Pointwise domination of the squared slice by the `ℋ⁴`-integrand on the open quadrant. -/
theorem slice_sq_le_HkIntegrand_div_w_sq (α : ℝ) {f : ℝ → ℝ → ℝ} {s θ : ℝ} (hs : 0 < s)
    (hθ0 : 0 < θ) (hθ1 : θ < π / 2) :
    (f s θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 4 f s θ / (Work.Spaces.w s) ^ 2 := by
  have hsin : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  set S : ℝ := (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) with hSdef
  have hSpos : 0 < S := by rw [hSdef]; exact Real.rpow_pos_of_pos hsin _
  have hSsq : S ^ 2 ≤ 1 := by
    have h2 : S ^ 2 = (Real.sin (2 * θ)) ^ Work.Spaces.eta := by
      rw [hSdef, ← Real.rpow_natCast, ← Real.rpow_mul hsin.le]; norm_num
    calc S ^ 2 = (Real.sin (2 * θ)) ^ Work.Spaces.eta := h2
      _ ≤ 1 := Real.rpow_le_one hsin.le (Real.sin_le_one _) (le_of_lt Work.Spaces.eta_pos)
  have hkey : (f s θ * (Work.Spaces.w s / S)) ^ 2 ≤ Work.Spaces.HkIntegrand α 4 f s θ := by
    simpa only [Work.Spaces.DzIter_zero] using
      Work.Spaces.sq_le_HkIntegrand_z α 4 f s θ 0 (by norm_num)
  have hwpos : 0 < Work.Spaces.w s := by rw [Work.Spaces.w]; positivity
  have hstep : (f s θ) ^ 2 * (Work.Spaces.w s) ^ 2 ≤ Work.Spaces.HkIntegrand α 4 f s θ := by
    calc (f s θ) ^ 2 * (Work.Spaces.w s) ^ 2
        ≤ (f s θ) ^ 2 * (Work.Spaces.w s) ^ 2 / S ^ 2 := by
          rw [le_div_iff₀ (pow_pos hSpos 2)]
          nlinarith [mul_nonneg (sq_nonneg (f s θ)) (sq_nonneg (Work.Spaces.w s)), hSsq]
      _ = (f s θ * (Work.Spaces.w s / S)) ^ 2 := by rw [mul_pow, div_pow, mul_div_assoc]
      _ ≤ _ := hkey
  exact (le_div_iff₀ (pow_pos hwpos 2)).mpr hstep

/-- The `L₁₂`-density obeys `|L₁₂dens K f s| ≤ √3 · (s/(1+s)²) · √(B4 α f s)` for `s > 0`. -/
theorem dens_abs_le (α : ℝ) {f : ℝ → ℝ → ℝ} (hsm : Work.FTS.LocData.SmoothQuad f)
    (hmem : Work.Spaces.HkMem α 4 f) {s : ℝ} (hs : 0 < s) :
    |Work.FM.L12dens Work.Spaces.K f s|
      ≤ Real.sqrt 3 * (s / (1 + s) ^ 2) * Real.sqrt (B4 α f s) := by
  have hsl : MeasureTheory.IntegrableOn (fun θ : ℝ => (f s θ) ^ 2) Work.Spaces.Iθ :=
    Work.FTS.H2.l12q_slice_sq_integrableOn α f hsm hmem hs
  have h1 : |Work.Elliptic.L12dens f s| ≤ Real.sqrt 3 * Real.sqrt
      (∫ θ in Work.Spaces.Iθ, (f s θ) ^ 2) / s :=
    Work.FTS.H2.l12q_l12dens_slice f hs hsl
  rw [Work.FTS.H2.L12dens_eq_FM_K f s] at h1
  have hwpos : 0 < Work.Spaces.w s := by rw [Work.Spaces.w]; positivity
  -- the a.e. pointwise domination `(f s θ)^2 ≤ HkIntegrand α 4 f s θ / (w s)^2`
  have hpt : (fun θ => (f s θ) ^ 2) ≤ᵐ[volume.restrict Work.Spaces.Iθ]
      (fun θ => Work.Spaces.HkIntegrand α 4 f s θ / (Work.Spaces.w s) ^ 2) := by
    have hcongr : volume.restrict Work.Spaces.Iθ
        = volume.restrict (Set.Ioo (0 : ℝ) (π / 2)) := by
      rw [Work.Spaces.Iθ]
      exact MeasureTheory.Measure.restrict_congr_set
        (MeasureTheory.Ioo_ae_eq_Icc (μ := volume) (a := (0 : ℝ)) (b := (π / 2))).symm
    rw [hcongr]
    exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo
      (fun θ hθ => slice_sq_le_HkIntegrand_div_w_sq α hs hθ.1 hθ.2)
  have hint : ∫ θ in Work.Spaces.Iθ, (f s θ) ^ 2
      ≤ B4 α f s / (Work.Spaces.w s) ^ 2 := by
    have hg : MeasureTheory.Integrable
        (fun θ => Work.Spaces.HkIntegrand α 4 f s θ / (Work.Spaces.w s) ^ 2)
        (volume.restrict Work.Spaces.Iθ) := (hmem.1 s hs.le).div_const _
    have h := MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun θ => sq_nonneg (f s θ)) hg hpt
    rwa [MeasureTheory.integral_div] at h
  have h4 : Real.sqrt (∫ θ in Work.Spaces.Iθ, (f s θ) ^ 2)
      ≤ Real.sqrt (B4 α f s) / Work.Spaces.w s := by
    calc Real.sqrt (∫ θ in Work.Spaces.Iθ, (f s θ) ^ 2)
        ≤ Real.sqrt (B4 α f s / (Work.Spaces.w s) ^ 2) := Real.sqrt_le_sqrt hint
      _ = Real.sqrt (B4 α f s) / Real.sqrt ((Work.Spaces.w s) ^ 2) :=
          Real.sqrt_div (B4_nonneg α f s) _
      _ = Real.sqrt (B4 α f s) / Work.Spaces.w s := by
          rw [Real.sqrt_sq_eq_abs, abs_of_pos hwpos]
  have h5 : Real.sqrt 3 * Real.sqrt (∫ θ in Work.Spaces.Iθ, (f s θ) ^ 2) / s
      ≤ Real.sqrt 3 * (s / (1 + s) ^ 2) * Real.sqrt (B4 α f s) := by
    calc Real.sqrt 3 * Real.sqrt (∫ θ in Work.Spaces.Iθ, (f s θ) ^ 2) / s
        ≤ Real.sqrt 3 * (Real.sqrt (B4 α f s) / Work.Spaces.w s) / s := by
          apply div_le_div_of_nonneg_right _ (le_of_lt hs)
          exact mul_le_mul_of_nonneg_left h4 (Real.sqrt_nonneg 3)
      _ = Real.sqrt 3 * (s / (1 + s) ^ 2) * Real.sqrt (B4 α f s) := by
          rw [Work.Spaces.w]
          field_simp
  exact le_trans h1 h5

/-- `∫_θ (f s θ)² ≤ B4 α f s / w(s)²` for `s > 0` (the slice `L²`-bound against the
`ℋ⁴`-integrand). -/
theorem phi_le_B4_div_w_sq (α : ℝ) {f : ℝ → ℝ → ℝ} (hmem : Work.Spaces.HkMem α 4 f)
    {s : ℝ} (hs : 0 < s) :
    ∫ θ in Work.Spaces.Iθ, (f s θ) ^ 2 ≤ B4 α f s / (Work.Spaces.w s) ^ 2 := by
  have hwpos : 0 < Work.Spaces.w s := by rw [Work.Spaces.w]; positivity
  have hpt : (fun θ => (f s θ) ^ 2) ≤ᵐ[volume.restrict Work.Spaces.Iθ]
      (fun θ => Work.Spaces.HkIntegrand α 4 f s θ / (Work.Spaces.w s) ^ 2) := by
    have hcongr : volume.restrict Work.Spaces.Iθ
        = volume.restrict (Set.Ioo (0 : ℝ) (π / 2)) := by
      rw [Work.Spaces.Iθ]
      exact MeasureTheory.Measure.restrict_congr_set
        (MeasureTheory.Ioo_ae_eq_Icc (μ := volume) (a := (0 : ℝ)) (b := (π / 2))).symm
    rw [hcongr]
    exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo
      (fun θ hθ => slice_sq_le_HkIntegrand_div_w_sq α hs hθ.1 hθ.2)
  have hg : MeasureTheory.Integrable
      (fun θ => Work.Spaces.HkIntegrand α 4 f s θ / (Work.Spaces.w s) ^ 2)
      (volume.restrict Work.Spaces.Iθ) := (hmem.1 s hs.le).div_const _
  have h := MeasureTheory.integral_mono_of_nonneg
    (Filter.Eventually.of_forall fun θ => sq_nonneg (f s θ)) hg hpt
  rwa [MeasureTheory.integral_div] at h

/-- The angular slice `θ ↦ K(θ) f z θ / z` is integrable on `Iθ` for `z > 0`. -/
theorem Kslice_integrableOn (α : ℝ) {f : ℝ → ℝ → ℝ} (hsm : Work.FTS.LocData.SmoothQuad f)
    (hmem : Work.Spaces.HkMem α 4 f) {z : ℝ} (hz : 0 < z) :
    MeasureTheory.IntegrableOn (fun θ => Work.Spaces.K θ * f z θ / z) Work.Spaces.Iθ := by
  have hsl : MeasureTheory.IntegrableOn (fun θ : ℝ => (f z θ) ^ 2) Work.Spaces.Iθ :=
    Work.FTS.H2.l12q_slice_sq_integrableOn α f hsm hmem hz
  have hcont : ContinuousOn (Function.uncurry f) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
    have h := hsm
    rw [Work.FTS.LocData.SmoothQuad] at h
    exact h.continuousOn.mono (fun p hp => by
      simp only [Set.mem_prod, Set.mem_Ioi, Set.mem_Ioo] at hp ⊢
      exact ⟨by linarith [hp.1], hp.2⟩)
  have haesm : AEStronglyMeasurable (fun θ => f z θ) (volume.restrict Work.Spaces.Iθ) :=
    Work.Spaces.aesm_slice_of_continuousOn_Qd (Function.uncurry f) hcont hz
  have hK : Continuous (fun θ : ℝ => Work.Spaces.K θ) := Work.Coercivity.K_facts_continuous
  have hmaj : MeasureTheory.IntegrableOn (fun θ : ℝ => (3 / z) * (1 + (f z θ) ^ 2))
      Work.Spaces.Iθ := by
    have h1 : MeasureTheory.IntegrableOn (fun _ : ℝ => (1 : ℝ)) Work.Spaces.Iθ :=
      MeasureTheory.integrableOn_const (by
        rw [Work.Spaces.Iθ, Real.volume_Icc]
        exact ENNReal.ofReal_ne_top)
    exact ((h1.add hsl).const_mul (3 / z))
  have haesm2 : AEStronglyMeasurable
      (fun θ => Work.Spaces.K θ * f z θ / z) (volume.restrict Work.Spaces.Iθ) := by
    have h2 := (hK.aestronglyMeasurable.mul haesm).mul_const (1 / z)
    simpa [div_eq_mul_inv, mul_assoc] using h2
  refine hmaj.mono' haesm2 ?_
  filter_upwards [self_mem_ae_restrict measurableSet_Icc] with θ hθ
  have hKnn : 0 ≤ Work.Spaces.K θ := Work.Coercivity.K_facts_nonneg θ hθ
  have hKle : Work.Spaces.K θ ≤ 3 := Work.Coercivity.K_facts_le_three θ hθ
  rw [Real.norm_eq_abs, abs_div, abs_mul, abs_of_nonneg hKnn, abs_of_pos hz]
  have habs : |f z θ| ≤ 1 + (f z θ) ^ 2 := by
    nlinarith [sq_nonneg (|f z θ| - 1), sq_abs (f z θ), abs_nonneg (f z θ)]
  calc Work.Spaces.K θ * |f z θ| / z ≤ 3 * |f z θ| / z := by
        apply div_le_div_of_nonneg_right _ (le_of_lt hz)
        exact mul_le_mul_of_nonneg_right hKle (abs_nonneg _)
    _ ≤ (3 / z) * (1 + (f z θ) ^ 2) := by
        rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right hz]
        nlinarith [habs]
    _ = _ := rfl

/-- The pointwise bound behind `intB`: `(∫_θ f z θ²)/z^{2j} ≤ B4 α f z` for `z > 0`, `j ≤ 2`. -/
theorem phi_div_rpow_le_B4 (α : ℝ) {f : ℝ → ℝ → ℝ} (hmem : Work.Spaces.HkMem α 4 f)
    {z : ℝ} (hz : 0 < z) (j : ℕ) (hj : j ≤ 2) :
    (∫ θ in Work.Spaces.Iθ, (f z θ) ^ 2) / z ^ (2 * (j : ℝ)) ≤ B4 α f z := by
  have hwpos : 0 < Work.Spaces.w z := by rw [Work.Spaces.w]; positivity
  have h1 : ∫ θ in Work.Spaces.Iθ, (f z θ) ^ 2 ≤ B4 α f z / (Work.Spaces.w z) ^ 2 :=
    phi_le_B4_div_w_sq α hmem hz
  have hB : 0 ≤ B4 α f z := B4_nonneg α f z
  -- `w(z)^2 * z^{2j} ≥ 1`
  have key : 1 ≤ Work.Spaces.w z ^ 2 * z ^ (2 * (j : ℝ)) := by
    rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2) with h | h | h
    · subst h
      rw [show (2 * ((0 : ℕ) : ℝ)) = 0 by norm_num, Real.rpow_zero, mul_one]
      have hw1 : 1 ≤ Work.Spaces.w z := by
        rw [Work.Spaces.w, one_le_div (by positivity)]
        nlinarith
      nlinarith
    · subst h
      rw [show (2 * ((1 : ℕ) : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      rw [Work.Spaces.w, div_pow]
      field_simp
      nlinarith [sq_nonneg z, sq_nonneg (1 + z), le_of_lt hz]
    · subst h
      rw [show (2 * ((2 : ℕ) : ℝ)) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      rw [Work.Spaces.w, div_pow]
      field_simp
      have h1z : (1 : ℝ) ≤ 1 + z := by linarith
      have h4 : (1 : ℝ) ^ 4 ≤ (1 + z) ^ 4 := pow_le_pow_left₀ (by norm_num) h1z 4
      norm_num at h4
      linarith
  have hden_pos : 0 < Work.Spaces.w z ^ 2 * z ^ (2 * (j : ℝ)) :=
    mul_pos (pow_pos hwpos 2) (Real.rpow_pos_of_pos hz _)
  have h2 : B4 α f z / (Work.Spaces.w z) ^ 2 / z ^ (2 * (j : ℝ)) ≤ B4 α f z := by
    rw [div_div, div_le_iff₀ hden_pos]
    nlinarith
  calc (∫ θ in Work.Spaces.Iθ, (f z θ) ^ 2) / z ^ (2 * (j : ℝ))
      ≤ B4 α f z / (Work.Spaces.w z) ^ 2 / z ^ (2 * (j : ℝ)) :=
        div_le_div_of_nonneg_right h1 (le_of_lt (Real.rpow_pos_of_pos hz _))
    _ ≤ B4 α f z := h2

/-- `intB` of `HardyHyp`: `z ↦ (∫_θ f z θ²)/z^{2j}` is integrable on `(0,∞)` for `j ≤ 2`. -/
theorem intB_integrableOn (α : ℝ) {f : ℝ → ℝ → ℝ} (hsm : Work.FTS.LocData.SmoothQuad f)
    (hmem : Work.Spaces.HkMem α 4 f) (j : ℕ) (hj : j ≤ 2) :
    MeasureTheory.IntegrableOn
      (fun z => (∫ θ in Work.Spaces.Iθ, (f z θ) ^ 2) / z ^ (2 * (j : ℝ))) (Set.Ioi 0) := by
  have hnum : AEMeasurable (fun z : ℝ => ∫ θ in Work.Spaces.Iθ, (f z θ) ^ 2)
      (volume.restrict (Set.Ioi 0)) := (Work.FTS.H2.l12q_phi_aesm f hsm).aemeasurable
  have hden : AEMeasurable (fun z : ℝ => z ^ (2 * (j : ℝ)))
      (volume.restrict (Set.Ioi 0)) := by
    have hEq : (fun z : ℝ => z ^ (2 * (j : ℝ))) = fun z => z ^ (2 * j) := by
      funext z
      rw [show (2 * (j : ℝ)) = ((2 * j : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
    rw [hEq]
    exact ((continuous_pow (2 * j)).measurable).aemeasurable
  have haesm : AEStronglyMeasurable
      (fun z => (∫ θ in Work.Spaces.Iθ, (f z θ) ^ 2) / z ^ (2 * (j : ℝ)))
      (volume.restrict (Set.Ioi 0)) := (hnum.div hden).aestronglyMeasurable
  refine (B4_integrableOn α f hmem).mono' haesm ?_
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with z hz
  rw [Real.norm_of_nonneg (div_nonneg (integral_nonneg fun θ => sq_nonneg _)
    (le_of_lt (Real.rpow_pos_of_pos hz _)))]
  exact phi_div_rpow_le_B4 α hmem hz j hj

theorem B4_aesm (α : ℝ) {f : ℝ → ℝ → ℝ} (hsm : Work.FTS.LocData.SmoothQuad f) :
    AEStronglyMeasurable (B4 α f) (volume.restrict Work.Spaces.Iz) := by
  have hcont : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α 4 f p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
    Work.FTS.LocData.continuousOn_HkIntegrand_smoothQuad α 4 f hsm
  have h := (Work.Spaces.aesm_of_continuousOn_Qd _ hcont).integral_prod_right'
  exact h

theorem B4_sqrt_aesm (α : ℝ) {f : ℝ → ℝ → ℝ} (hsm : Work.FTS.LocData.SmoothQuad f) :
    AEStronglyMeasurable (fun s => Real.sqrt (B4 α f s)) (volume.restrict Work.Spaces.Iz) :=
  Real.continuous_sqrt.comp_aestronglyMeasurable (B4_aesm α hsm)

theorem B4_zero (α : ℝ) (f : ℝ → ℝ → ℝ) : B4 α f 0 = 0 := by
  rw [B4]
  simp [Work.Spaces.HkIntegrand, Work.Spaces.w, Work.Spaces.Wt]

/-- The tail of the `L₁₂`-density is minus the primitive: for `z > 0`,
`L12f f z = -∫_0^z L12dens K f`. -/
theorem L12f_eq_neg_prim {f : ℝ → ℝ → ℝ}
    (hint : MeasureTheory.IntegrableOn (fun s => Work.FM.L12dens Work.Spaces.K f s)
      (Set.Ioi 0))
    (hl12 : Work.Coercivity.L12f f 0 = 0) {z : ℝ} (hz : 0 < z) :
    Work.Coercivity.L12f f z
      = -∫ s in (0 : ℝ)..z, Work.FM.L12dens Work.Spaces.K f s := by
  set G : ℝ → ℝ := fun s => Work.FM.L12dens Work.Spaces.K f s with hGdef
  have h1 : MeasureTheory.IntegrableOn G (Set.Ioc (0 : ℝ) z) :=
    hint.mono_set fun t ht => ht.1
  have h2 : MeasureTheory.IntegrableOn G (Set.Ioi z) :=
    hint.mono_set (Set.Ioi_subset_Ioi hz.le)
  have hdisj : Disjoint (Set.Ioc (0 : ℝ) z) (Set.Ioi z) := by
    rw [Set.disjoint_left]
    intro t ht1 ht2
    exact absurd ht2 (not_lt.mpr ht1.2)
  have hU : Set.Ioc (0 : ℝ) z ∪ Set.Ioi z = Set.Ioi (0 : ℝ) := by
    ext t
    simp only [Set.mem_union, Set.mem_Ioc, Set.mem_Ioi]
    constructor
    · rintro (h | h)
      · exact h.1
      · exact lt_trans hz h
    · intro h
      rcases lt_trichotomy t z with h' | h' | h'
      · exact Or.inl ⟨h, h'.le⟩
      · exact Or.inl ⟨h, le_of_eq h'⟩
      · exact Or.inr h'
  have hsum := MeasureTheory.setIntegral_union hdisj (measurableSet_Ioi) h1 h2
  rw [hU] at hsum
  have hl12' : ∫ s in Set.Ioi (0 : ℝ), G s = 0 := by
    simpa [G, Work.Coercivity.L12f, Work.FM.L12] using hl12
  have hkey : ∫ s in Set.Ioi z, G s = -∫ s in Set.Ioc (0 : ℝ) z, G s := by linarith
  rw [Work.Coercivity.L12f, Work.FM.L12, hkey, intervalIntegral.integral_of_le hz.le]

/-- Cauchy–Schwarz with the constant function `1` on `(0,z]`:
`(∫_{(0,z]} Ψ)² ≤ z · ∫_{(0,z]} Ψ²`. -/
theorem cs_one {z : ℝ} (hz : 0 < z) {Ψ : ℝ → ℝ}
    (hΨ : MemLp Ψ 2 (volume.restrict (Set.Ioc 0 z))) :
    (∫ s in Set.Ioc 0 z, Ψ s) ^ 2 ≤ z * ∫ s in Set.Ioc 0 z, (Ψ s) ^ 2 := by
  have h1 : MemLp (fun _ : ℝ => (1 : ℝ)) 2 (volume.restrict (Set.Ioc 0 z)) := memLp_const 1
  have hcs := Work.Spaces.cs_integral h1 hΨ
  have hone : (∫ s in Set.Ioc 0 z, (1 : ℝ) ^ 2) = z := by
    rw [MeasureTheory.setIntegral_const]
    simp only [smul_eq_mul, one_pow, mul_one]
    rw [MeasureTheory.Measure.real, Real.volume_Ioc, ENNReal.toReal_ofReal (by linarith)]
    ring
  have hmul : (∫ s in Set.Ioc 0 z, (1 : ℝ) * Ψ s) = ∫ s in Set.Ioc 0 z, Ψ s := by
    simp
  rw [hmul, hone] at hcs
  linarith

theorem B4_sqrt_aesm_mono (α : ℝ) {f : ℝ → ℝ → ℝ} (hsm : Work.FTS.LocData.SmoothQuad f)
    {u : Set ℝ} (hu : u ⊆ Work.Spaces.Iz) :
    AEStronglyMeasurable (fun s => Real.sqrt (B4 α f s)) (volume.restrict u) :=
  (B4_sqrt_aesm α hsm).mono_measure
    (MeasureTheory.Measure.restrict_mono_set volume hu)

/-- `|L12f f z| ≤ √3 ∫_{(0,z]} s √(B4 α f s)` for `0 < z ≤ 1`. -/
theorem L12f_abs_le_prim (α : ℝ) {f : ℝ → ℝ → ℝ} (hsm : Work.FTS.LocData.SmoothQuad f)
    (hmem : Work.Spaces.HkMem α 4 f)
    (hint : MeasureTheory.IntegrableOn (fun s => Work.FM.L12dens Work.Spaces.K f s) (Set.Ioi 0))
    (hl12 : Work.Coercivity.L12f f 0 = 0) {z : ℝ} (hz : 0 < z) (hz1 : z ≤ 1) :
    |Work.Coercivity.L12f f z|
      ≤ Real.sqrt 3 * ∫ s in Set.Ioc 0 z, s * Real.sqrt (B4 α f s) := by
  set G : ℝ → ℝ := fun s => Work.FM.L12dens Work.Spaces.K f s with hGdef
  have hrepr : Work.Coercivity.L12f f z = -(∫ s in Set.Ioc 0 z, G s) := by
    rw [L12f_eq_neg_prim hint hl12 hz, intervalIntegral.integral_of_le hz.le]
  rw [hrepr, abs_neg]
  -- the majorant `maj s = √3 * (s * √(B4 s))`
  have hu : Set.Ioc (0 : ℝ) z ⊆ Work.Spaces.Iz := fun t ht => le_of_lt ht.1
  have hmaj_aesm : AEStronglyMeasurable
      (fun s : ℝ => Real.sqrt 3 * (s * Real.sqrt (B4 α f s)))
      (volume.restrict (Set.Ioc 0 z)) :=
    ((continuous_id.aestronglyMeasurable.mul (B4_sqrt_aesm_mono α hsm hu)).const_mul
      (Real.sqrt 3))
  -- the majorant is integrable
  have hBint : MeasureTheory.IntegrableOn (B4 α f) (Set.Ioc 0 z) :=
    (B4_integrableOn α f hmem).mono_set (fun t ht => ht.1)
  have hconst : MeasureTheory.IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Set.Ioc 0 z) :=
    MeasureTheory.integrableOn_const (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
  have hmaj_bound : ∀ s ∈ Set.Ioc 0 z, Real.sqrt 3 * (s * Real.sqrt (B4 α f s))
      ≤ (Real.sqrt 3 / 2) * (1 + B4 α f s) := by
    intro s hs
    have hBs : 0 ≤ B4 α f s := B4_nonneg α f s
    have hle1 : s ≤ 1 := le_trans hs.2 hz1
    have hs0 : 0 < s := hs.1
    have hsqrt_le : Real.sqrt (B4 α f s) ≤ (1 + B4 α f s) / 2 := by
      nlinarith [Real.sq_sqrt hBs, sq_nonneg (Real.sqrt (B4 α f s) - 1)]
    have hsle : s * Real.sqrt (B4 α f s) ≤ Real.sqrt (B4 α f s) := by
      nlinarith [hle1, hs0, Real.sqrt_nonneg (B4 α f s)]
    nlinarith [hsqrt_le, hsle, Real.sqrt_nonneg 3]
  have hmaj_int : MeasureTheory.IntegrableOn
      (fun s : ℝ => Real.sqrt 3 * (s * Real.sqrt (B4 α f s))) (Set.Ioc 0 z) :=
    ((hconst.add hBint).const_mul (Real.sqrt 3 / 2)).mono' hmaj_aesm
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioc (fun x hx => by
        rw [Real.norm_of_nonneg (by
          have hx0 : 0 < x := hx.1
          positivity)]
        exact hmaj_bound x hx))
  -- the pointwise domination of `G`
  have hG_bd : ∀ᵐ s ∂(volume.restrict (Set.Ioc 0 z)), ‖G s‖
      ≤ Real.sqrt 3 * (s * Real.sqrt (B4 α f s)) := by
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioc (fun s hs => ?_)
    have hs0 : 0 < s := hs.1
    have h1 := dens_abs_le α hsm hmem hs0
    have h2 : s / (1 + s) ^ 2 ≤ s := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith [sq_nonneg s, le_of_lt hs0]
    rw [Real.norm_eq_abs]
    calc |G s| ≤ Real.sqrt 3 * (s / (1 + s) ^ 2) * Real.sqrt (B4 α f s) := h1
      _ ≤ Real.sqrt 3 * s * Real.sqrt (B4 α f s) := by
          apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
          exact mul_le_mul_of_nonneg_left h2 (Real.sqrt_nonneg 3)
      _ = Real.sqrt 3 * (s * Real.sqrt (B4 α f s)) := by ring
  have hbd := MeasureTheory.norm_integral_le_of_norm_le hmaj_int hG_bd
  rw [Real.norm_eq_abs] at hbd
  calc |∫ s in Set.Ioc 0 z, G s|
      ≤ ∫ s in Set.Ioc 0 z, Real.sqrt 3 * (s * Real.sqrt (B4 α f s)) := hbd
    _ = Real.sqrt 3 * ∫ s in Set.Ioc 0 z, s * Real.sqrt (B4 α f s) := by
        rw [MeasureTheory.integral_const_mul]

/-- Near the origin the tail of the density grows at most like `z^{3/2}`:
`(L12f f z)² ≤ 3 z³ ∫_{(0,z]} B4 α f` for `0 < z ≤ 1`. -/
theorem L12f_sq_le_small (α : ℝ) {f : ℝ → ℝ → ℝ} (hsm : Work.FTS.LocData.SmoothQuad f)
    (hmem : Work.Spaces.HkMem α 4 f)
    (hint : MeasureTheory.IntegrableOn (fun s => Work.FM.L12dens Work.Spaces.K f s) (Set.Ioi 0))
    (hl12 : Work.Coercivity.L12f f 0 = 0) {z : ℝ} (hz : 0 < z) (hz1 : z ≤ 1) :
    (Work.Coercivity.L12f f z) ^ 2 ≤ 3 * z ^ 3 * ∫ s in Set.Ioc 0 z, B4 α f s := by
  set Ψ : ℝ → ℝ := fun s => s * Real.sqrt (B4 α f s) with hΨdef
  have hu : Set.Ioc (0 : ℝ) z ⊆ Work.Spaces.Iz := fun t ht => le_of_lt ht.1
  have hBint : MeasureTheory.IntegrableOn (B4 α f) (Set.Ioc 0 z) :=
    (B4_integrableOn α f hmem).mono_set (fun t ht => ht.1)
  have hΨ_aesm : AEStronglyMeasurable Ψ (volume.restrict (Set.Ioc 0 z)) :=
    continuous_id.aestronglyMeasurable.mul (B4_sqrt_aesm_mono α hsm hu)
  have hΨ2_eq : ∀ s, (Ψ s) ^ 2 = s ^ 2 * B4 α f s := by
    intro s
    rw [hΨdef]
    simp only
    rw [mul_pow, Real.sq_sqrt (B4_nonneg α f s)]
  have hΨ2_int : MeasureTheory.IntegrableOn (fun s => (Ψ s) ^ 2) (Set.Ioc 0 z) := by
    refine (hBint.const_mul (z ^ 2)).mono' (hΨ_aesm.pow 2) ?_
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioc (fun s hs => ?_)
    rw [Real.norm_of_nonneg (sq_nonneg _), hΨ2_eq s]
    have hs2 : s ^ 2 ≤ z ^ 2 := by nlinarith [hs.1, hs.2, le_of_lt hz]
    exact mul_le_mul_of_nonneg_right hs2 (B4_nonneg α f s)
  have hΨmem : MemLp Ψ 2 (volume.restrict (Set.Ioc 0 z)) :=
    (MeasureTheory.memLp_two_iff_integrable_sq hΨ_aesm).mpr hΨ2_int
  have hcs := cs_one hz hΨmem
  have hΨ2_le : ∫ s in Set.Ioc 0 z, (Ψ s) ^ 2 ≤ z ^ 2 * ∫ s in Set.Ioc 0 z, B4 α f s := by
    rw [← MeasureTheory.integral_const_mul]
    refine MeasureTheory.integral_mono_of_nonneg (Filter.Eventually.of_forall fun s => sq_nonneg _)
      (hBint.const_mul (z ^ 2)) ?_
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioc (fun s hs => ?_)
    show Ψ s ^ 2 ≤ z ^ 2 * B4 α f s
    rw [hΨ2_eq s]
    have hs2 : s ^ 2 ≤ z ^ 2 := by nlinarith [hs.1, hs.2, le_of_lt hz]
    exact mul_le_mul_of_nonneg_right hs2 (B4_nonneg α f s)
  have hAnn : 0 ≤ ∫ s in Set.Ioc 0 z, Ψ s :=
    MeasureTheory.setIntegral_nonneg measurableSet_Ioc
      (fun s hs => mul_nonneg (le_of_lt hs.1) (Real.sqrt_nonneg _))
  have h1 := L12f_abs_le_prim α hsm hmem hint hl12 hz hz1
  have habs := abs_le.mp h1
  have key : (Work.Coercivity.L12f f z) ^ 2 ≤ 3 * (∫ s in Set.Ioc 0 z, Ψ s) ^ 2 := by
    have h3A : 0 ≤ Real.sqrt 3 * ∫ s in Set.Ioc 0 z, Ψ s :=
      mul_nonneg (Real.sqrt_nonneg 3) hAnn
    have h1' : (Work.Coercivity.L12f f z) ^ 2
        ≤ (Real.sqrt 3 * ∫ s in Set.Ioc 0 z, Ψ s) ^ 2 :=
      sq_le_sq' (by linarith [habs.1]) habs.2
    rw [mul_pow, Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)] at h1'
    linarith
  calc (Work.Coercivity.L12f f z) ^ 2 ≤ 3 * (∫ s in Set.Ioc 0 z, Ψ s) ^ 2 := key
    _ ≤ 3 * (z * ∫ s in Set.Ioc 0 z, (Ψ s) ^ 2) := by linarith [hcs]
    _ ≤ 3 * (z * (z ^ 2 * ∫ s in Set.Ioc 0 z, B4 α f s)) := by
        have hz0 : (0 : ℝ) ≤ z := le_of_lt hz
        have := mul_le_mul_of_nonneg_left hΨ2_le hz0
        linarith
    _ = 3 * z ^ 3 * ∫ s in Set.Ioc 0 z, B4 α f s := by ring

/-- `∫_{s>z} s⁻² = 1/z`. -/
theorem integral_Ioi_inv_sq {z : ℝ} (hz : 0 < z) :
    ∫ s in Set.Ioi z, (s⁻¹) ^ 2 = 1 / z := by
  have h := integral_Ioi_rpow_of_lt (a := (-2 : ℝ)) (c := z) (by norm_num) hz
  have h1 : ∫ s in Set.Ioi z, s ^ (-2 : ℝ) = 1 / z := by
    rw [h, show (-2 : ℝ) + 1 = -1 by norm_num, Real.rpow_neg_one]
    field_simp
  rw [← h1]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun s hs => ?_)
  have hs0 : 0 < s := lt_trans hz hs
  rw [show (-2 : ℝ) = -((2 : ℕ) : ℝ) by norm_num, Real.rpow_neg hs0.le, Real.rpow_natCast,
    inv_pow]

theorem inv_sq_integrableOn {z : ℝ} (hz : 0 < z) :
    MeasureTheory.IntegrableOn (fun s : ℝ => (s⁻¹) ^ 2) (Set.Ioi z) := by
  refine (integrableOn_Ioi_rpow_of_lt (a := (-2 : ℝ)) (c := z) (by norm_num) hz).congr_fun
    (fun s hs => ?_) measurableSet_Ioi
  have hs0 : 0 < s := lt_trans hz hs
  show s ^ (-2 : ℝ) = (s⁻¹) ^ 2
  rw [show (-2 : ℝ) = -((2 : ℕ) : ℝ) by norm_num, Real.rpow_neg hs0.le, Real.rpow_natCast,
    inv_pow]

theorem inv_memLp_Ioi {z : ℝ} (hz : 0 < z) :
    MemLp (fun s : ℝ => s⁻¹) 2 (volume.restrict (Set.Ioi z)) :=
  (MeasureTheory.memLp_two_iff_integrable_sq measurable_inv.aestronglyMeasurable).mpr
    (inv_sq_integrableOn hz)

theorem sqrt_B4_memLp_Ioi (α : ℝ) {f : ℝ → ℝ → ℝ} (hsm : Work.FTS.LocData.SmoothQuad f)
    (hmem : Work.Spaces.HkMem α 4 f) {z : ℝ} (hz : 0 < z) :
    MemLp (fun s : ℝ => Real.sqrt (B4 α f s)) 2 (volume.restrict (Set.Ioi z)) := by
  refine (MeasureTheory.memLp_two_iff_integrable_sq
    (B4_sqrt_aesm_mono α hsm (fun t ht => le_of_lt (lt_trans hz ht)))).mpr ?_
  refine ((B4_integrableOn α f hmem).mono_set
    (fun t ht => lt_trans hz ht)).congr_fun (fun s _ => ?_) measurableSet_Ioi
  exact (Real.sq_sqrt (B4_nonneg α f s)).symm

/-- The majorant `s ↦ s⁻¹ √(B4 α f s)` is integrable on `(z,∞)` for `z > 0`. -/
theorem inv_mul_sqrt_B4_integrableOn (α : ℝ) {f : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.LocData.SmoothQuad f) (hmem : Work.Spaces.HkMem α 4 f)
    {z : ℝ} (hz : 0 < z) :
    MeasureTheory.IntegrableOn (fun s => s⁻¹ * Real.sqrt (B4 α f s)) (Set.Ioi z) :=
  (inv_memLp_Ioi hz).integrable_mul (sqrt_B4_memLp_Ioi α hsm hmem hz)

/-- `|L12f f z| ≤ √3 · √(1/z) · √(∫_{s>z} B4 α f s)` for `z ≥ 1`. -/
theorem L12f_abs_le_large (α : ℝ) {f : ℝ → ℝ → ℝ} (hsm : Work.FTS.LocData.SmoothQuad f)
    (hmem : Work.Spaces.HkMem α 4 f) {z : ℝ} (hz1 : 1 ≤ z) :
    |Work.Coercivity.L12f f z|
      ≤ Real.sqrt 3 * (Real.sqrt (1 / z) * Real.sqrt (∫ s in Set.Ioi z, B4 α f s)) := by
  have hz : 0 < z := lt_of_lt_of_le one_pos hz1
  set G : ℝ → ℝ := fun s => Work.FM.L12dens Work.Spaces.K f s with hGdef
  have hmaj_int : MeasureTheory.IntegrableOn
      (fun s => s⁻¹ * Real.sqrt (B4 α f s)) (Set.Ioi z) :=
    inv_mul_sqrt_B4_integrableOn α hsm hmem hz
  have h1 : |Work.Coercivity.L12f f z| ≤ ∫ s in Set.Ioi z, |G s| := by
    have h := MeasureTheory.norm_integral_le_integral_norm (f := G)
      (μ := volume.restrict (Set.Ioi z))
    rw [Work.Coercivity.L12f, Work.FM.L12]
    simpa [G, Real.norm_eq_abs] using h
  have h2 : ∫ s in Set.Ioi z, |G s|
      ≤ Real.sqrt 3 * ∫ s in Set.Ioi z, s⁻¹ * Real.sqrt (B4 α f s) := by
    rw [← MeasureTheory.integral_const_mul]
    refine MeasureTheory.integral_mono_of_nonneg (Filter.Eventually.of_forall fun s => abs_nonneg _)
      (hmaj_int.const_mul (Real.sqrt 3)) ?_
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi (fun s hs => ?_)
    have hs0 : 0 < s := lt_trans hz hs
    have hb := dens_abs_le α hsm hmem hs0
    have hle : s / (1 + s) ^ 2 ≤ s⁻¹ := by
      rw [div_le_iff₀ (by positivity)]
      field_simp
      nlinarith [le_of_lt hs0]
    calc |G s| ≤ Real.sqrt 3 * (s / (1 + s) ^ 2) * Real.sqrt (B4 α f s) := hb
      _ ≤ Real.sqrt 3 * s⁻¹ * Real.sqrt (B4 α f s) := by
          apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
          exact mul_le_mul_of_nonneg_left hle (Real.sqrt_nonneg 3)
      _ = Real.sqrt 3 * (s⁻¹ * Real.sqrt (B4 α f s)) := by ring
  have hcs := Work.Spaces.cs_integral (u := fun s : ℝ => s⁻¹)
    (v := fun s : ℝ => Real.sqrt (B4 α f s)) (s := Set.Ioi z)
    (inv_memLp_Ioi hz) (sqrt_B4_memLp_Ioi α hsm hmem hz)
  have hv2 : ∫ s in Set.Ioi z, (Real.sqrt (B4 α f s)) ^ 2 = ∫ s in Set.Ioi z, B4 α f s := by
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun s _ => ?_)
    exact Real.sq_sqrt (B4_nonneg α f s)
  rw [integral_Ioi_inv_sq hz, hv2] at hcs
  have hC : 0 ≤ (1 / z) * ∫ s in Set.Ioi z, B4 α f s := by
    have : (0 : ℝ) ≤ ∫ s in Set.Ioi z, B4 α f s :=
      MeasureTheory.setIntegral_nonneg measurableSet_Ioi (fun s _ => B4_nonneg α f s)
    positivity
  have hsqrt : ∫ s in Set.Ioi z, s⁻¹ * Real.sqrt (B4 α f s)
      ≤ Real.sqrt ((1 / z) * ∫ s in Set.Ioi z, B4 α f s) := by
    have hsq : (∫ s in Set.Ioi z, s⁻¹ * Real.sqrt (B4 α f s)) ^ 2
        ≤ (Real.sqrt ((1 / z) * ∫ s in Set.Ioi z, B4 α f s)) ^ 2 := by
      rw [Real.sq_sqrt hC]
      exact hcs
    exact le_trans (le_abs_self _) (abs_le_of_sq_le_sq hsq (Real.sqrt_nonneg _))
  have hfinal : Real.sqrt 3 * (∫ s in Set.Ioi z, s⁻¹ * Real.sqrt (B4 α f s))
      ≤ Real.sqrt 3 * (Real.sqrt (1 / z) * Real.sqrt (∫ s in Set.Ioi z, B4 α f s)) := by
    refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg 3)
    refine le_trans hsqrt (le_of_eq ?_)
    rw [Real.sqrt_mul (by positivity)]
  linarith [h1, h2, hfinal]

/-- `∫_{(0,z]} B4 ≤ ∫_{(0,∞)} B4`. -/
theorem Ioc_B4_le (α : ℝ) {f : ℝ → ℝ → ℝ} (hmem : Work.Spaces.HkMem α 4 f)
    {z : ℝ} (hz : 0 < z) :
    ∫ s in Set.Ioc 0 z, B4 α f s ≤ ∫ s in Set.Ioi 0, B4 α f s := by
  have h1 : MeasureTheory.IntegrableOn (B4 α f) (Set.Ioc (0 : ℝ) z) :=
    (B4_integrableOn α f hmem).mono_set (fun t ht => ht.1)
  have h2 : MeasureTheory.IntegrableOn (B4 α f) (Set.Ioi z) :=
    (B4_integrableOn α f hmem).mono_set (Set.Ioi_subset_Ioi hz.le)
  have hdisj : Disjoint (Set.Ioc (0 : ℝ) z) (Set.Ioi z) := by
    rw [Set.disjoint_left]
    intro t ht1 ht2
    exact absurd ht2 (not_lt.mpr ht1.2)
  have hU : Set.Ioc (0 : ℝ) z ∪ Set.Ioi z = Set.Ioi (0 : ℝ) := by
    ext t
    simp only [Set.mem_union, Set.mem_Ioc, Set.mem_Ioi]
    constructor
    · rintro (h | h)
      · exact h.1
      · exact lt_trans hz h
    · intro h
      rcases lt_trichotomy t z with h' | h' | h'
      · exact Or.inl ⟨h, h'.le⟩
      · exact Or.inl ⟨h, le_of_eq h'⟩
      · exact Or.inr h'
  have hsum := MeasureTheory.setIntegral_union hdisj measurableSet_Ioi h1 h2
  rw [hU] at hsum
  have h3 : 0 ≤ ∫ s in Set.Ioi z, B4 α f s :=
    MeasureTheory.setIntegral_nonneg measurableSet_Ioi (fun s _ => B4_nonneg α f s)
  linarith

theorem B4_tail_tendsto (α : ℝ) (f : ℝ → ℝ → ℝ) :
    Filter.Tendsto (fun z : ℝ => ∫ s in Set.Ioi z, B4 α f s) Filter.atTop (𝓝 0) :=
  MeasureTheory.tendsto_integral_Ioi_zero (b := fun z : ℝ => z) tendsto_id

/-- `L12f f` is continuous on `(0,∞)` as soon as the density is continuous there. -/
theorem L12f_continuousOn {f : ℝ → ℝ → ℝ}
    (hint : MeasureTheory.IntegrableOn (fun s => Work.FM.L12dens Work.Spaces.K f s)
      (Set.Ioi 0))
    (hcont : ∀ z ∈ Set.Ioi (0 : ℝ), ContinuousAt (Work.FM.L12dens Work.Spaces.K f) z) :
    ContinuousOn (Work.Coercivity.L12f f) (Set.Ioi (0 : ℝ)) := by
  intro z hz
  exact ((Work.FM.hasDerivAt_L12 (K := Work.Spaces.K) (f := f) (a := 0) (ρ := z)
    hint (hcont z hz) hz).continuousAt).continuousWithinAt

/-- A.e. strong measurability of `L12f f` on any subset of `(0,∞)`. -/
theorem L12f_aesm_mono {f : ℝ → ℝ → ℝ}
    (hint : MeasureTheory.IntegrableOn (fun s => Work.FM.L12dens Work.Spaces.K f s)
      (Set.Ioi 0))
    (hcont : ∀ z ∈ Set.Ioi (0 : ℝ), ContinuousAt (Work.FM.L12dens Work.Spaces.K f) z)
    {u : Set ℝ} (hu : u ⊆ Set.Ioi (0 : ℝ)) :
    AEStronglyMeasurable (Work.Coercivity.L12f f) (volume.restrict u) :=
  (L12f_continuousOn hint hcont).aestronglyMeasurable measurableSet_Ioi |>.mono_measure
    (MeasureTheory.Measure.restrict_mono_set volume hu)

/-- The density is a.e. strongly measurable on `(1,∞)` as soon as it is continuous there. -/
theorem L12dens_aesm_Ioi {f : ℝ → ℝ → ℝ}
    (hcont : ∀ z ∈ Set.Ioi (0 : ℝ), ContinuousAt (Work.FM.L12dens Work.Spaces.K f) z) :
    AEStronglyMeasurable (Work.FM.L12dens Work.Spaces.K f) (volume.restrict (Set.Ioi 1)) := by
  have hcontOn : ContinuousOn (Work.FM.L12dens Work.Spaces.K f) (Set.Ioi (0 : ℝ)) :=
    fun z hz => (hcont z hz).continuousWithinAt
  exact (hcontOn.aestronglyMeasurable measurableSet_Ioi).mono_measure
    (MeasureTheory.Measure.restrict_mono_set volume (Set.Ioi_subset_Ioi zero_le_one))

/-- `∫_{(0,z]} B4 → 0` as `z → 0⁺`. -/
theorem Ioc_B4_tendsto_zero (α : ℝ) {f : ℝ → ℝ → ℝ} (hmem : Work.Spaces.HkMem α 4 f) :
    Filter.Tendsto (fun z => ∫ s in Set.Ioc 0 z, B4 α f s) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  set g : ℝ → ℝ := (Set.Ioi (0 : ℝ)).indicator (B4 α f) with hgdef
  have hg_int : MeasureTheory.Integrable g volume := by
    rw [hgdef, MeasureTheory.integrable_indicator_iff measurableSet_Ioi]
    exact B4_integrableOn α f hmem
  have hg_aesm : AEStronglyMeasurable g volume := hg_int.aestronglyMeasurable
  have hmain : Filter.Tendsto (fun z => ∫ s, (Set.Ioc 0 z).indicator g s ∂volume)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have h := MeasureTheory.tendsto_integral_filter_of_dominated_convergence
      (F := fun (z : ℝ) (s : ℝ) => (Set.Ioc 0 z).indicator g s)
      (f := fun _ : ℝ => (0 : ℝ)) (bound := fun s => |g s|) (l := 𝓝[>] (0 : ℝ))
      (Filter.Eventually.of_forall fun z => hg_aesm.indicator measurableSet_Ioc)
      (Filter.Eventually.of_forall fun z => Filter.Eventually.of_forall fun s => by
        rw [Real.norm_eq_abs]
        by_cases hs : s ∈ Set.Ioc 0 z
        · rw [Set.indicator_of_mem hs]
        · rw [Set.indicator_of_notMem hs, abs_zero]
          exact abs_nonneg _)
      hg_int.abs
      (Filter.Eventually.of_forall fun s => ?_)
    simpa using h
    by_cases hs : (0 : ℝ) < s
    · refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
      filter_upwards [Ioo_mem_nhdsGT hs] with z hz
      rw [Set.indicator_of_notMem]
      exact fun hmem => absurd hmem.2 (not_le.mpr hz.2)
    · have hz0 : g s = 0 := by
        rw [hgdef, Set.indicator_of_notMem]
        simp only [Set.mem_Ioi, not_lt]
        linarith [not_lt.mp hs]
      rw [show (fun z => (Set.Ioc 0 z).indicator g s) = fun _ => (0 : ℝ) from
        funext fun z => by
          rw [Set.indicator_of_notMem]
          exact fun hmem => absurd hmem.1 (not_lt.mpr (not_lt.mp hs))]
      exact tendsto_const_nhds
  refine Filter.Tendsto.congr' ?_ hmain
  filter_upwards [self_mem_nhdsWithin] with z hz
  rw [MeasureTheory.integral_indicator measurableSet_Ioc]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioc (fun s hs => ?_)
  rw [hgdef, Set.indicator_of_mem]
  exact hs.1

/-- `s ↦ (L12dens K f s)² · s²` is integrable on `(1,∞)`. -/
theorem G_sq_mul_sq_integrableOn (α : ℝ) {f : ℝ → ℝ → ℝ} (hsm : Work.FTS.LocData.SmoothQuad f)
    (hmem : Work.Spaces.HkMem α 4 f)
    (hcont : ∀ z ∈ Set.Ioi (0 : ℝ), ContinuousAt (Work.FM.L12dens Work.Spaces.K f) z) :
    MeasureTheory.IntegrableOn
      (fun s => (Work.FM.L12dens Work.Spaces.K f s) ^ 2 * s ^ 2) (Set.Ioi 1) := by
  have hG : AEStronglyMeasurable (Work.FM.L12dens Work.Spaces.K f)
      (volume.restrict (Set.Ioi 1)) := L12dens_aesm_Ioi hcont
  have hmaj : MeasureTheory.IntegrableOn (fun s => 3 * B4 α f s) (Set.Ioi 1) :=
    ((B4_integrableOn α f hmem).mono_set (Set.Ioi_subset_Ioi zero_le_one)).const_mul 3
  refine hmaj.mono' ((hG.pow 2).mul (continuous_pow 2).aestronglyMeasurable) ?_
  refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi (fun s hs => ?_)
  have hs0 : 0 < s := lt_trans zero_lt_one hs
  have hb := dens_abs_le α hsm hmem hs0
  have hB : 0 ≤ B4 α f s := B4_nonneg α f s
  have habs := abs_le.mp hb
  rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))]
  have hsq : (Work.FM.L12dens Work.Spaces.K f s) ^ 2
      ≤ (Real.sqrt 3 * (s / (1 + s) ^ 2) * Real.sqrt (B4 α f s)) ^ 2 := by
    nlinarith [habs.1, habs.2]
  refine le_trans (mul_le_mul_of_nonneg_right hsq (sq_nonneg s)) ?_
  rw [mul_pow, mul_pow, Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num), Real.sq_sqrt hB]
  rw [div_pow]
  have h4 : s ^ 4 ≤ (1 + s) ^ 4 := by
    have h2 : s ≤ (1 + s) ^ 2 := by nlinarith [sq_nonneg s]
    nlinarith [h2, sq_nonneg s, sq_nonneg (s ^ 2)]
  rw [show ((1 + s) ^ 2) ^ 2 = (1 + s) ^ 4 by ring]
  rw [show 3 * (s ^ 2 / (1 + s) ^ 4) * B4 α f s * s ^ 2
      = 3 * ((s ^ 2 * s ^ 2) / (1 + s) ^ 4) * B4 α f s by ring]
  rw [show s ^ 2 * s ^ 2 = s ^ 4 by ring]
  have h1 : s ^ 4 / (1 + s) ^ 4 ≤ 1 := by
    rw [div_le_one (by positivity)]
    exact h4
  nlinarith [h1, hB]

/-- `(L12f f z)²` is integrable on `(1,∞)`. -/
theorem L12f_sq_integrableOn_Ioi_one (α : ℝ) {f : ℝ → ℝ → ℝ} (hsm : Work.FTS.LocData.SmoothQuad f)
    (hmem : Work.Spaces.HkMem α 4 f)
    (hint : MeasureTheory.IntegrableOn (fun s => Work.FM.L12dens Work.Spaces.K f s) (Set.Ioi 0))
    (hcont : ∀ z ∈ Set.Ioi (0 : ℝ), ContinuousAt (Work.FM.L12dens Work.Spaces.K f) z) :
    MeasureTheory.IntegrableOn (fun z => (Work.Coercivity.L12f f z) ^ 2) (Set.Ioi 1) := by
  have hG_int := G_sq_mul_sq_integrableOn α hsm hmem hcont
  have hGmem : MeasureTheory.IntegrableOn (Work.FM.L12dens Work.Spaces.K f) (Set.Ioi 1) :=
    hint.mono_set (Set.Ioi_subset_Ioi zero_le_one)
  have h := (Work.FTS.CoercivityFix.Coer1T.Hardy.Ioi_tail_sq_integrable
    (Work.FM.L12dens Work.Spaces.K f) hG_int hGmem).1
  simpa [Work.Coercivity.L12f, Work.FM.L12] using h

/-- `(L12f f z)²/z⁴` is integrable on `(0,1]`. -/
theorem L12f_sq_div_z4_integrableOn_Ioc (α : ℝ) {f : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.LocData.SmoothQuad f) (hmem : Work.Spaces.HkMem α 4 f)
    (hint : MeasureTheory.IntegrableOn (fun s => Work.FM.L12dens Work.Spaces.K f s) (Set.Ioi 0))
    (hl12 : Work.Coercivity.L12f f 0 = 0)
    (hcont : ∀ z ∈ Set.Ioi (0 : ℝ), ContinuousAt (Work.FM.L12dens Work.Spaces.K f) z) :
    MeasureTheory.IntegrableOn (fun z => (Work.Coercivity.L12f f z) ^ 2 / z ^ 4)
      (Set.Ioc 0 1) := by
  set Ψ : ℝ → ℝ := fun s => s * Real.sqrt (B4 α f s) with hΨdef
  have hPsi : MeasureTheory.IntegrableOn (fun s => (Ψ s) ^ 2 / s ^ 2) (Set.Ioc 0 1) := by
    refine ((B4_integrableOn α f hmem).mono_set (fun t ht => ht.1)).congr_fun
      (fun s hs => ?_) measurableSet_Ioc
    have hs0 : s ≠ 0 := ne_of_gt hs.1
    show B4 α f s = (s * Real.sqrt (B4 α f s)) ^ 2 / s ^ 2
    rw [mul_pow, Real.sq_sqrt (B4_nonneg α f s)]
    field_simp
  have hHT := (Work.FTS.CoercivityFix.Coer1T.Hardy.Ioc_prim_sq_integrable Ψ hPsi).1
  have hL12 : AEStronglyMeasurable (Work.Coercivity.L12f f) (volume.restrict (Set.Ioc 0 1)) :=
    L12f_aesm_mono hint hcont (fun t ht => ht.1)
  have hden : AEStronglyMeasurable (fun z : ℝ => (z ^ 4)⁻¹) (volume.restrict (Set.Ioc 0 1)) := by
    have hmeas : Measurable (fun z : ℝ => (z ^ 4)⁻¹) :=
      (continuous_pow 4).measurable.inv
    exact hmeas.aestronglyMeasurable.mono_measure (MeasureTheory.Measure.restrict_mono_set volume
      (fun t ht => ht.1))
  have haesm : AEStronglyMeasurable
      (fun z => (Work.Coercivity.L12f f z) ^ 2 / z ^ 4) (volume.restrict (Set.Ioc 0 1)) := by
    have h := (hL12.pow 2).mul hden
    convert h using 1
    funext z
    simp only [Pi.pow_apply, Pi.mul_apply, div_eq_mul_inv]
  have hHT3 : MeasureTheory.IntegrableOn
      (fun z => 3 * ((∫ s in Set.Ioc 0 z, Ψ s) ^ 2 / z ^ 4)) (Set.Ioc 0 1) := hHT.const_mul 3
  refine hHT3.mono' haesm ?_
  refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioc (fun z hz => ?_)
  have hz1 : z ≤ 1 := hz.2
  have h1 := L12f_abs_le_prim α hsm hmem hint hl12 hz.1 hz1
  have hAnn : 0 ≤ ∫ s in Set.Ioc 0 z, Ψ s :=
    MeasureTheory.setIntegral_nonneg measurableSet_Ioc
      (fun s hs => mul_nonneg (le_of_lt hs.1) (Real.sqrt_nonneg _))
  have hkey : (Work.Coercivity.L12f f z) ^ 2 ≤ 3 * (∫ s in Set.Ioc 0 z, Ψ s) ^ 2 := by
    have habs := abs_le.mp h1
    have h3A : 0 ≤ Real.sqrt 3 * ∫ s in Set.Ioc 0 z, Ψ s :=
      mul_nonneg (Real.sqrt_nonneg 3) hAnn
    have h1' : (Work.Coercivity.L12f f z) ^ 2
        ≤ (Real.sqrt 3 * ∫ s in Set.Ioc 0 z, Ψ s) ^ 2 :=
      sq_le_sq' (by linarith [habs.1]) habs.2
    rw [mul_pow, Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)] at h1'
    linarith
  rw [Real.norm_of_nonneg (div_nonneg (sq_nonneg _) (by positivity))]
  calc (Work.Coercivity.L12f f z) ^ 2 / z ^ 4
      ≤ 3 * ((∫ s in Set.Ioc 0 z, Ψ s) ^ 2 / z ^ 4) := by
        rw [show 3 * ((∫ s in Set.Ioc 0 z, Ψ s) ^ 2 / z ^ 4)
            = (3 * (∫ s in Set.Ioc 0 z, Ψ s) ^ 2) / z ^ 4 by ring]
        exact div_le_div_of_nonneg_right hkey (by positivity)

/-- `(L12f f z)²/z^{2j}` is integrable on `(0,1]` for every `j ≤ 2`. -/
theorem L12f_sq_div_small (α : ℝ) {f : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.LocData.SmoothQuad f) (hmem : Work.Spaces.HkMem α 4 f)
    (hint : MeasureTheory.IntegrableOn (fun s => Work.FM.L12dens Work.Spaces.K f s) (Set.Ioi 0))
    (hl12 : Work.Coercivity.L12f f 0 = 0)
    (hcont : ∀ z ∈ Set.Ioi (0 : ℝ), ContinuousAt (Work.FM.L12dens Work.Spaces.K f) z)
    (j : ℕ) (hj : j ≤ 2) :
    MeasureTheory.IntegrableOn
      (fun z => (Work.Coercivity.L12f f z) ^ 2 / z ^ (2 * (j : ℝ))) (Set.Ioc 0 1) := by
  have h4 := L12f_sq_div_z4_integrableOn_Ioc α hsm hmem hint hl12 hcont
  have hL12 : AEStronglyMeasurable (Work.Coercivity.L12f f) (volume.restrict (Set.Ioc 0 1)) :=
    L12f_aesm_mono hint hcont (fun t ht => ht.1)
  have hden : AEStronglyMeasurable (fun z : ℝ => (z ^ (2 * (j : ℝ)))⁻¹)
      (volume.restrict (Set.Ioc 0 1)) := by
    have hEq : (fun z : ℝ => (z ^ (2 * (j : ℝ)))⁻¹) = fun z => (z ^ (2 * j))⁻¹ := by
      funext z
      rw [show (2 * (j : ℝ)) = ((2 * j : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
    rw [hEq]
    exact (((continuous_pow (2 * j)).measurable.inv).aestronglyMeasurable).mono_measure
      (MeasureTheory.Measure.restrict_mono_set volume (fun t ht => ht.1))
  have haesm : AEStronglyMeasurable
      (fun z => (Work.Coercivity.L12f f z) ^ 2 / z ^ (2 * (j : ℝ)))
      (volume.restrict (Set.Ioc 0 1)) := by
    have h := (hL12.pow 2).mul hden
    convert h using 1
    funext z
    simp only [Pi.pow_apply, Pi.mul_apply, div_eq_mul_inv]
  refine h4.mono' haesm ?_
  refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioc (fun z hz => ?_)
  have hz1 : z ≤ 1 := hz.2
  have h2j : (2 * (j : ℝ)) ≤ 4 := by
    have : ((2 * j : ℕ) : ℝ) ≤ ((4 : ℕ) : ℝ) := by
      have h2 : 2 * j ≤ 4 := by omega
      exact_mod_cast h2
    rw [show (2 * (j : ℝ)) = ((2 * j : ℕ) : ℝ) by push_cast; ring]
    exact this
  have hzj : z ^ 4 ≤ z ^ (2 * (j : ℝ)) := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_ge hz.1 hz1 h2j
  have hpos : 0 < z ^ (2 * (j : ℝ)) := Real.rpow_pos_of_pos hz.1 _
  have hpos4 : 0 < z ^ 4 := pow_pos hz.1 4
  rw [Real.norm_of_nonneg (div_nonneg (sq_nonneg _) (le_of_lt hpos))]
  calc (Work.Coercivity.L12f f z) ^ 2 / z ^ (2 * (j : ℝ))
      ≤ (Work.Coercivity.L12f f z) ^ 2 / z ^ 4 :=
        div_le_div_of_nonneg_left (sq_nonneg _) hpos4 hzj
    _ = _ := rfl

/-- `(L12f f z)²/z^{2j}` is integrable on `(1,∞)`. -/
theorem L12f_sq_div_large (α : ℝ) {f : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.LocData.SmoothQuad f) (hmem : Work.Spaces.HkMem α 4 f)
    (hint : MeasureTheory.IntegrableOn (fun s => Work.FM.L12dens Work.Spaces.K f s) (Set.Ioi 0))
    (hcont : ∀ z ∈ Set.Ioi (0 : ℝ), ContinuousAt (Work.FM.L12dens Work.Spaces.K f) z)
    (j : ℕ) :
    MeasureTheory.IntegrableOn
      (fun z => (Work.Coercivity.L12f f z) ^ 2 / z ^ (2 * (j : ℝ))) (Set.Ioi 1) := by
  have h1 := L12f_sq_integrableOn_Ioi_one α hsm hmem hint hcont
  have hL12 : AEStronglyMeasurable (Work.Coercivity.L12f f) (volume.restrict (Set.Ioi 1)) :=
    L12f_aesm_mono hint hcont (Set.Ioi_subset_Ioi zero_le_one)
  have hden : AEStronglyMeasurable (fun z : ℝ => (z ^ (2 * (j : ℝ)))⁻¹)
      (volume.restrict (Set.Ioi 1)) := by
    have hEq : (fun z : ℝ => (z ^ (2 * (j : ℝ)))⁻¹) = fun z => (z ^ (2 * j))⁻¹ := by
      funext z
      rw [show (2 * (j : ℝ)) = ((2 * j : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
    rw [hEq]
    exact (((continuous_pow (2 * j)).measurable.inv).aestronglyMeasurable).mono_measure
      (MeasureTheory.Measure.restrict_mono_set volume (Set.Ioi_subset_Ioi zero_le_one))
  have haesm : AEStronglyMeasurable
      (fun z => (Work.Coercivity.L12f f z) ^ 2 / z ^ (2 * (j : ℝ)))
      (volume.restrict (Set.Ioi 1)) := by
    have h := (hL12.pow 2).mul hden
    convert h using 1
    funext z
    simp only [Pi.pow_apply, Pi.mul_apply, div_eq_mul_inv]
  refine h1.mono' haesm ?_
  refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi (fun z hz => ?_)
  have hz1 : 1 ≤ z := le_of_lt hz
  have hzj : (1 : ℝ) ≤ z ^ (2 * (j : ℝ)) := by
    have h2j : (0 : ℝ) ≤ 2 * (j : ℝ) := by positivity
    rw [show (2 * (j : ℝ)) = ((2 * j : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
    exact one_le_pow₀ hz1
  rw [Real.norm_of_nonneg (div_nonneg (sq_nonneg _) (by positivity))]
  calc (Work.Coercivity.L12f f z) ^ 2 / z ^ (2 * (j : ℝ))
      ≤ (Work.Coercivity.L12f f z) ^ 2 / 1 :=
        div_le_div_of_nonneg_left (sq_nonneg _) one_pos hzj
    _ = _ := by ring

/-- The `z → 0⁺` boundary terms of `HardyHyp`. -/
theorem L12f_bd0 (α : ℝ) {f : ℝ → ℝ → ℝ} (hsm : Work.FTS.LocData.SmoothQuad f)
    (hmem : Work.Spaces.HkMem α 4 f)
    (hint : MeasureTheory.IntegrableOn (fun s => Work.FM.L12dens Work.Spaces.K f s) (Set.Ioi 0))
    (hl12 : Work.Coercivity.L12f f 0 = 0) (j : ℕ) (hj : j ≤ 2) :
    Filter.Tendsto (fun z => (Work.Coercivity.L12f f z) ^ 2 / z ^ (2 * (j : ℝ) - 1))
        (𝓝[>] (0 : ℝ)) (𝓝 0) ∧
      Filter.Tendsto (fun z => Work.Spaces.w z * (Work.Coercivity.L12f f z) ^ 2)
        (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hmem1 : Set.Ioc (0 : ℝ) 1 ∈ 𝓝[>] (0 : ℝ) :=
    Filter.mem_of_superset (Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1))
      (fun z hz => ⟨hz.1, le_of_lt hz.2⟩)
  have hβ : Filter.Tendsto (fun z => ∫ s in Set.Ioc 0 z, B4 α f s) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    Ioc_B4_tendsto_zero α hmem
  have h2j : (2 * (j : ℝ)) ≤ 4 := by
    have h2 : 2 * j ≤ 4 := by omega
    rw [show (2 * (j : ℝ)) = ((2 * j : ℕ) : ℝ) by push_cast; ring]
    exact_mod_cast h2
  constructor
  · refine squeeze_zero' (g := fun z => 3 * ∫ s in Set.Ioc 0 z, B4 α f s) ?_ ?_
      (by simpa using hβ.const_mul 3)
    · filter_upwards [self_mem_nhdsWithin] with z hz
      exact div_nonneg (sq_nonneg _) (le_of_lt (Real.rpow_pos_of_pos hz _))
    · filter_upwards [self_mem_nhdsWithin, hmem1] with z hz hz1
      have hX := L12f_sq_le_small α hsm hmem hint hl12 hz hz1.2
      have hzpow : z ^ (3 : ℕ) ≤ z ^ (2 * (j : ℝ) - 1) := by
        have h := Real.rpow_le_rpow_of_exponent_ge hz hz1.2
          (show (2 * (j : ℝ) - 1) ≤ 3 by linarith)
        simpa using h
      have hstep : (Work.Coercivity.L12f f z) ^ 2 / z ^ (2 * (j : ℝ) - 1)
          ≤ (Work.Coercivity.L12f f z) ^ 2 / z ^ 3 :=
        div_le_div_of_nonneg_left (sq_nonneg _) (pow_pos hz 3) hzpow
      have hstep2 : (Work.Coercivity.L12f f z) ^ 2 / z ^ 3
          ≤ 3 * (∫ s in Set.Ioc 0 z, B4 α f s) := by
        rw [div_le_iff₀ (pow_pos hz 3)]
        nlinarith [hX]
      exact le_trans hstep hstep2
  · refine squeeze_zero' (g := fun z => 12 * ∫ s in Set.Ioc 0 z, B4 α f s) ?_ ?_
      (by simpa using hβ.const_mul 12)
    · filter_upwards with z
      have hw : 0 ≤ Work.Spaces.w z := by rw [Work.Spaces.w]; positivity
      exact mul_nonneg hw (sq_nonneg _)
    · filter_upwards [self_mem_nhdsWithin, hmem1] with z hz hz1
      have hX := L12f_sq_le_small α hsm hmem hint hl12 hz hz1.2
      have hβnn : 0 ≤ ∫ s in Set.Ioc 0 z, B4 α f s :=
        MeasureTheory.setIntegral_nonneg measurableSet_Ioc (fun s _ => B4_nonneg α f s)
      have hw : Work.Spaces.w z = (1 + z) ^ 2 / z ^ 2 := rfl
      have h4 : (1 + z) ^ 2 ≤ 4 := by
        have h5 : 1 + z ≤ 2 := by linarith [hz1.2]
        have hz0 : (0 : ℝ) < z := hz
        have h6 : (0 : ℝ) ≤ 1 + z := by linarith
        calc (1 + z) ^ 2 = (1 + z) * (1 + z) := by ring
          _ ≤ 2 * 2 := mul_le_mul h5 h5 h6 (by linarith)
          _ = 4 := by norm_num
      rw [hw]
      have hz0 : (0 : ℝ) < z := hz
      rw [div_mul_eq_mul_div, div_le_iff₀ (pow_pos hz0 2)]
      have h1 : (1 + z) ^ 2 * (Work.Coercivity.L12f f z) ^ 2
          ≤ 4 * (3 * z ^ 3 * ∫ s in Set.Ioc 0 z, B4 α f s) :=
        mul_le_mul h4 hX (sq_nonneg _) (by norm_num)
      have h2 : 4 * (3 * z ^ 3 * ∫ s in Set.Ioc 0 z, B4 α f s)
          ≤ 12 * (∫ s in Set.Ioc 0 z, B4 α f s) * z ^ 2 := by
        nlinarith [hβnn, hz0, hz1.2, sq_nonneg z, pow_pos hz0 2,
          mul_le_mul_of_nonneg_left hz1.2 (mul_nonneg (show (0:ℝ) ≤ 12 by norm_num) hβnn)]
      linarith [h1, h2]

/-- The `z → ∞` boundary terms of `HardyHyp`. -/
theorem L12f_bdTop (α : ℝ) {f : ℝ → ℝ → ℝ} (hsm : Work.FTS.LocData.SmoothQuad f)
    (hmem : Work.Spaces.HkMem α 4 f) (j : ℕ) :
    Filter.Tendsto (fun z => (Work.Coercivity.L12f f z) ^ 2 / z ^ (2 * (j : ℝ) - 1))
        Filter.atTop (𝓝 0) ∧
      Filter.Tendsto (fun z => Work.Spaces.w z * (Work.Coercivity.L12f f z) ^ 2)
        Filter.atTop (𝓝 0) := by
  have hT : Filter.Tendsto (fun z => ∫ s in Set.Ioi z, B4 α f s) Filter.atTop (𝓝 0) :=
    B4_tail_tendsto α f
  have hmem1 : Set.Ici (1 : ℝ) ∈ Filter.atTop := Filter.Ici_mem_atTop 1
  constructor
  · refine squeeze_zero' (g := fun z => 3 * ∫ s in Set.Ioi z, B4 α f s) ?_ ?_
      (by simpa using hT.const_mul 3)
    · filter_upwards [hmem1] with z hz
      have hz0 : 0 < z := lt_of_lt_of_le one_pos hz
      exact div_nonneg (sq_nonneg _) (le_of_lt (Real.rpow_pos_of_pos hz0 _))
    · filter_upwards [hmem1] with z hz
      have hz1 : 1 ≤ z := hz
      have hz0 : 0 < z := lt_of_lt_of_le one_pos hz1
      have hX := L12f_abs_le_large α hsm hmem hz1
      have hTnn : 0 ≤ ∫ s in Set.Ioi z, B4 α f s :=
        MeasureTheory.setIntegral_nonneg measurableSet_Ioi (fun s _ => B4_nonneg α f s)
      have hsq' : (Work.Coercivity.L12f f z) ^ 2
          ≤ 3 * ((1 / z) * ∫ s in Set.Ioi z, B4 α f s) := by
        have h1 : (Real.sqrt (1 / z)) ^ 2 = 1 / z := Real.sq_sqrt (by positivity)
        have h2 : (Real.sqrt (∫ s in Set.Ioi z, B4 α f s)) ^ 2
            = ∫ s in Set.Ioi z, B4 α f s := Real.sq_sqrt hTnn
        have habs := abs_le.mp hX
        have h3 : (Work.Coercivity.L12f f z) ^ 2
            ≤ (Real.sqrt 3 * (Real.sqrt (1 / z) * Real.sqrt (∫ s in Set.Ioi z, B4 α f s))) ^ 2 :=
          sq_le_sq' (by linarith [habs.1]) habs.2
        rw [mul_pow, Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num), mul_pow, h1, h2] at h3
        linarith [h3]
      have hzj : (1 : ℝ) ≤ z ^ (2 * (j : ℝ) - 1) * z := by
        have h2j : (-1 : ℝ) ≤ 2 * (j : ℝ) - 1 := by
          have : (0 : ℝ) ≤ 2 * (j : ℝ) := by positivity
          linarith
        have h3 : z ^ (-1 : ℝ) ≤ z ^ (2 * (j : ℝ) - 1) :=
          Real.rpow_le_rpow_of_exponent_le hz1 h2j
        rw [Real.rpow_neg_one] at h3
        have := mul_le_mul_of_nonneg_right h3 hz0.le
        rw [inv_mul_cancel₀ (ne_of_gt hz0)] at this
        linarith
      have hstep : (Work.Coercivity.L12f f z) ^ 2 / z ^ (2 * (j : ℝ) - 1)
          ≤ 3 * (∫ s in Set.Ioi z, B4 α f s) := by
        have hz_inv : 1 / z ≤ z ^ (2 * (j : ℝ) - 1) := (div_le_iff₀ hz0).mpr hzj
        have hstep2 : 3 * (1 / z * ∫ s in Set.Ioi z, B4 α f s)
            ≤ 3 * (∫ s in Set.Ioi z, B4 α f s) * z ^ (2 * (j : ℝ) - 1) := by
          have h3T : (0 : ℝ) ≤ 3 * (∫ s in Set.Ioi z, B4 α f s) := by linarith
          have := mul_le_mul_of_nonneg_right hz_inv h3T
          nlinarith [this]
        rw [div_le_iff₀ (Real.rpow_pos_of_pos hz0 (2 * (j : ℝ) - 1))]
        linarith [hsq', hstep2]
      exact hstep
  · refine squeeze_zero' (g := fun z => 12 * ∫ s in Set.Ioi z, B4 α f s) ?_ ?_
      (by simpa using hT.const_mul 12)
    · filter_upwards with z
      have hw : 0 ≤ Work.Spaces.w z := by rw [Work.Spaces.w]; positivity
      exact mul_nonneg hw (sq_nonneg _)
    · filter_upwards [hmem1] with z hz
      have hz1 : 1 ≤ z := hz
      have hz0 : 0 < z := lt_of_lt_of_le one_pos hz1
      have hX := L12f_abs_le_large α hsm hmem hz1
      have hTnn : 0 ≤ ∫ s in Set.Ioi z, B4 α f s :=
        MeasureTheory.setIntegral_nonneg measurableSet_Ioi (fun s _ => B4_nonneg α f s)
      have habs := abs_le.mp hX
      have hsq' : (Work.Coercivity.L12f f z) ^ 2
          ≤ 3 * ((1 / z) * ∫ s in Set.Ioi z, B4 α f s) := by
        have h1 : (Real.sqrt (1 / z)) ^ 2 = 1 / z := Real.sq_sqrt (by positivity)
        have h2 : (Real.sqrt (∫ s in Set.Ioi z, B4 α f s)) ^ 2
            = ∫ s in Set.Ioi z, B4 α f s := Real.sq_sqrt hTnn
        have h3 : (Work.Coercivity.L12f f z) ^ 2
            ≤ (Real.sqrt 3 * (Real.sqrt (1 / z) * Real.sqrt (∫ s in Set.Ioi z, B4 α f s))) ^ 2 :=
          sq_le_sq' (by linarith [habs.1]) habs.2
        rw [mul_pow, Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num), mul_pow, h1, h2] at h3
        linarith [h3]
      have hw : Work.Spaces.w z = (1 + z) ^ 2 / z ^ 2 := rfl
      have h4 : (1 + z) ^ 2 ≤ 4 * z ^ 2 := by nlinarith [hz1, sq_nonneg z, sq_nonneg (z - 1)]
      have hz2 : (0 : ℝ) < z ^ 2 := by positivity
      have hstep2 : (1 + z) ^ 2 * (Work.Coercivity.L12f f z) ^ 2
          ≤ 12 * (∫ s in Set.Ioi z, B4 α f s) * z ^ 2 := by
        have h5 : (1 + z) ^ 2 * (Work.Coercivity.L12f f z) ^ 2
            ≤ 4 * z ^ 2 * (3 * (1 / z * ∫ s in Set.Ioi z, B4 α f s)) :=
          mul_le_mul h4 hsq' (sq_nonneg _) (by positivity)
        have h6 : 4 * z ^ 2 * (3 * (1 / z * ∫ s in Set.Ioi z, B4 α f s))
            = 12 * (∫ s in Set.Ioi z, B4 α f s) * z := by
          field_simp
          ring
        rw [h6] at h5
        have h7 : 12 * (∫ s in Set.Ioi z, B4 α f s) * z
            ≤ 12 * (∫ s in Set.Ioi z, B4 α f s) * z ^ 2 := by
          have := mul_le_mul_of_nonneg_left hz1 (by linarith : (0:ℝ) ≤ 12 * (∫ s in Set.Ioi z, B4 α f s))
          nlinarith [this]
        linarith [h5, h7]
      rw [hw, div_mul_eq_mul_div, div_le_iff₀ hz2]
      linarith [hstep2]

end Work.FTS.CoercivityFix.Coer1T
