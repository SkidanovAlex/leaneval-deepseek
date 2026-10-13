import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.EllipticEst.Honest.Basic
import Submission.Work.FTS.EllipticEst.Honest.HonEnergyAux
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.EllipticEst.SgamBound.integrableOn_abs_of_sq_mul_sEta
import Submission.Work.FTS.EllipticEst.Honest.HonZSecondSwapSigma

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Honest

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

/-! ## Elementary a.e. facts on `Iθ` -/

theorem ae_mem_Iθ' : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ), θ ∈ Work.Spaces.Iθ :=
  ae_restrict_mem measurableSet_Icc

theorem ae_mem_Ioo_Iθ' :
    ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ), θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
  rw [restrict_Iθ_eq_Ioo]
  exact ae_restrict_mem measurableSet_Ioo

theorem aesm_sEta' : AEStronglyMeasurable (fun θ : ℝ => Work.FTS.EllipticEst.sEta θ)
    (volume.restrict Work.Spaces.Iθ) :=
  sEta_integrableOn.aestronglyMeasurable

theorem sEta_nonneg_Ioo {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    0 ≤ Work.FTS.EllipticEst.sEta θ :=
  sEta_nonneg ⟨hθ.1.le, hθ.2.le⟩

theorem one_le_sEta_Ioo {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    1 ≤ Work.FTS.EllipticEst.sEta θ :=
  one_le_sEta hθ

instance instIsFiniteMeasureIθ : IsFiniteMeasure (volume.restrict Work.Spaces.Iθ) :=
  ⟨by rw [Measure.restrict_apply_univ, Work.Spaces.Iθ, Real.volume_Icc]
      exact ENNReal.ofReal_lt_top⟩

theorem integrableOn_const_Iθ' (c : ℝ) :
    IntegrableOn (fun _ : ℝ => c) Work.Spaces.Iθ :=
  integrable_const c

/-! ## From an a.e. bound and a.e. strong measurability, the square is integrable -/

theorem integrableOn_sq_of_aebdd' {u : ℝ → ℝ} {C : ℝ}
    (haesm : AEStronglyMeasurable u (volume.restrict Work.Spaces.Iθ))
    (hbdd : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ), |u θ| ≤ C) :
    IntegrableOn (fun θ => (u θ) ^ 2) Work.Spaces.Iθ :=
  MeasureTheory.Integrable.of_bound (haesm.pow 2) (C ^ 2) (by
    filter_upwards [hbdd] with θ hθ
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    nlinarith [abs_nonneg (u θ), hθ, sq_abs (u θ)])

/-! ## Slicewise boundedness of `Ψ` and `∂_θΨ` -/

/-- The `θ`-slice of `∂_θθΨ` is continuous on the open interval. -/
theorem continuousOn_pthIter2' {α : ℝ} {F Ψ : ℝ → ℝ → ℝ} (h : Hon α F Ψ)
    {z : ℝ} (hz : 0 < z) :
    ContinuousOn (fun θ => Work.Spaces.pthIter 2 Ψ z θ) (Set.Ioo 0 (Real.pi / 2)) := by
  have hslice : ContDiffOn ℝ 2 (fun θ => Ψ z θ) (Set.Ioo 0 (Real.pi / 2)) := by
    have h2 := h.sm 2
    have hmap : Set.MapsTo (fun θ : ℝ => (z, θ)) (Set.Ioo 0 (Real.pi / 2))
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := fun θ hθ => ⟨hz, hθ⟩
    exact h2.comp (by fun_prop) hmap
  have h1 : ContDiffOn ℝ 1 (deriv (fun θ' => Ψ z θ')) (Set.Ioo 0 (Real.pi / 2)) :=
    hslice.deriv_of_isOpen isOpen_Ioo (by norm_num)
  have h2 : ContDiffOn ℝ 0 (deriv (deriv (fun θ' => Ψ z θ'))) (Set.Ioo 0 (Real.pi / 2)) :=
    h1.deriv_of_isOpen isOpen_Ioo (by norm_num)
  have hfun : (fun θ => Work.Spaces.pthIter 2 Ψ z θ)
      = deriv (deriv (fun θ' => Ψ z θ')) := rfl
  rw [hfun]
  exact h2.continuousOn

/-- `|∂_θθΨ(z,·)|` is integrable on `Iθ`. -/
theorem integrableOn_abs_pthIter2' {α : ℝ} {F Ψ : ℝ → ℝ → ℝ} (h : Hon α F Ψ)
    {z : ℝ} (hz : 0 < z) :
    IntegrableOn (fun θ => |Work.Spaces.pthIter 2 Ψ z θ|) Work.Spaces.Iθ :=
  Work.FTS.EllipticEst.SgamBound.integrableOn_abs_of_sq_mul_sEta
    (continuousOn_pthIter2' h hz) (hon_memB_sigma h hz)

/-- Abs-value of an interval integral over a subinterval of `(0,π/2)` is bounded by the
set integral of `|f|` over `Iθ`. -/
theorem abs_intervalIntegral_le_setIntegral' {f : ℝ → ℝ} {a b : ℝ}
    (ha : a ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) (hb : b ∈ Set.Ioo (0 : ℝ) (Real.pi / 2))
    (hI : IntervalIntegrable (fun x => |f x|) volume 0 (Real.pi / 2)) :
    |∫ x in a..b, f x| ≤ ∫ x in Work.Spaces.Iθ, |f x| := by
  have hIeq : (∫ x in (0 : ℝ)..(Real.pi / 2), |f x|) = ∫ x in Work.Spaces.Iθ, |f x| := by
    rw [intervalIntegral.integral_of_le (by positivity), Work.Spaces.Iθ,
      ← MeasureTheory.integral_Icc_eq_integral_Ioc]
  rcases le_total a b with hh | hh
  · exact le_trans (intervalIntegral.abs_integral_le_integral_abs hh) (by
      rw [← hIeq]
      exact intervalIntegral.integral_mono_interval ha.1.le hh hb.2.le
        (Eventually.of_forall (fun x => abs_nonneg _)) hI)
  · rw [intervalIntegral.integral_symm b a, abs_neg]
    exact le_trans (intervalIntegral.abs_integral_le_integral_abs hh) (by
      rw [← hIeq]
      exact intervalIntegral.integral_mono_interval hb.1.le hh ha.2.le
        (Eventually.of_forall (fun x => abs_nonneg _)) hI)

/-- **FTC bound for `∂_θΨ` on a slice.** -/
theorem slice_pth_bdd {α : ℝ} {F Ψ : ℝ → ℝ → ℝ} (h : Hon α F Ψ) {z : ℝ} (hz : 0 < z) :
    ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      |Work.Spaces.pth Ψ z θ| ≤ |Work.Spaces.pth Ψ z (Real.pi / 4)|
        + ∫ t in Work.Spaces.Iθ, |Work.Spaces.pthIter 2 Ψ z t| := by
  have hslice : ContDiffOn ℝ 2 (fun θ => Ψ z θ) (Set.Ioo 0 (Real.pi / 2)) := by
    have h2 := h.sm 2
    have hmap : Set.MapsTo (fun θ : ℝ => (z, θ)) (Set.Ioo 0 (Real.pi / 2))
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := fun θ hθ => ⟨hz, hθ⟩
    exact h2.comp (by fun_prop) hmap
  have hint := integrableOn_abs_pthIter2' h hz
  have hIi : IntervalIntegrable (fun t : ℝ => |Work.Spaces.pthIter 2 Ψ z t|) volume 0
      (Real.pi / 2) := by
    rw [intervalIntegrable_iff, Set.uIoc_of_le (by positivity : (0 : ℝ) ≤ Real.pi / 2)]
    exact hint.mono_set Set.Ioc_subset_Icc_self
  have h1 : ContDiffOn ℝ 1 (fun t => Work.Spaces.pth Ψ z t) (Set.Ioo 0 (Real.pi / 2)) := by
    have hd : ContDiffOn ℝ 1 (deriv (fun θ' => Ψ z θ')) (Set.Ioo 0 (Real.pi / 2)) :=
      hslice.deriv_of_isOpen isOpen_Ioo (by norm_num)
    have hfun : (fun t => Work.Spaces.pth Ψ z t) = deriv (fun θ' => Ψ z θ') := rfl
    rwa [hfun]
  intro θ hθ
  have hpi4 : Real.pi / 4 ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
    refine ⟨by positivity, ?_⟩; nlinarith [Real.pi_pos]
  have hseg : Set.uIcc (Real.pi / 4) θ ⊆ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
    intro x hx
    rw [Set.mem_uIcc] at hx
    rcases hx with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨lt_of_lt_of_le hpi4.1 h1, lt_of_le_of_lt h2 hθ.2⟩
    · exact ⟨lt_of_lt_of_le hθ.1 h1, lt_of_le_of_lt h2 hpi4.2⟩
  have hFTC : (∫ t in (Real.pi / 4)..θ, Work.Spaces.pthIter 2 Ψ z t)
      = Work.Spaces.pth Ψ z θ - Work.Spaces.pth Ψ z (Real.pi / 4) := by
    have := intervalIntegral.integral_deriv_of_contDiffOn_uIcc (h1.mono hseg)
    simpa only [Work.Spaces.pthIter_succ, Work.Spaces.pthIter_zero, Work.Spaces.pth] using this
  have hval : Work.Spaces.pth Ψ z θ
      = Work.Spaces.pth Ψ z (Real.pi / 4)
        + ∫ t in (Real.pi / 4)..θ, Work.Spaces.pthIter 2 Ψ z t := by linarith [hFTC]
  calc |Work.Spaces.pth Ψ z θ|
      = |Work.Spaces.pth Ψ z (Real.pi / 4)
          + ∫ t in (Real.pi / 4)..θ, Work.Spaces.pthIter 2 Ψ z t| := by rw [hval]
    _ ≤ |Work.Spaces.pth Ψ z (Real.pi / 4)|
          + |∫ t in (Real.pi / 4)..θ, Work.Spaces.pthIter 2 Ψ z t| := abs_add_le _ _
    _ ≤ |Work.Spaces.pth Ψ z (Real.pi / 4)|
          + ∫ t in Work.Spaces.Iθ, |Work.Spaces.pthIter 2 Ψ z t| := by
        have := abs_intervalIntegral_le_setIntegral' hpi4 hθ hIi
        linarith

/-- The `θ`-slice of `∂_θΨ` is a.e. strongly measurable. -/
theorem aesm_pth_slice {α : ℝ} {F Ψ : ℝ → ℝ → ℝ} (h : Hon α F Ψ) {z : ℝ} (hz : 0 < z) :
    AEStronglyMeasurable (fun θ => Work.Spaces.pth Ψ z θ) (volume.restrict Work.Spaces.Iθ) := by
  have hslice : ContDiffOn ℝ 2 (fun θ => Ψ z θ) (Set.Ioo 0 (Real.pi / 2)) := by
    have h2 := h.sm 2
    have hmap : Set.MapsTo (fun θ : ℝ => (z, θ)) (Set.Ioo 0 (Real.pi / 2))
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := fun θ hθ => ⟨hz, hθ⟩
    exact h2.comp (by fun_prop) hmap
  have h1 : ContDiffOn ℝ 1 (deriv (fun θ' => Ψ z θ')) (Set.Ioo 0 (Real.pi / 2)) :=
    hslice.deriv_of_isOpen isOpen_Ioo (by norm_num)
  have hc : ContinuousOn (deriv (fun θ' => Ψ z θ')) (Set.Ioo 0 (Real.pi / 2)) :=
    h1.continuousOn
  rw [restrict_Iθ_eq_Ioo]
  have hfun : (fun θ => Work.Spaces.pth Ψ z θ) = deriv (fun θ' => Ψ z θ') := rfl
  rw [hfun]
  exact hc.aestronglyMeasurable measurableSet_Ioo

/-- **FTC bound for `Ψ` on a slice.** -/
theorem slice_psi_bdd {α : ℝ} {F Ψ : ℝ → ℝ → ℝ} (h : Hon α F Ψ) {z : ℝ} (hz : 0 < z) :
    ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      |Ψ z θ| ≤ |Ψ z (Real.pi / 4)|
        + (Real.pi / 2) * (|Work.Spaces.pth Ψ z (Real.pi / 4)|
          + ∫ t in Work.Spaces.Iθ, |Work.Spaces.pthIter 2 Ψ z t|) := by
  have hslice : ContDiffOn ℝ 2 (fun θ => Ψ z θ) (Set.Ioo 0 (Real.pi / 2)) := by
    have h2 := h.sm 2
    have hmap : Set.MapsTo (fun θ : ℝ => (z, θ)) (Set.Ioo 0 (Real.pi / 2))
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := fun θ hθ => ⟨hz, hθ⟩
    exact h2.comp (by fun_prop) hmap
  have hpth := slice_pth_bdd h hz
  set B : ℝ := |Work.Spaces.pth Ψ z (Real.pi / 4)|
    + ∫ t in Work.Spaces.Iθ, |Work.Spaces.pthIter 2 Ψ z t| with hBdef
  have hB0 : 0 ≤ B := by
    rw [hBdef]
    have := integral_nonneg (μ := volume.restrict Work.Spaces.Iθ)
      (f := fun t => |Work.Spaces.pthIter 2 Ψ z t|) (fun t => abs_nonneg _)
    linarith [abs_nonneg (Work.Spaces.pth Ψ z (Real.pi / 4))]
  intro θ hθ
  have hpi4 : Real.pi / 4 ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
    refine ⟨by positivity, ?_⟩; nlinarith [Real.pi_pos]
  have hseg : Set.uIcc (Real.pi / 4) θ ⊆ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
    intro x hx
    rw [Set.mem_uIcc] at hx
    rcases hx with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨lt_of_lt_of_le hpi4.1 h1, lt_of_le_of_lt h2 hθ.2⟩
    · exact ⟨lt_of_lt_of_le hθ.1 h1, lt_of_le_of_lt h2 hpi4.2⟩
  have hFTC : (∫ t in (Real.pi / 4)..θ, Work.Spaces.pth Ψ z t)
      = Ψ z θ - Ψ z (Real.pi / 4) := by
    have hc1 : ContDiffOn ℝ 1 (fun t => Ψ z t) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
      hslice.of_le (by norm_num)
    have := intervalIntegral.integral_deriv_of_contDiffOn_uIcc (hc1.mono hseg)
    simpa only [Work.Spaces.pth] using this
  have hval : Ψ z θ = Ψ z (Real.pi / 4) + ∫ t in (Real.pi / 4)..θ, Work.Spaces.pth Ψ z t := by
    linarith [hFTC]
  have hbound : (∀ x ∈ Set.uIoc (Real.pi / 4) θ, ‖Work.Spaces.pth Ψ z x‖ ≤ B) := by
    intro x hx
    rw [Real.norm_eq_abs]
    refine le_trans (hpth x ?_) le_rfl
    rw [Set.mem_uIoc] at hx
    rcases hx with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨lt_of_lt_of_le hpi4.1 (le_of_lt h1), lt_of_le_of_lt h2 hθ.2⟩
    · exact ⟨lt_of_lt_of_le hθ.1 (le_of_lt h1), lt_of_le_of_lt h2 hpi4.2⟩
  have habs : |θ - Real.pi / 4| ≤ Real.pi / 2 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [hθ.1, hθ.2, Real.pi_pos]
  calc |Ψ z θ| = |Ψ z (Real.pi / 4) + ∫ t in (Real.pi / 4)..θ, Work.Spaces.pth Ψ z t| := by
        rw [hval]
    _ ≤ |Ψ z (Real.pi / 4)| + |∫ t in (Real.pi / 4)..θ, Work.Spaces.pth Ψ z t| := abs_add_le _ _
    _ ≤ |Ψ z (Real.pi / 4)| + B * |θ - Real.pi / 4| := by
        have h := intervalIntegral.norm_integral_le_of_norm_le_const hbound
        rw [Real.norm_eq_abs] at h
        linarith
    _ ≤ |Ψ z (Real.pi / 4)| + B * (Real.pi / 2) := by
        have := mul_le_mul_of_nonneg_left habs hB0
        linarith
    _ = |Ψ z (Real.pi / 4)| + (Real.pi / 2) * B := by ring

/-- The `θ`-slice of `Ψ` is a.e. strongly measurable. -/
theorem aesm_psi_slice {α : ℝ} {F Ψ : ℝ → ℝ → ℝ} (h : Hon α F Ψ) {z : ℝ} (_hz : 0 < z) :
    AEStronglyMeasurable (fun θ => Ψ z θ) (volume.restrict Work.Spaces.Iθ) := by
  simpa using SmoothOpen.aesm_slice_pzIter (smoothOpen_of_forall h.sm) 0 _hz

/-! ## The five slices -/

theorem integrableOn_sq_psi' {α : ℝ} {F Ψ : ℝ → ℝ → ℝ} (h : Hon α F Ψ) {z : ℝ} (hz : 0 < z) :
    IntegrableOn (fun θ => (Ψ z θ) ^ 2) Work.Spaces.Iθ :=
  integrableOn_sq_of_aebdd' (aesm_psi_slice h hz)
    ((ae_mem_Ioo_Iθ').mono fun θ hθ => slice_psi_bdd h hz θ hθ)

theorem integrableOn_sq_pth' {α : ℝ} {F Ψ : ℝ → ℝ → ℝ} (h : Hon α F Ψ) {z : ℝ} (hz : 0 < z) :
    IntegrableOn (fun θ => (Work.Spaces.pth Ψ z θ) ^ 2) Work.Spaces.Iθ :=
  integrableOn_sq_of_aebdd' (aesm_pth_slice h hz)
    ((ae_mem_Ioo_Iθ').mono fun θ hθ => slice_pth_bdd h hz θ hθ)

theorem integrableOn_sq_pzIter2' {α : ℝ} {F Ψ : ℝ → ℝ → ℝ} (h : Hon α F Ψ) {z : ℝ}
    (hz : 0 < z) :
    IntegrableOn (fun θ => (Work.Spaces.pzIter 2 Ψ z θ) ^ 2) Work.Spaces.Iθ :=
  integrableOn_sq_of_sigma (SmoothOpen.aesm_slice_pzIter (smoothOpen_of_forall h.sm) 2 hz)
    (hon_memA_sigma h hz)

theorem integrableOn_sq_sEta_psi {α : ℝ} {F Ψ : ℝ → ℝ → ℝ} (h : Hon α F Ψ) {z : ℝ}
    (hz : 0 < z) :
    IntegrableOn (fun θ => (Ψ z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ := by
  set C : ℝ := |Ψ z (Real.pi / 4)|
      + (Real.pi / 2) * (|Work.Spaces.pth Ψ z (Real.pi / 4)|
        + ∫ t in Work.Spaces.Iθ, |Work.Spaces.pthIter 2 Ψ z t|) with hCdef
  have hC0 : 0 ≤ C := by
    rw [hCdef]
    have := integral_nonneg (μ := volume.restrict Work.Spaces.Iθ)
      (f := fun t => |Work.Spaces.pthIter 2 Ψ z t|) (fun t => abs_nonneg _)
    have h2 : (0 : ℝ) ≤ Real.pi / 2 := by positivity
    have h3 : 0 ≤ |Work.Spaces.pth Ψ z (Real.pi / 4)|
        + ∫ t in Work.Spaces.Iθ, |Work.Spaces.pthIter 2 Ψ z t| := by
      linarith [abs_nonneg (Work.Spaces.pth Ψ z (Real.pi / 4))]
    have h4 := mul_nonneg h2 h3
    linarith [abs_nonneg (Ψ z (Real.pi / 4))]
  have hb : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), |Ψ z θ| ≤ C := by
    intro θ hθ
    rw [hCdef]
    exact slice_psi_bdd h hz θ hθ
  have haesm : AEStronglyMeasurable
      (fun θ => (Ψ z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) (volume.restrict Work.Spaces.Iθ) :=
    ((aesm_psi_slice h hz).pow 2).mul aesm_sEta'
  refine (sEta_integrableOn.const_mul (C ^ 2)).mono' haesm ?_
  filter_upwards [ae_mem_Ioo_Iθ'] with θ hθ
  have hs := sEta_nonneg_Ioo hθ
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) hs)]
  have h1 : (Ψ z θ) ^ 2 ≤ C ^ 2 := by
    rw [sq_le_sq, abs_of_nonneg hC0]
    exact hb θ hθ
  exact mul_le_mul_of_nonneg_right h1 hs

theorem pz_slice_sq_le' {α : ℝ} {F Ψ : ℝ → ℝ → ℝ} (h : Hon α F Ψ) {z θ : ℝ} (hz : 0 < z)
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2))
    (hInt : MeasureTheory.IntegrableOn
      (fun u => (1 + u) ^ 4 * (Work.Spaces.pzIter 2 Ψ u θ) ^ 2) Work.Spaces.Iz) :
    (Work.Spaces.pz Ψ z θ) ^ 2
      ≤ (∫ x in Set.Ioi z, ((x + 1) ^ (-(2 : ℝ))) ^ 2) *
        (∫ u in Work.Spaces.Iz, (1 + u) ^ 4 * (Work.Spaces.pzIter 2 Ψ u θ) ^ 2) := by
  have hS := smoothOpen_of_forall h.sm
  set k : ℝ → ℝ := fun u => Work.Spaces.pzIter 2 Ψ u θ with hkdef
  -- (1) the derivative of the slice `z ↦ ∂_zΨ z θ`
  have hderiv : ∀ Y : ℝ, 0 < Y →
      HasDerivAt (fun s : ℝ => Work.Spaces.pz Ψ s θ) (k Y) Y := by
    intro Y hY
    have h1 := SmoothOpen.hasDerivAt_slice_pzIter hS 1 hθ hY
    rw [hkdef]
    simpa only [Work.Spaces.pzIter_succ, Work.Spaces.pzIter_zero, Nat.reduceAdd] using h1
  have hslice_deriv : ∀ Y : ℝ, 0 < Y →
      HasDerivAt (fun s : ℝ => Ψ s θ) (Work.Spaces.pz Ψ Y θ) Y :=
    fun Y hY => SmoothOpen.hasDerivAt_slice hS hθ hY
  -- (2) integrability of `(1+u)^4 k u ^ 2` on `(z,∞)`
  have hKz : MeasureTheory.IntegrableOn (fun u : ℝ => (1 + u) ^ 4 * (k u) ^ 2)
      (Set.Ioi z) := by
    have h1 : MeasureTheory.IntegrableOn
        (fun u : ℝ => (1 + u) ^ 4 * (Work.Spaces.pzIter 2 Ψ u θ) ^ 2) (Set.Ioi z) :=
      hInt.mono_set (by
        intro u hu
        rw [Work.Spaces.Iz]
        exact le_of_lt (lt_trans hz (Set.mem_Ioi.mp hu)))
    refine h1.congr_fun (fun u _ => ?_) measurableSet_Ioi
    rw [hkdef]
  -- (3) the weight integral is finite
  have hw_int : MeasureTheory.IntegrableOn (fun x : ℝ => (x + 1) ^ (-(4 : ℝ))) (Set.Ioi z) :=
    integrableOn_add_rpow_Ioi_of_lt (a := -(4 : ℝ)) (c := z) (m := 1)
      (by norm_num) (by linarith)
  -- (4) the two `MemLp` facts
  have hu_mem : MeasureTheory.MemLp (fun x : ℝ => (x + 1) ^ (-(2 : ℝ))) 2
      (volume.restrict (Set.Ioi z)) := by
    rw [MeasureTheory.memLp_two_iff_integrable_sq (by
      exact ((continuousOn_id.add continuousOn_const).rpow_const
        (fun x hx => Or.inl (by
          simp only [Pi.add_apply, id_eq]
          linarith [Set.mem_Ioi.mp hx, hz]))).aestronglyMeasurable
        measurableSet_Ioi)]
    refine hw_int.congr ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with x hx
    rw [← Real.rpow_natCast ((x + 1) ^ (-(2 : ℝ))) 2,
      ← Real.rpow_mul (by linarith [Set.mem_Ioi.mp hx, hz] : (0 : ℝ) ≤ x + 1)]
    congr 1
    norm_num
  have hk_aesm : MeasureTheory.AEStronglyMeasurable k (volume.restrict (Set.Ioi z)) := by
    refine (((SmoothOpen.curry_z (hS.pzIter 2) hθ).continuousOn).mono (by
      intro u hu; exact lt_trans hz (Set.mem_Ioi.mp hu))).aestronglyMeasurable
      measurableSet_Ioi
  have hv_mem : MeasureTheory.MemLp (fun x : ℝ => (x + 1) ^ 2 * k x) 2
      (volume.restrict (Set.Ioi z)) := by
    rw [MeasureTheory.memLp_two_iff_integrable_sq (by
      exact (((continuousOn_id.add continuousOn_const).pow 2).aestronglyMeasurable
        measurableSet_Ioi).mul hk_aesm)]
    refine hKz.congr (Eventually.of_forall fun x => ?_)
    simp only [Pi.pow_apply]
    ring
  -- (5) integrability of `k` on `(z,∞)`
  have hk_int : MeasureTheory.IntegrableOn k (Set.Ioi z) := by
    have hmul := MeasureTheory.MemLp.mul (p := 2) (q := 2) (r := 1) hu_mem hv_mem
    have hint : MeasureTheory.Integrable
        (fun x : ℝ => (x + 1) ^ (-(2 : ℝ)) * ((x + 1) ^ 2 * k x))
        (volume.restrict (Set.Ioi z)) :=
      MeasureTheory.memLp_one_iff_integrable.mp hmul
    refine MeasureTheory.IntegrableOn.congr_fun hint (fun x hx => ?_) measurableSet_Ioi
    have hxpos : (0 : ℝ) < x + 1 := by linarith [Set.mem_Ioi.mp hx, hz]
    have hne : (x + 1) ^ 2 ≠ 0 := pow_ne_zero 2 (by linarith)
    rw [Real.rpow_neg (le_of_lt hxpos)]
    have h2 : (x + 1) ^ (2 : ℝ) = (x + 1) ^ 2 := by
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    rw [h2]
    exact inv_mul_cancel_left₀ hne (k x)
  -- (6) the limit of `∂_zΨ(·,θ)` at `∞`
  have hlim : Filter.Tendsto (fun Y : ℝ => Work.Spaces.pz Ψ Y θ) Filter.atTop
      (nhds (Work.Spaces.pz Ψ z θ + ∫ x in Set.Ioi z, k x)) := by
    have hftc : ∀ Y : ℝ, z ≤ Y → Work.Spaces.pz Ψ Y θ
        = Work.Spaces.pz Ψ z θ + ∫ y in z..Y, k y := by
      intro Y hY
      have hd : ∀ y ∈ Set.uIcc z Y, HasDerivAt (fun s : ℝ => Work.Spaces.pz Ψ s θ) (k y) y := by
        intro y hy
        have hy0 : 0 < y := by
          rw [Set.mem_uIcc] at hy
          rcases hy with ⟨h1, _⟩ | ⟨h1, _⟩ <;> linarith
        exact hderiv y hy0
      have hii : IntervalIntegrable k volume z Y := by
        rw [intervalIntegrable_iff, Set.uIoc_of_le hY]
        exact hk_int.mono_set (by intro x hx; exact hx.1)
      have h1 := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hii
      linarith [h1]
    have h2 : Filter.Tendsto (fun Y : ℝ => ∫ y in z..Y, k y) Filter.atTop
        (nhds (∫ x in Set.Ioi z, k x)) :=
      MeasureTheory.intervalIntegral_tendsto_integral_Ioi z hk_int Filter.tendsto_id
    refine Filter.Tendsto.congr' ?_ (h2.const_add _)
    filter_upwards [Filter.eventually_ge_atTop z] with Y hY
    exact (hftc Y hY).symm
  -- (7) the limit is zero, by the mean value theorem along a sequence
  have hL0 : Work.Spaces.pz Ψ z θ + ∫ x in Set.Ioi z, k x = 0 := by
    have hmvt : ∀ n : ℕ, ∃ ξ ∈ Set.Ioo ((n : ℝ) + z + 1) ((n : ℝ) + z + 2),
        Work.Spaces.pz Ψ ξ θ = Ψ ((n : ℝ) + z + 2) θ - Ψ ((n : ℝ) + z + 1) θ := by
      intro n
      have hab : (n : ℝ) + z + 1 < (n : ℝ) + z + 2 := by linarith
      have hcont : ContinuousOn (fun s : ℝ => Ψ s θ)
          (Set.Icc ((n : ℝ) + z + 1) ((n : ℝ) + z + 2)) :=
        ((SmoothOpen.curry_z hS hθ).continuousOn).mono (by
          intro s hs
          rw [Set.mem_Icc] at hs
          exact lt_of_lt_of_le (by linarith : (0 : ℝ) < (n : ℝ) + z + 1) hs.1)
      have hdiff : ∀ x ∈ Set.Ioo ((n : ℝ) + z + 1) ((n : ℝ) + z + 2),
          HasDerivAt (fun s : ℝ => Ψ s θ) (Work.Spaces.pz Ψ x θ) x := by
        intro x hx
        exact hslice_deriv x (by linarith [hx.1])
      obtain ⟨c, hc, hcval⟩ := exists_hasDerivAt_eq_slope (fun s : ℝ => Ψ s θ)
        (fun s => Work.Spaces.pz Ψ s θ) hab hcont hdiff
      refine ⟨c, hc, ?_⟩
      have hden : ((n : ℝ) + z + 2) - ((n : ℝ) + z + 1) = 1 := by ring
      rw [hden, div_one] at hcval
      exact hcval
    choose ξ hξmem hξval using hmvt
    have hξtend : Filter.Tendsto ξ Filter.atTop Filter.atTop := by
      have h1 : Filter.Tendsto (fun n : ℕ => (n : ℝ) + z + 1) Filter.atTop Filter.atTop := by
        have h2 := Filter.tendsto_atTop_add_const_right Filter.atTop (1 : ℝ)
          (Filter.tendsto_atTop_add_const_right Filter.atTop z tendsto_natCast_atTop_atTop)
        simpa only [add_assoc] using h2
      refine Filter.tendsto_atTop_mono (f := fun n : ℕ => (n : ℝ) + z + 1) (fun n => ?_) h1
      linarith [(hξmem n).1]
    have hval : Filter.Tendsto (fun n : ℕ => Work.Spaces.pz Ψ (ξ n) θ) Filter.atTop (nhds 0) := by
      have h1 : Filter.Tendsto (fun n : ℕ => Ψ ((n : ℝ) + z + 2) θ) Filter.atTop (nhds 0) :=
        (h.dec θ ⟨hθ.1.le, hθ.2.le⟩).comp
          (Filter.tendsto_atTop_add_const_right Filter.atTop (2 : ℝ)
            (Filter.tendsto_atTop_add_const_right Filter.atTop z tendsto_natCast_atTop_atTop))
      have h2 : Filter.Tendsto (fun n : ℕ => Ψ ((n : ℝ) + z + 1) θ) Filter.atTop (nhds 0) :=
        (h.dec θ ⟨hθ.1.le, hθ.2.le⟩).comp
          (Filter.tendsto_atTop_add_const_right Filter.atTop (1 : ℝ)
            (Filter.tendsto_atTop_add_const_right Filter.atTop z tendsto_natCast_atTop_atTop))
      have h3 : Filter.Tendsto
          (fun n : ℕ => Ψ ((n : ℝ) + z + 2) θ - Ψ ((n : ℝ) + z + 1) θ)
          Filter.atTop (nhds 0) := by
        have := h1.sub h2
        simpa using this
      exact Filter.Tendsto.congr' (Filter.Eventually.of_forall fun n => (hξval n).symm) h3
    exact tendsto_nhds_unique (hlim.comp hξtend) hval
  have hz_eq : Work.Spaces.pz Ψ z θ = -(∫ x in Set.Ioi z, k x) := by linarith [hL0]
  -- (8) Cauchy–Schwarz
  have hcs := Work.Spaces.cs_integral (u := fun x : ℝ => (x + 1) ^ (-(2 : ℝ)))
    (v := fun x : ℝ => (x + 1) ^ 2 * k x) (s := Set.Ioi z) hu_mem hv_mem
  have hleft : (∫ x in Set.Ioi z, (x + 1) ^ (-(2 : ℝ)) * ((x + 1) ^ 2 * k x))
      = ∫ x in Set.Ioi z, k x := by
    refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
    have hxpos : (0 : ℝ) < x + 1 := by linarith [Set.mem_Ioi.mp hx, hz]
    have hne : (x + 1) ^ 2 ≠ 0 := pow_ne_zero 2 (by linarith)
    rw [Real.rpow_neg (le_of_lt hxpos)]
    have h2 : (x + 1) ^ (2 : ℝ) = (x + 1) ^ 2 := by
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    rw [h2]
    exact inv_mul_cancel_left₀ hne (k x)
  have hright2 : (∫ x in Set.Ioi z, ((x + 1) ^ 2 * k x) ^ 2)
      ≤ ∫ u in Work.Spaces.Iz, (1 + u) ^ 4 * (Work.Spaces.pzIter 2 Ψ u θ) ^ 2 := by
    have hsub : Set.Ioi z ⊆ Work.Spaces.Iz := by
      intro u hu
      rw [Work.Spaces.Iz]
      exact le_of_lt (lt_trans hz (Set.mem_Ioi.mp hu))
    have h1 : (∫ x in Set.Ioi z, ((x + 1) ^ 2 * k x) ^ 2)
        = ∫ x in Set.Ioi z, (1 + x) ^ 4 * (Work.Spaces.pzIter 2 Ψ x θ) ^ 2 := by
      refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
      rw [hkdef]; ring
    rw [h1]
    exact MeasureTheory.setIntegral_mono_set hInt
      (Filter.Eventually.of_forall fun u => by positivity)
      (Filter.Eventually.of_forall hsub)
  rw [hz_eq, neg_sq]
  have h' : (∫ x in Set.Ioi z, k x) ^ 2
      ≤ (∫ x in Set.Ioi z, ((x + 1) ^ (-(2 : ℝ))) ^ 2)
        * (∫ x in Set.Ioi z, ((x + 1) ^ 2 * k x) ^ 2) := by
    rw [hleft] at hcs
    exact hcs
  exact le_trans h' (mul_le_mul_of_nonneg_left hright2
    (integral_nonneg fun x => by positivity))


/-! ## The `∂_zΨ` slice (the hard one) -/

theorem integrableOn_zpz_sigma' {α : ℝ} {F Ψ : ℝ → ℝ → ℝ} (h : Hon α F Ψ) {z : ℝ}
    (hz : 0 < z) :
    IntegrableOn (fun θ => (Work.Spaces.pz Ψ z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      Work.Spaces.Iθ := by
  set P : ℝ → ℝ≥0∞ := fun θ => ∫⁻ u in Work.Spaces.Iz,
    ENNReal.ofReal ((1 + u) ^ 4 * (Work.Spaces.pzIter 2 Ψ u θ) ^ 2) with hPdef
  have hA := HonZSecondSwapSigma α F Ψ h
  have hstep : (∫⁻ θ in Work.Spaces.Iθ, ∫⁻ u in Work.Spaces.Iz,
        ENNReal.ofReal ((1 + u) ^ 4 * (Work.Spaces.pzIter 2 Ψ u θ) ^ 2
          * Work.FTS.EllipticEst.sEta θ))
      = ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (Work.FTS.EllipticEst.sEta θ) * P θ := by
    refine MeasureTheory.lintegral_congr fun θ => ?_
    rw [hPdef, ← MeasureTheory.lintegral_const_mul'
      (ENNReal.ofReal (Work.FTS.EllipticEst.sEta θ)) _ ENNReal.ofReal_ne_top]
    refine MeasureTheory.lintegral_congr fun u => ?_
    rw [ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ (1 + u) ^ 4
      * (Work.Spaces.pzIter 2 Ψ u θ) ^ 2), mul_comm]
  rw [hstep] at hA
  -- a.e. finiteness of `P`
  have hP : AEMeasurable P (volume.restrict Work.Spaces.Iθ) := by
    rw [hPdef]
    have hjoint : AEMeasurable (fun p : ℝ × ℝ =>
        ENNReal.ofReal ((1 + p.1) ^ 4 * (Work.Spaces.pzIter 2 Ψ p.1 p.2) ^ 2))
        ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) := by
      have hS := smoothOpen_of_forall h.sm
      have hc : ContinuousOn (fun p : ℝ × ℝ =>
          (1 + p.1) ^ 4 * (Work.Spaces.pzIter 2 Ψ p.1 p.2) ^ 2)
          (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
        (((continuousOn_const.add continuousOn_fst).pow 4).mul ((hS.pzIter 2).continuousOn.pow 2))
      have haesm : AEMeasurable (fun p : ℝ × ℝ =>
          (1 + p.1) ^ 4 * (Work.Spaces.pzIter 2 Ψ p.1 p.2) ^ 2)
          ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) :=
        (Work.Spaces.aesm_of_continuousOn_Qd _ hc).aemeasurable
      exact ENNReal.measurable_ofReal.comp_aemeasurable haesm
    exact AEMeasurable.lintegral_prod_left hjoint
  have haeQ : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
      ENNReal.ofReal (Work.FTS.EllipticEst.sEta θ) * P θ < ⊤ :=
    ae_lt_top' ((ENNReal.measurable_ofReal.comp_aemeasurable aesm_sEta'.aemeasurable).mul hP)
      (ne_of_lt hA)
  have haeP : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ), P θ < ⊤ := by
    filter_upwards [haeQ, ae_mem_Ioo_Iθ'] with θ hQ hθ
    have hσ : ENNReal.ofReal (Work.FTS.EllipticEst.sEta θ) ≠ 0 :=
      ENNReal.ofReal_ne_zero_iff.mpr (lt_of_lt_of_le zero_lt_one (one_le_sEta_Ioo hθ))
    rcases ENNReal.mul_lt_top_iff.mp hQ with ⟨-, h2⟩ | h1 | h2
    · exact h2
    · exact absurd h1 hσ
    · rw [h2]; exact ENNReal.zero_lt_top
  -- the weight integral of the Cauchy–Schwarz step
  set Cz : ℝ := ∫ x in Set.Ioi z, ((x + 1) ^ (-(2 : ℝ))) ^ 2 with hCzdef
  have hCz0 : 0 ≤ Cz := by
    rw [hCzdef]
    exact integral_nonneg fun x => by positivity
  -- the bound
  have hbound : (∫⁻ θ in Work.Spaces.Iθ,
        ENNReal.ofReal ((Work.Spaces.pz Ψ z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ))
      ≤ ENNReal.ofReal Cz *
        (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (Work.FTS.EllipticEst.sEta θ) * P θ) := by
    rw [← MeasureTheory.lintegral_const_mul' (ENNReal.ofReal Cz)
      (fun θ => ENNReal.ofReal (Work.FTS.EllipticEst.sEta θ) * P θ) ENNReal.ofReal_ne_top]
    refine MeasureTheory.lintegral_mono_ae ?_
    filter_upwards [haeP, ae_mem_Ioo_Iθ'] with θ hθP hθIoo
    have haesm : AEStronglyMeasurable
        (fun u : ℝ => (1 + u) ^ 4 * (Work.Spaces.pzIter 2 Ψ u θ) ^ 2)
        (volume.restrict Work.Spaces.Iz) := by
      have hS := smoothOpen_of_forall h.sm
      have hc : ContinuousOn (fun p : ℝ × ℝ =>
          (1 + p.1) ^ 4 * (Work.Spaces.pzIter 2 Ψ p.1 p.2) ^ 2)
          (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
        (((continuousOn_const.add continuousOn_fst).pow 4).mul ((hS.pzIter 2).continuousOn.pow 2))
      have hmap : Set.MapsTo (fun u : ℝ => (u, θ)) (Set.Ioi 0)
          (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := fun u hu => ⟨hu, hθIoo.1, hθIoo.2⟩
      have hg : ContinuousOn (fun u : ℝ => (u, θ)) (Set.Ioi 0) := by fun_prop
      have hcomp := hc.comp hg hmap
      have hms : volume.restrict Work.Spaces.Iz = volume.restrict (Set.Ioi 0) := by
        rw [Work.Spaces.Iz]
        exact MeasureTheory.Measure.restrict_congr_set (MeasureTheory.Ioi_ae_eq_Ici).symm
      rw [hms]
      exact hcomp.aestronglyMeasurable measurableSet_Ioi
    have hInt : IntegrableOn
        (fun u : ℝ => (1 + u) ^ 4 * (Work.Spaces.pzIter 2 Ψ u θ) ^ 2) Work.Spaces.Iz :=
      (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable haesm
        (Eventually.of_forall fun u => by positivity)).mp (ne_of_lt hθP)
    have hB := pz_slice_sq_le' h hz hθIoo hInt
    have hPeq : ENNReal.ofReal (∫ u in Work.Spaces.Iz,
        (1 + u) ^ 4 * (Work.Spaces.pzIter 2 Ψ u θ) ^ 2) = P θ := by
      rw [hPdef]
      exact MeasureTheory.ofReal_integral_eq_lintegral_ofReal hInt
        (Eventually.of_forall fun u => by positivity)
    have hs := sEta_nonneg_Ioo hθIoo
    calc ENNReal.ofReal ((Work.Spaces.pz Ψ z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
        ≤ ENNReal.ofReal (Cz *
            (∫ u in Work.Spaces.Iz, (1 + u) ^ 4 * (Work.Spaces.pzIter 2 Ψ u θ) ^ 2)
            * Work.FTS.EllipticEst.sEta θ) := by
          refine ENNReal.ofReal_le_ofReal ?_
          exact mul_le_mul_of_nonneg_right hB hs
      _ = ENNReal.ofReal Cz * P θ
            * ENNReal.ofReal (Work.FTS.EllipticEst.sEta θ) := by
          rw [ENNReal.ofReal_mul (mul_nonneg hCz0 (integral_nonneg fun u => by positivity))]
          rw [ENNReal.ofReal_mul hCz0]
          rw [hPeq]
      _ = ENNReal.ofReal Cz
            * (ENNReal.ofReal (Work.FTS.EllipticEst.sEta θ) * P θ) := by ring
  have hfin : (∫⁻ θ in Work.Spaces.Iθ,
      ENNReal.ofReal ((Work.Spaces.pz Ψ z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)) < ⊤ :=
    lt_of_le_of_lt hbound (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hA)
  exact (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable
    (((SmoothOpen.aesm_slice_pzIter (smoothOpen_of_forall h.sm) 1 hz).pow 2).mul aesm_sEta')
    (by filter_upwards [ae_mem_Iθ'] with θ hθ
        exact mul_nonneg (sq_nonneg _) (sEta_nonneg hθ))).mp (ne_of_lt hfin)

theorem integrableOn_sq_pz' {α : ℝ} {F Ψ : ℝ → ℝ → ℝ} (h : Hon α F Ψ) {z : ℝ} (hz : 0 < z) :
    IntegrableOn (fun θ => (Work.Spaces.pz Ψ z θ) ^ 2) Work.Spaces.Iθ :=
  integrableOn_sq_of_sigma (SmoothOpen.aesm_slice_pzIter (smoothOpen_of_forall h.sm) 1 hz)
    (integrableOn_zpz_sigma' h hz)

/-! ## The `Ψ / cos θ` slice -/

theorem contDiffOn_slice_tan_mul {α : ℝ} {F Ψ : ℝ → ℝ → ℝ} (h : Hon α F Ψ) {z : ℝ}
    (hz : 0 < z) (n : ℕ) :
    ContDiffOn ℝ n (fun θ => Real.tan θ * Ψ z θ) (Set.Ioo 0 (Real.pi / 2)) := by
  have htan : ContDiffOn ℝ n (fun θ : ℝ => Real.tan θ) (Set.Ioo 0 (Real.pi / 2)) := by
    have hfun : (fun θ : ℝ => Real.tan θ) = fun θ : ℝ => Real.sin θ / Real.cos θ := by
      funext θ; exact Real.tan_eq_sin_div_cos θ
    rw [hfun]
    refine ContDiffOn.div (Real.contDiff_sin.contDiffOn) (Real.contDiff_cos.contDiffOn) ?_
    intro θ hθ
    exact ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩)
  have hψ : ContDiffOn ℝ n (fun θ => Ψ z θ) (Set.Ioo 0 (Real.pi / 2)) := by
    have h2 := h.sm n
    have hmap : Set.MapsTo (fun θ : ℝ => (z, θ)) (Set.Ioo 0 (Real.pi / 2))
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := fun θ hθ => ⟨hz, hθ⟩
    exact h2.comp (by fun_prop) hmap
  exact htan.mul hψ

theorem aesm_pth_tan_mul {α : ℝ} {F Ψ : ℝ → ℝ → ℝ} (h : Hon α F Ψ) {z : ℝ} (hz : 0 < z) :
    AEStronglyMeasurable (fun θ => Work.Spaces.pth (fun z θ => Real.tan θ * Ψ z θ) z θ)
      (volume.restrict Work.Spaces.Iθ) := by
  have hslice := contDiffOn_slice_tan_mul h hz 1
  have h1 : ContDiffOn ℝ 0 (deriv (fun θ => Real.tan θ * Ψ z θ))
      (Set.Ioo 0 (Real.pi / 2)) :=
    hslice.deriv_of_isOpen isOpen_Ioo (by norm_num)
  rw [restrict_Iθ_eq_Ioo]
  have hfun : (fun θ => Work.Spaces.pth (fun z θ => Real.tan θ * Ψ z θ) z θ)
      = deriv (fun θ => Real.tan θ * Ψ z θ) := rfl
  rw [hfun]
  exact h1.continuousOn.aestronglyMeasurable measurableSet_Ioo

theorem continuousOn_pth_tan_mul {α : ℝ} {F Ψ : ℝ → ℝ → ℝ} (h : Hon α F Ψ) {z : ℝ}
    (hz : 0 < z) :
    ContinuousOn (fun θ => Work.Spaces.pth (fun z θ => Real.tan θ * Ψ z θ) z θ)
      (Set.Ioo 0 (Real.pi / 2)) := by
  have hslice := contDiffOn_slice_tan_mul h hz 1
  have h1 : ContDiffOn ℝ 0 (deriv (fun θ => Real.tan θ * Ψ z θ))
      (Set.Ioo 0 (Real.pi / 2)) :=
    hslice.deriv_of_isOpen isOpen_Ioo (by norm_num)
  have hfun : (fun θ => Work.Spaces.pth (fun z θ => Real.tan θ * Ψ z θ) z θ)
      = deriv (fun θ => Real.tan θ * Ψ z θ) := rfl
  rw [hfun]
  exact h1.continuousOn

theorem sq_sum_five_le' (a b c d e : ℝ) :
    (a + b + c + d + e) ^ 2 ≤ 5 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 + e ^ 2) := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - d), sq_nonneg (a - e),
    sq_nonneg (b - c), sq_nonneg (b - d), sq_nonneg (b - e), sq_nonneg (c - d),
    sq_nonneg (c - e), sq_nonneg (d - e)]

/-- The pointwise identity for `∂_θ(tan θ Ψ)`. -/
theorem pth_tan_eq {α : ℝ} {F Ψ : ℝ → ℝ → ℝ} (h : Hon α F Ψ) {z θ : ℝ} (hz : 0 < z)
    (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2) :
    Work.Spaces.pth (fun z θ => Real.tan θ * Ψ z θ) z θ
      = α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) + F z θ
        + α * (5 + α) * (z * Work.Spaces.pz Ψ z θ)
        + Work.Spaces.pthIter 2 Ψ z θ + 6 * Ψ z θ := by
  have h0 := h.eq_solve hz hθ0 hθ1
  linarith [h0]

theorem integrableOn_sq_sEta_pth_tan' {α : ℝ} {F Ψ : ℝ → ℝ → ℝ} (h : Hon α F Ψ) {z : ℝ}
    (hz : 0 < z) :
    IntegrableOn (fun θ => (Work.Spaces.pth (fun z θ => Real.tan θ * Ψ z θ) z θ) ^ 2
      * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ := by
  have hA := hon_memA_sigma h hz
  have hB := hon_memB_sigma h hz
  have hF := hon_memF_sigma h hz
  have hG := integrableOn_zpz_sigma' h hz
  have hPsi := integrableOn_sq_sEta_psi h hz
  -- the five weighted squares
  have h1 : IntegrableOn (fun θ => (α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) ^ 2
      * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ := by
    have := hA.const_mul ((α ^ 2 * z ^ 2) ^ 2)
    refine this.congr (Eventually.of_forall fun θ => ?_)
    ring
  have h2 : IntegrableOn (fun θ => (F z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      Work.Spaces.Iθ := hF
  have h3 : IntegrableOn (fun θ => (α * (5 + α) * (z * Work.Spaces.pz Ψ z θ)) ^ 2
      * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ := by
    have := hG.const_mul ((α * (5 + α) * z) ^ 2)
    refine this.congr (Eventually.of_forall fun θ => ?_)
    ring
  have h4 : IntegrableOn (fun θ => (Work.Spaces.pthIter 2 Ψ z θ) ^ 2
      * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ := hB
  have h5 : IntegrableOn (fun θ => (6 * Ψ z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      Work.Spaces.Iθ := by
    have := hPsi.const_mul 36
    refine this.congr (Eventually.of_forall fun θ => ?_)
    ring
  have hmaj : IntegrableOn (fun θ => 5 * ((α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) ^ 2
      * Work.FTS.EllipticEst.sEta θ
      + (F z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ
      + (α * (5 + α) * (z * Work.Spaces.pz Ψ z θ)) ^ 2 * Work.FTS.EllipticEst.sEta θ
      + (Work.Spaces.pthIter 2 Ψ z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ
      + (6 * Ψ z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)) Work.Spaces.Iθ :=
    ((((h1.add h2).add h3).add h4).add h5).const_mul 5
  refine hmaj.mono' ?_ ?_
  · -- a.e. strong measurability
    exact ((aesm_pth_tan_mul h hz).pow 2).mul aesm_sEta'
  · filter_upwards [ae_mem_Ioo_Iθ'] with θ hθ
    have hs := sEta_nonneg_Ioo hθ
    have hid := pth_tan_eq h hz hθ.1 hθ.2
    have hsq := sq_sum_five_le' (α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) (F z θ)
      (α * (5 + α) * (z * Work.Spaces.pz Ψ z θ)) (Work.Spaces.pthIter 2 Ψ z θ)
      (6 * Ψ z θ)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) hs)]
    rw [hid]
    have h5 : 5 * ((α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) ^ 2 * Work.FTS.EllipticEst.sEta θ
        + (F z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ
        + (α * (5 + α) * (z * Work.Spaces.pz Ψ z θ)) ^ 2 * Work.FTS.EllipticEst.sEta θ
        + (Work.Spaces.pthIter 2 Ψ z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ
        + (6 * Ψ z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
        = 5 * ((α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) ^ 2
            + (F z θ) ^ 2
            + (α * (5 + α) * (z * Work.Spaces.pz Ψ z θ)) ^ 2
            + (Work.Spaces.pthIter 2 Ψ z θ) ^ 2
            + (6 * Ψ z θ) ^ 2) * Work.FTS.EllipticEst.sEta θ := by ring
    rw [h5]
    exact mul_le_mul_of_nonneg_right hsq hs

theorem integrableOn_abs_pth_tan' {α : ℝ} {F Ψ : ℝ → ℝ → ℝ} (h : Hon α F Ψ) {z : ℝ}
    (hz : 0 < z) :
    IntegrableOn (fun θ => |Work.Spaces.pth (fun z θ => Real.tan θ * Ψ z θ) z θ|)
      Work.Spaces.Iθ :=
  Work.FTS.EllipticEst.SgamBound.integrableOn_abs_of_sq_mul_sEta
    (continuousOn_pth_tan_mul h hz) (integrableOn_sq_sEta_pth_tan' h hz)

theorem integrableOn_psi_div_cos_sq' {α : ℝ} {F Ψ : ℝ → ℝ → ℝ} (h : Hon α F Ψ) {z : ℝ}
    (hz : 0 < z) :
    IntegrableOn (fun θ => (Ψ z θ / Real.cos θ) ^ 2) Work.Spaces.Iθ := by
  -- the bounds on `Ψ`
  have hpsi := slice_psi_bdd h hz
  set Cψ : ℝ := |Ψ z (Real.pi / 4)| + (Real.pi / 2) * (|Work.Spaces.pth Ψ z (Real.pi / 4)|
    + ∫ t in Work.Spaces.Iθ, |Work.Spaces.pthIter 2 Ψ z t|) with hCψdef
  have hCψ0 : 0 ≤ Cψ := by
    rw [hCψdef]
    have h1 := integral_nonneg (μ := volume.restrict Work.Spaces.Iθ)
      (f := fun t => |Work.Spaces.pthIter 2 Ψ z t|) (fun t => abs_nonneg _)
    have h2 : (0 : ℝ) ≤ Real.pi / 2 := by positivity
    have h3 : 0 ≤ |Work.Spaces.pth Ψ z (Real.pi / 4)|
        + ∫ t in Work.Spaces.Iθ, |Work.Spaces.pthIter 2 Ψ z t| := by
      linarith [abs_nonneg (Work.Spaces.pth Ψ z (Real.pi / 4))]
    have h4 := mul_nonneg h2 h3
    linarith [abs_nonneg (Ψ z (Real.pi / 4))]
  -- `G = ∂_θ(tan θ · Ψ)`
  set G : ℝ → ℝ := fun θ => Work.Spaces.pth (fun z θ => Real.tan θ * Ψ z θ) z θ with hGdef
  have hGσ : IntegrableOn (fun θ => (G θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ := by
    rw [hGdef]
    exact integrableOn_sq_sEta_pth_tan' h hz
  have hGabs : IntegrableOn (fun θ => |G θ|) Work.Spaces.Iθ := by
    rw [hGdef]
    exact integrableOn_abs_pth_tan' h hz
  have hGint : IntegrableOn (fun θ => G θ) Work.Spaces.Iθ := by
    have hmaj : IntegrableOn (fun θ => 1 + (G θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
        Work.Spaces.Iθ := (integrableOn_const_Iθ' 1).add hGσ
    refine hmaj.mono' ?_ ?_
    · exact aesm_pth_tan_mul h hz
    · filter_upwards [ae_mem_Ioo_Iθ'] with θ hθ
      have hs := one_le_sEta_Ioo hθ
      rw [Real.norm_eq_abs]
      have h2 : |G θ| ≤ 1 + (G θ) ^ 2 := by
        nlinarith [sq_nonneg (|G θ| - 1), abs_nonneg (G θ), sq_abs (G θ)]
      have h3 : (G θ) ^ 2 ≤ (G θ) ^ 2 * Work.FTS.EllipticEst.sEta θ := by
        have := mul_le_mul_of_nonneg_left hs (sq_nonneg (G θ))
        simpa using this
      linarith
  have hGii : IntervalIntegrable G volume 0 (Real.pi / 2) := by
    rw [intervalIntegrable_iff, Set.uIoc_of_le (by positivity : (0 : ℝ) ≤ Real.pi / 2)]
    exact hGint.mono_set Set.Ioc_subset_Icc_self
  have hGiiAbs : IntervalIntegrable (fun t => |G t|) volume 0 (Real.pi / 2) := by
    rw [intervalIntegrable_iff, Set.uIoc_of_le (by positivity : (0 : ℝ) ≤ Real.pi / 2)]
    exact hGabs.mono_set Set.Ioc_subset_Icc_self
  -- the pointwise bound `|tan θ · Ψ z θ| ≤ |tan (π/4) · Ψ z (π/4)| + ∫ |G|` for `θ > π/4`
  have hΦbound : ∀ θ ∈ Set.Ioo (Real.pi / 4) (Real.pi / 2),
      |Real.tan θ * Ψ z θ| ≤ |Real.tan (Real.pi / 4) * Ψ z (Real.pi / 4)|
        + ∫ t in Work.Spaces.Iθ, |G t| := by
    intro θ hθ
    have hθ' : θ ∈ Set.Ioo 0 (Real.pi / 2) := ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
    have hslice : ContDiffOn ℝ 1 (fun t => Real.tan t * Ψ z t) (Set.Ioo 0 (Real.pi / 2)) :=
      contDiffOn_slice_tan_mul h hz 1
    have hpi4 : Real.pi / 4 ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
      refine ⟨by positivity, ?_⟩; nlinarith [Real.pi_pos]
    have hseg : Set.uIcc (Real.pi / 4) θ ⊆ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
      intro x hx
      rw [Set.mem_uIcc] at hx
      rcases hx with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact ⟨lt_of_lt_of_le hpi4.1 h1, lt_of_le_of_lt h2 hθ.2⟩
      · exact ⟨lt_of_lt_of_le hθ'.1 h1, lt_of_le_of_lt h2 hpi4.2⟩
    have hFTC : (∫ t in (Real.pi / 4)..θ, G t)
        = Real.tan θ * Ψ z θ - Real.tan (Real.pi / 4) * Ψ z (Real.pi / 4) := by
      have hd : ∀ x ∈ Set.uIcc (Real.pi / 4) θ,
          HasDerivAt (fun t => Real.tan t * Ψ z t) (G x) x := by
        intro x hx
        have hxIoo := hseg hx
        have hdiff : DifferentiableAt ℝ (fun t => Real.tan t * Ψ z t) x :=
          (hslice.differentiableOn (one_ne_zero)).differentiableAt (isOpen_Ioo.mem_nhds hxIoo)
        have hfun : deriv (fun t => Real.tan t * Ψ z t) x = G x := by
          rw [hGdef]; rfl
        rw [← hfun]
        exact hdiff.hasDerivAt
      have hii : IntervalIntegrable G volume (Real.pi / 4) θ :=
        hGii.mono_set (by
          intro x hx
          rw [Set.mem_uIcc] at hx ⊢
          rcases hx with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · exact Or.inl ⟨by linarith [h1, Real.pi_pos], by linarith [h2, hθ.2]⟩
          · exact Or.inl ⟨by linarith [h1, hθ'.1], by linarith [h2, Real.pi_pos]⟩)
      exact intervalIntegral.integral_eq_sub_of_hasDerivAt hd hii
    have hval : Real.tan θ * Ψ z θ = Real.tan (Real.pi / 4) * Ψ z (Real.pi / 4)
        + ∫ t in (Real.pi / 4)..θ, G t := by linarith [hFTC]
    calc |Real.tan θ * Ψ z θ|
        = |Real.tan (Real.pi / 4) * Ψ z (Real.pi / 4) + ∫ t in (Real.pi / 4)..θ, G t| := by
          rw [hval]
      _ ≤ |Real.tan (Real.pi / 4) * Ψ z (Real.pi / 4)| + |∫ t in (Real.pi / 4)..θ, G t| :=
          abs_add_le _ _
      _ ≤ |Real.tan (Real.pi / 4) * Ψ z (Real.pi / 4)| + ∫ t in Work.Spaces.Iθ, |G t| := by
          have := abs_intervalIntegral_le_setIntegral' hpi4 hθ' hGiiAbs
          linarith
  -- the constant bound on `|Ψ / cos|`
  set D : ℝ := |Real.tan (Real.pi / 4) * Ψ z (Real.pi / 4)|
    + ∫ t in Work.Spaces.Iθ, |G t| with hDdef
  have hD0 : 0 ≤ D := by
    rw [hDdef]
    have h1 := integral_nonneg (μ := volume.restrict Work.Spaces.Iθ)
      (f := fun t => |G t|) (fun t => abs_nonneg _)
    linarith [abs_nonneg (Real.tan (Real.pi / 4) * Ψ z (Real.pi / 4))]
  have hK : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), |Ψ z θ / Real.cos θ| ≤ max (2 * Cψ) (2 * D) := by
    intro θ hθ
    by_cases hle : θ ≤ Real.pi / 4
    · -- `θ ≤ π/4`: `cos θ ≥ 1/2`
      have hmem : θ ∈ Set.Icc (0 : ℝ) (Real.pi) :=
        ⟨hθ.1.le, by linarith [hθ.2, Real.pi_pos]⟩
      have hmem4 : Real.pi / 4 ∈ Set.Icc (0 : ℝ) (Real.pi) :=
        ⟨by positivity, by linarith [Real.pi_pos]⟩
      have hcos : Real.cos (Real.pi / 4) ≤ Real.cos θ :=
        Real.strictAntiOn_cos.antitoneOn hmem hmem4 hle
      have hcos4 : Real.cos (Real.pi / 4) = Real.sqrt 2 / 2 := Real.cos_pi_div_four
      have hhalf : (1 / 2 : ℝ) ≤ Real.cos θ := by
        rw [hcos4] at hcos
        nlinarith [Real.one_lt_sqrt_two, hcos]
      have habs := hpsi θ hθ
      have hcospos : 0 < Real.cos θ := by linarith
      have h2cos : (1 : ℝ) ≤ 2 * Real.cos θ := by linarith
      have h1 : |Ψ z θ / Real.cos θ| ≤ 2 * Cψ := by
        rw [abs_div, abs_of_pos hcospos, div_le_iff₀ hcospos]
        nlinarith [habs, hCψ0, h2cos, abs_nonneg (Ψ z θ)]
      exact le_trans h1 (le_max_left _ _)
    · -- `θ > π/4`: `sin θ ≥ 1/2`
      have hlt : Real.pi / 4 < θ := lt_of_not_ge hle
      have hmem : θ ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) :=
        ⟨by linarith [hθ.1, Real.pi_pos], hθ.2.le⟩
      have hmem4 : Real.pi / 4 ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) :=
        ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
      have hsin : Real.sin (Real.pi / 4) ≤ Real.sin θ :=
        Real.strictMonoOn_sin.monotoneOn hmem4 hmem hlt.le
      have hsin4 : Real.sin (Real.pi / 4) = Real.sqrt 2 / 2 := Real.sin_pi_div_four
      have hhalf : (1 / 2 : ℝ) ≤ Real.sin θ := by
        rw [hsin4] at hsin
        nlinarith [Real.one_lt_sqrt_two, hsin]
      have hΦ := hΦbound θ ⟨hlt, hθ.2⟩
      have hsinpos : 0 < Real.sin θ := by linarith
      have hcospos : 0 < Real.cos θ :=
        Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
      have heq : Real.tan θ * Ψ z θ = Real.sin θ * (Ψ z θ / Real.cos θ) := by
        rw [Real.tan_eq_sin_div_cos]; field_simp
      rw [heq, abs_mul, abs_of_pos hsinpos] at hΦ
      have hΦ' : Real.sin θ * |Ψ z θ| ≤ D * Real.cos θ := by
        rw [abs_div, abs_of_pos hcospos] at hΦ
        have hmul := mul_le_mul_of_nonneg_right hΦ hcospos.le
        rwa [mul_assoc, div_mul_cancel₀ _ (ne_of_gt hcospos)] at hmul
      have h1 : |Ψ z θ / Real.cos θ| ≤ 2 * D := by
        rw [abs_div, abs_of_pos hcospos, div_le_iff₀ hcospos]
        nlinarith [hΦ', hhalf, hsinpos, hcospos, hD0, abs_nonneg (Ψ z θ)]
      exact le_trans h1 (le_max_right _ _)
  refine integrableOn_sq_of_aebdd' (u := fun θ => Ψ z θ / Real.cos θ)
    (C := max (2 * Cψ) (2 * D)) ?_ ?_
  · rw [restrict_Iθ_eq_Ioo]
    have hslicePsi : ContDiffOn ℝ 1 (fun θ => Ψ z θ) (Set.Ioo 0 (Real.pi / 2)) := by
      have h2 := h.sm 1
      have hmap : Set.MapsTo (fun θ : ℝ => (z, θ)) (Set.Ioo 0 (Real.pi / 2))
          (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := fun θ hθ => ⟨hz, hθ⟩
      exact h2.comp (by fun_prop) hmap
    exact (hslicePsi.continuousOn.div Real.continuous_cos.continuousOn
      (fun θ hθ => ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩))
      ).aestronglyMeasurable measurableSet_Ioo
  · filter_upwards [ae_mem_Ioo_Iθ'] with θ hθ
    exact hK θ hθ

/-! ## The main statement -/

/-- **The slicewise finiteness of an honest solution.**  For `Hon α F Ψ` and every `z > 0`, all the
`θ`-slice integrals of the derivatives of `Ψ` occurring in the energy identity are honest Bochner
integrals: `∫_θ Ψ²`, `∫_θ (∂_θΨ)²`, `∫_θ (∂_z²Ψ)²`, `∫_θ (∂_zΨ)²` and `∫_θ (Ψ/cos θ)²` are all
integrable functions of `θ` on `Iθ`. -/
theorem HonSliceFinite (α : ℝ) (F Ψ : ℝ → ℝ → ℝ) (h : Hon α F Ψ) :
    ∀ z : ℝ, 0 < z →
      MeasureTheory.IntegrableOn (fun θ => (Ψ z θ) ^ 2) Work.Spaces.Iθ ∧
      MeasureTheory.IntegrableOn (fun θ => (Work.Spaces.pth Ψ z θ) ^ 2) Work.Spaces.Iθ ∧
      MeasureTheory.IntegrableOn (fun θ => (Work.Spaces.pzIter 2 Ψ z θ) ^ 2) Work.Spaces.Iθ ∧
      MeasureTheory.IntegrableOn (fun θ => (Work.Spaces.pz Ψ z θ) ^ 2) Work.Spaces.Iθ ∧
      MeasureTheory.IntegrableOn (fun θ => (Ψ z θ / Real.cos θ) ^ 2) Work.Spaces.Iθ := by
  intro z hz
  exact ⟨integrableOn_sq_psi' h hz, integrableOn_sq_pth' h hz, integrableOn_sq_pzIter2' h hz,
    integrableOn_sq_pz' h hz, integrableOn_psi_div_cos_sq' h hz⟩

end Work.FTS.EllipticEst.Honest
