import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.H2.STBasic
import Submission.Work.FTS.StrongEps.EComparison.L12_sub_HkMem
import Submission.Work.FTS.TransportS.SupDzAux.SdaAux
import Submission.Work.FTS_EllLimOK.Decay.DecayTools
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q

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


theorem ae_mem_Ioo_Iθ' :
    ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ), θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
  rw [restrict_Iθ_eq_Ioo]
  exact ae_restrict_mem measurableSet_Ioo


theorem sEta_nonneg_Ioo {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    0 ≤ Work.FTS.EllipticEst.sEta θ :=
  sEta_nonneg ⟨hθ.1.le, hθ.2.le⟩

theorem one_le_sEta_Ioo {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    1 ≤ Work.FTS.EllipticEst.sEta θ :=
  one_le_sEta hθ

instance instIsFiniteMeasureIθ : IsFiniteMeasure (volume.restrict Work.Spaces.Iθ) :=
  ⟨by rw [Measure.restrict_apply_univ, Work.Spaces.Iθ, Real.volume_Icc]
      exact ENNReal.ofReal_lt_top⟩


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






/-! ## The `∂_zΨ` slice (the hard one) -/



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







/-! ## The main statement -/


end Work.FTS.EllipticEst.Honest
