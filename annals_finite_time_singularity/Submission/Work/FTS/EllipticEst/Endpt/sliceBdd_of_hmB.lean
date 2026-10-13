import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff
import Mathlib.Order.CompletePartialOrder
import Mathlib.Order.Interval.Basic
import Submission.Work.FTS.EllipticEst.remov.SourceBound.sliceTendstoZeroOfMoment
import Submission.Work.FTS.EllipticEst.remov.wsAux
import Submission.Work.FTS.EllipticEst.StraightDefs
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.EllipticEst.mul_w_sin_rpow_sq
import Submission.Work.FTS.EllipticEst.SgamBound.integrableOn_abs_of_sq_mul_sEta

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology Interval
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Endpt

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

variable {Ψ : ℝ → ℝ → ℝ}

/-! ## Slicewise facts for a function smooth on the open strip

The hypotheses of `sliceBdd_of_hmB` are: `Ψ` is smooth on the *open* strip
`(0,∞) × (0,π/2)`, and the second angular derivative `∂_θθΨ` lies in the level-`0` weighted
space `ℋ⁰`, i.e. `(∂_θθΨ · w/ sin(2θ)^{η/2})²` is honestly integrable.  Since the level-`0`
integrand is the single square `(∂_θθΨ)² w² sin(2θ)^{-η}`, for every `z > 0` the slice
`θ ↦ ∂_θθΨ(z,θ)` is integrable against the angular weight `σ = sin(2θ)^{-η}` on `Iθ`; the
fundamental theorem of calculus on the open interval `(0,π/2)` then bounds `∂_θΨ` and, once
more, `Ψ` itself on that interval.

The same argument is carried out for the honest class of
`Submission/Work/FTS/EllipticEst/Honest/HonSliceBdd.lean`; here it is restated for the two
hypotheses actually used, without the Dirichlet data, the orthogonality conditions or the
smoothness of `z²∂_zzΨ`. -/

/-- The `θ`-slices of a function smooth on the open strip `(0,∞) × (0,π/2)` are smooth on
`(0,π/2)`. -/
theorem contDiffOn_slice_of_strip
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry Ψ) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)))
    {z : ℝ} (hz : 0 < z) (n : ℕ) : ContDiffOn ℝ n (fun θ => Ψ z θ) (Set.Ioo 0 (π / 2)) := by
  have hmap : Set.MapsTo (fun θ : ℝ => (z, θ)) (Set.Ioo 0 (π / 2))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := fun θ hθ => ⟨hz, hθ⟩
  exact (hsm n).comp (by fun_prop) hmap

/-- The slice `θ ↦ ∂_θθΨ(z,·)` of the second angular derivative is continuous on the open
interval `(0,π/2)`. -/
theorem continuousOn_pthIter2_of_strip
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry Ψ) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)))
    {z : ℝ} (hz : 0 < z) :
    ContinuousOn (fun θ => Work.Spaces.pthIter 2 Ψ z θ) (Set.Ioo 0 (π / 2)) := by
  have hslice : ContDiffOn ℝ 2 (fun θ => Ψ z θ) (Set.Ioo 0 (π / 2)) :=
    contDiffOn_slice_of_strip hsm hz 2
  have hfun : (fun θ => Work.Spaces.pthIter 2 Ψ z θ)
      = fun θ => deriv (deriv (fun θ' => Ψ z θ')) θ := rfl
  rw [hfun]
  have h1 : ContDiffOn ℝ 1 (deriv (fun θ' => Ψ z θ')) (Set.Ioo 0 (π / 2)) :=
    hslice.deriv_of_isOpen isOpen_Ioo (by norm_num)
  have h2 : ContDiffOn ℝ 0 (deriv (deriv (fun θ' => Ψ z θ'))) (Set.Ioo 0 (π / 2)) :=
    h1.deriv_of_isOpen isOpen_Ioo (by norm_num)
  exact h2.continuousOn

/-- On `Iθ` the level-`0` `HkIntegrand` is the single weighted square
`g² w² σ` with `σ = sEta = sin(2θ)^{-η}` (the mixed-derivative sum of `HkIntegrand` is empty
at level `0`). -/
theorem HkIntegrand_zero_eq_sEta (α : ℝ) (g : ℝ → ℝ → ℝ) (z : ℝ) {θ : ℝ}
    (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Spaces.HkIntegrand α 0 g z θ
      = (g z θ) ^ 2 * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.sEta θ := by
  have hkey : Work.Spaces.HkIntegrand α 0 g z θ
      = (g z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
    simp [Work.Spaces.HkIntegrand]
  rw [hkey]
  exact Work.FTS.EllipticEst.mul_w_sin_rpow_sq (g z θ) (Work.Spaces.w z) hθ

/-- `HkMem α 0 (∂_θθΨ)` gives the slicewise `σ`-weighted integrability of `∂_θθΨ`: for
every `z > 0` the function `θ ↦ (∂_θθΨ(z,θ))² σ θ` is integrable on `Iθ`. -/
theorem integrableOn_pthIter2_sEta_of_HkMem {α : ℝ}
    (hmB : Work.Spaces.HkMem α 0 (Work.Spaces.pthIter 2 Ψ)) {z : ℝ} (hz : 0 < z) :
    MeasureTheory.IntegrableOn
      (fun θ => (Work.Spaces.pthIter 2 Ψ z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      Work.Spaces.Iθ := by
  have hzI : z ∈ Work.Spaces.Iz := le_of_lt hz
  have h1 := hmB.1 z hzI
  have h2 : MeasureTheory.IntegrableOn
      (fun θ => (Work.Spaces.pthIter 2 Ψ z θ) ^ 2 * (Work.Spaces.w z) ^ 2
        * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ :=
    h1.congr_fun (fun θ hθ => HkIntegrand_zero_eq_sEta α (Work.Spaces.pthIter 2 Ψ) z hθ)
      measurableSet_Icc
  have hw' : Work.Spaces.w z ≠ 0 := by
    rw [Work.Spaces.w]
    exact div_ne_zero (pow_ne_zero _ (by linarith)) (pow_ne_zero _ (ne_of_gt hz))
  have h3 := h2.mul_const ((Work.Spaces.w z) ^ 2)⁻¹
  refine h3.congr (Filter.Eventually.of_forall (fun θ => ?_))
  show ((Work.Spaces.pthIter 2 Ψ z θ) ^ 2 * (Work.Spaces.w z) ^ 2
        * Work.FTS.EllipticEst.sEta θ) * ((Work.Spaces.w z) ^ 2)⁻¹
      = (Work.Spaces.pthIter 2 Ψ z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ
  field_simp

/-- `|∂_θθΨ(z,·)|` is integrable on `Iθ`. -/
theorem integrableOn_abs_pthIter2_of_HkMem {α : ℝ}
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry Ψ) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)))
    (hmB : Work.Spaces.HkMem α 0 (Work.Spaces.pthIter 2 Ψ)) {z : ℝ} (hz : 0 < z) :
    MeasureTheory.IntegrableOn (fun θ => |Work.Spaces.pthIter 2 Ψ z θ|) Work.Spaces.Iθ :=
  SgamBound.integrableOn_abs_of_sq_mul_sEta (continuousOn_pthIter2_of_strip hsm hz)
    (integrableOn_pthIter2_sEta_of_HkMem hmB hz)

/-- The absolute value of an interval integral over a subinterval of `(0,π/2)` is bounded by
the set integral of `|f|` over `Iθ`. -/
theorem abs_intervalIntegral_le_setIntegral {f : ℝ → ℝ} {a b : ℝ}
    (ha : a ∈ Set.Ioo (0 : ℝ) (π / 2)) (hb : b ∈ Set.Ioo (0 : ℝ) (π / 2))
    (hI : IntervalIntegrable (fun x => |f x|) volume 0 (π / 2)) :
    |∫ x in a..b, f x| ≤ ∫ x in Work.Spaces.Iθ, |f x| := by
  have hIeq : (∫ x in (0 : ℝ)..(π / 2), |f x|) = ∫ x in Work.Spaces.Iθ, |f x| := by
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

/-- **Boundedness of `∂_θΨ` on a slice.**  For `z > 0`, the first angular derivative of the
slice is bounded by its value at `π/4` plus the total `σ`-weighted `L¹`-mass of `∂_θθΨ`
(the fundamental theorem of calculus on `(0,π/2)`, whose endpoints are not in the open
interval). -/
theorem pth_le_of_strip_HkMem {α : ℝ}
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry Ψ) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)))
    (hmB : Work.Spaces.HkMem α 0 (Work.Spaces.pthIter 2 Ψ)) {z : ℝ} (hz : 0 < z) :
    ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
      |Work.Spaces.pth Ψ z θ| ≤ |Work.Spaces.pth Ψ z (π / 4)|
        + ∫ t in Work.Spaces.Iθ, |Work.Spaces.pthIter 2 Ψ z t| := by
  have hslice : ContDiffOn ℝ 2 (fun θ => Ψ z θ) (Set.Ioo 0 (π / 2)) :=
    contDiffOn_slice_of_strip hsm hz 2
  have hint := integrableOn_abs_pthIter2_of_HkMem hsm hmB hz
  have hIi : IntervalIntegrable (fun t : ℝ => |Work.Spaces.pthIter 2 Ψ z t|)
      volume 0 (π / 2) := by
    rw [intervalIntegrable_iff, Set.uIoc_of_le (by positivity : (0 : ℝ) ≤ π / 2)]
    exact hint.mono_set Set.Ioc_subset_Icc_self
  have h1 : ContDiffOn ℝ 1 (fun t => Work.Spaces.pth Ψ z t) (Set.Ioo 0 (π / 2)) := by
    have hd : ContDiffOn ℝ 1 (deriv (fun θ' => Ψ z θ')) (Set.Ioo 0 (π / 2)) :=
      hslice.deriv_of_isOpen isOpen_Ioo (by norm_num)
    have hfun : (fun t => Work.Spaces.pth Ψ z t) = deriv (fun θ' => Ψ z θ') := rfl
    rwa [hfun]
  intro θ hθ
  have hpi4 : π / 4 ∈ Set.Ioo (0 : ℝ) (π / 2) := by
    refine ⟨by positivity, ?_⟩
    nlinarith [Real.pi_pos]
  have hseg : Set.uIcc (π / 4) θ ⊆ Set.Ioo (0 : ℝ) (π / 2) := by
    intro x hx
    rw [Set.mem_uIcc] at hx
    rcases hx with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨lt_of_lt_of_le hpi4.1 h1, lt_of_le_of_lt h2 hθ.2⟩
    · exact ⟨lt_of_lt_of_le hθ.1 h1, lt_of_le_of_lt h2 hpi4.2⟩
  have hFTC : (∫ t in (π / 4)..θ, Work.Spaces.pthIter 2 Ψ z t)
      = Work.Spaces.pth Ψ z θ - Work.Spaces.pth Ψ z (π / 4) := by
    have := intervalIntegral.integral_deriv_of_contDiffOn_uIcc (h1.mono hseg)
    simpa only [Work.Spaces.pthIter_succ, Work.Spaces.pthIter_zero, Work.Spaces.pth] using this
  have hval : Work.Spaces.pth Ψ z θ
      = Work.Spaces.pth Ψ z (π / 4)
        + ∫ t in (π / 4)..θ, Work.Spaces.pthIter 2 Ψ z t := by linarith [hFTC]
  calc |Work.Spaces.pth Ψ z θ|
      = |Work.Spaces.pth Ψ z (π / 4)
          + ∫ t in (π / 4)..θ, Work.Spaces.pthIter 2 Ψ z t| := by rw [hval]
    _ ≤ |Work.Spaces.pth Ψ z (π / 4)|
          + |∫ t in (π / 4)..θ, Work.Spaces.pthIter 2 Ψ z t| := abs_add_le _ _
    _ ≤ |Work.Spaces.pth Ψ z (π / 4)|
          + ∫ t in Work.Spaces.Iθ, |Work.Spaces.pthIter 2 Ψ z t| := by
        have := abs_intervalIntegral_le_setIntegral hpi4 hθ hIi
        linarith

/-- **Boundedness of `Ψ` on a slice.**  For `z > 0`, the slice is bounded by its value at
`π/4` plus `(π/2)` times the bound of `∂_θΨ` obtained above. -/
theorem psi_le_of_strip_HkMem {α : ℝ}
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry Ψ) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)))
    (hmB : Work.Spaces.HkMem α 0 (Work.Spaces.pthIter 2 Ψ)) {z : ℝ} (hz : 0 < z) :
    ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
      |Ψ z θ| ≤ |Ψ z (π / 4)|
        + (π / 2) * (|Work.Spaces.pth Ψ z (π / 4)|
          + ∫ t in Work.Spaces.Iθ, |Work.Spaces.pthIter 2 Ψ z t|) := by
  have hslice : ContDiffOn ℝ 2 (fun θ => Ψ z θ) (Set.Ioo 0 (π / 2)) :=
    contDiffOn_slice_of_strip hsm hz 2
  have hpth := pth_le_of_strip_HkMem hsm hmB hz
  set B : ℝ := |Work.Spaces.pth Ψ z (π / 4)|
    + ∫ t in Work.Spaces.Iθ, |Work.Spaces.pthIter 2 Ψ z t| with hBdef
  have hB0 : 0 ≤ B := by
    rw [hBdef]
    have := integral_nonneg (μ := volume.restrict Work.Spaces.Iθ)
      (f := fun t => |Work.Spaces.pthIter 2 Ψ z t|) (fun t => abs_nonneg _)
    linarith [abs_nonneg (Work.Spaces.pth Ψ z (π / 4))]
  intro θ hθ
  have hpi4 : π / 4 ∈ Set.Ioo (0 : ℝ) (π / 2) := by
    refine ⟨by positivity, ?_⟩
    nlinarith [Real.pi_pos]
  have hseg : Set.uIcc (π / 4) θ ⊆ Set.Ioo (0 : ℝ) (π / 2) := by
    intro x hx
    rw [Set.mem_uIcc] at hx
    rcases hx with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨lt_of_lt_of_le hpi4.1 h1, lt_of_le_of_lt h2 hθ.2⟩
    · exact ⟨lt_of_lt_of_le hθ.1 h1, lt_of_le_of_lt h2 hpi4.2⟩
  have hFTC : (∫ t in (π / 4)..θ, Work.Spaces.pth Ψ z t) = Ψ z θ - Ψ z (π / 4) := by
    have hc1 : ContDiffOn ℝ 1 (fun t => Ψ z t) (Set.Ioo (0 : ℝ) (π / 2)) :=
      hslice.of_le (by norm_num)
    have := intervalIntegral.integral_deriv_of_contDiffOn_uIcc (hc1.mono hseg)
    simpa only [Work.Spaces.pth] using this
  have hval : Ψ z θ = Ψ z (π / 4) + ∫ t in (π / 4)..θ, Work.Spaces.pth Ψ z t := by
    linarith [hFTC]
  have hbound : (∀ x ∈ Set.uIoc (π / 4) θ, ‖Work.Spaces.pth Ψ z x‖ ≤ B) := by
    intro x hx
    rw [Real.norm_eq_abs]
    refine le_trans (hpth x ?_) le_rfl
    rw [Set.mem_uIoc] at hx
    rcases hx with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨lt_of_lt_of_le hpi4.1 (le_of_lt h1), lt_of_le_of_lt h2 hθ.2⟩
    · exact ⟨lt_of_lt_of_le hθ.1 (le_of_lt h1), lt_of_le_of_lt h2 hpi4.2⟩
  have habs : |θ - π / 4| ≤ π / 2 := by
    rw [abs_sub_le_iff]
    constructor <;> linarith [hθ.1, hθ.2, Real.pi_pos]
  calc |Ψ z θ| = |Ψ z (π / 4) + ∫ t in (π / 4)..θ, Work.Spaces.pth Ψ z t| := by rw [hval]
    _ ≤ |Ψ z (π / 4)| + |∫ t in (π / 4)..θ, Work.Spaces.pth Ψ z t| := abs_add_le _ _
    _ ≤ |Ψ z (π / 4)| + B * |θ - π / 4| := by
        have h := intervalIntegral.norm_integral_le_of_norm_le_const hbound
        rw [Real.norm_eq_abs] at h
        linarith
    _ ≤ |Ψ z (π / 4)| + B * (π / 2) := by
        have := mul_le_mul_of_nonneg_left habs hB0
        linarith
    _ = |Ψ z (π / 4)| + (π / 2) * B := by ring

/-! ## The target -/

theorem sliceBdd_of_hmB {α : ℝ} {Ψ : ℝ → ℝ → ℝ}
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry Ψ) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)))
    (hmB : Work.Spaces.HkMem α 0 (Work.Spaces.pthIter 2 Ψ)) {z : ℝ} (hz : 0 < z) :
    ∃ C : ℝ, 0 < C ∧ ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
      |Ψ z θ| ≤ C ∧ |deriv (fun θ' => Ψ z θ') θ| ≤ C := by
  have hpth := pth_le_of_strip_HkMem hsm hmB hz
  have hpsi := psi_le_of_strip_HkMem hsm hmB hz
  have hI0 : 0 ≤ ∫ t in Work.Spaces.Iθ, |Work.Spaces.pthIter 2 Ψ z t| :=
    integral_nonneg (fun t => abs_nonneg _)
  have hp40 : 0 ≤ |Work.Spaces.pth Ψ z (π / 4)| := abs_nonneg _
  have hB : 0 ≤ |Work.Spaces.pth Ψ z (π / 4)|
      + ∫ t in Work.Spaces.Iθ, |Work.Spaces.pthIter 2 Ψ z t| := add_nonneg hp40 hI0
  have h2B : 0 ≤ (π / 2) * (|Work.Spaces.pth Ψ z (π / 4)|
      + ∫ t in Work.Spaces.Iθ, |Work.Spaces.pthIter 2 Ψ z t|) :=
    mul_nonneg (by positivity) hB
  refine ⟨|Ψ z (π / 4)| + (π / 2) * (|Work.Spaces.pth Ψ z (π / 4)|
      + ∫ t in Work.Spaces.Iθ, |Work.Spaces.pthIter 2 Ψ z t|)
      + (|Work.Spaces.pth Ψ z (π / 4)| + ∫ t in Work.Spaces.Iθ, |Work.Spaces.pthIter 2 Ψ z t|)
      + 1, ?_, ?_⟩
  · linarith [abs_nonneg (Ψ z (π / 4))]
  · intro θ hθ
    have hψ := hpsi θ hθ
    have hθ' : |deriv (fun θ' => Ψ z θ') θ| = |Work.Spaces.pth Ψ z θ| := rfl
    constructor
    · linarith
    · rw [hθ']
      have hp := hpth θ hθ
      linarith [hp, abs_nonneg (Ψ z (π / 4))]

end Work.FTS.EllipticEst.Endpt
