/-
# `Work.FTS.PhiStar.Psi0Ode` — the angular model `ψ`, its equation, its moment

Continuing `Psi0Defs.lean`: with `P = G₀/(2C³)` we set

  `w₀(θ) = ∫_0^θ P(t)/sin²t dt`,   `ψ = sin 2θ · (K + w₀)`,

where the constant `K = −(15/2)∫_0^{π/2} sin²t cos³t w₀(t)dt` is chosen so that the moment
`∫_0^{π/2} ψ sinθcos²θ` vanishes.  This file proves

* `hasDerivAt_wZer`: `w₀' = P/sin²θ`;
* `psiSol_ode`: `Lzero1 ψ = Γ̄` on `(0,π/2)` (via the substitution identity `L₀(2SCw)`);
* `psiSol_moment`: `∫ ψ sinθcos²θ = 0`;
* `continuousOn_psiSol`, `contDiffOn_psiSol`: regularity of `ψ`, and `psiSol 0 = psiSol (π/2) = 0`.
-/
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Submission.Work.FTS.PhiStar.Psi0Defs
import Submission.Work.FTS.H2.StarPkg.LzeroSubst.lzero_sin_cos_mul

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ContDiff
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## Global continuity of the source integrands -/

/-- The integrand `S C² Γ` of `Ψ_Γ` is continuous on all of `ℝ` (for `α ≥ 0`). -/
lemma continuous_sin_cos_sq_Gam' (α : ℝ) (hα : 0 ≤ α) :
    Continuous fun t : ℝ => Real.sin t * Real.cos t ^ 2 * Work.Spaces.Gam α t :=
  (Real.continuous_sin.mul (Real.continuous_cos.pow 2)).mul
    (((Real.continuous_sin.mul (Real.continuous_cos.pow 2))).rpow_const
      (fun _ => Or.inr (by positivity)))

/-- The source integrand `S C² Γ̄` is continuous on all of `ℝ` (for `α ≥ 0`). -/
lemma continuous_sin_cos_sq_GamBar' (α : ℝ) (hα : 0 ≤ α) :
    Continuous fun t : ℝ => Real.sin t * Real.cos t ^ 2 * Work.FTS.VocabO.GamBar α t := by
  have h1 := continuous_sin_cos_sq_Gam' α hα
  rw [show (fun t : ℝ => Real.sin t * Real.cos t ^ 2 * Work.FTS.VocabO.GamBar α t)
      = fun t => (Real.sin t * Real.cos t ^ 2 * Work.Spaces.Gam α t) / Work.Spaces.c α
        - (5 / 2) * (Real.sin t ^ 2 * Real.cos t ^ 3) by
    funext t; rw [Work.FTS.VocabO.GamBar, Real.sin_two_mul]; ring]
  exact (h1.div_const _).sub (by fun_prop)

/-- `G₀` is continuous on all of `ℝ`. -/
lemma continuous_Gzero (α : ℝ) (hα : 0 ≤ α) : Continuous (Gzero α) := by
  have hF := continuous_sin_cos_sq_GamBar' α hα
  have hpr : Continuous fun θ : ℝ =>
      ∫ t in (0:ℝ)..θ, Real.sin t * Real.cos t ^ 2 * Work.FTS.VocabO.GamBar α t := by
    rw [continuous_iff_continuousAt]
    intro θ
    exact (intervalIntegral.integral_hasDerivAt_right (hF.intervalIntegrable 0 θ)
      (Continuous.stronglyMeasurableAtFilter hF volume (𝓝 θ)) hF.continuousAt).continuousAt
  have hfun : Gzero α = fun θ => (∫ t in (0:ℝ)..(π / 2),
      Real.sin t * Real.cos t ^ 2 * Work.FTS.VocabO.GamBar α t)
      - ∫ t in (0:ℝ)..θ, Real.sin t * Real.cos t ^ 2 * Work.FTS.VocabO.GamBar α t := by
    funext θ
    simp only [Gzero]
    have h1 : IntervalIntegrable (fun t : ℝ =>
        Real.sin t * Real.cos t ^ 2 * Work.FTS.VocabO.GamBar α t) volume 0 θ :=
      hF.intervalIntegrable 0 θ
    have h2 : IntervalIntegrable (fun t : ℝ =>
        Real.sin t * Real.cos t ^ 2 * Work.FTS.VocabO.GamBar α t) volume θ (π / 2) :=
      hF.intervalIntegrable θ (π / 2)
    have hadd := intervalIntegral.integral_add_adjacent_intervals h1 h2
    linarith [hadd]
  rw [hfun]
  exact continuous_const.sub hpr

lemma measurable_Gzero (α : ℝ) (hα : 0 ≤ α) : Measurable (Gzero α) :=
  (continuous_Gzero α hα).measurable

lemma measurable_Pfun (α : ℝ) (hα : 0 ≤ α) : Measurable (Pfun α) :=
  (measurable_Gzero α hα).div (by fun_prop : Measurable fun t : ℝ => 2 * Real.cos t ^ 3)

/-! ## `w₀ = ∫_0^θ P/sin²` -/

/-- `w₀(α,θ) = ∫_0^θ P(t)/sin²t dt`. -/
def wZer (α : ℝ) (θ : ℝ) : ℝ := ∫ t in (0:ℝ)..θ, Pfun α t / (Real.sin t) ^ 2

/-- `P/sin²` is integrable on `[0,π/2]` (for `0 < α ≤ 1/4`). -/
lemma integrableOn_Pfun_div (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1 / 4) :
    MeasureTheory.IntegrableOn (fun t : ℝ => Pfun α t / (Real.sin t) ^ 2)
      (Set.uIcc (0:ℝ) (π / 2)) volume := by
  refine MeasureTheory.IntegrableOn.of_bound (by simp) ?_ 500 ?_
  · exact (Measurable.div (measurable_Pfun α (le_of_lt hα)) (by fun_prop :
      Measurable fun t : ℝ => (Real.sin t) ^ 2)).aestronglyMeasurable
  · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_uIcc] with t ht
    rw [Real.norm_eq_abs]
    have ht' : t ∈ Set.Icc (0:ℝ) (π / 2) := by
      rwa [Set.uIcc_of_le (by linarith [Real.pi_pos])] at ht
    exact Pfun_div_sin_sq_le α hα hα1 ht'

/-- `P/sin²` is interval-integrable on `[0,θ]` for `θ ≤ π/2`. -/
lemma intervalIntegrable_Pfun_div (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1 / 4) {θ : ℝ}
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ π / 2) :
    IntervalIntegrable (fun t : ℝ => Pfun α t / (Real.sin t) ^ 2) volume 0 θ := by
  rw [intervalIntegrable_iff]
  refine (integrableOn_Pfun_div α hα hα1).mono_set (fun t ht => ?_)
  rw [Set.uIoc_of_le hθ0] at ht
  rw [Set.uIcc_of_le (by linarith [Real.pi_pos] : (0:ℝ) ≤ π / 2)]
  exact ⟨le_of_lt ht.1, le_trans ht.2 hθ1⟩

/-- `w₀` is continuous on `[0,π/2]`. -/
lemma continuousOn_wZer (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1 / 4) :
    ContinuousOn (wZer α) (Set.Icc 0 (π / 2)) := by
  have hint := integrableOn_Pfun_div α hα hα1
  have h := intervalIntegral.continuousOn_primitive_interval (a := (0:ℝ)) (b := π / 2) hint
  rw [Set.uIcc_of_le (by linarith [Real.pi_pos] : (0:ℝ) ≤ π / 2)] at h
  show ContinuousOn (fun x : ℝ => ∫ t in (0:ℝ)..x, Pfun α t / (Real.sin t) ^ 2)
    (Set.Icc 0 (π / 2))
  exact h

/-- `w₀` is bounded by `500·(π/2)` on `[0,π/2]`. -/
lemma abs_wZer_le (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1 / 4) {θ : ℝ}
    (hθ : θ ∈ Set.Icc 0 (π / 2)) : |wZer α θ| ≤ 500 * (π / 2) := by
  rw [wZer]
  refine le_trans (intervalIntegral.abs_integral_le_integral_abs hθ.1) ?_
  have h1 : IntervalIntegrable (fun t : ℝ => |Pfun α t / (Real.sin t) ^ 2|) volume 0 θ :=
    (intervalIntegrable_Pfun_div α hα hα1 hθ.1 hθ.2).abs
  have h2 : IntervalIntegrable (fun _ : ℝ => (500 : ℝ)) volume 0 θ := intervalIntegrable_const
  have hm := intervalIntegral.integral_mono_on hθ.1 h1 h2 (fun t ht =>
    Pfun_div_sin_sq_le α hα hα1 ⟨ht.1, le_trans ht.2 hθ.2⟩)
  have hv : (∫ _ in (0:ℝ)..θ, (500 : ℝ)) = 500 * θ := by
    rw [intervalIntegral.integral_const]; ring
  rw [hv] at hm
  linarith [hm, hθ.2, Real.pi_pos]

/-- **The derivative of `w₀`**: `w₀' = P/sin²θ`. -/
theorem hasDerivAt_wZer (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1 / 4) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    HasDerivAt (wZer α) (Pfun α θ / (Real.sin θ) ^ 2) θ := by
  have hint := intervalIntegrable_Pfun_div α hα hα1 (le_of_lt hθ.1) (le_of_lt hθ.2)
  have hcont : ContinuousOn (fun t : ℝ => Pfun α t / (Real.sin t) ^ 2)
      (Set.Ioo 0 (π / 2)) := by
    refine ((continuous_Gzero α (le_of_lt hα)).continuousOn.div
      (by fun_prop : ContinuousOn (fun t : ℝ => 2 * Real.cos t ^ 3) _) ?_).div
      (by fun_prop : ContinuousOn (fun t : ℝ => (Real.sin t) ^ 2) _) ?_
    · intro t ht
      have hc : 0 < Real.cos t :=
        Real.cos_pos_of_mem_Ioo ⟨by linarith [ht.1, Real.pi_pos], ht.2⟩
      exact ne_of_gt (by positivity)
    · intro t ht
      have hs : 0 < Real.sin t :=
        Real.sin_pos_of_pos_of_lt_pi ht.1 (by linarith [ht.2, Real.pi_gt_three])
      exact ne_of_gt (by positivity)
  have hcat : ContinuousAt (fun t : ℝ => Pfun α t / (Real.sin t) ^ 2) θ :=
    hcont.continuousAt (isOpen_Ioo.mem_nhds hθ)
  have hmeas : StronglyMeasurableAtFilter (fun t : ℝ => Pfun α t / (Real.sin t) ^ 2)
      (𝓝 θ) volume :=
    ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioo hcont θ hθ
  exact intervalIntegral.integral_hasDerivAt_right hint hmeas hcat

/-- The derivative of `P/sin²` at an interior point. -/
theorem hasDerivAt_Pfun_div (α : ℝ) (hα : 0 ≤ α) {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    HasDerivAt (fun t : ℝ => Pfun α t / (Real.sin t) ^ 2)
      (deriv (Pfun α) θ / (Real.sin θ) ^ 2
        - Pfun α θ * (2 * Real.sin θ * Real.cos θ) / (Real.sin θ) ^ 4) θ := by
  have hS : Real.sin θ ≠ 0 := ne_of_gt (Real.sin_pos_of_pos_of_lt_pi hθ.1
    (by linarith [hθ.2, Real.pi_gt_three]))
  have hden : HasDerivAt (fun t : ℝ => (Real.sin t) ^ 2) (2 * Real.sin θ * Real.cos θ) θ := by
    have h := (Real.hasDerivAt_sin θ).pow 2
    rw [show ((fun t : ℝ => Real.sin t) ^ 2) = fun t : ℝ => Real.sin t ^ 2 from by
      funext t; rw [Pi.pow_apply]] at h
    simpa using h
  have hnum : HasDerivAt (Pfun α) (deriv (Pfun α) θ) θ :=
    (hasDerivAt_Pfun α hα hθ).differentiableAt.hasDerivAt
  have hq := hnum.div hden (pow_ne_zero 2 hS)
  have hfun : (fun t : ℝ => Pfun α t / (Real.sin t) ^ 2)
      = (Pfun α / fun t : ℝ => (Real.sin t) ^ 2) := rfl
  rw [hfun]
  convert hq using 1
  field_simp

/-! ## `Kc` and `psiSol` -/

/-- The constant fixing the moment: `Kc = −(15/2)∫_0^{π/2} sin²θ cos³θ w₀(θ)dθ`. -/
def Kc (α : ℝ) : ℝ := -(15 / 2) * ∫ θ in (0:ℝ)..(π / 2),
  Real.sin θ ^ 2 * Real.cos θ ^ 3 * wZer α θ

/-- **The explicit angular model**: `ψ(θ) = sin 2θ · (Kc + w₀(θ))`. -/
def psiSol (α : ℝ) : ℝ → ℝ := fun θ => Real.sin (2 * θ) * (Kc α + wZer α θ)

lemma continuousOn_wZer' (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1 / 4) :
    ContinuousOn (fun θ => Real.sin θ ^ 2 * Real.cos θ ^ 3 * wZer α θ)
      (Set.Icc 0 (π / 2)) :=
  (by fun_prop : ContinuousOn (fun θ : ℝ => Real.sin θ ^ 2 * Real.cos θ ^ 3)
    (Set.Icc 0 (π / 2))).mul (continuousOn_wZer α hα hα1)

/-- `psiSol 0 = 0`. -/
lemma psiSol_zero (α : ℝ) : psiSol α 0 = 0 := by
  simp [psiSol]

/-- `psiSol (π/2) = 0`. -/
lemma psiSol_pi_div_two (α : ℝ) : psiSol α (π / 2) = 0 := by
  rw [psiSol, show 2 * (π / 2) = π from by ring, Real.sin_pi]
  ring

/-- `psiSol` is continuous on `[0,π/2]`. -/
lemma continuousOn_psiSol (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1 / 4) :
    ContinuousOn (psiSol α) (Set.Icc 0 (π / 2)) :=
  (by fun_prop : ContinuousOn (fun θ : ℝ => Real.sin (2 * θ)) (Set.Icc 0 (π / 2))).mul
    (continuousOn_const.add (continuousOn_wZer α hα hα1))

/-- `psiSol` is `C^∞` on `(0,π/2)`. -/
lemma contDiffOn_psiSol (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1 / 4) :
    ContDiffOn ℝ (∞ : ℕ∞ω) (psiSol α) (Set.Ioo 0 (π / 2)) := by
  have hw : ContDiffOn ℝ (∞ : ℕ∞ω) (wZer α) (Set.Ioo 0 (π / 2)) := by
    have hP : ContDiffOn ℝ (∞ : ℕ∞ω) (fun t : ℝ => Pfun α t / (Real.sin t) ^ 2)
        (Set.Ioo 0 (π / 2)) := by
      refine (contDiffOn_Pfun α (le_of_lt hα)).div (by fun_prop) ?_
      intro t ht
      exact pow_ne_zero 2 (ne_of_gt (Real.sin_pos_of_pos_of_lt_pi ht.1
        (by linarith [ht.2, Real.pi_gt_three])))
    rw [contDiffOn_infty_iff_deriv_of_isOpen isOpen_Ioo]
    exact ⟨fun t ht => (hasDerivAt_wZer α hα hα1 ht).differentiableAt.differentiableWithinAt,
      hP.congr (fun t ht => (hasDerivAt_wZer α hα hα1 ht).deriv)⟩
  exact (by fun_prop : ContDiffOn ℝ (∞ : ℕ∞ω) (fun θ : ℝ => Real.sin (2 * θ))
    (Set.Ioo 0 (π / 2))).mul (contDiffOn_const.add hw)

/-! ## The model equation -/

/-- **The angular model equation**: `Lzero1 ψ = Γ̄` on `(0,π/2)`. -/
theorem psiSol_ode (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1 / 4) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    Work.FTS.EllipticEst.Lzero1 (psiSol α) θ = Work.FTS.VocabO.GamBar α θ := by
  have hS : Real.sin θ ≠ 0 := ne_of_gt (Real.sin_pos_of_pos_of_lt_pi hθ.1
    (by linarith [hθ.2, Real.pi_gt_three]))
  have hC : Real.cos θ ≠ 0 := ne_of_gt (Real.cos_pos_of_mem_Ioo
    ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩)
  set w : ℝ → ℝ := fun t => Kc α + wZer α t with hw
  have hd1 : DifferentiableOn ℝ (fun t : ℝ => 2 * w t) (Set.Ioo 0 (π / 2)) := fun t ht =>
    ((hasDerivAt_wZer α hα hα1 ht).const_add (Kc α)).const_mul 2
      |>.differentiableAt.differentiableWithinAt
  have hd2 : DifferentiableOn ℝ (fun t : ℝ => deriv (fun s : ℝ => 2 * w s) t)
      (Set.Ioo 0 (π / 2)) := by
    intro t ht
    have heq : deriv (fun s : ℝ => 2 * w s) = fun s => 2 * deriv w s := by
      funext s; rw [Work.Spaces.deriv_const_mul']
    rw [heq]
    have h2 : DifferentiableAt ℝ (fun s : ℝ => 2 * (Pfun α s / (Real.sin s) ^ 2)) t :=
      ((hasDerivAt_Pfun_div α (le_of_lt hα) ht).const_mul 2).differentiableAt
    have hev : (fun s : ℝ => 2 * deriv w s)
        =ᶠ[𝓝 t] fun s => 2 * (Pfun α s / (Real.sin s) ^ 2) := by
      filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
      rw [(hasDerivAt_wZer α hα hα1 hs).const_add (Kc α) |>.deriv]
    exact (h2.congr_of_eventuallyEq hev).differentiableWithinAt
  have hsub := Work.FTS.H2.StarPkg.LzeroSubst.lzero_sin_cos_mul (fun _ t : ℝ => 2 * w t)
    (z := 0) (θ := θ) hθ hd1 hd2
  have hpth : ∀ t ∈ Set.Ioo (0:ℝ) (π / 2),
      Work.Spaces.pth (fun _ s : ℝ => 2 * w s) 0 t = 2 * (Pfun α t / (Real.sin t) ^ 2) := by
    intro t ht
    rw [Work.Spaces.pth, Work.Spaces.deriv_const_mul']
    exact congrArg (fun x => 2 * x) ((hasDerivAt_wZer α hα hα1 ht).const_add (Kc α) |>.deriv)
  have hpth2 : Work.Spaces.pthIter 2 (fun _ s : ℝ => 2 * w s) 0 θ
      = 2 * (deriv (Pfun α) θ / (Real.sin θ) ^ 2
        - Pfun α θ * (2 * Real.sin θ * Real.cos θ) / (Real.sin θ) ^ 4) := by
    show deriv (fun t : ℝ => Work.Spaces.pth (fun _ s : ℝ => 2 * w s) 0 t) θ = _
    have hev : (fun t : ℝ => Work.Spaces.pth (fun _ s : ℝ => 2 * w s) 0 t)
        =ᶠ[𝓝 θ] fun t => 2 * (Pfun α t / (Real.sin t) ^ 2) := by
      filter_upwards [isOpen_Ioo.mem_nhds hθ] with t ht
      exact hpth t ht
    rw [hev.deriv_eq, Work.Spaces.deriv_const_mul']
    exact congrArg (fun x => 2 * x) (hasDerivAt_Pfun_div α (le_of_lt hα) hθ).deriv
  have hfun : (fun x t : ℝ => psiSol α t)
      = fun z t : ℝ => Real.sin t * Real.cos t * (2 * w t) := by
    funext x t
    rw [psiSol, hw, Real.sin_two_mul]; ring
  rw [Work.FTS.EllipticEst.Lzero1_eq_Lzero]
  simp only []
  rw [hfun, hsub, hpth θ hθ, hpth2, (hasDerivAt_Pfun α (le_of_lt hα) hθ).deriv]
  field_simp
  ring

end Work.FTS.PhiStar
