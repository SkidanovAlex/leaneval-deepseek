/-
# `Work.FTS.PhiStar.Series.eFamEneAux` -- the Sturm-Liouville equation and the energy of `eFam`

Auxiliary (analytic) part of `Work.FTS.PhiStar.Series.eFam_growth`: the `theta`-form of the
Gegenbauer equation for `eFam m theta = cos theta * gC (2m+1) (sin theta)`,

  `(cos theta * f')' = (1/cos theta - M cos theta) * f`,   `M = eM m`,

the reduced form of the second derivative, the derivative of the energy

  `eEne m theta = cos theta f'^2 - sin theta f f' + (M cos theta - 1/(2 cos theta)) f^2`,

namely `eEne m' = -(3 sin theta/(2 cos^2 theta)) f^2 <= 0`, the resulting energy monotonicity
`eEne m theta <= eEne m 0` on `[0, pi/2]`, and the value of `eEne m` at a critical point of `f`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.PhiStar.Series.eFamEneDefs
import Submission.Work.FTS.PhiStar.Gegenbauer.gC_ode
import Submission.Work.FTS.PhiStar.Gegenbauer.eFam_Lzero
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open Filter Set SignType

namespace Work.FTS.PhiStar.Series

set_option autoImplicit false

open Work.FTS.PhiStar.Gegenbauer

/-! ## The `θ`-form of the Gegenbauer equation -/

/-- **The Sturm–Liouville form of the Gegenbauer equation.**  If `q` solves the Gegenbauer
equation of index `n` then `f = cos θ · q(sin θ)` satisfies
`(cos θ · f')' = (1/cos θ - (n+1)(n+2) cos θ) · f` wherever `cos θ ≠ 0`. -/
lemma ode_of_gC {q : ℝ → ℝ} {n : ℕ} (hq : ContDiff ℝ 3 q)
    (hode : ∀ x : ℝ, (1 - x^2) * deriv (deriv q) x - 4 * x * deriv q x
      + (n:ℝ) * ((n:ℝ)+3) * q x = 0)
    (θ : ℝ) (hθ : Real.cos θ ≠ 0) :
    deriv (fun θ' => Real.cos θ' * deriv (fun θ' : ℝ => Real.cos θ' * q (Real.sin θ')) θ') θ
      = (1 / Real.cos θ - (((n:ℝ)+1) * ((n:ℝ)+2)) * Real.cos θ)
          * (Real.cos θ * q (Real.sin θ)) := by
  have hdiffq : Differentiable ℝ q := hq.differentiable (by norm_num)
  have hddiffq : Differentiable ℝ (deriv q) :=
    (ContDiff.deriv' (n := 2) hq).differentiable (by norm_num)
  have hfun : (fun θ' => Real.cos θ' * deriv (fun θ' : ℝ => Real.cos θ' * q (Real.sin θ')) θ')
      = fun θ' => Real.cos θ' ^ 3 * deriv q (Real.sin θ')
          - Real.cos θ' * Real.sin θ' * q (Real.sin θ') := by
    funext θ'
    rw [deriv_cos_comp_sin q hq]
    ring
  rw [hfun]
  have hcos : HasDerivAt Real.cos (-Real.sin θ) θ := Real.hasDerivAt_cos θ
  have hsin : HasDerivAt Real.sin (Real.cos θ) θ := Real.hasDerivAt_sin θ
  have hqs : HasDerivAt (fun θ' : ℝ => q (Real.sin θ')) (deriv q (Real.sin θ) * Real.cos θ) θ :=
    ((hdiffq.differentiableAt).hasDerivAt).comp θ hsin
  have hdqs : HasDerivAt (fun θ' : ℝ => deriv q (Real.sin θ'))
      (deriv (deriv q) (Real.sin θ) * Real.cos θ) θ :=
    ((hddiffq.differentiableAt).hasDerivAt).comp θ hsin
  have hA : HasDerivAt (fun θ' => Real.cos θ' * Real.sin θ' * q (Real.sin θ'))
      ((-Real.sin θ * Real.sin θ + Real.cos θ * Real.cos θ) * q (Real.sin θ)
        + (Real.cos θ * Real.sin θ) * (deriv q (Real.sin θ) * Real.cos θ)) θ :=
    (hcos.mul hsin).mul hqs
  have hB : HasDerivAt (fun θ' => Real.cos θ' ^ 3 * deriv q (Real.sin θ'))
      ((3 * Real.cos θ ^ 2 * (-Real.sin θ)) * deriv q (Real.sin θ)
        + Real.cos θ ^ 3 * (deriv (deriv q) (Real.sin θ) * Real.cos θ)) θ :=
    (hcos.pow 3).mul hdqs
  have htot : HasDerivAt (fun θ' => Real.cos θ' ^ 3 * deriv q (Real.sin θ')
        - Real.cos θ' * Real.sin θ' * q (Real.sin θ')) _ θ := hB.sub hA
  rw [htot.deriv]
  have ho := hode (Real.sin θ)
  have hs' : Real.sin θ ^ 2 + Real.cos θ ^ 2 - 1 = 0 := by
    linarith [Real.sin_sq_add_cos_sq θ]
  field_simp
  linear_combination (Real.cos θ^2) * ho
    + (q (Real.sin θ) + Real.cos θ^2 * deriv (deriv q) (Real.sin θ)) * hs'

/-- The `θ`-form of the Gegenbauer equation for `eFam m`. -/
lemma eFam_ode (m : ℕ) (θ : ℝ) (hθ : Real.cos θ ≠ 0) :
    deriv (fun θ' => Real.cos θ' * deriv (eFam m) θ') θ
      = (1 / Real.cos θ - eM m * Real.cos θ) * eFam m θ := by
  have h := ode_of_gC (q := gC (2 * m + 1)) (n := 2 * m + 1) (contDiff_gC (2 * m + 1))
    (fun x => (gC_ode (2 * m + 1)).2 x) θ hθ
  have harith : ((((2 * m + 1 : ℕ) : ℝ) + 1) * (((2 * m + 1 : ℕ) : ℝ) + 2)) = eM m := by
    unfold eM; push_cast; ring
  rw [harith] at h
  exact h

/-- At `θ = 0` the `cos` prefactor contributes nothing to the derivative, so
`(eFam m)'(0) = (gC (2m+1))'(0)`. -/
lemma deriv_eFam_zero (m : ℕ) : deriv (eFam m) 0 = deriv (gC (2 * m + 1)) 0 := by
  change deriv (Real.cos * fun θ : ℝ => gC (2 * m + 1) (Real.sin θ)) 0 = _
  have hB : HasDerivAt (gC (2 * m + 1)) (deriv (gC (2 * m + 1)) (Real.sin 0)) (Real.sin 0) :=
    (((contDiff_gC (2 * m + 1)).differentiable (by norm_num)).differentiableAt).hasDerivAt
  have hcomp : HasDerivAt (fun θ : ℝ => gC (2 * m + 1) (Real.sin θ))
      (deriv (gC (2 * m + 1)) (Real.sin 0) * Real.cos 0) 0 :=
    hB.comp 0 (Real.hasDerivAt_sin 0)
  have h := ((Real.hasDerivAt_cos 0).mul hcomp).deriv
  simpa using h

/-- The derivative of `eFam m` is differentiable everywhere. -/
lemma differentiableAt_deriv_eFam (m : ℕ) (θ : ℝ) :
    DifferentiableAt ℝ (deriv (eFam m)) θ := by
  have hq : Differentiable ℝ (gC (2 * m + 1)) :=
    (contDiff_gC (2 * m + 1)).differentiable (by norm_num)
  have hdq : Differentiable ℝ (deriv (gC (2 * m + 1))) :=
    ((ContDiff.deriv' (n := 2) (contDiff_gC (2 * m + 1))).differentiable (by norm_num))
  have hform : deriv (eFam m)
      = fun θ : ℝ => -Real.sin θ * gC (2 * m + 1) (Real.sin θ)
          + Real.cos θ ^ 2 * deriv (gC (2 * m + 1)) (Real.sin θ) := by
    change deriv (fun θ : ℝ => Real.cos θ * gC (2 * m + 1) (Real.sin θ)) = _
    exact deriv_cos_comp_sin (gC (2 * m + 1)) (contDiff_gC (2 * m + 1))
  rw [hform]
  exact (((Real.differentiableAt_sin).neg).mul
      (hq.differentiableAt.comp θ (Real.differentiableAt_sin))).add
    ((Real.differentiableAt_cos.pow 2).mul
      (hdq.differentiableAt.comp θ (Real.differentiableAt_sin)))

/-- The second derivative of `eFam m`, in reduced (first-order) form. -/
lemma eFam_deriv2_eq (m : ℕ) (θ : ℝ) (hθ : Real.cos θ ≠ 0) :
    deriv (deriv (eFam m)) θ
      = Real.tan θ * deriv (eFam m) θ + (1 / (Real.cos θ)^2 - eM m) * eFam m θ := by
  have hmul : deriv (fun θ' => Real.cos θ' * deriv (eFam m) θ') θ
      = deriv Real.cos θ * deriv (eFam m) θ + Real.cos θ * deriv (deriv (eFam m)) θ :=
    deriv_mul Real.differentiableAt_cos (differentiableAt_deriv_eFam m θ)
  rw [eFam_ode m θ hθ, Real.deriv_cos] at hmul
  have h2 : Real.cos θ * deriv (deriv (eFam m)) θ
      = Real.cos θ * (Real.tan θ * deriv (eFam m) θ
          + (1 / (Real.cos θ)^2 - eM m) * eFam m θ) := by
    have h3 : Real.cos θ * (Real.tan θ * deriv (eFam m) θ
          + (1 / (Real.cos θ)^2 - eM m) * eFam m θ)
        = (1 / Real.cos θ - eM m * Real.cos θ) * eFam m θ
          + Real.sin θ * deriv (eFam m) θ := by
      rw [Real.tan_eq_sin_div_cos]; field_simp; ring
    rw [h3, hmul]; ring
  exact mul_left_cancel₀ hθ h2

/-! ## The energy `eEne` -/

/-- `eEne m 0 = (eFam m)'(0)²`. -/
lemma eEne_at_zero (m : ℕ) : eEne m 0 = (deriv (eFam m) 0)^2 := by
  unfold eEne
  rw [eFam_zero m]
  simp

/-- `eEne m (π/2) = 0`. -/
lemma eEne_at_pi_half (m : ℕ) : eEne m (Real.pi / 2) = 0 := by
  unfold eEne
  rw [eFam_pi_half m]
  simp [Real.cos_pi_div_two, Real.sin_pi_div_two]

/-- Differentiability of the energy where `cos θ ≠ 0`. -/
lemma differentiableAt_eEne (m : ℕ) {θ : ℝ} (hθ : Real.cos θ ≠ 0) :
    DifferentiableAt ℝ (eEne m) θ := by
  have hf : DifferentiableAt ℝ (eFam m) θ := (differentiable_eFam m).differentiableAt
  have hg : DifferentiableAt ℝ (deriv (eFam m)) θ := differentiableAt_deriv_eFam m θ
  have hcos : DifferentiableAt ℝ Real.cos θ := Real.differentiableAt_cos
  have hsin : DifferentiableAt ℝ Real.sin θ := Real.differentiableAt_sin
  have hinv : DifferentiableAt ℝ (fun x : ℝ => 1 / (2 * Real.cos x)) θ := by
    have h2 : DifferentiableAt ℝ (fun x : ℝ => 2 * Real.cos x) θ :=
      (differentiableAt_const 2).mul hcos
    have h3 := h2.inv (by simpa using hθ)
    have heq : (fun x : ℝ => 1 / (2 * Real.cos x)) = fun x : ℝ => (2 * Real.cos x)⁻¹ := by
      funext x; rw [div_eq_mul_inv, one_mul]
    rw [heq]; exact h3
  unfold eEne
  exact ((hcos.mul (hg.pow 2)).sub ((hsin.mul hf).mul hg)).add
    ((((differentiableAt_const (eM m)).mul hcos).sub hinv).mul (hf.pow 2))

/-- **The derivative of the energy.** `eEne m' = -(3 sin θ/(2 cos²θ)) f²`. -/
lemma eEne_deriv (m : ℕ) (θ : ℝ) (hθ : Real.cos θ ≠ 0) :
    deriv (eEne m) θ
      = -(3 * Real.sin θ / (2 * (Real.cos θ)^2)) * (eFam m θ)^2 := by
  have hf : HasDerivAt (eFam m) (deriv (eFam m) θ) θ :=
    ((differentiable_eFam m).differentiableAt).hasDerivAt
  have hg : HasDerivAt (deriv (eFam m)) (deriv (deriv (eFam m)) θ) θ :=
    (differentiableAt_deriv_eFam m θ).hasDerivAt
  have hcos : HasDerivAt Real.cos (-Real.sin θ) θ := Real.hasDerivAt_cos θ
  have hsin : HasDerivAt Real.sin (Real.cos θ) θ := Real.hasDerivAt_sin θ
  have hcinv : HasDerivAt (fun x : ℝ => (Real.cos x)⁻¹) (- -Real.sin θ / Real.cos θ ^ 2) θ :=
    hcos.inv hθ
  have hhalf : HasDerivAt (fun x : ℝ => (1/2:ℝ) * (Real.cos x)⁻¹)
      ((1/2:ℝ) * (- -Real.sin θ / Real.cos θ ^ 2)) θ := hcinv.const_mul _
  have hpoint : ∀ x : ℝ, 1 / (2 * Real.cos x) = (1/2:ℝ) * (Real.cos x)⁻¹ := by
    intro x
    have key : (2 * Real.cos x)⁻¹ = (1/2:ℝ) * (Real.cos x)⁻¹ := by
      rw [show (1/2:ℝ) = (2:ℝ)⁻¹ from by norm_num, mul_inv_rev, mul_comm]
    rwa [div_eq_mul_inv, one_mul]
  have hfun : (fun x : ℝ => 1 / (2 * Real.cos x)) =ᶠ[𝓝 θ]
      fun x => (1/2:ℝ) * (Real.cos x)⁻¹ := Filter.Eventually.of_forall hpoint
  have hinv : HasDerivAt (fun x : ℝ => 1 / (2 * Real.cos x))
      (Real.sin θ / (2 * Real.cos θ^2)) θ := by
    have h := hhalf.congr_of_eventuallyEq hfun
    have hval : (1/2:ℝ) * (- -Real.sin θ / Real.cos θ ^ 2)
        = Real.sin θ / (2 * Real.cos θ ^ 2) := by
      field_simp
    rwa [hval] at h
  have hE : HasDerivAt (fun θ' => Real.cos θ' * deriv (eFam m) θ' ^ 2
        - Real.sin θ' * eFam m θ' * deriv (eFam m) θ'
        + (eM m * Real.cos θ' - 1 / (2 * Real.cos θ')) * eFam m θ' ^ 2) _ θ :=
    (((hcos.mul (hg.pow 2)).sub ((hsin.mul hf).mul hg)).add
      (((hcos.const_mul (eM m)).sub hinv).mul (hf.pow 2)))
  change deriv (fun θ' => Real.cos θ' * deriv (eFam m) θ' ^ 2
        - Real.sin θ' * eFam m θ' * deriv (eFam m) θ'
        + (eM m * Real.cos θ' - 1 / (2 * Real.cos θ')) * eFam m θ' ^ 2) θ = _
  rw [hE.deriv]
  simp only [Pi.mul_apply, Pi.sub_apply, Pi.pow_apply, show (2:ℕ) - 1 = 1 from rfl, pow_one]
  rw [eFam_deriv2_eq m θ hθ, Real.tan_eq_sin_div_cos]
  have hs' : Real.sin θ ^ 2 + Real.cos θ ^ 2 - 1 = 0 := by
    linarith [Real.sin_sq_add_cos_sq θ]
  field_simp
  ring_nf
  linear_combination
    (-2 * deriv (eFam m) θ * Real.cos θ * eFam m θ) * hs'

/-- The energy is non-increasing on `(0, π/2)`. -/
lemma eEne_deriv_nonpos (m : ℕ) {x : ℝ} (hx : x ∈ Set.Ioo 0 (Real.pi/2)) :
    deriv (eEne m) x ≤ 0 := by
  have hcos : Real.cos x ≠ 0 := ne_of_gt (Real.cos_pos_of_mem_Ioo
    ⟨by linarith [hx.1, Real.pi_pos], by linarith [hx.2, Real.pi_pos]⟩)
  rw [eEne_deriv m x hcos]
  have h1 : 0 ≤ Real.sin x :=
    Real.sin_nonneg_of_mem_Icc ⟨le_of_lt hx.1, by linarith [hx.2, Real.pi_pos]⟩
  have h3 : 0 ≤ 3 * Real.sin x / (2 * (Real.cos x)^2) :=
    div_nonneg (by linarith) (by positivity)
  nlinarith [sq_nonneg (eFam m x)]

/-- **Energy monotonicity**: `eEne m θ ≤ eEne m 0` for `θ ∈ [0, π/2]`. -/
lemma eEne_le_eEne_zero (m : ℕ) {θ : ℝ} (hθ : θ ∈ Set.Icc (0:ℝ) (Real.pi/2)) :
    eEne m θ ≤ eEne m 0 := by
  rcases lt_or_eq_of_le hθ.2 with hlt | heq
  · rcases eq_or_lt_of_le hθ.1 with h0 | hpos
    · rw [h0]
    · have hcos_ne : ∀ x ∈ Set.Icc (0:ℝ) θ, Real.cos x ≠ 0 := by
        intro x hx
        exact ne_of_gt (Real.cos_pos_of_mem_Ioo
          ⟨by linarith [hx.1, Real.pi_pos], by linarith [hx.2, hlt]⟩)
      have hcont : ContinuousOn (eEne m) (Set.Icc 0 θ) := by
        have hgd : Differentiable ℝ (deriv (eFam m)) :=
          fun x => differentiableAt_deriv_eFam m x
        have hg : ContinuousOn (fun x : ℝ => deriv (eFam m) x) (Set.Icc 0 θ) :=
          hgd.continuous.continuousOn
        have hf : ContinuousOn (fun x : ℝ => eFam m x) (Set.Icc 0 θ) :=
          (continuous_eFam m).continuousOn
        have hinv : ContinuousOn (fun x : ℝ => 1 / (2 * Real.cos x)) (Set.Icc 0 θ) := by
          refine ContinuousOn.div continuousOn_const ?_ ?_
          · exact (continuous_const.mul Real.continuous_cos).continuousOn
          · intro x hx; exact mul_ne_zero two_ne_zero (hcos_ne x hx)
        change ContinuousOn (fun x : ℝ => Real.cos x * deriv (eFam m) x ^ 2
            - Real.sin x * eFam m x * deriv (eFam m) x
            + (eM m * Real.cos x - 1 / (2 * Real.cos x)) * eFam m x ^ 2) (Set.Icc 0 θ)
        exact (((Real.continuous_cos.continuousOn.mul (hg.pow 2)).sub
              (((Real.continuous_sin.continuousOn).mul hf).mul hg)).add
            (((continuous_const.mul Real.continuous_cos).continuousOn.sub hinv).mul (hf.pow 2)))
      have hdiff : DifferentiableOn ℝ (eEne m) (Set.Ioo 0 θ) := fun x hx =>
        (differentiableAt_eEne m (hcos_ne x ⟨le_of_lt hx.1, le_of_lt hx.2⟩)).differentiableWithinAt
      obtain ⟨c, hc, hcd⟩ :=
        exists_deriv_eq_slope (f := eEne m) (a := 0) (b := θ) hpos hcont hdiff
      have hle : deriv (eEne m) c ≤ 0 :=
        eEne_deriv_nonpos m ⟨hc.1, by linarith [hc.2, hlt]⟩
      have hkey : eEne m θ - eEne m 0 = θ * deriv (eEne m) c := by
        rw [hcd, sub_zero]; field_simp
      nlinarith [hkey, hle, hθ.1]
  · rw [heq, eEne_at_pi_half, eEne_at_zero]; positivity

/-- At a critical point of `f = eFam m`, `eEne m` is the height of `f` times the bracket. -/
lemma eEne_at_critical (m : ℕ) {θ : ℝ} (hθ : deriv (eFam m) θ = 0) :
    eEne m θ = (eM m * Real.cos θ - 1 / (2 * Real.cos θ)) * (eFam m θ)^2 := by
  unfold eEne
  rw [hθ]; ring
end Work.FTS.PhiStar.Series
