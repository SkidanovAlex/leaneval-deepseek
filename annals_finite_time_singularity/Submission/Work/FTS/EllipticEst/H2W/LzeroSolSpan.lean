/-
Copyright: work module for the Elgindi finite-time singularity project.

# The solution space of `Lzero1 u = -u'' + (tan θ · u)' - 6u = 0` on `(0, π/2)`

`Lzero1 u = 0` is a second-order linear ODE in normal form `u'' = p u' + q u` with
`p = tan θ`, `q = 1/cos²θ - 6` on the open interval `I = (0, π/2)`.  Two solutions are

* `LzeroReg θ = sin 2θ` (regular), and
* `LzeroSing θ = sin(2θ) ∫_{π/4}^{π/2-θ} ds/(sin s · sin(2s)²)` (the solution with a pole
  `≍ -1/(4t)` at `t = π/2 - θ → 0⁺`),

whose Wronskian is `W = -1/cos θ ≠ 0` on `I` (`LzeroSingWronskian`).  Since the solution
space of a second-order linear ODE with continuous coefficients is `2`-dimensional, every
solution on `I` is a linear combination of these two.  This module proves that, by the
classical **Wronskian (Cramer) argument**, which needs no Grönwall/uniqueness input:

* for any solution `f`, the Wronskians `wron f LzeroSing`, `wron LzeroReg f` and
  `wron LzeroReg LzeroSing` satisfy the *first-order* equations `A' = p A` (the
  product-rule terms cancel and the two second-order equations are used);
* hence the two quotients by the (nowhere vanishing) Wronskian `W` have vanishing
  derivative, so they are constant on the connected set `I` — these two constants are the
  coefficients of the decomposition;
* multiplying the two Cramer identities by `LzeroReg` and `LzeroSing` and adding kills the
  `f'` terms and leaves `f · W = (c₁ LzeroReg + c₂ LzeroSing) · W`, so `W ≠ 0` gives the
  result.

Everything is formalised for a general `p`, `q` and a general pair of independent solutions
(`deriv_wron`, `span_of_two_solutions`), and then instantiated at the two special solutions.
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.EllipticEst.LzeroSingDefs
import Submission.Work.FTS.EllipticEst.LzeroSingWronskian
import Submission.Work.FTS.EllipticEst.LzeroSingODE

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.H2W

set_option autoImplicit false

/-! ## The Wronskian of two solutions of `y'' = p y' + q y` -/

/-- The Wronskian `W f g = f g' - f' g` of the two functions `f`, `g`. -/
def wron (f g : ℝ → ℝ) : ℝ → ℝ := fun x => f x * deriv g x - deriv f x * g x

theorem wron_apply (f g : ℝ → ℝ) (x : ℝ) :
    wron f g x = f x * deriv g x - deriv f x * g x := rfl

/-- **The Wronskian of two solutions of `y'' = p y' + q y` solves `W' = p W`.**  The product
rule contributions of the two first-order pieces cancel; the hypotheses supply the second
derivatives. -/
theorem deriv_wron {p q : ℝ → ℝ} {s : Set ℝ} {f g : ℝ → ℝ}
    (hf : ∀ x ∈ s, HasDerivAt f (deriv f x) x)
    (hf2 : ∀ x ∈ s, HasDerivAt (deriv f) (deriv (deriv f) x) x)
    (hg : ∀ x ∈ s, HasDerivAt g (deriv g x) x)
    (hg2 : ∀ x ∈ s, HasDerivAt (deriv g) (deriv (deriv g) x) x)
    (hf' : ∀ x ∈ s, deriv (deriv f) x = p x * deriv f x + q x * f x)
    (hg' : ∀ x ∈ s, deriv (deriv g) x = p x * deriv g x + q x * g x) :
    ∀ x ∈ s, HasDerivAt (wron f g) (p x * wron f g x) x := by
  intro x hx
  have hmain : HasDerivAt (wron f g)
      (f x * deriv (deriv g) x - deriv (deriv f) x * g x) x :=
    (((hf x hx).mul (hg2 x hx)).sub ((hf2 x hx).mul (hg x hx))).congr_deriv (by ring)
  have hval : f x * deriv (deriv g) x - deriv (deriv f) x * g x = p x * wron f g x := by
    rw [hf' x hx, hg' x hx]
    simp only [wron]
    ring
  exact hmain.congr_deriv hval

/-- **Solution space of `y'' = p y' + q y` on a connected open set**: if `y₁`, `y₂` are two
solutions with nowhere vanishing Wronskian and `u` is any solution, then `u` is a linear
combination of `y₁` and `y₂` on `s`. -/
theorem span_of_two_solutions {p q : ℝ → ℝ} {s : Set ℝ} (hs : IsOpen s)
    (hsc : IsPreconnected s)
    {y₁ y₂ u : ℝ → ℝ}
    (hy₁ : ∀ x ∈ s, HasDerivAt y₁ (deriv y₁ x) x)
    (hy₁2 : ∀ x ∈ s, HasDerivAt (deriv y₁) (deriv (deriv y₁) x) x)
    (hy₂ : ∀ x ∈ s, HasDerivAt y₂ (deriv y₂ x) x)
    (hy₂2 : ∀ x ∈ s, HasDerivAt (deriv y₂) (deriv (deriv y₂) x) x)
    (hu : ∀ x ∈ s, HasDerivAt u (deriv u x) x)
    (hu2 : ∀ x ∈ s, HasDerivAt (deriv u) (deriv (deriv u) x) x)
    (h₁ : ∀ x ∈ s, deriv (deriv y₁) x = p x * deriv y₁ x + q x * y₁ x)
    (h₂ : ∀ x ∈ s, deriv (deriv y₂) x = p x * deriv y₂ x + q x * y₂ x)
    (hu' : ∀ x ∈ s, deriv (deriv u) x = p x * deriv u x + q x * u x)
    (hW : ∀ x ∈ s, wron y₁ y₂ x ≠ 0) :
    ∃ c₁ c₂ : ℝ, ∀ x ∈ s, u x = c₁ * y₁ x + c₂ * y₂ x := by
  have huW : ∀ x ∈ s, HasDerivAt (wron u y₂) (p x * wron u y₂ x) x :=
    deriv_wron hu hu2 hy₂ hy₂2 hu' h₂
  have hyW : ∀ x ∈ s, HasDerivAt (wron y₁ u) (p x * wron y₁ u x) x :=
    deriv_wron hy₁ hy₁2 hu hu2 h₁ hu'
  have hWW : ∀ x ∈ s, HasDerivAt (wron y₁ y₂) (p x * wron y₁ y₂ x) x :=
    deriv_wron hy₁ hy₁2 hy₂ hy₂2 h₁ h₂
  -- the two quotients by the Wronskian have vanishing derivative
  have hz1 : ∀ x ∈ s, deriv (fun y => wron u y₂ y / wron y₁ y₂ y) x = 0 := by
    intro x hx
    have h : HasDerivAt (fun y : ℝ => wron u y₂ y / wron y₁ y₂ y)
        (((p x * wron u y₂ x) * wron y₁ y₂ x - wron u y₂ x * (p x * wron y₁ y₂ x))
          / wron y₁ y₂ x ^ 2) x :=
      (huW x hx).div (hWW x hx) (hW x hx)
    have hnum : (p x * wron u y₂ x) * wron y₁ y₂ x
        - wron u y₂ x * (p x * wron y₁ y₂ x) = 0 := by ring
    rw [h.deriv, hnum, zero_div]
  have hz2 : ∀ x ∈ s, deriv (fun y => wron y₁ u y / wron y₁ y₂ y) x = 0 := by
    intro x hx
    have h : HasDerivAt (fun y : ℝ => wron y₁ u y / wron y₁ y₂ y)
        (((p x * wron y₁ u x) * wron y₁ y₂ x - wron y₁ u x * (p x * wron y₁ y₂ x))
          / wron y₁ y₂ x ^ 2) x :=
      (hyW x hx).div (hWW x hx) (hW x hx)
    have hnum : (p x * wron y₁ u x) * wron y₁ y₂ x
        - wron y₁ u x * (p x * wron y₁ y₂ x) = 0 := by ring
    rw [h.deriv, hnum, zero_div]
  have hd1 : DifferentiableOn ℝ (fun y => wron u y₂ y / wron y₁ y₂ y) s :=
    DifferentiableOn.div (fun x hx => (huW x hx).differentiableAt.differentiableWithinAt)
      (fun x hx => (hWW x hx).differentiableAt.differentiableWithinAt) (fun x hx => hW x hx)
  have hd2 : DifferentiableOn ℝ (fun y => wron y₁ u y / wron y₁ y₂ y) s :=
    DifferentiableOn.div (fun x hx => (hyW x hx).differentiableAt.differentiableWithinAt)
      (fun x hx => (hWW x hx).differentiableAt.differentiableWithinAt) (fun x hx => hW x hx)
  obtain ⟨c₁, hc₁⟩ := hs.exists_is_const_of_deriv_eq_zero hsc hd1 (fun x hx => hz1 x hx)
  obtain ⟨c₂, hc₂⟩ := hs.exists_is_const_of_deriv_eq_zero hsc hd2 (fun x hx => hz2 x hx)
  have hA : ∀ x ∈ s, wron u y₂ x = c₁ * wron y₁ y₂ x := by
    intro x hx
    have h1 : wron u y₂ x / wron y₁ y₂ x * wron y₁ y₂ x = c₁ * wron y₁ y₂ x := by
      rw [hc₁ x hx]
    rwa [div_mul_cancel₀ _ (hW x hx)] at h1
  have hB : ∀ x ∈ s, wron y₁ u x = c₂ * wron y₁ y₂ x := by
    intro x hx
    have h1 : wron y₁ u x / wron y₁ y₂ x * wron y₁ y₂ x = c₂ * wron y₁ y₂ x := by
      rw [hc₂ x hx]
    rwa [div_mul_cancel₀ _ (hW x hx)] at h1
  refine ⟨c₁, c₂, fun x hx => ?_⟩
  -- multiply the two Cramer identities by `y₁`, `y₂` and add
  have key : u x * wron y₁ y₂ x = (c₁ * y₁ x + c₂ * y₂ x) * wron y₁ y₂ x := by
    have hA' := hA x hx
    have hB' := hB x hx
    simp only [wron] at hA' hB' ⊢
    linear_combination y₁ x * hA' + y₂ x * hB'
  exact mul_right_cancel₀ (hW x hx) key

/-! ## `ContDiffOn ℝ 2` supplies the two derivative facts needed at each point -/

theorem hasDerivAt_of_contDiffOn {f : ℝ → ℝ} {s : Set ℝ} (hs : IsOpen s)
    (hf : ContDiffOn ℝ 2 f s) :
    (∀ x ∈ s, HasDerivAt f (deriv f x) x) ∧
      (∀ x ∈ s, HasDerivAt (deriv f) (deriv (deriv f) x) x) := by
  constructor
  · intro x hx
    have h2 : ContDiffAt ℝ 2 f x := hf.contDiffAt (hs.mem_nhds hx)
    exact ((h2.of_le (show (1 : WithTop ℕ∞) ≤ 2 by norm_num)).differentiableAt
      (show (1 : WithTop ℕ∞) ≠ 0 by norm_num)).hasDerivAt
  · intro x hx
    have h2 : ContDiffAt ℝ 2 f x := hf.contDiffAt (hs.mem_nhds hx)
    exact ((h2.derivWithin (m := 1) (show (1 : WithTop ℕ∞) + 1 ≤ 2 by norm_num)).differentiableAt
      (show (1 : WithTop ℕ∞) ≠ 0 by norm_num)).hasDerivAt

/-! ## The two special solutions of `Lzero1 u = -u'' + (tan θ · u)' - 6u = 0` -/

private theorem deriv_sin_two (t : ℝ) :
    deriv (fun x : ℝ => Real.sin (2 * x)) t = 2 * Real.cos (2 * t) := by
  have h2 : HasDerivAt (fun x : ℝ => (2 : ℝ) * x) 2 t := by
    simpa only [id_eq, mul_one] using (hasDerivAt_id t).const_mul 2
  have h : HasDerivAt (fun x : ℝ => Real.sin (2 * x)) (Real.cos (2 * t) * 2) t := by
    simpa only [Function.comp_def] using (Real.hasDerivAt_sin (2 * t)).comp t h2
  rw [h.deriv, mul_comm]

private theorem deriv_deriv_sin_two (t : ℝ) :
    deriv (deriv (fun x : ℝ => Real.sin (2 * x))) t = -4 * Real.sin (2 * t) := by
  have hfun : deriv (fun x : ℝ => Real.sin (2 * x)) = fun x : ℝ => 2 * Real.cos (2 * x) := by
    funext x
    exact deriv_sin_two x
  rw [hfun]
  have h2 : HasDerivAt (fun x : ℝ => (2 : ℝ) * x) 2 t := by
    simpa only [id_eq, mul_one] using (hasDerivAt_id t).const_mul 2
  have hc : HasDerivAt (fun x : ℝ => Real.cos (2 * x)) (-2 * Real.sin (2 * t)) t := by
    have h := (Real.hasDerivAt_cos (2 * t)).comp t h2
    refine h.congr_deriv ?_
    ring
  exact ((hc.const_mul 2).congr_deriv (by ring)).deriv

/-- `θ ↦ sin 2θ` solves `Lzero1 y = 0` in the normal form `y'' = p y' + q y`. -/
private theorem deriv2_sin_two (θ : ℝ) (hcos : Real.cos θ ≠ 0) :
    deriv (deriv (fun t : ℝ => Real.sin (2 * t))) θ
      = Real.tan θ * deriv (fun t : ℝ => Real.sin (2 * t)) θ
        + (1 / Real.cos θ ^ 2 - 6) * Real.sin (2 * θ) := by
  rw [deriv_sin_two θ, deriv_deriv_sin_two θ]
  rw [Real.tan_eq_sin_div_cos, Real.sin_two_mul θ, Real.cos_two_mul θ]
  field_simp
  ring

/-- `LzeroSing` is differentiable on `(0, π/2)` with derivative `SingY1`. -/
private theorem hasDerivAt_LzeroSing' (θ : ℝ) (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    HasDerivAt Work.FTS.EllipticEst.LzeroSing (Work.FTS.EllipticEst.SingY1 θ) θ := by
  have hsin : HasDerivAt (fun t : ℝ => Real.sin (2 * t)) (2 * Real.cos (2 * θ)) θ := by
    have h2 : HasDerivAt (fun t : ℝ => (2 : ℝ) * t) 2 θ := by
      simpa only [id_eq, mul_one] using (hasDerivAt_id θ).const_mul 2
    exact ((Real.hasDerivAt_sin (2 * θ)).comp θ h2).congr_deriv (by ring)
  have hint : HasDerivAt Work.FTS.EllipticEst.SingInt
      (-(Work.FTS.EllipticEst.LzeroSingIntegrand (Real.pi / 2 - θ))) θ :=
    Work.FTS.EllipticEst.SingInt_hasDerivAt θ hθ
  have hval : 2 * Real.cos (2 * θ) * Work.FTS.EllipticEst.SingInt θ
      + Real.sin (2 * θ) * (-(Work.FTS.EllipticEst.LzeroSingIntegrand (Real.pi / 2 - θ)))
        = Work.FTS.EllipticEst.SingY1 θ := by
    rw [Work.FTS.EllipticEst.SingY1_apply,
      ← Work.FTS.EllipticEst.LzeroAux.sin_mul_integrand θ hθ]
    ring
  exact (hsin.mul hint).congr_deriv hval

/-- `LzeroSing` is differentiable on `(0, π/2)`. -/
private theorem hasDerivAt_LzeroSing (θ : ℝ) (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    HasDerivAt Work.FTS.EllipticEst.LzeroSing
      (deriv Work.FTS.EllipticEst.LzeroSing θ) θ :=
  (hasDerivAt_LzeroSing' θ hθ).congr_deriv (hasDerivAt_LzeroSing' θ hθ).deriv.symm

/-- `deriv LzeroSing` is differentiable on `(0, π/2)`. -/
private theorem hasDerivAt_deriv_LzeroSing (θ : ℝ) (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    HasDerivAt (deriv Work.FTS.EllipticEst.LzeroSing)
      (deriv (deriv Work.FTS.EllipticEst.LzeroSing) θ) θ := by
  have hev : deriv Work.FTS.EllipticEst.LzeroSing =ᶠ[𝓝 θ] Work.FTS.EllipticEst.SingY1 := by
    filter_upwards [isOpen_Ioo.mem_nhds hθ] with y hy
    exact (hasDerivAt_LzeroSing' y hy).deriv
  have h2 : HasDerivAt Work.FTS.EllipticEst.SingY1 (Work.FTS.EllipticEst.SingY2 θ) θ :=
    Work.FTS.EllipticEst.SingY1_hasDerivAt_self θ hθ
  have hval : deriv (deriv Work.FTS.EllipticEst.LzeroSing) θ
      = Work.FTS.EllipticEst.SingY2 θ := by
    rw [Filter.EventuallyEq.deriv_eq hev, h2.deriv]
  exact (hev.hasDerivAt_iff.mpr h2).congr_deriv hval.symm

/-- `LzeroSing` solves `Lzero1 y = 0` in the normal form `y'' = p y' + q y`. -/
private theorem deriv2_LzeroSing (θ : ℝ) (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    deriv (deriv Work.FTS.EllipticEst.LzeroSing) θ
      = Real.tan θ * deriv Work.FTS.EllipticEst.LzeroSing θ
        + (1 / Real.cos θ ^ 2 - 6) * Work.FTS.EllipticEst.LzeroSing θ := by
  have hcos : Real.cos θ ≠ 0 :=
    ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, hθ.1], hθ.2⟩)
  have hprod : HasDerivAt (fun τ : ℝ => Real.tan τ * Work.FTS.EllipticEst.LzeroSing τ)
      ((1 / Real.cos θ ^ 2) * Work.FTS.EllipticEst.LzeroSing θ
        + Real.tan θ * deriv Work.FTS.EllipticEst.LzeroSing θ) θ :=
    (Real.hasDerivAt_tan hcos).mul (hasDerivAt_LzeroSing θ hθ)
  have h := Work.FTS.EllipticEst.LzeroSingODE θ hθ
  rw [hprod.deriv] at h
  linarith

/-- The Wronskian of `sin 2θ` and `LzeroSing` is `-1/cos θ` on `(0, π/2)`. -/
private theorem wron_sin_LzeroSing (θ : ℝ) (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    wron (fun t : ℝ => Real.sin (2 * t)) Work.FTS.EllipticEst.LzeroSing θ
      = -1 / Real.cos θ := by
  have hWR := Work.FTS.EllipticEst.LzeroSingWronskian θ hθ
  rw [wron_apply]
  exact hWR

/-- **Every solution of `Lzero1 u = 0` on `(0, π/2)` is a linear combination of the two
solutions `sin 2θ` and `LzeroSing`.** -/
theorem LzeroSolSpan {u : ℝ → ℝ} (hsm : ContDiffOn ℝ 2 u (Set.Ioo (0 : ℝ) (Real.pi / 2)))
    (hu : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      -(deriv (deriv u) θ) + deriv (fun θ' => Real.tan θ' * u θ') θ - 6 * u θ = 0) :
    ∃ a b : ℝ, ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      u θ = a * Real.sin (2 * θ) + b * Work.FTS.EllipticEst.LzeroSing θ := by
  have hsm₁ : ContDiffOn ℝ 2 (fun t : ℝ => Real.sin (2 * t)) (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
    fun_prop
  obtain ⟨hy₁, hy₁2⟩ := hasDerivAt_of_contDiffOn isOpen_Ioo hsm₁
  obtain ⟨hu1, hu2⟩ := hasDerivAt_of_contDiffOn isOpen_Ioo hsm
  -- the normal form of the equation for `u`
  have hu' : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      deriv (deriv u) θ = Real.tan θ * deriv u θ + (1 / Real.cos θ ^ 2 - 6) * u θ := by
    intro θ hθ
    have hcos : Real.cos θ ≠ 0 :=
      ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, hθ.1], hθ.2⟩)
    have hd : deriv (fun θ' : ℝ => Real.tan θ' * u θ') θ
        = (1 / Real.cos θ ^ 2) * u θ + Real.tan θ * deriv u θ :=
      ((Real.hasDerivAt_tan hcos).mul (hu1 θ hθ)).deriv
    have h0 := hu θ hθ
    rw [hd] at h0
    linarith
  have h₁ : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      deriv (deriv (fun t : ℝ => Real.sin (2 * t))) θ
        = Real.tan θ * deriv (fun t : ℝ => Real.sin (2 * t)) θ
          + (1 / Real.cos θ ^ 2 - 6) * Real.sin (2 * θ) := by
    intro θ hθ
    exact deriv2_sin_two θ (ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, hθ.1], hθ.2⟩))
  have hW : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      wron (fun t : ℝ => Real.sin (2 * t)) Work.FTS.EllipticEst.LzeroSing θ ≠ 0 := by
    intro θ hθ
    have hcos : Real.cos θ ≠ 0 :=
      ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, hθ.1], hθ.2⟩)
    rw [wron_sin_LzeroSing θ hθ]
    exact div_ne_zero (by norm_num) hcos
  obtain ⟨a, b, hab⟩ := span_of_two_solutions (p := Real.tan)
    (q := fun θ => 1 / Real.cos θ ^ 2 - 6) (y₁ := fun t : ℝ => Real.sin (2 * t))
    (y₂ := Work.FTS.EllipticEst.LzeroSing) (u := u) isOpen_Ioo isPreconnected_Ioo
    hy₁ hy₁2 (fun x hx => hasDerivAt_LzeroSing x hx)
    (fun x hx => hasDerivAt_deriv_LzeroSing x hx) hu1 hu2 h₁ deriv2_LzeroSing hu' hW
  exact ⟨a, b, hab⟩

end Work.FTS.EllipticEst.H2W
