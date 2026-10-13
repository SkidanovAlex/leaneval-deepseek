/-
Continuity of the transported operator `kopDr ψ` in the `(σ,θ)`-coordinates on the half-strip
`ℝ × (0, π/2)`.

For a jointly smooth `ψ : ℝ → ℝ → ℝ`, all the ingredients of

`kopDr ψ σ θ = - ψ_{σσ} - ψ_{θθ} - 5 ψ_σ + tan θ · ψ_θ + (tan θ² - 5) · ψ`

are continuous: the second derivatives because `fderiv` of a `C^∞` function is again `C^∞`
(and the one-dimensional `deriv` of a slice is `fderiv` of the ambient function applied to the
unit coordinate vector), and `tan` because `cos θ ≠ 0` on `(0, π/2)`.

The two auxiliary operators `pderivσ` / `pderivθ` take the partial derivative of a function of
two variables *as a function of the point*, which is what the recursion for higher derivatives
needs.
-/
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.EllipticEst.InteriorRegularity.Q0.RRKop

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.EllipticEst.InteriorRegularity.Q0

set_option autoImplicit false
set_option linter.unusedVariables false

/-- The `σ`-partial derivative of a function of two variables, as a function of the point. -/
def pderivσ (Φ : ℝ × ℝ → ℝ) : ℝ × ℝ → ℝ := fun q => deriv (fun σ' => Φ (σ', q.2)) q.1

/-- The `θ`-partial derivative of a function of two variables, as a function of the point. -/
def pderivθ (Φ : ℝ × ℝ → ℝ) : ℝ × ℝ → ℝ := fun q => deriv (fun θ' => Φ (q.1, θ')) q.2

/-- The `σ`-partial derivative at a point is `fderiv` applied to the first coordinate vector. -/
lemma pderivσ_eq_fderiv {Φ : ℝ × ℝ → ℝ} {σ θ : ℝ} (hΦ : DifferentiableAt ℝ Φ (σ, θ)) :
    pderivσ Φ (σ, θ) = fderiv ℝ Φ (σ, θ) (1, 0) := by
  show deriv (fun σ' => Φ (σ', θ)) σ = fderiv ℝ Φ (σ, θ) (1, 0)
  have h1 : HasFDerivAt (fun e : ℝ => (e, θ)) (ContinuousLinearMap.inl ℝ ℝ ℝ) σ :=
    hasFDerivAt_prodMk_left σ θ
  have h2 : HasFDerivAt (fun e : ℝ => Φ (e, θ))
      ((fderiv ℝ Φ (σ, θ)).comp (ContinuousLinearMap.inl ℝ ℝ ℝ)) σ := by
    have h := hΦ.hasFDerivAt.comp σ h1
    simpa [Function.comp_def] using h
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply]
    using h2.hasDerivAt.deriv

/-- The `θ`-partial derivative at a point is `fderiv` applied to the second coordinate vector. -/
lemma pderivθ_eq_fderiv {Φ : ℝ × ℝ → ℝ} {σ θ : ℝ} (hΦ : DifferentiableAt ℝ Φ (σ, θ)) :
    pderivθ Φ (σ, θ) = fderiv ℝ Φ (σ, θ) (0, 1) := by
  show deriv (fun θ' => Φ (σ, θ')) θ = fderiv ℝ Φ (σ, θ) (0, 1)
  have h1 : HasFDerivAt (fun e : ℝ => (σ, e)) (ContinuousLinearMap.inr ℝ ℝ ℝ) θ :=
    hasFDerivAt_prodMk_right σ θ
  have h2 : HasFDerivAt (fun e : ℝ => Φ (σ, e))
      ((fderiv ℝ Φ (σ, θ)).comp (ContinuousLinearMap.inr ℝ ℝ ℝ)) θ := by
    have h := hΦ.hasFDerivAt.comp θ h1
    simpa [Function.comp_def] using h
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply]
    using h2.hasDerivAt.deriv

/-- `pderivσ` preserves smoothness. -/
lemma contDiff_pderivσ {Φ : ℝ × ℝ → ℝ} (hΦ : ∀ n : ℕ, ContDiff ℝ n Φ) :
    ∀ n : ℕ, ContDiff ℝ n (pderivσ Φ) := by
  intro n
  have h1 : ContDiff ℝ (n : WithTop ℕ∞)
      (fun p : (ℝ × ℝ) × (ℝ × ℝ) => (fderiv ℝ Φ p.1 : (ℝ × ℝ) →L[ℝ] ℝ) p.2) :=
    (hΦ (n + 1)).contDiff_fderiv_apply (by simp)
  have h2 : ContDiff ℝ (n : WithTop ℕ∞)
      (fun q : ℝ × ℝ => (fderiv ℝ Φ q : (ℝ × ℝ) →L[ℝ] ℝ) ((1 : ℝ), 0)) :=
    h1.comp (ContDiff.prodMk contDiff_id contDiff_const)
  rw [show pderivσ Φ = fun q : ℝ × ℝ => (fderiv ℝ Φ q : (ℝ × ℝ) →L[ℝ] ℝ) ((1 : ℝ), 0) from
    funext fun q => pderivσ_eq_fderiv ((hΦ 1).differentiable (by norm_num) q)]
  exact h2

/-- `pderivθ` preserves smoothness. -/
lemma contDiff_pderivθ {Φ : ℝ × ℝ → ℝ} (hΦ : ∀ n : ℕ, ContDiff ℝ n Φ) :
    ∀ n : ℕ, ContDiff ℝ n (pderivθ Φ) := by
  intro n
  have h1 : ContDiff ℝ (n : WithTop ℕ∞)
      (fun p : (ℝ × ℝ) × (ℝ × ℝ) => (fderiv ℝ Φ p.1 : (ℝ × ℝ) →L[ℝ] ℝ) p.2) :=
    (hΦ (n + 1)).contDiff_fderiv_apply (by simp)
  have h2 : ContDiff ℝ (n : WithTop ℕ∞)
      (fun q : ℝ × ℝ => (fderiv ℝ Φ q : (ℝ × ℝ) →L[ℝ] ℝ) ((0 : ℝ), 1)) :=
    h1.comp (ContDiff.prodMk contDiff_id contDiff_const)
  rw [show pderivθ Φ = fun q : ℝ × ℝ => (fderiv ℝ Φ q : (ℝ × ℝ) →L[ℝ] ℝ) ((0 : ℝ), 1) from
    funext fun q => pderivθ_eq_fderiv ((hΦ 1).differentiable (by norm_num) q)]
  exact h2

/-- **Continuity of the transported operator.**  For a jointly smooth `ψ`, the operator
`kopDr ψ` is continuous on the half-strip `ℝ × (0, π/2)`. -/
theorem continuousOn_kopDr {ψ : ℝ → ℝ → ℝ} (hψ : ∀ n : ℕ, ContDiff ℝ n (Function.uncurry ψ)) :
    ContinuousOn (fun q : ℝ × ℝ => kopDr ψ q.1 q.2) (Set.univ ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
  let s : Set (ℝ × ℝ) := Set.univ ×ˢ Set.Ioo 0 (Real.pi / 2)
  change ContinuousOn (fun q : ℝ × ℝ => kopDr ψ q.1 q.2) s
  have hF : ∀ n : ℕ, ContDiff ℝ n (Function.uncurry ψ) := hψ
  have hσ : ∀ n : ℕ, ContDiff ℝ n (pderivσ (Function.uncurry ψ)) := contDiff_pderivσ hF
  have hθ : ∀ n : ℕ, ContDiff ℝ n (pderivθ (Function.uncurry ψ)) := contDiff_pderivθ hF
  have hσσ : ∀ n : ℕ, ContDiff ℝ n (pderivσ (pderivσ (Function.uncurry ψ))) :=
    contDiff_pderivσ hσ
  have hθθ : ∀ n : ℕ, ContDiff ℝ n (pderivθ (pderivθ (Function.uncurry ψ))) :=
    contDiff_pderivθ hθ
  have cF : ContinuousOn (Function.uncurry ψ) s := (hF 0).continuous.continuousOn
  have cσ : ContinuousOn (pderivσ (Function.uncurry ψ)) s := (hσ 0).continuous.continuousOn
  have cθ : ContinuousOn (pderivθ (Function.uncurry ψ)) s := (hθ 0).continuous.continuousOn
  have cσσ : ContinuousOn (pderivσ (pderivσ (Function.uncurry ψ))) s :=
    (hσσ 0).continuous.continuousOn
  have cθθ : ContinuousOn (pderivθ (pderivθ (Function.uncurry ψ))) s :=
    (hθθ 0).continuous.continuousOn
  have hcos : ∀ q ∈ s, Real.cos q.2 ≠ 0 := by
    intro q hq
    exact ne_of_gt (Real.cos_pos_of_mem_Ioo
      ⟨by linarith [Real.pi_pos, hq.2.1], hq.2.2⟩)
  have ctan : ContinuousOn (fun q : ℝ × ℝ => Real.tan q.2) s :=
    Real.continuousOn_tan.comp continuous_snd.continuousOn hcos
  have hmain : ContinuousOn (fun q : ℝ × ℝ =>
      - pderivσ (pderivσ (Function.uncurry ψ)) q - pderivθ (pderivθ (Function.uncurry ψ)) q
      - 5 * pderivσ (Function.uncurry ψ) q + Real.tan q.2 * pderivθ (Function.uncurry ψ) q
      + ((Real.tan q.2) ^ 2 - 5) * Function.uncurry ψ q) s := by
    have hA : ContinuousOn (fun q : ℝ × ℝ => - pderivσ (pderivσ (Function.uncurry ψ)) q
        - pderivθ (pderivθ (Function.uncurry ψ)) q - 5 * pderivσ (Function.uncurry ψ) q) s :=
      (cσσ.neg.sub cθθ).sub (cσ.const_mul 5)
    have hB : ContinuousOn (fun q : ℝ × ℝ => Real.tan q.2 * pderivθ (Function.uncurry ψ) q
        + ((Real.tan q.2) ^ 2 - 5) * Function.uncurry ψ q) s :=
      (ctan.mul cθ).add (((ctan.pow 2).sub continuousOn_const).mul cF)
    refine (hA.add hB).congr fun q hq => ?_
    simp only [Pi.add_apply]
    ring
  refine hmain.congr fun q hq => ?_
  simp only [kopDr, pderivσ, pderivθ, Function.uncurry]

end Work.EllipticEst.InteriorRegularity.Q0
