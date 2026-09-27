import Mathlib
import Submission.Work.Drive.sepFamDefs

/-!
# The parameter-derivative of the loop family of the separated germ route is onto

`Work.Drive.SepLoopMfderivSurj Ξ Q A B τ y` (`Submission/Work/Drive/sepFamDefs.lean`) says that the
manifold parameter-derivative at the shift `τ` of

> `τ' ↦ famLoop (sepLoopFam Ξ Q A B τ') y`

is **onto**.  This is the loop-side `hsurj` brick of the parametric-Sard engines of the separated
germ route: the perturbation parameter `τ` moves the *loop's* chart only, so the derivative of the
loop family is onto as soon as the perturbation family is.

## The mechanism

`famLoop (sepLoopFam Ξ Q A B τ') y` only reads the perturbed chart at the *single* point
`Q (exp (π * (y 1) * I))` of the disk (and the shift enters only through `sepPathL A B (y 0) + τ'`);
in coordinates the family is

> `τ' ↦ Ξ (sepPathL A B (y 0) + τ') p₀`,   `p₀ = Q (exp (π * (y 1 : ℂ) * I))`,

which is the composite of the *translation* `τ' ↦ c + τ'` (`c = sepPathL A B (y 0)`) with the
perturbation family `σ ↦ Ξ σ p₀` — both `C^∞`, the first a diffeomorphism.  By the chain rule the
parameter-derivative at `τ` is the composite of `mfderiv (fun σ => Ξ σ p₀) (c + τ)` — which is onto
at *every* parameter and every point of the capping space, by the third clause of
`Work.Drive.ChartPert` — with `mfderiv (fun τ' => c + τ') τ`, which is the identity of the model
space (`fderiv` of a translation).  Composing an onto map with an onto map is onto.

The sub-step is isolated as the reusable lemma `Work.Drive.surjective_mfderiv_chartPert_translate`.

Note that `IsSmoothChart Q` is *not* used: the loop family enters through the perturbation parameter
only, and the disk presentation `Q` contributes just the fixed point `p₀` the family is evaluated at.
-/

namespace Work.Drive

open Manifold Filter Set
open scoped Manifold ContDiff Topology

attribute [local instance] Work.Drive.cappingCharted Work.Drive.isManifold_cappingCharted
  Work.Drive.t2Space_cappingSpace Work.Drive.projCharted

noncomputable section

set_option linter.unusedVariables false
set_option maxHeartbeats 800000

/-- **The parameter-derivative of the perturbation family along a translated path is onto.**

If `Ξ` is a chart perturbation (`Work.Drive.ChartPert Q m Ξ`) then for every point `p` of the capping
space and every translation `τ' ↦ c + τ'` of the parameter space, the parameter-derivative of
`τ' ↦ Ξ (c + τ') p` at `τ` is onto: the translation's derivative is the identity of the model space
and the perturbation family's derivative is onto at every parameter and every point. -/
theorem surjective_mfderiv_chartPert_translate {m : ℕ}
    {Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace}
    {Q : ℂ → CappingSpace} (hΞ : ChartPert Q m Ξ)
    (p : CappingSpace) (c τ : EuclideanSpace ℝ (Fin m)) :
    Function.Surjective (mfderiv (𝓡 m) (𝓡 4)
      (fun τ' : EuclideanSpace ℝ (Fin m) => Ξ (c + τ') p) τ) := by
  -- both factors are differentiable: the translation (a map of model spaces) ...
  have hmd₂ : MDifferentiableAt (𝓡 m) (𝓡 m)
      (fun τ' : EuclideanSpace ℝ (Fin m) => c + τ') τ :=
    (differentiableAt_id.const_add c).mdifferentiableAt
  -- ... and the perturbation family at the fixed point `p`
  have hmd₁ : MDifferentiableAt (𝓡 m) (𝓡 4)
      (fun σ : EuclideanSpace ℝ (Fin m) => Ξ σ p) (c + τ) := by
    have hpair : ContMDiffAt (𝓡 m) ((𝓡 m).prod (𝓡 4)) Ctop
        (fun σ : EuclideanSpace ℝ (Fin m) => (σ, p)) (c + τ) :=
      ContMDiffAt.prodMk contMDiffAt_id contMDiffAt_const
    exact ((hΞ.2.1.contMDiffAt (x := (c + τ, p))).comp (c + τ) hpair).mdifferentiableAt (by simp)
  -- reindex the family as a composite (definitionally, so `rfl`)
  rw [show (fun τ' : EuclideanSpace ℝ (Fin m) => Ξ (c + τ') p)
      = (fun σ : EuclideanSpace ℝ (Fin m) => Ξ σ p) ∘
        (fun τ' : EuclideanSpace ℝ (Fin m) => c + τ') from rfl]
  -- the chain rule
  rw [mfderiv_comp (I := 𝓡 m) (I' := 𝓡 m) (I'' := 𝓡 4)
    (f := fun τ' : EuclideanSpace ℝ (Fin m) => c + τ')
    (g := fun σ : EuclideanSpace ℝ (Fin m) => Ξ σ p) τ hmd₁ hmd₂]
  -- the derivative of the translation is the identity of `ℝᵐ`
  have h2 : Function.Surjective
      (mfderiv (𝓡 m) (𝓡 m) (fun τ' : EuclideanSpace ℝ (Fin m) => c + τ') τ) := by
    rw [mfderiv_eq_fderiv]
    have hd : fderiv ℝ (fun τ' : EuclideanSpace ℝ (Fin m) => c + τ') τ
        = ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin m)) := by
      have h := ((hasFDerivAt_id (𝕜 := ℝ) (x := τ)).const_add c).fderiv
      simpa using h
    rw [hd]
    intro v
    exact ⟨v, ContinuousLinearMap.id_apply v⟩
  -- compose the two onto derivatives
  intro w
  obtain ⟨u, hu⟩ := hΞ.2.2 (c + τ) p w
  obtain ⟨v, hv⟩ := h2 u
  exact ⟨v, by rw [ContinuousLinearMap.comp_apply, hv, hu]⟩

theorem sepLoopMfderivSurj {m : ℕ}
    (Ξ : EuclideanSpace ℝ (Fin m) → Work.Drive.CappingSpace → Work.Drive.CappingSpace)
    (Q : ℂ → Work.Drive.CappingSpace) (hΞ : Work.Drive.ChartPert Q m Ξ)
    (hQ : Work.Drive.IsSmoothChart Q)
    (A B : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m))
    (τ : EuclideanSpace ℝ (Fin m)) (y : EuclideanSpace ℝ (Fin 5)) :
    Work.Drive.SepLoopMfderivSurj Ξ Q A B τ y := by
  rw [SepLoopMfderivSurj]
  -- in coordinates the loop family is the perturbation family along the translated path
  show Function.Surjective (mfderiv (𝓡 m) (𝓡 4)
    ((fun σ : EuclideanSpace ℝ (Fin m) =>
        Ξ σ (Q (Complex.exp (Real.pi * ((y 1 : ℝ) : ℂ) * Complex.I)))) ∘
      (fun τ' : EuclideanSpace ℝ (Fin m) => sepPathL A B (y 0) + τ')) τ)
  exact surjective_mfderiv_chartPert_translate hΞ _ _ _

end

end Work.Drive
