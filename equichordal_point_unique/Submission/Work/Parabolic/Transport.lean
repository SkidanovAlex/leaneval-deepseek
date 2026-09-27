import Submission.Work.Parabolic.Deps
import Submission.Work.Parabolic.harmonicOnX_comp_biholomorph

/-!
# Transport of Green functions along a biholomorphism

`IsGreenFunctionAt` is a *conformal* invariant: if `Φ : X ≃ₘ⟮mℂ, mℂ⟯ Y` is a biholomorphism of
one-dimensional complex manifolds (the plain notation is Mathlib's smoothness level `∞`, which for
the model `modelWithCornersSelf ℂ ℂ` means complex-analytic, see
`Work.Parabolic.harmonicOnX_comp_biholomorph`) and `E` is a Green function on `Y` with pole `y₀`,
then `x ↦ E (Φ x)` is a Green function on `X` with pole `Φ.symm y₀`:

* positivity is transported pointwise (using the bijectivity of `Φ`);
* harmonicity is transported by `Work.Parabolic.harmonicOnX_comp_biholomorph`;
* relative compactness of the superlevel sets is transported by the homeomorphism `Φ` (preimages of
  closures are closures of preimages).

The main consumers are `Work.Parabolic.hasGreenFunction_of_biholomorphic_upperHalfPlane` and
`Work.Parabolic.isParabolic.not_nonempty_diffeomorph_upperHalfPlane` (`Reduction.lean`): the
hyperbolic end of the uniformization dichotomy is incompatible with parabolicity.
-/

open LeanEval.Geometry
open scoped Manifold ContDiff Topology

set_option linter.unusedSectionVars false

noncomputable section

open Filter Set
open Classical

namespace Work.Parabolic

/-- **Transport of a Green function along a biholomorphism.** -/
theorem isGreenFunctionAt_comp_diffeomorph {X Y : Type*} [TopologicalSpace X] [T2Space X]
    [ChartedSpace ℂ X] [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] [TopologicalSpace Y] [T2Space Y]
    [ChartedSpace ℂ Y] [IsManifold (modelWithCornersSelf ℂ ℂ) 1 Y]
    (Φ : X ≃ₘ⟮modelWithCornersSelf ℂ ℂ, modelWithCornersSelf ℂ ℂ⟯ Y) {y₀ : Y} {E : Y → ℝ}
    (h : IsGreenFunctionAt (X := Y) y₀ E) :
    IsGreenFunctionAt (X := X) (Φ.symm y₀) (fun x => E (Φ x)) := by
  have hkey : ∀ x : X, (Φ x = y₀) ↔ (x = Φ.symm y₀) := by
    intro x
    constructor
    · intro hx
      have h1 := congrArg Φ.symm hx
      rwa [Diffeomorph.symm_apply_apply] at h1
    · intro hx
      rw [hx, Φ.apply_symm_apply]
  refine ⟨?_, ?_, ?_⟩
  · intro y hy
    exact h.pos (x := Φ y) (fun hcon => hy ((hkey y).mp hcon))
  · have hpre : Φ ⁻¹' (Set.univ \ {y₀}) = Set.univ \ {Φ.symm y₀} := by
      ext x
      simp only [Set.mem_preimage, Set.mem_sdiff, Set.mem_univ, true_and, Set.mem_singleton_iff]
      exact not_congr (hkey x)
    have := harmonicOnX_comp_biholomorph (Φ := Φ) h.harmonic
    rwa [hpre] at this
  · intro ε hε
    have hc := h.isCompact_closure_level hε
    have hpre : {x : X | ε ≤ E (Φ x)} = Φ.toHomeomorph ⁻¹' {y : Y | ε ≤ E y} := rfl
    rw [hpre, ← Φ.toHomeomorph.preimage_closure]
    exact (Φ.toHomeomorph.isCompact_preimage).mpr hc

/-- **Transport of the existence of a Green function along a biholomorphism.** -/
theorem hasGreenFunctionAt_of_diffeomorph {X Y : Type*} [TopologicalSpace X] [T2Space X]
    [ChartedSpace ℂ X] [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] [TopologicalSpace Y] [T2Space Y]
    [ChartedSpace ℂ Y] [IsManifold (modelWithCornersSelf ℂ ℂ) 1 Y]
    (Φ : X ≃ₘ⟮modelWithCornersSelf ℂ ℂ, modelWithCornersSelf ℂ ℂ⟯ Y) {y₀ : Y}
    (h : HasGreenFunctionAt (X := Y) y₀) :
    HasGreenFunctionAt (X := X) (Φ.symm y₀) :=
  let ⟨E, hE⟩ := h
  ⟨fun x => E (Φ x), isGreenFunctionAt_comp_diffeomorph Φ hE⟩

/-- **A complex manifold biholomorphic to a hyperbolic one is hyperbolic.** -/
theorem hasGreenFunction_of_diffeomorph {X Y : Type*} [TopologicalSpace X] [T2Space X]
    [ChartedSpace ℂ X] [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] [TopologicalSpace Y] [T2Space Y]
    [ChartedSpace ℂ Y] [IsManifold (modelWithCornersSelf ℂ ℂ) 1 Y]
    (Φ : X ≃ₘ⟮modelWithCornersSelf ℂ ℂ, modelWithCornersSelf ℂ ℂ⟯ Y)
    (h : HasGreenFunction Y) : HasGreenFunction X := by
  obtain ⟨y₀, hy₀⟩ := h
  exact ⟨Φ.symm y₀, hasGreenFunctionAt_of_diffeomorph Φ hy₀⟩

end Work.Parabolic
