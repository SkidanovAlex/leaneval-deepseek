/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Lifting generalized loops through a covering map

This file contains the two covering-space ingredients of the asphericity argument:

* `IsCoveringMap.exists_lift_genLoop`: a generalized loop `f : Ω^k X x` lifts to the total space
  of a covering map `p : E → X` through any prescribed lift of the basepoint;
* `lift_genLoop_boundary`: the lift of a generalized loop is *constant* on the boundary `∂I^k`
  (`k ≥ 2`), because the boundary maps into a fibre of `p`, which is discrete.
-/
import Mathlib
import Submission.Work.Aspherical.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open scoped Topology unitInterval

namespace Work.Aspherical

noncomputable section

variable {X E : Type*} [TopologicalSpace X] [TopologicalSpace E] {p : E → X}

/-- **Lifting of generalized loops.** A generalized loop `f : Ω^k X x` in the base of a covering
map `p : E → X`, together with a lift `e₀` of the basepoint `x` and a boundary point `a₀` of the
cube, lifts to a map `F : I^k → E` with `F a₀ = e₀` and `p ∘ F = f`. -/
theorem IsCoveringMap.exists_lift_genLoop (hp : IsCoveringMap p) {k : ℕ} {x : X}
    (f : GenLoop (Fin k) X x) {a₀ : I^Fin k} (ha₀ : a₀ ∈ Cube.boundary (Fin k)) {e₀ : E}
    (he : p e₀ = x) :
    ∃ F : C(I^Fin k, E), F a₀ = e₀ ∧ p ∘ F = f.1 := by
  obtain ⟨F, hF, -⟩ :=
    hp.existsUnique_continuousMap_lifts f.1 a₀ e₀ (by rw [he]; exact (f.2 a₀ ha₀).symm)
  exact ⟨F, hF.1, hF.2⟩

/-- **A lift of a generalized loop is constant on the boundary.** If `F : I^k → E` lifts a
generalized loop `f : Ω^k X x` and `F a₀ = e₀` for a boundary point `a₀`, then `F` is constant
equal to `e₀` on the whole boundary, provided any two boundary points can be joined by a path
inside the boundary (compare `Work.Aspherical.cube_joinedIn_boundary`). -/
theorem lift_genLoop_boundary (hp : IsCoveringMap p) {k : ℕ} {x : X} {f : GenLoop (Fin k) X x}
    {F : C(I^Fin k, E)} (hF : p ∘ F = f.1) {a₀ : I^Fin k} (ha₀ : a₀ ∈ Cube.boundary (Fin k))
    {e₀ : E} (hF₀ : F a₀ = e₀) {y : I^Fin k} (hy : y ∈ Cube.boundary (Fin k)) (γ : Path a₀ y)
    (hγ : ∀ t, γ t ∈ Cube.boundary (Fin k)) : F y = e₀ := by
  -- `p e₀ = x`
  have hpe : p e₀ = x := by
    have h1 : p (F a₀) = (p ∘ ⇑F) a₀ := rfl
    rw [← hF₀, h1, congr_fun hF a₀, f.2 a₀ ha₀]
  -- `f ∘ γ` is the constant path at `x`
  have hconst : f.1.comp γ.toContinuousMap = ContinuousMap.const I x := by
    ext t
    exact f.2 (γ t) (hγ t)
  -- the base point of the lift of `f ∘ γ`
  have h0 : (f.1.comp γ.toContinuousMap) 0 = p e₀ := by
    rw [ContinuousMap.comp_apply, Path.coe_toContinuousMap, γ.source]
    exact (f.2 a₀ ha₀).trans hpe.symm
  -- `F ∘ γ` is a lift of `f ∘ γ` starting at `e₀`, hence equals `liftPath`
  have hbase : (F.comp γ.toContinuousMap) 0 = e₀ := by
    rw [ContinuousMap.comp_apply, Path.coe_toContinuousMap, γ.source]
    exact hF₀
  have hlifts : p ∘ (F.comp γ.toContinuousMap) = f.1.comp γ.toContinuousMap := by
    ext t
    exact congr_fun hF (γ t)
  have hlift : F.comp γ.toContinuousMap =
      hp.liftPath (f.1.comp γ.toContinuousMap) e₀ h0 := by
    rw [IsCoveringMap.eq_liftPath_iff']
    exact ⟨hlifts, hbase⟩
  -- the constant path is also a lift, so it *is* `liftPath`
  have key : ContinuousMap.const I e₀ =
      hp.liftPath (f.1.comp γ.toContinuousMap) e₀ h0 := by
    rw [IsCoveringMap.eq_liftPath_iff']
    refine ⟨?_, rfl⟩
    rw [hconst]
    ext t
    exact hpe
  calc F y = (F.comp γ.toContinuousMap) 1 := by
        rw [ContinuousMap.comp_apply, Path.coe_toContinuousMap, γ.target]
    _ = hp.liftPath (f.1.comp γ.toContinuousMap) e₀ h0 1 := by rw [hlift]
    _ = e₀ := by rw [← key]; rfl

/-- A covering map with path connected base and nonempty total space is surjective: any point of
the base is reached by a lift of a path from a point in the image. -/
theorem IsCoveringMap.surjective_of_pathConnectedSpace (hp : IsCoveringMap p)
    [PathConnectedSpace X] [Nonempty E] : Function.Surjective p := by
  intro x
  obtain ⟨e⟩ := (inferInstance : Nonempty E)
  obtain ⟨γ⟩ := PathConnectedSpace.joined (p e) x
  refine ⟨hp.liftPath γ e γ.source 1, ?_⟩
  have h := congr_fun (hp.liftPath_lifts γ e γ.source) 1
  rw [Function.comp_apply] at h
  rw [h]
  simpa using γ.target

end

end Work.Aspherical
