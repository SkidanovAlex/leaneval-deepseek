import Mathlib
import Submission.Work.SymQuot.Chart.exists_basicOpen_invariant_sub
import Submission.Work.SymQuot.Chart.chartRes_aux

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


namespace Work.SymQuot.Chart

universe u

/-- **A piece of an invariant affine chart inside the preimage of an affine open.**

Let `Γ` be a finite group acting on a scheme `X` through `A : GAction Γ X`, let `U ⊆ X` be a
`Γ`-invariant affine open and `f : X ⟶ Z` a `Γ`-invariant morphism.  Then every point `y` of `U`
admits a basic open `X.basicOpen s` of a `Γ`-invariant section `s ∈ Γ(X,U)^Γ` which contains `y`
and is contained in `U ⊓ f ⁻¹ᵁ V` for some affine open `V ⊆ Z`.

In other words, the invariant affine chart `U` can be cut down, around any of its points, to an
invariant affine basic open lying over an affine open of `Z`. -/
theorem exists_piece_index {Γ : Type u} [Group Γ] [Fintype Γ]
    {X : AlgebraicGeometry.Scheme.{u}} (A : Work.SymQuot.GAction Γ X)
    {U : X.Opens} (hUa : AlgebraicGeometry.IsAffineOpen U) (hUi : A.IsInvariantOpen U)
    {Z : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Z) (hf : A.IsInvariantMorphism f)
    (y : U.toScheme) :
    ∃ (V : Z.Opens) (hVa : AlgebraicGeometry.IsAffineOpen V)
      (s : ↥(A.invariants U hUi)),
      X.basicOpen (s : X.presheaf.obj (Opposite.op U)) ≤
          U ⊓ (TopologicalSpace.Opens.map f.base).obj V ∧
        U.ι y ∈ X.basicOpen (s : X.presheaf.obj (Opposite.op U)) := by
  classical
  -- An affine open neighbourhood `V` of the image of `y` under `f`.
  obtain ⟨V, hVa, hfV, -⟩ :=
    AlgebraicGeometry.exists_isAffineOpen_mem_and_subset (X := Z) (x := f (U.ι y))
      (U := ⊤) (by simp)
  -- Its preimage is `Γ`-invariant because `f` is.
  have hInv : A.IsInvariantOpen ((TopologicalSpace.Opens.map f.base).obj V) := by
    intro g
    rw [← AlgebraicGeometry.Scheme.Hom.comp_preimage (A.hom g) f V, hf g]
  have hyU : U.ι y ∈ U := y.2
  -- Cut `U` down to an invariant basic open around `y` inside `U ⊓ f ⁻¹ᵁ V`.
  obtain ⟨s, hs, hsub⟩ :=
    exists_basicOpen_invariant_sub A hUa hUi (hUi.inf hInv) inf_le_left
      (show U.ι y ∈ U ⊓ (TopologicalSpace.Opens.map f.base).obj V from ⟨hyU, hfV⟩)
  exact ⟨V, hVa, s, hsub, hs⟩

end Work.SymQuot.Chart
