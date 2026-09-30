import Mathlib
import Submission.Work.Serre.DiscPair.discCellStep
import Submission.Work.StemsB.RelCochainDualR
import Submission.Work.StemsB.FieldDualUCT

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The disc-pair cell step in cohomology

`Work.Serre.DiscPair.discCellStep` computes the *homology* of the disc-pair cell step:

  `H_m(cyl q, (cylRetract q)⁻¹Γ ∪ range (cylIncl q)) ≅ ⊕_i H_{m-D}(cylRetract q)⁻¹{c_i}, range (cylIncl q)`.

This file proves the *cohomological* companion `Work.Serre.DiscPair.discCellStepCoh`, in which the
direct sum is replaced by its dual, the product over `i`:

  `H^m(cyl q, (cylRetract q)⁻¹Γ ∪ range (cylIncl q))
      ≅ ∏_i H^{m-D}(cylRetract q)⁻¹{c_i}, range (cylIncl q)`.

The two ingredients are standard and already in the workspace:

* `Work.StemsB.relCochainDualR` — relative cochains are the duals of relative chains,
  `C^*(X,A;R) ≅ Hom_R(C_*(X,A;R),R)`, for an arbitrary coefficient ring `R`;
* `Work.StemsB.fieldDualUCT` — the universal coefficient theorem over a field,
  `H^n(Hom_F(C,F)) ≅ Hom_F(H_n(C),F)`.

Combining them gives, for any pair `(X,A)` and any `n`, the bridge
`Work.Serre.DiscPair.relativeCohomologyDualRelH`:

  `H^n(X,A;ℚ) ≅ Hom_ℚ(H_n(X,A;ℚ), ℚ)`.

The rest is linear algebra: `Hom` of a direct sum is the product of the `Hom`s
(`Work.Serre.DiscPair.dsDualEquiv`), and the `ℚ`-dual of each summand is identified with the
corresponding relative cohomology group, again by the universal coefficient theorem.
-/

namespace Work.Serre.DiscPair

open CategoryTheory CategoryTheory.Limits

noncomputable section

/-- **Universal coefficients over `ℚ` for a relative pair**: relative cohomology is the `ℚ`-dual of
relative homology.  This is the composite of `Work.StemsB.relCochainDualR` (relative cochains are
the duals of relative chains) with `Work.StemsB.fieldDualUCT` (over a field, the cohomology of the
dual complex is the dual of the homology). -/
theorem relativeCohomologyDualRelH (X : TopCat) (A : Set X) (n : ℕ) :
    Nonempty ((Work.Cohomology.relComplex ℚ X A).homology n ≅
      ModuleCat.of ℚ (Module.Dual ℚ ↥((Work.StemsB.relChainsR ℚ X A).homology n))) := by
  obtain ⟨e⟩ := Work.StemsB.relCochainDualR ℚ X A
  obtain ⟨g⟩ := Work.StemsB.fieldDualUCT ℚ (Work.StemsB.relChainsR ℚ X A) n
  exact ⟨(HomologicalComplex.homologyFunctor (ModuleCat ℚ) (ComplexShape.up ℕ) n).mapIso e ≪≫ g⟩

/-- **The dual of a direct sum is the product of the duals**: for a family of `ℚ`-modules `V i`,

  `Hom_ℚ(⨁_i V i, ℚ) ≅ ∏_i Hom_ℚ(V i, ℚ)`.

This is the universal property of the direct sum (a linear map out of `⨁_i V i` is exactly a
family of linear maps out of the summands). -/
def dsDualEquiv {ι : Type} [DecidableEq ι] (V : ι → Type)
    [∀ i, AddCommGroup (V i)] [∀ i, Module ℚ (V i)] :
    ((DirectSum ι V) →ₗ[ℚ] ℚ) ≃ₗ[ℚ] (∀ i, V i →ₗ[ℚ] ℚ) where
  toFun f := fun i => f.comp (DirectSum.lof ℚ ι V i)
  invFun g := DirectSum.toModule ℚ ι ℚ g
  left_inv f := by
    apply LinearMap.ext
    intro x
    exact (DirectSum.toModule.unique (R := ℚ) f x).symm
  right_inv g := by
    funext i
    apply LinearMap.ext
    intro x
    exact DirectSum.toModule_lof ℚ i x
  map_add' f g := by
    funext i
    apply LinearMap.ext
    intro x
    rfl
  map_smul' a f := by
    funext i
    apply LinearMap.ext
    intro x
    rfl

end

theorem discCellStepCoh (D : ℕ) (hD : 2 ≤ D) (Γ : Type) [TopologicalSpace Γ] (ι : Type)
    (f : ι → C(Work.RatHurewicz.cellSphere (D-2), Γ)) {X : Type} [TopologicalSpace X]
    (q : C(X, Work.RatHurewicz.attachCells (D-2) Γ ι f)) (hq : Work.StemsB.IsSerreFibration q)
    (hne : ∀ i : ι, Nonempty (Work.StemsB.fibre q (Work.Serre.csrCentre (D - 2) Γ ι f i)))
    (m : ℕ) (hmD : D ≤ m) :
    Nonempty (Work.Thom.RelCoh ℚ m (Work.Serre.cyl q)
        ((Work.Serre.cylRetract q) ⁻¹' Set.range (Work.RatHurewicz.attachIncl (D-2) Γ ι f) ∪
          Set.range (Work.Serre.cylIncl q)) ≅
      ModuleCat.of ℚ (∀ i : ι, ↥(Work.Thom.RelCoh ℚ (m - D)
        ↥((Work.Serre.cylRetract q) ⁻¹' {Work.Serre.csrCentre (D - 2) Γ ι f i})
        {x | (x : Work.Serre.cyl q) ∈ Set.range (Work.Serre.cylIncl q)}))) := by
  classical
  -- the cell step in homology
  obtain ⟨eH⟩ := Work.Serre.DiscPair.discCellStep D hD Γ ι f q hq hne m hmD
  -- relative cohomology of the disc pair is the dual of its relative homology
  obtain ⟨el⟩ : Nonempty (Work.Thom.RelCoh ℚ m (Work.Serre.cyl q)
        ((Work.Serre.cylRetract q) ⁻¹' Set.range (Work.RatHurewicz.attachIncl (D-2) Γ ι f) ∪
          Set.range (Work.Serre.cylIncl q)) ≅
      ModuleCat.of ℚ (Module.Dual ℚ ↥((Work.StemsB.relChainsR ℚ (TopCat.of (Work.Serre.cyl q))
        ((Work.Serre.cylRetract q) ⁻¹' Set.range (Work.RatHurewicz.attachIncl (D-2) Γ ι f) ∪
          Set.range (Work.Serre.cylIncl q))).homology m))) :=
    Work.Serre.DiscPair.relativeCohomologyDualRelH (TopCat.of (Work.Serre.cyl q))
      ((Work.Serre.cylRetract q) ⁻¹' Set.range (Work.RatHurewicz.attachIncl (D-2) Γ ι f) ∪
        Set.range (Work.Serre.cylIncl q)) m
  -- and the cohomology of each cell pair is the dual of the corresponding homology
  have euc : ∀ i : ι, Nonempty (Work.Thom.RelCoh ℚ (m - D)
        ↥((Work.Serre.cylRetract q) ⁻¹' {Work.Serre.csrCentre (D - 2) Γ ι f i})
        {x | (x : Work.Serre.cyl q) ∈ Set.range (Work.Serre.cylIncl q)} ≅
      ModuleCat.of ℚ (Module.Dual ℚ ↥((Work.StemsB.relChainsR ℚ
        (TopCat.of ↥((Work.Serre.cylRetract q) ⁻¹' {Work.Serre.csrCentre (D-2) Γ ι f i}))
        {x | (x : Work.Serre.cyl q) ∈ Set.range (Work.Serre.cylIncl q)}).homology (m - D)))) :=
    fun i => Work.Serre.DiscPair.relativeCohomologyDualRelH
      (TopCat.of ↥((Work.Serre.cylRetract q) ⁻¹' {Work.Serre.csrCentre (D - 2) Γ ι f i}))
      {x | (x : Work.Serre.cyl q) ∈ Set.range (Work.Serre.cylIncl q)} (m - D)
  -- assemble: dualise the homology cell step, then exchange `Hom(⨁,ℚ)` with `∏ Hom`
  refine ⟨el ≪≫ (LinearEquiv.toModuleIso
    ((LinearEquiv.dualMap (CategoryTheory.Iso.toLinearEquiv eH)).symm.trans
      ((Work.Serre.DiscPair.dsDualEquiv (fun i => ↥((Work.StemsB.relChainsR ℚ
          (TopCat.of ↥((Work.Serre.cylRetract q) ⁻¹' {Work.Serre.csrCentre (D-2) Γ ι f i}))
          {x | (x : Work.Serre.cyl q) ∈ Set.range (Work.Serre.cylIncl q)}).homology (m - D)))).trans
        (LinearEquiv.piCongrRight (fun i => (euc i).some.toLinearEquiv.symm)))))⟩

end Work.Serre.DiscPair
