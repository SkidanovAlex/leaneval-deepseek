import Mathlib
import Submission.Work.Final.Framework
import Submission.Work.Final.Basic
import Submission.Work.Final.Mhat
import Submission.Work.Final.Homology
import Submission.Work.Final.Cover
import Submission.Work.Final.MhatCover
import Submission.Work.Final.Main
import Submission.Work.Final.mvRightX_zero_surjective
import Submission.Work.Final.secNonpos_of_chartModels
import Submission.Work.Final.curvLe_of_models
import Submission.Work.Final.CurvField
import Submission.Work.HomologyIso.Algebra
import Submission.Work.HomologyMV.Basic
import Submission.Work.HomologyMV.Model
import Submission.Work.HomologyMV.LinAlg
import Submission.Work.HomologyMV.Data
import Submission.Work.HomologyMV.Concrete
import Submission.Work.HomologyMV.ker_toLin_iso_int_of_normalForm
import Submission.Work.HomologyMV.Interface
import Submission.Work.HomologyMV.kerModel_succ_iso_Sol
import Submission.Work.HomologyMV.wConcrete_surj
import Submission.Work.HomologyMV.wConcrete_ker
import Submission.Work.HomologyMV.Step
import Submission.Work.HomologyMV.Main

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option linter.style.haveILetI false

namespace Work.HomologyIso

open CategoryTheory CategoryTheory.Limits HomologicalComplex

open CategoryTheory CategoryTheory.Limits HomologicalComplex in
/-- **The homology-level Mayer–Vietoris square from a chain-level square.**

Let `U, V ⊆ X` be subsets with chain-level comparison maps `q₁ : C₁ ⟶ C_*(U ∩ V)` and
`q₂ : C₂ ⟶ C_*(U) ⊞ C_*(V)` which are quasi-isomorphisms (`C₁`, `C₂` being the finite complexes
of a `Δ`-complex structure with SDR certificates), and let `φ : C₁ ⟶ C₂` be a chain map whose
square with the Mayer–Vietoris map `mvLeft = (incl_*, incl_*)` commutes up to homotopy.  Then the
identifications of the two slots of the Mayer–Vietoris sequence obtained by composing the
algebraic identifications `eM`, `eN` of `C₁.homology`, `C₂.homology` with the free models with the
quasi-isomorphisms satisfy the square with the *same* matrix `wConcrete k`.

This reduces the bridge input of `Work.HomologyIso.Inputs.hsq` to (i) a chain-level
commuting-up-to-homotopy square (the subdivision/bridge witnesses of the geometry) and (ii) an
algebraic square on the finite complexes (checkable on bases). -/
theorem hsq_of_chainLevel {X : TopCat} (U V : Set X)
    {C₁ C₂ : ChainComplex (ModuleCat ℤ) ℕ}
    (q₁ : C₁ ⟶ Work.HomologyMV.singCx (TopCat.of ↥(U ∩ V))) (hq₁ : QuasiIso q₁)
    (q₂ : C₂ ⟶ (Work.HomologyMV.singCx (TopCat.of U) ⊞ Work.HomologyMV.singCx (TopCat.of V)))
    (hq₂ : QuasiIso q₂) (φ : C₁ ⟶ C₂)
    (hφ : Homotopy (q₁ ≫ Work.Cohomology.mvLeft U V) (φ ≫ q₂))
    (eM : ∀ k : ℕ, Work.HomologyMV.ModelM (k : ℤ) ≅ C₁.homology k)
    (eN : ∀ k : ℕ, Work.HomologyMV.ModelN (k : ℤ) ≅ C₂.homology k)
    (hsq : ∀ k : ℕ, (eM k).hom ≫ homologyMap φ k
      = Work.HomologyMV.wConcrete (k : ℤ) ≫ (eN k).hom)
    (k : ℕ) :
    (eM k ≪≫ asIso (homologyMap q₁ k)).hom ≫ Work.Final.mvF U V k
      = Work.HomologyMV.wConcrete (k : ℤ) ≫ (eN k ≪≫ asIso (homologyMap q₂ k)).hom := by
  haveI : QuasiIso q₁ := hq₁
  haveI : QuasiIso q₂ := hq₂
  -- `Work.Final.mvF U V k` is *definitionally* `homologyMap (Work.Cohomology.mvLeft U V) k`.
  calc (eM k ≪≫ asIso (homologyMap q₁ k)).hom ≫ Work.Final.mvF U V k
      = (eM k).hom ≫ (homologyMap q₁ k ≫ homologyMap (Work.Cohomology.mvLeft U V) k) := by
        simp only [Iso.trans_hom, asIso_hom, Work.Final.mvF, Category.assoc]
    _ = (eM k).hom ≫ homologyMap (q₁ ≫ Work.Cohomology.mvLeft U V) k := by
        rw [HomologicalComplex.homologyMap_comp]
    _ = (eM k).hom ≫ homologyMap (φ ≫ q₂) k := by
        rw [Homotopy.homologyMap_eq hφ k]
    _ = (eM k).hom ≫ (homologyMap φ k ≫ homologyMap q₂ k) := by
        rw [HomologicalComplex.homologyMap_comp]
    _ = ((eM k).hom ≫ homologyMap φ k) ≫ homologyMap q₂ k := by
        rw [Category.assoc]
    _ = (Work.HomologyMV.wConcrete (k : ℤ) ≫ (eN k).hom) ≫ homologyMap q₂ k := by
        rw [hsq k]
    _ = Work.HomologyMV.wConcrete (k : ℤ) ≫ ((eN k).hom ≫ homologyMap q₂ k) := by
        rw [Category.assoc]
    _ = Work.HomologyMV.wConcrete (k : ℤ) ≫ (eN k ≪≫ asIso (homologyMap q₂ k)).hom := by
        simp only [Iso.trans_hom, asIso_hom]

end Work.HomologyIso
