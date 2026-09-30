import Mathlib
import Submission.Work.Serre.RatMVDefs

/-!
# `dqMap` preserves quasi-isomorphisms

`Work.Serre.dqMap φ : DQ D ⟶ DQ C` is the transpose of the base change to `ℚ` of a morphism of
`ℤ`-chain complexes `φ : C ⟶ D`, where `DQ C = dualComplex ℚ (IntRatCM.obj C)`
(`Submission/Work/Serre/RatMVDefs.lean`).  Here we show that `dqMap` carries quasi-isomorphisms
to quasi-isomorphisms.

The proof has three steps.

* `φ` being a quasi-isomorphism, so is its base change `IntRatCM.map φ`: the functor
  `IntRatF = ModuleCat.extendScalars (ℤ → ℚ)` is flat, hence preserves homology, and
  `HomologicalComplex.quasiIso_map_of_preservesHomology` transports quasi-isomorphisms along
  functors preserving homology.
* For chain complexes of modules over a commutative ring whose terms are projective, the `R`-dual of
  a quasi-isomorphism is again a quasi-isomorphism (`dualComplexMap_quasiIso_of_projective` below,
  a restatement of the `ℤ`-coefficient result `Work.Cohomology.dualComplexMap_quasiIso` valid over
  an arbitrary commutative ring).  The proof dualises the fact that a quasi-isomorphism between
  complexes of projectives is a homotopy equivalence
  (`ChainComplex.quasiIso_iff_of_projective`).
* Every `ℚ`-module is projective (it is a vector space over a field, hence free), so the previous
  step applies to `IntRatCM.obj C` and `IntRatCM.obj D`.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false

open CategoryTheory CategoryTheory.Limits

namespace Work.Serre

noncomputable section

/-- **The `R`-dual of a quasi-isomorphism between degreewise projective chain complexes is a
quasi-isomorphism.**

A quasi-isomorphism between chain complexes concentrated in non-negative degrees whose terms are
projective is a *homotopy equivalence* (`ChainComplex.quasiIso_iff_of_projective`), and the `R`-dual
of a homotopy equivalence is a homotopy equivalence
(`Work.Cohomology.dualHomotopy`, `Work.Cohomology.dualComplexMap_id`), whence a quasi-isomorphism.

This is `Work.Cohomology.dualComplexMap_quasiIso` with the coefficient ring `ℤ` replaced by an
arbitrary commutative ring `R`. -/
theorem dualComplexMap_quasiIso_of_projective {R : Type} [CommRing R]
    {C D : ChainComplex (ModuleCat R) ℕ} (φ : C ⟶ D)
    (hC : ∀ n, CategoryTheory.Projective (C.X n)) (hD : ∀ n, CategoryTheory.Projective (D.X n))
    (h : ∀ n, CategoryTheory.IsIso (HomologicalComplex.homologyMap φ n)) (n : ℕ) :
    CategoryTheory.IsIso
      (HomologicalComplex.homologyMap (Work.Cohomology.dualComplexMap R C D φ) n) := by
  haveI hprojC : ∀ n, CategoryTheory.Projective (C.X n) := hC
  haveI hprojD : ∀ n, CategoryTheory.Projective (D.X n) := hD
  -- `φ` is a quasi-isomorphism
  have hq : QuasiIso φ := by
    rw [quasiIso_iff]
    intro i
    rw [quasiIsoAt_iff_isIso_homologyMap]
    exact h i
  -- hence a homotopy equivalence, because both complexes consist of projectives
  obtain ⟨e, he⟩ := (ChainComplex.quasiIso_iff_of_projective φ).mp hq
  -- the two composites used to dualise the homotopy equivalence
  have hcomp1 : (Work.Cohomology.dualComplexMap R C D φ)
      ≫ (Work.Cohomology.dualComplexMap R D C e.inv)
      = Work.Cohomology.dualComplexMap R D D (e.inv ≫ e.hom) := by
    rw [← he, ← Work.Cohomology.dualComplexMap_comp (R := R) (f := e.inv) (g := e.hom)]
  have hcomp2 : (Work.Cohomology.dualComplexMap R D C e.inv)
      ≫ (Work.Cohomology.dualComplexMap R C D φ)
      = Work.Cohomology.dualComplexMap R C C (e.hom ≫ e.inv) := by
    rw [← he, ← Work.Cohomology.dualComplexMap_comp (R := R) (f := e.hom) (g := e.inv)]
  -- dualising the homotopy equivalence
  let ee : HomotopyEquiv (Work.Cohomology.dualComplex R D) (Work.Cohomology.dualComplex R C) :=
    { hom := Work.Cohomology.dualComplexMap R C D φ
      inv := Work.Cohomology.dualComplexMap R D C e.inv
      homotopyHomInvId := by
        rw [hcomp1]
        simpa [Work.Cohomology.dualComplexMap_id] using
          (Work.Cohomology.dualHomotopy R e.homotopyInvHomId).symm
      homotopyInvHomId := by
        rw [hcomp2]
        simpa [Work.Cohomology.dualComplexMap_id] using
          (Work.Cohomology.dualHomotopy R e.homotopyHomInvId).symm }
  haveI : QuasiIso ee.hom := HomotopyEquiv.quasiIso_hom ee
  exact inferInstanceAs (CategoryTheory.IsIso (HomologicalComplex.homologyMap ee.hom n))

/-- `dqMap` carries quasi-isomorphisms of `ℤ`-chain complexes to quasi-isomorphisms of `ℚ`-cochain
complexes. -/
theorem dq_quasiIso {C D : ChainComplex (ModuleCat Int) Nat} (φ : C ⟶ D) (h : ∀ n : Nat, CategoryTheory.IsIso (HomologicalComplex.homologyMap φ n)) (n : Nat) : CategoryTheory.IsIso (HomologicalComplex.homologyMap (Work.Serre.dqMap φ) n) := by
  -- base change `ℤ → ℚ` preserves quasi-isomorphisms (it is flat, hence preserves homology)
  haveI hfl : PreservesFiniteLimits Work.StemsB.IntRatF :=
    ModuleCat.preservesFiniteLimits_extendScalars_of_flat (by rw [RingHom.Flat]; infer_instance)
  haveI hph : Work.StemsB.IntRatF.PreservesHomology := by infer_instance
  have hq : QuasiIso φ := by
    rw [quasiIso_iff]
    intro i
    rw [quasiIsoAt_iff_isIso_homologyMap]
    exact h i
  have hqQ : QuasiIso (Work.StemsB.IntRatCM.map φ) :=
    HomologicalComplex.quasiIso_map_of_preservesHomology φ Work.StemsB.IntRatF
  have hQ : ∀ n, CategoryTheory.IsIso
      (HomologicalComplex.homologyMap (Work.StemsB.IntRatCM.map φ) n) := by
    intro k
    exact (quasiIsoAt_iff_isIso_homologyMap _ k).mp (hqQ.quasiIsoAt k)
  -- over a field every module is projective, so the dual of the base changed map is a quasi-iso
  exact dualComplexMap_quasiIso_of_projective (R := ℚ)
    (C := Work.StemsB.IntRatCM.obj C) (D := Work.StemsB.IntRatCM.obj D)
    (Work.StemsB.IntRatCM.map φ) (fun k => inferInstance) (fun k => inferInstance) hQ n

end

end Work.Serre
