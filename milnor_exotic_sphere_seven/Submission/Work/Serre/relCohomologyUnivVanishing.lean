import Mathlib
import Submission.Work.Cohomology.RelCup
import Submission.Work.Cohomology.relCochain_shortExact

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

open CategoryTheory AlgebraicTopology CategoryTheory.Limits

namespace Work.Serre

noncomputable section

/-! ## The pair `(Y, Y)` with an arbitrary coefficient ring

This is a coefficient-agnostic reproduction of the argument of
`Submission/Work/Cohomology/relCohomology_univ_vanishing.lean` (the case `R = ℤ`).  The relative
cochain complex of the pair `(Y, Y)` is the kernel of the restriction map
`C^*(Y) ⟶ C^*(↥univ) ≅ C^*(Y)`, which is the identity; it is invertible, so its kernel is zero in
every degree, and a complex all of whose terms are zero objects is acyclic. -/

/-- The canonical inclusion `Y ⟶ ↥(Set.univ : Set Y)`. -/
def univInclY (Y : TopCat) : Y ⟶ TopCat.of (Set.univ : Set Y) :=
  TopCat.ofHom ⟨fun y => ⟨y, Set.mem_univ y⟩,
    Continuous.subtype_mk continuous_id (fun y => Set.mem_univ y)⟩

/-- The composite of the inclusion of the full subspace with the projection back is the identity. -/
theorem univInclY_comp_subtype (Y : TopCat) :
    univInclY Y ≫ Work.Cohomology.subtypeIncl Y (Set.univ : Set Y) = 𝟙 Y := by
  apply TopCat.hom_ext
  ext y
  rfl

/-- The restriction along `Y ⟶ ↥univ` is a section of the restriction along `↥univ ⟶ Y`, on
cochains. -/
theorem dualChainMap_univInclY_comp (R : Type) [CommRing R] (Y : TopCat) (n : ℕ)
    (x : (Work.Cohomology.singularCochainComplex R Y).X n) :
    ((Work.Cohomology.dualChainMap R Y (TopCat.of (Set.univ : Set Y)) (univInclY Y)).f n).hom
        (((Work.Cohomology.dualChainMap R (TopCat.of (Set.univ : Set Y)) Y
          (Work.Cohomology.subtypeIncl Y (Set.univ : Set Y))).f n).hom x) = x := by
  have hid := Work.Cohomology.dualChainMap_comp R (univInclY Y)
    (Work.Cohomology.subtypeIncl Y (Set.univ : Set Y))
  rw [univInclY_comp_subtype Y, Work.Cohomology.dualChainMap_id] at hid
  have h2 := congrArg (fun φ => φ.f n) hid
  have h3 := congrArg ModuleCat.Hom.hom h2
  rw [HomologicalComplex.comp_f, ModuleCat.hom_comp] at h3
  have h4 := congrArg (fun (φ : (Work.Cohomology.singularCochainComplex R Y).X n →ₗ[R]
      (Work.Cohomology.singularCochainComplex R Y).X n) => φ x) h3
  simpa using h4.symm

/-- **The relative cochains of the pair `(Y, Y)` are zero**, with coefficients in an arbitrary
commutative ring. -/
theorem relKern_univ_subsingleton (R : Type) [CommRing R] (Y : TopCat) (n : ℕ) :
    Subsingleton ↥(Work.Cohomology.relKern R Y (Set.univ : Set Y) n) := by
  have hzero : ∀ a : Work.Cohomology.relKern R Y (Set.univ : Set Y) n,
      (a : (Work.Cohomology.singularCochainComplex R Y).X n) = 0 := by
    intro a
    have hmem : ((Work.Cohomology.dualChainMap R (TopCat.of (Set.univ : Set Y)) Y
        (Work.Cohomology.subtypeIncl Y (Set.univ : Set Y))).f n).hom a.1 = 0 := a.2
    rw [← dualChainMap_univInclY_comp R Y n a.1, hmem, map_zero]
  exact ⟨fun a b => Subtype.ext (by rw [hzero a, hzero b])⟩

/-- **The relative cohomology of a space modulo itself vanishes**, with coefficients in an
arbitrary commutative ring: `H^n(Y,Y;R) = 0` for every space `Y` and every `n`
(`Work.Cohomology.relCohomology R Y Set.univ n` is `ModuleCat R`, so `Subsingleton` of its carrier).
The integral case `R = ℤ` is `Work.Cohomology.relCohomology_univ_vanishing`
(`Submission/Work/Cohomology/relCohomology_univ_vanishing.lean`); its proof goes through
`relKern_univ_subsingleton` (the relative cochains of `(Y,Y)` are the kernel of the identity of the
cochain complex of `Y`, since the restriction along the identity is surjective/invertible, hence all
their terms are zero objects) followed by `HomologicalComplex.ExactAt.of_isZero` (a complex all of
whose terms are zero objects is acyclic).  The argument is coefficient-agnostic: the only
ℤ-specific inputs in that file are the statements of `dualChainMap_comp`, `dualChainMap_id`,
`relKern` and `relComplex`, all of which are proved for an arbitrary commutative ring `R`.  The task
is to reproduce the argument with `ℤ` replaced by `R`. -/
theorem relCohomologyUnivVanishing (R : Type) [CommRing R] (Y : TopCat) (n : ℕ) :
    Subsingleton (Work.Cohomology.relCohomology R Y Set.univ n) := by
  haveI hX : IsZero ((Work.Cohomology.relComplex R Y (Set.univ : Set Y)).X n) := by
    rw [ModuleCat.isZero_iff_subsingleton]
    exact relKern_univ_subsingleton R Y n
  haveI h : IsZero (HomologicalComplex.homology
      (Work.Cohomology.relComplex R Y (Set.univ : Set Y)) n) :=
    (HomologicalComplex.ExactAt.of_isZero (K := Work.Cohomology.relComplex R Y (Set.univ : Set Y))
      hX).isZero_homology
  exact ModuleCat.isZero_iff_subsingleton.mp h

end

end Work.Serre
