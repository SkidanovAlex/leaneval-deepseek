import Mathlib
import Submission.Work.ThomBordism.valuePmOneV2Defs
import Submission.Work.Tubular.PuncturedDiscPair.puncturedNormalPair_vanishing
import Submission.Work.ThomBordism.tubeRelChains_iso_puncturedNormalPair
import Submission.Work.ThomBordism.relCohomology_zeroSection_punct
import Submission.Work.Tubular.relHomologyIntOfCohCopy
import Submission.Work.ThomBordism.punctRelHomologyFinite

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option linter.style.haveILetI false

namespace Work.ThomBordism

open CategoryTheory

/-!
# The `(7+k)`-th relative homology of the punctured tube pair is free

The target is `Module.Free ℤ H_{7+k}(C.U ∖ {pt}, tubeInvPunct)`.  The proof has four parts.

* The sibling `Work.ThomBordism.tubeRelChains_iso_puncturedNormalPair` identifies the relative
  homology of the punctured tube pair with that of the *punctured normal pair*
  `(ν ∖ {0_x}, ν ∖ 0)` — the normal total space with the zero-section point `0_x` removed, relative
  to the complement of the zero section — in every degree.  So it suffices to treat the punctured
  normal pair.
* The relative *cohomology* of the punctured normal pair vanishes in the ambient degree `8 + k`
  (`Work.ThomBordism.relCohomology_zeroSection_punct`), so by the integral universal coefficient
  criterion (`Work.Tubular.isTorsionFree_homology`) its `(7+k)`-th relative *homology* is
  torsion-free.
* The relative homology of the punctured normal pair is finitely generated in every degree
  (`Work.ThomBordism.punctRelHomologyFinite`), and a finitely generated torsion-free `ℤ`-module is
  free.
* Freeness is transported back along the isomorphism of the first step.
-/

/-- **The relative cohomology of the punctured normal pair vanishes in degree `8+k`**, in the
`IsZero` form required by the universal coefficient torsion-freeness criterion. -/
theorem punctRel_cohomology_vanishing {V : Work.ThomBordism.Man8} [ConnectedSpace V.pt] {k : ℕ}
    (hk : 1 ≤ k) (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) (x : V.pt) :
    CategoryTheory.Limits.IsZero
      ((Work.Cohomology.relComplex ℤ (TopCat.of (Work.Tubular.PuncturedDiscPair.Punct E x))
        (Work.Tubular.PuncturedDiscPair.PunctRel E x)).homology (8 + k)) := by
  haveI : Subsingleton
      ((Work.Cohomology.relComplex ℤ (TopCat.of (Work.Tubular.PuncturedDiscPair.Punct E x))
        (Work.Tubular.PuncturedDiscPair.PunctRel E x)).homology (8 + k)) :=
    Work.ThomBordism.relCohomology_zeroSection_punct (V := V) (k := k) hk E x
  exact ModuleCat.isZero_of_subsingleton _

/-- **The `(7+k)`-th relative homology of the punctured normal pair is torsion-free.**

The integral universal coefficient criterion `Work.Tubular.isTorsionFree_homology` states that the
`n`-th relative homology of a pair is torsion-free as soon as its `(n+1)`-st *cohomology* vanishes;
here `n = 7 + k` and the vanishing is `punctRel_cohomology_vanishing`. -/
theorem punctRelHomologyTorsionFree {V : Work.ThomBordism.Man8} [ConnectedSpace V.pt] {k : ℕ}
    (hk : 1 ≤ k) (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) (x : V.pt) :
    Module.IsTorsionFree ℤ
      ↥((Work.Cohomology.relChains (TopCat.of (Work.Tubular.PuncturedDiscPair.Punct E x))
        (Work.Tubular.PuncturedDiscPair.PunctRel E x)).homology (7 + k)) :=
  Work.Tubular.isTorsionFree_homology
    (X := TopCat.of (Work.Tubular.PuncturedDiscPair.Punct E x))
    (A := Work.Tubular.PuncturedDiscPair.PunctRel E x) (n := 7 + k)
    (CategoryTheory.Limits.IsZero.of_iso (punctRel_cohomology_vanishing (V := V) (k := k) hk E x)
      (eqToIso (congrArg
        (fun m : ℕ => (Work.Cohomology.relComplex ℤ
          (TopCat.of (Work.Tubular.PuncturedDiscPair.Punct E x))
          (Work.Tubular.PuncturedDiscPair.PunctRel E x)).homology m)
        (by omega : 7 + k + 1 = 8 + k))))

/-- **The relative homology of the punctured normal pair is free in degree `7+k`**: it is finitely
generated (`punctRelHomologyFinite`) and torsion-free (`punctRelHomologyTorsionFree`). -/
theorem punctRelHomologyFree {V : Work.ThomBordism.Man8} [ConnectedSpace V.pt] {k : ℕ}
    (hk : 1 ≤ k) (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) (x : V.pt) :
    Module.Free ℤ
      ↥((Work.Cohomology.relChains (TopCat.of (Work.Tubular.PuncturedDiscPair.Punct E x))
        (Work.Tubular.PuncturedDiscPair.PunctRel E x)).homology (7 + k)) := by
  haveI hfin : Module.Finite ℤ
      ↥((Work.Cohomology.relChains (TopCat.of (Work.Tubular.PuncturedDiscPair.Punct E x))
        (Work.Tubular.PuncturedDiscPair.PunctRel E x)).homology (7 + k)) :=
    Work.ThomBordism.punctRelHomologyFinite (V := V) (k := k) hk E x (7 + k)
  haveI htors : Module.IsTorsionFree ℤ
      ↥((Work.Cohomology.relChains (TopCat.of (Work.Tubular.PuncturedDiscPair.Punct E x))
        (Work.Tubular.PuncturedDiscPair.PunctRel E x)).homology (7 + k)) :=
    punctRelHomologyTorsionFree (V := V) (k := k) hk E x
  exact Module.free_of_finite_type_torsion_free'

theorem tubeRelChains_tubePtSet_free_seven_plus_k {V : Work.ThomBordism.Man8}
    [ConnectedSpace V.pt] {k : ℕ} (hk : 1 ≤ k)
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) {ε : ℝ}
    (C : Work.Tubular.TubeChart E ε) (x : V.pt) :
    Module.Free ℤ ↥((Work.Cohomology.relChains (TopCat.of ↥(Work.ThomBordism.tubePtSet E C x))
      {a : ↥(Work.ThomBordism.tubePtSet E C x) |
        (a : ↥C.U) ∈ Work.ThomBordism.tubeInvPunct E C}).homology (7 + k)) := by
  obtain ⟨e⟩ := Work.ThomBordism.tubeRelChains_iso_puncturedNormalPair (V := V) (k := k) hk E C x
    (7 + k)
  exact Module.Free.of_equiv' (punctRelHomologyFree (V := V) (k := k) hk E x) e.toLinearEquiv.symm

end Work.ThomBordism
