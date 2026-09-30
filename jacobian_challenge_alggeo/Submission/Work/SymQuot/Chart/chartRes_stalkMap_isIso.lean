import Mathlib
import Submission.Work.SymQuot.Chart
import Submission.Work.SymQuot.Chart.chartRes_aux
import Submission.Work.SymQuot.Chart.chartRes_cover

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open CategoryTheory Limits AlgebraicGeometry
open scoped Classical

namespace Work.SymQuot.Chart

variable {G : Type*} [Group G] {X : AlgebraicGeometry.Scheme} (A : Work.SymQuot.GAction G X)

/-- The restriction of sections is insensitive to the proof of the inclusion `V ≤ U`. -/
lemma restrictSections_congr_le {V U : X.Opens} (h h' : V ≤ U) :
    Work.SymQuot.GAction.restrictSections V U h = Work.SymQuot.GAction.restrictSections V U h' := by
  simp only [Work.SymQuot.GAction.restrictSections]

/-- The map on invariants is insensitive to the proof of the inclusion `V ≤ U`. -/
lemma invariantsRes_congr_le {V U : X.Opens} (h h' : V ≤ U) (hU : A.IsInvariantOpen U)
    (hV : A.IsInvariantOpen V) :
    A.invariantsRes V U h hU hV = A.invariantsRes V U h' hU hV := by
  apply RingHom.ext
  intro s
  apply Subtype.ext
  show (Work.SymQuot.GAction.restrictSections V U h) s.1
      = (Work.SymQuot.GAction.restrictSections V U h') s.1
  have h2 : Work.SymQuot.GAction.restrictSections V U h
      = Work.SymQuot.GAction.restrictSections V U h' := by
    simp only [Work.SymQuot.GAction.restrictSections]
  rw [h2]

/-- The restriction map between charts is insensitive to the proof of the inclusion `V ≤ U`. -/
lemma chartRes_congr_le {V U : X.Opens} (h h' : V ≤ U) (hU : A.IsInvariantOpen U)
    (hV : A.IsInvariantOpen V) :
    A.chartRes V U h hU hV = A.chartRes V U h' hU hV := by
  have h1 : A.invariantsRes V U h hU hV = A.invariantsRes V U h' hU hV :=
    invariantsRes_congr_le A h h' hU hV
  show Spec.map (CommRingCat.ofHom (A.invariantsRes V U h hU hV))
      = Spec.map (CommRingCat.ofHom (A.invariantsRes V U h' hU hV))
  rw [h1]

/-- For a `G`-invariant affine open `V` inside a `G`-invariant affine open `U`, the restriction
map of charts `chart V ⟶ chart U` is an isomorphism on stalks: it is an open immersion, since
around every point of `chart V` one can cut out `V` by a basic open of a `G`-fixed section of `U`
and then use the distinguished case of the basic-open restriction. -/
theorem chartRes_stalkMap_isIso {G : Type*} [Group G] [Finite G] {X : AlgebraicGeometry.Scheme}
    (A : Work.SymQuot.GAction G X) {V U : X.Opens} (hVU : V ≤ U)
    (hU : AlgebraicGeometry.IsAffineOpen U) (hV : AlgebraicGeometry.IsAffineOpen V)
    (hUi : A.IsInvariantOpen U) (hVi : A.IsInvariantOpen V)
    (y : (Work.SymQuot.GAction.chart A V hVi : AlgebraicGeometry.Scheme)) :
    CategoryTheory.IsIso ((Work.SymQuot.GAction.chartRes A V U hVU hUi hVi).stalkMap y) := by
  -- a `G`-fixed section `h` of `U` with `X.basicOpen h ≤ V` and a preimage `y'` of `y`
  obtain ⟨h, hh, hle, hy⟩ := chartRes_cover A hVU hU hV hUi hVi y
  obtain ⟨y', hy'⟩ := hy
  have hW : A.IsInvariantOpen (X.basicOpen h) := isInvariantOpen_basicOpen A hUi h hh
  -- both chart restrictions through `X.basicOpen h` are open immersions
  have hα : IsOpenImmersion (A.chartRes (X.basicOpen h) V hle hVi hW) :=
    chartRes_isOpenImmersion_basicOpen_le A hVU hV hVi hUi h hh hle hW
  have hβ : IsOpenImmersion (A.chartRes (X.basicOpen h) U (hle.trans hVU) hUi hW) := by
    have key := chartRes_isOpenImmersion_basicOpen A hU hUi h hh hW
    rw [← chartRes_congr_le A (X.basicOpen_le h) (hle.trans hVU) hUi hW]
    exact key
  -- they compose to the chart restriction of the pair `X.basicOpen h ≤ U`
  have hfac : A.chartRes (X.basicOpen h) V hle hVi hW ≫ A.chartRes V U hVU hUi hVi
      = A.chartRes (X.basicOpen h) U (hle.trans hVU) hUi hW :=
    Work.SymQuot.GAction.chartRes_comp A (X.basicOpen h) V U hle hVU hUi hVi hW
  have hAB : IsOpenImmersion (A.chartRes (X.basicOpen h) V hle hVi hW
      ≫ A.chartRes V U hVU hUi hVi) := by rw [hfac]; exact hβ
  -- cancel the isomorphism on the stalks
  haveI iα : IsIso ((A.chartRes (X.basicOpen h) V hle hVi hW).stalkMap y') :=
    (IsOpenImmersion.iff_isIso_stalkMap.mp hα).2 y'
  rw [← hy']
  haveI : IsIso (Scheme.Hom.stalkMap (A.chartRes V U hVU hUi hVi)
      (A.chartRes (X.basicOpen h) V hle hVi hW y')
      ≫ Scheme.Hom.stalkMap (A.chartRes (X.basicOpen h) V hle hVi hW) y') := by
    rw [← Scheme.Hom.stalkMap_comp]
    exact (IsOpenImmersion.iff_isIso_stalkMap.mp hAB).2 y'
  exact IsIso.of_isIso_comp_right
    (Scheme.Hom.stalkMap (A.chartRes V U hVU hUi hVi)
      ((A.chartRes (X.basicOpen h) V hle hVi hW) y'))
    (Scheme.Hom.stalkMap (A.chartRes (X.basicOpen h) V hle hVi hW) y')

end Work.SymQuot.Chart
