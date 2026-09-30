import Mathlib
import Submission.Work.SymQuot.Sym
import Submission.Work.SymQuot.SymGeomInst
import Submission.Work.SymQuot.CurveInstance
import Submission.Work.SymQuot.Quotient
import Submission.Work.SymQuot.QuotientData
import Submission.Work.SymQuot.DivBaseInst
import Submission.Work.SymQuot.Chart.chartRes_isOpen_range
import Submission.Work.SymQuot.Sym.isIntegral_sym
import Submission.Work.SymQuot.Invariants.surjective_specMap_fixedPoints
import Submission.Work.Normality.Sym
import Submission.Work.Normality.Scheme
import Submission.Work.CurveFacts.smooth_sections

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


namespace Work.CurveFacts

universe u

open CategoryTheory Limits AlgebraicGeometry
open scoped Classical AlgebraicGeometry

set_option linter.style.haveILetI false

/-- **The ring of sections of the image of a chart.**

The `Γ`-chart `D.chartι U : Spec Γ(X,U)^Γ ⟶ D.Quotient` of an invariant affine open `U` of a
scheme `X` with an action of a finite group `Γ` is an open immersion.  Its image `V_U` therefore
has ring of sections the chart ring `D.action.chartRing U.1 U.2.2 = Γ(X, U.1)^Γ`:

* `Scheme.Opens.topIso` identifies `Γ(V_U.toScheme, ⊤)` with `Γ(D.Quotient, V_U)`;
* `Scheme.Hom.isoOpensRange` identifies `D.chart U` with `V_U.toScheme`, so applying the global
  sections functor `Scheme.Γ` gives `Γ(V_U.toScheme, ⊤) ≅ Γ(D.chart U, ⊤)`;
* `D.chart U` is `Spec (D.action.chartRing U.1 U.2.2)` by definition, so `Scheme.ΓSpecIso`
  identifies `Γ(D.chart U, ⊤)` with the chart ring. -/
noncomputable def sections_opensRange_chart {Γ : Type u} [Group Γ] [Fintype Γ] {X : Scheme.{u}}
    (D : Work.SymQuot.QuotientData Γ X) (U : D.Chart) :
    Γ(D.Quotient, (D.chartι U).opensRange) ≃+* ↥(D.action.chartRing U.1 U.2.2) :=
  ((Scheme.Opens.topIso (D.chartι U).opensRange).symm ≪≫
    Scheme.Γ.mapIso (D.chartι U).isoOpensRange.op ≪≫
    Scheme.ΓSpecIso (D.action.chartRing U.1 U.2.2)).commRingCatIsoToRingEquiv

/-- A chart whose spectrum is nonempty comes from a nonempty invariant affine open: the chart map
`U ⟶ Spec Γ(X,U)^Γ` is surjective. -/
private theorem nonempty_of_nonempty_chart {Γ : Type u} [Group Γ] [Fintype Γ] {X : Scheme.{u}}
    (D : Work.SymQuot.QuotientData Γ X) (U : D.Chart) (h : Nonempty (D.chart U)) :
    Nonempty U.1 := by
  obtain ⟨y⟩ := h
  obtain ⟨z, -⟩ := Work.SymQuot.Chart.chartMap_surjective_of_affine D.action U.2.1 U.2.2 y
  exact ⟨z.1, z.2⟩

/-- **Item A4, chart level.**  The chart ring `Γ(Cⁿ, U)^{S_n}` of an invariant affine open `U` of
the `n`-th power of a curve `C` over a field `K` is integrally closed.

Indeed `Γ(Cⁿ, U)` is a domain — it is the ring of sections of the nonempty open subscheme `U` of
the integral scheme `Cⁿ` (`Work.SymQuot.isIntegral_prod`) — and it is a smooth `K`-algebra, because
`Cⁿ ⟶ Spec K` is smooth (`Work.SymQuot.smooth_pi_prod`) and `U ⊆ Cⁿ` is affine, so that
`Work.CurveFacts.smooth_sections` applies.  Hence
`Work.Normality.isIntegrallyClosed_invariants_of_smooth` gives that the fixed points of the finite
group `S_n` acting on it are integrally closed. -/
private theorem chartRing_isIntegrallyClosed_aux {K : Type u} [Field K]
    (C : Work.CurveBasics.Curve K) (n : ℕ) (U : (Work.SymQuot.symData C n).Chart)
    (h : Nonempty U.1) :
    IsIntegrallyClosed ↥((Work.SymQuot.symData C n).action.chartRing U.1 U.2.2) := by
  haveI : Nonempty U.1 := h
  haveI : IsIntegral (Work.SymQuot.prod C.toOver n).left := Work.SymQuot.isIntegral_prod C n
  haveI : IsDomain Γ((Work.SymQuot.prod C.toOver n).left, U.1) := inferInstance
  haveI : Smooth (Work.SymQuot.prod C.toOver n).hom := Work.SymQuot.smooth_pi_prod C n
  let φ : K →+* Γ((Work.SymQuot.prod C.toOver n).left, U.1) :=
    (((Work.SymQuot.prod C.toOver n).hom).appLE ⊤ U.1 le_top).hom.comp
      (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom
  letI : Algebra K Γ((Work.SymQuot.prod C.toOver n).left, U.1) := φ.toAlgebra
  haveI : Algebra.Smooth K Γ((Work.SymQuot.prod C.toOver n).left, U.1) :=
    (smooth_sections (Work.SymQuot.prod C.toOver n).hom U.2.1).toAlgebra
  letI : MulSemiringAction (ULift.{u} (Equiv.Perm (Fin n)))
      Γ((Work.SymQuot.prod C.toOver n).left, U.1) :=
    (Work.SymQuot.symData C n).action.sectionMulSemiringAction U.1 U.2.2
  exact Work.Normality.isIntegrallyClosed_invariants_of_smooth (K := K)
    (B := Γ((Work.SymQuot.prod C.toOver n).left, U.1)) (G := ULift.{u} (Equiv.Perm (Fin n)))

/-- **Item A4, quotient level.**  Every local ring of the quotient `Cⁿ/S_n = Symⁿ C` is integrally
closed.

Given `x : D.Quotient`, choose a chart `U` and a point `y : D.chart U` mapping to `x`
(`QuotientData.chartι_jointly_surjective`).  Its image `V := (D.chartι U).opensRange` is an affine
open containing `x`, with

`Γ(D.Quotient, V) ≃+* (Γ(Cⁿ, U.1))^{S_n}`

(`sections_opensRange_chart`), so `Γ(D.Quotient, V)` is integrally closed by the chart-level
statement `chartRing_isIntegrallyClosed_aux` and a domain because `D.Quotient` is integral
(`Work.SymQuot.isIntegral_quotient`) and `V ≠ ∅`.
`Work.Normality.isIntegrallyClosed_stalk_of_isAffineOpen` then gives the stalk at `x`. -/
private theorem isIntegrallyClosed_stalk_quotient {K : Type u} [Field K]
    (C : Work.CurveBasics.Curve K) (n : ℕ)
    (x : (Work.SymQuot.symData C n).Quotient) :
    IsIntegrallyClosed ((Work.SymQuot.symData C n).Quotient.presheaf.stalk x) := by
  classical
  obtain ⟨U, y, hy⟩ :=
    Work.SymQuot.QuotientData.chartι_jointly_surjective (Work.SymQuot.symData C n) x
  haveI : IsIntegral (Work.SymQuot.prod C.toOver n).left := Work.SymQuot.isIntegral_prod C n
  haveI : IsIntegral (Work.SymQuot.symData C n).Quotient :=
    Work.SymQuot.isIntegral_quotient (Work.SymQuot.symData C n)
  have hVaff : IsAffineOpen ((Work.SymQuot.symData C n).chartι U).opensRange :=
    isAffineOpen_opensRange _
  have hxV : x ∈ ((Work.SymQuot.symData C n).chartι U).opensRange := by
    rw [Scheme.Hom.mem_opensRange]
    exact ⟨y, hy⟩
  haveI : Nonempty ((Work.SymQuot.symData C n).chartι U).opensRange := ⟨⟨x, hxV⟩⟩
  haveI hchart : IsIntegrallyClosed
      ↥((Work.SymQuot.symData C n).action.chartRing U.1 U.2.2) :=
    chartRing_isIntegrallyClosed_aux C n U (nonempty_of_nonempty_chart (Work.SymQuot.symData C n) U ⟨y⟩)
  haveI hchartV : IsIntegrallyClosed
      Γ((Work.SymQuot.symData C n).Quotient,
        ((Work.SymQuot.symData C n).chartι U).opensRange) :=
    IsIntegrallyClosed.of_equiv
      (sections_opensRange_chart (Work.SymQuot.symData C n) U).symm
  haveI : IsDomain Γ((Work.SymQuot.symData C n).Quotient,
      ((Work.SymQuot.symData C n).chartι U).opensRange) := inferInstance
  exact Work.Normality.isIntegrallyClosed_stalk_of_isAffineOpen hVaff hchartV hxV

/-- **Item A4 of the closure design: the local rings of `Symⁿ C` are integrally closed.**
This is the normality input `hstalk` (item O8) required by the chart construction over `k`.

Route.  `Work.SymQuot.Sym C n = (Work.SymQuot.symData C n).Quotient` is the locally directed
colimit of the chart diagram `U ↦ Spec Γ(Cⁿ, U)^{S_n}` over the invariant affine opens
`U ⊆ Cⁿ` (`Submission/Work/SymQuot/Quotient.lean`, `QuotientData.Chart`), and each chart map
`D.chartι U : D.chart U ⟶ D.Quotient` is an open immersion with affine source
(`QuotientData.chart`, `QuotientData.chartι`).  Its range `V_U` is therefore an affine open of
`Sym C n` with `Γ(Sym C n, V_U) ≅ Γ(Cⁿ, U)^{S_n}` (Mathlib's
`IsAffineOpen.image_of_isOpenImmersion` and `Scheme.Hom.isoImage`), and the `V_U` cover `Sym C n`
(`QuotientData.chartι_jointly_surjective`).  Each `B := Γ(Cⁿ, U)` is a smooth `K`-algebra and a
domain (it is the ring of sections of a nonempty affine open of the smooth integral scheme `Cⁿ`;
smoothness from `HasRingHomProperty.appLE`/`RingHom.smooth_algebraMap`, integrality from
`IsIntegral.isOpenImmersion`-style instances), so `B^{S_n}` is integrally closed by
`Work.Normality.isIntegrallyClosed_invariants_of_smooth`.  Conclude with
`Work.Normality.hasIntegrallyClosedStalks_of_invariants_charts` (or directly with
`Work.Normality.HasIntegrallyClosedStalks.of_isAffineOpen_cover`), which gives
`HasIntegrallyClosedStalks (Sym C n).left`, i.e. the stated pointwise form. -/
theorem isIntegrallyClosed_stalk_sym {K : Type u} [Field K] (C : Work.CurveBasics.Curve K) (n : ℕ)
    (x : (Work.SymQuot.Sym C n).left) :
    IsIntegrallyClosed ((Work.SymQuot.Sym C n).left.presheaf.stalk x) :=
  isIntegrallyClosed_stalk_quotient C n x

end Work.CurveFacts
