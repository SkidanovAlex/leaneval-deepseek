import Mathlib
import Submission.Work.Normality.All
import Submission.Work.SymQuot.SymGeomInst
import Submission.Work.SymQuot.QuotientMap
import Submission.Work.SymQuot.Sym.isIntegral_sym
import Submission.Work.Domain.Engine.isIntegrallyClosed_section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


universe u

set_option linter.style.haveILetI false

namespace Work.JacClose

open CategoryTheory Limits AlgebraicGeometry

/-- **The local rings of a quotient of a normal scheme by a finite group are integrally
closed.**

Let `D` be the data of a quotient `X/G` of a scheme `X` by a finite group `G` (an action, affine
intersections, and a `G`-invariant affine open cover), and suppose that the ring of sections
`Γ(X, U)` is integrally closed for every nonempty affine open `U` that occurs as a chart.  Then
every local ring of the quotient `X/G` is integrally closed.

Indeed, a point `x` of the quotient is the image of a point `y ∈ X` (`quotientMap_surjective`);
choose a `G`-invariant affine open `U ∋ y` (`QuotientData.covers`) and let `V` be the image of
the chart `Spec Γ(X,U)^G` in the quotient.  Then `V` is an affine open of `X/G` containing `x`
(`Scheme.Hom.opensRange`, `IsAffineOpen.image_of_isOpenImmersion`), and
`Γ(X/G, V) ≅ Γ(Spec Γ(X,U)^G, ⊤) ≅ Γ(X,U)^G` (`Scheme.Hom.appIso`, `Scheme.ΓSpecIso`).  The
invariants of a finite group acting on an integrally closed domain are integrally closed
(`Work.Normality.isIntegrallyClosed_invariants`), so `Γ(X/G, V)` is an integrally closed domain
and `Work.Normality.isIntegrallyClosed_stalk_of_isAffineOpen` finishes. -/
theorem isIntegrallyClosed_stalk_quotient {G : Type u} [Group G] [Fintype G] {X : Scheme.{u}}
    [IsIntegral X] (D : Work.SymQuot.QuotientData G X)
    (h : ∀ (U : X.Opens) (hU : IsAffineOpen U), D.action.IsInvariantOpen U → [Nonempty U] →
      IsIntegrallyClosed (X.presheaf.obj (Opposite.op U)))
    (x : D.Quotient) : IsIntegrallyClosed (D.Quotient.presheaf.stalk x) := by
  -- a point of `X` above `x`
  obtain ⟨y, hy⟩ := D.quotientMap_surjective x
  -- a `G`-invariant affine open containing it
  obtain ⟨U, hUaff, hUinv, hyU⟩ := D.covers y
  let Uc : D.Chart := ⟨U, hUaff, hUinv⟩
  have hyUc : y ∈ (Uc.1 : Set X) := hyU
  -- `x` lies in the chart image `V`
  have hxRange : x ∈ (D.chartι Uc).opensRange := by
    have hpre := Work.SymQuot.QuotientData.quotientMap_preimage_opensRange_chartι D Uc
    have h1 : y ∈ D.quotientMap ⁻¹ᵁ (D.chartι Uc).opensRange := by rw [hpre]; exact hyUc
    rw [Scheme.Hom.mem_preimage, hy] at h1
    exact h1
  have hxV : x ∈ (D.chartι Uc) ''ᵁ (⊤ : (D.chart Uc).Opens) := by
    rw [Scheme.Hom.image_top_eq_opensRange]
    exact hxRange
  have hVaff : IsAffineOpen ((D.chartι Uc) ''ᵁ (⊤ : (D.chart Uc).Opens)) :=
    IsAffineOpen.image_of_isOpenImmersion (U := (⊤ : (D.chart Uc).Opens))
      (isAffineOpen_top _) (D.chartι Uc)
  -- the chart ring `Γ(X,U)^G` is an integrally closed domain
  haveI : Nonempty Uc.1.toScheme := ⟨(⟨y, hyUc⟩ : Uc.1.toScheme)⟩
  letI : MulSemiringAction G Γ(X, Uc.1) := D.action.sectionMulSemiringAction Uc.1 Uc.2.2
  haveI hBdom : IsDomain Γ(X, Uc.1) := inferInstance
  haveI hBic : IsIntegrallyClosed Γ(X, Uc.1) := h Uc.1 Uc.2.1 Uc.2.2
  haveI hRic : IsIntegrallyClosed (D.action.chartRing Uc.1 Uc.2.2 : Type _) :=
    Work.Normality.isIntegrallyClosed_invariants G
  -- the sections of the quotient over `V` are the chart ring
  have e : Γ(D.Quotient, (D.chartι Uc) ''ᵁ (⊤ : (D.chart Uc).Opens)) ≃+*
      (D.action.chartRing Uc.1 Uc.2.2 : Type _) :=
    ((D.chartι Uc).appIso ⊤ ≪≫
      Scheme.ΓSpecIso (D.action.chartRing Uc.1 Uc.2.2)).commRingCatIsoToRingEquiv
  haveI hdom : IsDomain Γ(D.Quotient, (D.chartι Uc) ''ᵁ (⊤ : (D.chart Uc).Opens)) :=
    Function.Injective.isDomain e.toRingHom e.injective
  haveI hic : IsIntegrallyClosed Γ(D.Quotient, (D.chartι Uc) ''ᵁ (⊤ : (D.chart Uc).Opens)) :=
    IsIntegrallyClosed.of_equiv e.symm
  exact Work.Normality.isIntegrallyClosed_stalk_of_isAffineOpen hVaff hic hxV

/-- **The local rings of `Symⁿ C` are integrally closed** (item A4 of the closure design).

`Symⁿ C = Cⁿ/S_n` is the quotient of the smooth integral scheme `Cⁿ` by the finite symmetric
group `S_n` (`Work.SymQuot.symData`), so `Work.JacClose.isIntegrallyClosed_stalk_quotient`
applies: the sections of `Cⁿ` over a nonempty affine open are an integrally closed ring, since
`Cⁿ` is smooth over `K` (`Work.SymQuot.smooth_pi_prod`) and integral (`Work.SymQuot.isIntegral_prod`),
hence has integrally closed local rings (`Work.Normality.hasIntegrallyClosedStalks_of_smooth`),
and `Work.Domain.Engine.isIntegrallyClosed_section` passes from the local rings to the sections
over an affine open. -/
theorem normal_sym {K : Type u} [Field K] (C : Work.CurveBasics.Curve K) (n : ℕ)
    (x : (Work.SymQuot.Sym C n).left) :
    IsIntegrallyClosed ((Work.SymQuot.Sym C n).left.presheaf.stalk x) := by
  haveI : IsIntegral (Work.SymQuot.prod C.toOver n).left := Work.SymQuot.isIntegral_prod C n
  haveI : Smooth (Work.SymQuot.prod C.toOver n).hom := Work.SymQuot.smooth_pi_prod C n
  have hstalks : Work.Normality.HasIntegrallyClosedStalks
      (Work.SymQuot.prod C.toOver n).left :=
    Work.Normality.hasIntegrallyClosedStalks_of_smooth (Work.SymQuot.prod C.toOver n).hom
  have h : ∀ (U : (Work.SymQuot.prod C.toOver n).left.Opens)
      (hU : IsAffineOpen U), (Work.SymQuot.symData C n).action.IsInvariantOpen U →
      [Nonempty U] →
      IsIntegrallyClosed ((Work.SymQuot.prod C.toOver n).left.presheaf.obj (Opposite.op U)) :=
    fun U hU _ _ => Work.Domain.Engine.isIntegrallyClosed_section hstalks hU
  exact isIntegrallyClosed_stalk_quotient (X := (Work.SymQuot.prod C.toOver n).left)
    (G := ULift.{u} (Equiv.Perm (Fin n))) (Work.SymQuot.symData C n) h x

end Work.JacClose
