import Mathlib
import Submission.Work.Charts.Step3Defs
import Submission.Work.Charts.eq_divOf_of_linEquiv_of_landsIn
import Submission.Work.Domain.Resid.residMap_value
import Submission.Work.Domain.Resid.residMap_mem_domain
import Submission.Work.GroupChunk.exists_factor_resPt

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false

open CategoryTheory Limits AlgebraicGeometry
open scoped Classical AlgebraicGeometry MonoidalCategory
open scoped Work.GCBasics

universe u

namespace Work.Charts

noncomputable section

variable {K : Type u} [Field K] {C : Work.CurveBasics.Curve K} [Work.SpecLin.DivBase C]

/-- Base change of divisors commutes with subtraction. -/
private theorem bc_sub {F F' : Type u} [Field F] [Field F'] [Algebra K F] [Algebra K F']
    (e : F →ₐ[K] F') (A B : Work.GCBasics.Dv C F) :
    Work.SpecLin.DivBase.bc e (A - B)
      = Work.SpecLin.DivBase.bc e A - Work.SpecLin.DivBase.bc e B := by
  simp only [sub_eq_add_neg, Work.SpecLin.DivBase.bc_add, Work.SpecLin.DivBase.bc_neg]

/-- `divD` with `b = 𝟙`, unfolded. -/
private theorem divD_id_eq (symGeom : ∀ n, Work.SpecLin.SymGeom C n) (n : ℕ)
    (a : (symGeom (n + n)).S ⟶ (symGeom n).S)
    {F : Type u} [Field F] [Algebra K F] (p : Work.GCBasics.FPt ((symGeom (n + n)).S) F) :
    Work.Domain.Resid.divD symGeom a (𝟙 ((symGeom (n + n)).S)) p
      = (symGeom (n + n)).divOf p - (symGeom n).divOf (p ≫ a) := by
  simp only [Work.Domain.Resid.divD, CategoryTheory.Category.comp_id]

/-- `divD` with `b = 𝟙` is natural under base change of the field. -/
private theorem bc_divD_id (symGeom : ∀ n, Work.SpecLin.SymGeom C n) (n : ℕ)
    (a : (symGeom (n + n)).S ⟶ (symGeom n).S)
    {F F' : Type u} [Field F] [Field F'] [Algebra K F] [Algebra K F']
    (e : F →ₐ[K] F') (q : Work.GCBasics.FPt ((symGeom (n + n)).S) F)
    (p : Work.GCBasics.FPt ((symGeom (n + n)).S) F')
    (h : p = Work.GCBasics.RPt.map e q) :
    Work.SpecLin.DivBase.bc e
        (Work.Domain.Resid.divD symGeom a (𝟙 ((symGeom (n + n)).S)) q)
      = Work.Domain.Resid.divD symGeom a (𝟙 ((symGeom (n + n)).S)) p := by
  have hmap : Work.GCBasics.RPt.map e (q ≫ a) = p ≫ a := by
    rw [h]
    simp only [Work.GCBasics.RPt.map, Category.assoc]
  rw [divD_id_eq symGeom n a q, divD_id_eq symGeom n a p, bc_sub,
    ← Work.SpecLin.SymGeom.divOf_map e q, ← Work.SpecLin.SymGeom.divOf_map e (q ≫ a),
    Work.Domain.Resid.specLinRPtMap_eq, Work.Domain.Resid.specLinRPtMap_eq, hmap, ← h]

theorem landsIn_Wp_of_linEquiv {K : Type u} [Field K] {C : Work.CurveBasics.Curve K}
    [Work.SpecLin.DivBase C] (R : Work.Charts.RochData C)
    (symGeom : ∀ n, Work.SpecLin.SymGeom C n)
    (D : Work.Domain.Resid.ResidData (K := K) symGeom R.g)
    (G : Work.Charts.Step3Geo R symGeom)
    (a : (symGeom (R.g + R.g)).S ⟶ (symGeom R.g).S) {P0Div : Work.GCBasics.Dv C K}
    (ha : ∀ {F : Type u} [Field F] [Algebra K F]
      (p : Work.GCBasics.FPt ((symGeom (R.g + R.g)).S) F),
      (symGeom R.g).divOf (Work.Charts.ptComp p a) =
        (R.g : ℤ) • Work.Charts.pullK C P0Div)
    (d : Work.Charts.BNDataAt R symGeom)
    {F : Type u} [Field F] [Algebra K F] (p : Work.GCBasics.FPt ((symGeom (R.g + R.g)).S) F)
    (y : Work.GCBasics.FPt ((symGeom R.g).S) F) (hy : Work.GCBasics.RPt.LandsIn y d.V)
    (h : Work.GCBasics.LinEquiv C ((symGeom R.g).divOf y)
      ((symGeom (R.g + R.g)).divOf p - (R.g : ℤ) • Work.Charts.pullK C P0Div)) :
    Work.GCBasics.RPt.LandsIn p (Work.Charts.Wp R symGeom D G a d) := by
  haveI hInt : IsIntegral ((symGeom (R.g + R.g)).S).left := G.integral_gg
  haveI hRed : IsReduced ((symGeom (R.g + R.g)).S).left :=
    isReduced_of_isIntegral (X := ((symGeom (R.g + R.g)).S).left)
  haveI hLFT : LocallyOfFiniteType ((symGeom (R.g + R.g)).S).hom :=
    D.locallyOfFiniteType (R.g + R.g)
  haveI hNoeth : IsLocallyNoetherian ((symGeom (R.g + R.g)).S).left :=
    LocallyOfFiniteType.isLocallyNoetherian ((symGeom (R.g + R.g)).S).hom
  haveI hSepHom : IsSeparated ((symGeom R.g).S).hom := G.separated_g
  haveI hSepSch : ((symGeom R.g).S).left.IsSeparated := inferInstance
  let x : ((symGeom (R.g + R.g)).S).left := p.left (IsLocalRing.closedPoint F)
  have hdivD : Work.Domain.Resid.divD symGeom a (𝟙 ((symGeom (R.g + R.g)).S)) p
      = (symGeom (R.g + R.g)).divOf p - (R.g : ℤ) • Work.Charts.pullK C P0Div := by
    rw [divD_id_eq symGeom R.g a p]
    have ha' : (symGeom R.g).divOf (p ≫ a) = (R.g : ℤ) • Work.Charts.pullK C P0Div := ha p
    rw [ha']
  have h1 : Work.GCBasics.ell C
      (Work.Domain.Resid.divD symGeom a (𝟙 ((symGeom (R.g + R.g)).S)) p) = 1 := by
    rw [hdivD, ← Work.GCBasics.ell_eq_of_linEquiv h, d.ell_eq_one_of_landsIn y hy]
  obtain ⟨e, he⟩ := Work.GroupChunk.exists_factor_resPt (K := K) p
  have he' : p = Work.GCBasics.RPt.map e
      (Work.GCBasics.resPt ((symGeom (R.g + R.g)).S) x) := he
  have hbc : Work.SpecLin.DivBase.bc e
      (Work.Domain.Resid.divD symGeom a (𝟙 ((symGeom (R.g + R.g)).S))
        (Work.GCBasics.resPt ((symGeom (R.g + R.g)).S) x))
      = Work.Domain.Resid.divD symGeom a (𝟙 ((symGeom (R.g + R.g)).S)) p :=
    bc_divD_id symGeom R.g a e _ p he'
  have hxe : Work.GCBasics.ell C
      (Work.Domain.Resid.divD symGeom a (𝟙 ((symGeom (R.g + R.g)).S))
        (Work.GCBasics.resPt ((symGeom (R.g + R.g)).S) x)) = 1 := by
    rw [← D.ell_bc e (Work.Domain.Resid.divD symGeom a (𝟙 ((symGeom (R.g + R.g)).S))
        (Work.GCBasics.resPt ((symGeom (R.g + R.g)).S) x)), hbc]
    exact h1
  have hxmem : x ∈ (rho R symGeom D G a).domain :=
    Work.Domain.Resid.residMap_mem_domain (X := (symGeom (R.g + R.g)).S) D G.hstalk a
      (𝟙 ((symGeom (R.g + R.g)).S)) le_rfl x hxe
  have hp : Work.GCBasics.RPt.LandsIn p (rho R symGeom D G a).domain := hxmem
  have hσ : (rho R symGeom D G a).IsOver (Spec (CommRingCat.of K)) :=
    Work.Domain.Resid.ResidData.residMap_isOver (X := (symGeom (R.g + R.g)).S) D a
      (𝟙 ((symGeom (R.g + R.g)).S)) le_rfl
  let v : Work.GCBasics.FPt ((symGeom R.g).S) F :=
    Work.Domain.Resid.valueOf hRed hSepHom (rho R symGeom D G a) hσ p hp
  have hv_rel : Work.Domain.Resid.Rel symGeom a (𝟙 ((symGeom (R.g + R.g)).S)) p v :=
    Work.Domain.Resid.residMap_value (X := (symGeom (R.g + R.g)).S) D G.hstalk hRed hSepHom a
      (𝟙 ((symGeom (R.g + R.g)).S)) le_rfl p hp
  have hv_lin : Work.GCBasics.LinEquiv C ((symGeom R.g).divOf v)
      ((symGeom (R.g + R.g)).divOf p - (R.g : ℤ) • Work.Charts.pullK C P0Div) := by
    have hrel := (Work.Domain.Resid.rel_iff p v).mp hv_rel
    rwa [hdivD] at hrel
  have h_yv : Work.GCBasics.LinEquiv C ((symGeom R.g).divOf y) ((symGeom R.g).divOf v) :=
    h.trans hv_lin.symm
  have hyv : y = v := d.eq_of_landsIn_of_linEquiv y v hy h_yv
  have hv_lands : Work.GCBasics.RPt.LandsIn v d.V := hyv ▸ hy
  obtain ⟨q, hq, -⟩ :=
    Work.GCBasics.RPt.factor_of_closed_landsIn (rho R symGeom D G a).domain p hp
  have hqleft : Over.Hom.left q ≫ ((rho R symGeom D G a).domain).ι = Over.Hom.left p := by
    have h1 := congrArg Over.Hom.left hq
    simpa only [Over.comp_left, Work.GCBasics.Opens.ιOver_left] using h1
  have hcl : Over.Hom.left q (IsLocalRing.closedPoint F) = ⟨x, hxmem⟩ := by
    apply Subtype.ext
    have h2 : ((rho R symGeom D G a).domain).ι
        (Over.Hom.left q (IsLocalRing.closedPoint F)) = x := by
      have h3 := congrArg (fun m : Spec (CommRingCat.of F) ⟶
        ((symGeom (R.g + R.g)).S).left => m (IsLocalRing.closedPoint F)) hqleft
      exact h3
    exact h2
  have hval_hom : Over.Hom.left v (IsLocalRing.closedPoint F)
      = (rho R symGeom D G a).toPartialMap.hom ⟨x, hxmem⟩ := by
    have hvl := Work.Domain.Resid.valueOf_left_eq hRed hSepHom (rho R symGeom D G a) hσ p hp q hq
    rw [hvl]
    change (rho R symGeom D G a).toPartialMap.hom
      (Over.Hom.left q (IsLocalRing.closedPoint F))
      = (rho R symGeom D G a).toPartialMap.hom ⟨x, hxmem⟩
    rw [hcl]
    try rfl
  have hxV : (rho R symGeom D G a).toPartialMap.hom ⟨x, hxmem⟩ ∈ d.V := by
    rw [← hval_hom]
    exact hv_lands
  change p.left (IsLocalRing.closedPoint F) ∈
    ((rho R symGeom D G a).domain.ι ''ᵁ
      ((rho R symGeom D G a).toPartialMap.hom ⁻¹ᵁ d.V) : Set ((symGeom (R.g + R.g)).S).left)
  rw [Scheme.Hom.coe_image, Set.mem_image]
  exact ⟨⟨x, hxmem⟩, hxV, rfl⟩


end

end Work.Charts
