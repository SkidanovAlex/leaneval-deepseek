import Mathlib
import Submission.Work.SpecLin.Core.ordChart
import Submission.Work.SpecLin.Core.sectionPrime_sup_fibrePrime_eq_ker
import Submission.Work.SpecLin.Core.primeIdealOf_fromSpec_eq_comap
import Submission.Work.SpecLin.Core.linEquiv_of_sections
import Submission.Work.CurveBasics.All
import Submission.Work.SpecLin.Alt.chartDictionary

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.



universe u

open CategoryTheory Limits AlgebraicGeometry
open scoped Classical

namespace Work.SpecLin.Core

/-- **(D2-geom)** A chart section vanishes at the special-fibre point of a section exactly when
its value (the residue of `rgMap`) vanishes. -/
theorem mem_primeIdealOf_closedPt_iff {K : Type u} [Field K] {C : Work.CurveBasics.Curve K}
    {R : Type u} [CommRing R] [IsDomain R] [ValuationRing R] [Algebra K R]
    (W : C.left.Opens) (hW : AlgebraicGeometry.IsAffineOpen W)
    (s : Work.SpecLin.CurvePt C R)
    (hs : Set.range (s.left.base) ⊆ (W : Set C.left))
    (hle : C.bcOpens (IsLocalRing.ResidueField R) W ≤
      (TopologicalSpace.Opens.map
        (C.baseChangeFst (IsLocalRing.ResidueField R)).base).obj W)
    (a : C.left.presheaf.obj (Opposite.op W))
    (x : (C.baseChange (IsLocalRing.ResidueField R)).left)
    (hx : x ∈ C.bcOpens (IsLocalRing.ResidueField R) W)
    (hx' : x = Work.SpecLin.ptToPoint (Work.SpecLin.RPt.map
      (IsScalarTower.toAlgHom K R (IsLocalRing.ResidueField R)) s)) :
    (C.baseChangeFst (IsLocalRing.ResidueField R)).appLE W
        (C.bcOpens (IsLocalRing.ResidueField R) W) hle a
      ∈ ((Work.CurveBasics.BaseChange.isAffineOpen_bcOpens
          (IsLocalRing.ResidueField R) W hW).primeIdealOf ⟨x, hx⟩).asIdeal
    ↔ (Work.SpecLin.Core.rgMap R W hW s hs) a ∈ IsLocalRing.maximalIdeal R := by
  -- (1) The section `s`, read in the chart `Spec Γ(C,W)`, is the composite of `Spec.map` of the
  -- residue map `R → κ` with `Spec.map` of `rgMapHom`; its special-fibre point is therefore the
  -- point of `C` obtained from `Spec.map (residue ∘ rgMapHom)` evaluated at the closed point of
  -- `Spec κ`.
  have hmap :
      Over.Hom.left (Work.SpecLin.RPt.map
          (IsScalarTower.toAlgHom K R (IsLocalRing.ResidueField R)) s)
      = Spec.map (CommRingCat.ofHom
            (IsScalarTower.toAlgHom K R (IsLocalRing.ResidueField R)).toRingHom)
        ≫ Spec.map (CommRingCat.ofHom (Work.SpecLin.Core.rgMapHom R W hW s hs)) ≫ hW.fromSpec := by
    rw [show Work.SpecLin.RPt.map
          (IsScalarTower.toAlgHom K R (IsLocalRing.ResidueField R)) s
        = Work.SpecLin.specOfMap (K := K)
            (IsScalarTower.toAlgHom K R (IsLocalRing.ResidueField R)) ≫ s from rfl]
    rw [Over.comp_left]
    rw [show Over.Hom.left s
        = Spec.map (CommRingCat.ofHom (Work.SpecLin.Core.rgMapHom R W hW s hs)) ≫ hW.fromSpec
        from (Work.SpecLin.Core.rgMap_fac R W hW s hs).symm]
    rfl
  have hpt : (C.baseChangeFst (IsLocalRing.ResidueField R)) x
      = hW.fromSpec (Spec.map (CommRingCat.ofHom
          ((IsLocalRing.residue R).comp (Work.SpecLin.Core.rgMapHom R W hW s hs)))
            (IsLocalRing.closedPoint (IsLocalRing.ResidueField R))) := by
    rw [hx', Work.SpecLin.Alt.baseChangeFst_ptToPoint, hmap]
    rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]
    have h2 : (Spec.map (CommRingCat.ofHom
            ((IsLocalRing.residue R).comp (Work.SpecLin.Core.rgMapHom R W hW s hs))))
          (IsLocalRing.closedPoint (IsLocalRing.ResidueField R))
        = (Spec.map (CommRingCat.ofHom (Work.SpecLin.Core.rgMapHom R W hW s hs)))
          ((Spec.map (CommRingCat.ofHom
              (IsScalarTower.toAlgHom K R (IsLocalRing.ResidueField R)).toRingHom))
            (IsLocalRing.closedPoint (IsLocalRing.ResidueField R))) := by
      rw [show Spec.map (CommRingCat.ofHom
            ((IsLocalRing.residue R).comp (Work.SpecLin.Core.rgMapHom R W hW s hs)))
          = Spec.map (CommRingCat.ofHom
                (IsScalarTower.toAlgHom K R (IsLocalRing.ResidueField R)).toRingHom)
            ≫ Spec.map (CommRingCat.ofHom (Work.SpecLin.Core.rgMapHom R W hW s hs)) from by
        rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
        rfl]
      rw [Scheme.Hom.comp_apply]
    exact congrArg hW.fromSpec h2.symm
  -- (2) The prime of the point `baseChangeFst κ x` in the affine chart `W` is computed by the
  -- chart dictionary: it is the preimage under `residue ∘ rgMap` of the closed point of `Spec R`.
  have hB : hW.primeIdealOf ⟨(C.baseChangeFst (IsLocalRing.ResidueField R)) x, hle hx⟩
      = PrimeSpectrum.comap
          ((IsLocalRing.residue R).comp (Work.SpecLin.Core.rgMapHom R W hW s hs))
          (IsLocalRing.closedPoint (IsLocalRing.ResidueField R)) := by
    have hmem : hW.fromSpec (Spec.map (CommRingCat.ofHom
        ((IsLocalRing.residue R).comp (Work.SpecLin.Core.rgMapHom R W hW s hs)))
          (IsLocalRing.closedPoint (IsLocalRing.ResidueField R))) ∈ (W : Set C.left) := by
      rw [← hpt]
      exact hle hx
    have hsub : (⟨(C.baseChangeFst (IsLocalRing.ResidueField R)) x, hle hx⟩ : ↥W)
        = ⟨hW.fromSpec (Spec.map (CommRingCat.ofHom
            ((IsLocalRing.residue R).comp (Work.SpecLin.Core.rgMapHom R W hW s hs)))
              (IsLocalRing.closedPoint (IsLocalRing.ResidueField R))), hmem⟩ :=
      Subtype.ext hpt
    rw [hsub]
    exact Work.SpecLin.Core.primeIdealOf_fromSpec_eq_comap W hW
      ((IsLocalRing.residue R).comp (Work.SpecLin.Core.rgMapHom R W hW s hs))
      (IsLocalRing.closedPoint (IsLocalRing.ResidueField R))
  -- (3) Pulling back a chart section along `baseChangeFst κ` and testing membership in the
  -- prime of `x` is the same as testing membership of the section in the prime of
  -- `baseChangeFst κ x` in the chart `W` of `C`.
  have hA := IsAffineOpen.comap_primeIdealOf_appLE
    (f := C.baseChangeFst (IsLocalRing.ResidueField R)) W hW
    (C.bcOpens (IsLocalRing.ResidueField R) W)
    (Work.CurveBasics.BaseChange.isAffineOpen_bcOpens (IsLocalRing.ResidueField R) W hW) hle hx
  have key : (C.baseChangeFst (IsLocalRing.ResidueField R)).appLE W
        (C.bcOpens (IsLocalRing.ResidueField R) W) hle a
      ∈ ((Work.CurveBasics.BaseChange.isAffineOpen_bcOpens
          (IsLocalRing.ResidueField R) W hW).primeIdealOf ⟨x, hx⟩).asIdeal
      ↔ a ∈ (PrimeSpectrum.comap
          ((IsLocalRing.residue R).comp (Work.SpecLin.Core.rgMapHom R W hW s hs))
          (IsLocalRing.closedPoint (IsLocalRing.ResidueField R))).asIdeal := by
    have hAs : (PrimeSpectrum.comap (Scheme.Hom.appLE
          (C.baseChangeFst (IsLocalRing.ResidueField R)) W
          (C.bcOpens (IsLocalRing.ResidueField R) W) hle).hom
          ((Work.CurveBasics.BaseChange.isAffineOpen_bcOpens
            (IsLocalRing.ResidueField R) W hW).primeIdealOf ⟨x, hx⟩)).asIdeal
        = (PrimeSpectrum.comap
            ((IsLocalRing.residue R).comp (Work.SpecLin.Core.rgMapHom R W hW s hs))
            (IsLocalRing.closedPoint (IsLocalRing.ResidueField R))).asIdeal := by
      rw [hA, hB]
    rw [← hAs, PrimeSpectrum.comap_asIdeal, Ideal.mem_comap]
  -- (4) The value of `a` at the closed point of `Spec R` is the residue of `rgMap a`.
  rw [key, PrimeSpectrum.comap_asIdeal, Ideal.mem_comap]
  have hz : (IsLocalRing.closedPoint (IsLocalRing.ResidueField R)).asIdeal = ⊥ := by
    rw [show (IsLocalRing.closedPoint (IsLocalRing.ResidueField R)).asIdeal
          = IsLocalRing.maximalIdeal (IsLocalRing.ResidueField R) from rfl,
      IsLocalRing.maximalIdeal_eq_bot]
  rw [hz, Ideal.mem_bot]
  rw [show ((IsLocalRing.residue R).comp (Work.SpecLin.Core.rgMapHom R W hW s hs)) a
      = (IsLocalRing.residue R) ((Work.SpecLin.Core.rgMap R W hW s hs) a) from rfl,
    IsLocalRing.residue_eq_zero_iff]

end Work.SpecLin.Core
