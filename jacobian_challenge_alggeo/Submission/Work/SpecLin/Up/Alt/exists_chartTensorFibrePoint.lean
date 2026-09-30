/-
# Namespace mirror of `Work.SpecLin.Alt.exists_chartTensorFibrePoint`

This file is an exact copy of `Submission/Work/SpecLin/Alt/exists_chartTensorFibrePoint.lean` (module `Work.SpecLin.Alt.exists_chartTensorFibrePoint`), changed in exactly three ways:

* a `namespace Up` / `end Up` pair is inserted immediately inside the file's own namespace, so
  that every declaration `Work.SpecLin.<Area>.<x>` of the original appears here as
  `Work.SpecLin.<Area>.Up.<x>` (this avoids a name clash with the original, which cannot be
  removed: the original is part of the shared library);
* references to declarations *of the mirrored modules* are rewritten accordingly (full and
  area-relative forms), and imports of those modules point at their mirrors;
* an import of `Core/linEquiv_of_sections_of_chart.lean` (the module that *states* the
  affine-chart theorem) is replaced by an import of the upstream vocabulary module
  `Core/chartVocab.lean`, which declares the same chart algebra under the same names.

The point of the mirror is to break the import cycle
`vocabulary -> statement -> ... -> proof modules -> vocabulary`: the proof modules used to take
their vocabulary from the module that states the theorem, and this made a proof of that theorem
unreachable.  The mathematics is unchanged: the mirror is a verbatim copy of verified code.

The statements of the mirrored theorems mention only names that are *upstream* of the mirror, so
`Work.SpecLin.Core.Up.chartSpecialisation` (module
`Submission.Work.SpecLin.Up.Core.chartSpecialisation`) has literally the statement of
`Work.SpecLin.Core.linEquiv_of_sections_of_chart`, which is proved from it.
-/
import Mathlib
import Submission.Work.SpecLin.Up.Alt.chartMap
import Submission.Work.SpecLin.Up.Alt.chartTensorMap_isFractionRing
import Submission.Work.SpecLin.Alt.mem_range_algebraMap_iff_exists_mul_eq
import Submission.Work.SpecLin.Alt.not_isField_chartSections
import Submission.Work.SpecLin.Alt.isClosed_fromSpec_of_ne_bot
import Submission.Work.SpecLin.Alt.image_fractionSet_map_of_surjective
import Submission.Work.SpecLin.Setup.ord_eq_ordFrac_localization
import Submission.Work.CurveBasics.Place.Valuation
import Submission.Work.CurveBasics.BaseChange.mem_range_germ_iff
import Submission.Work.CurveBasics.Point.isClosed_of_coheight_eq_one

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000

universe u

open CategoryTheory Limits AlgebraicGeometry
open scoped TensorProduct

namespace Work.SpecLin.Alt
namespace Up

variable {K : Type u} [Field K] {C : Work.CurveBasics.Curve K}

/-- The coordinate ring of the affine chart `C.bcOpens κ W` of the special fibre. -/
abbrev fibreSections (R : Type u) [CommRing R] [IsDomain R] [ValuationRing R] [Algebra K R]
    (W : C.left.Opens) : Type u :=
  Γ((C.baseChange (IsLocalRing.ResidueField R)).left,
    C.bcOpens (IsLocalRing.ResidueField R) W)

theorem exists_chartTensorFibrePoint {K : Type _} [Field K] {C : Work.CurveBasics.Curve K}
    (R : Type _) [CommRing R] [IsDomain R] [ValuationRing R] [Algebra K R]
    (W : C.left.Opens) (hW : AlgebraicGeometry.IsAffineOpen W) [Nonempty W]
    (N : Ideal (Work.SpecLin.Core.chartTensor R W)) [N.IsMaximal]
    (hPN : Work.SpecLin.Core.chartFibrePrime R W ≤ N) :
    ∃ z : (C.baseChange (IsLocalRing.ResidueField R)).Place,
      z.point ∈ C.bcOpens (IsLocalRing.ResidueField R) W ∧
      (∀ x : (C.baseChange (IsLocalRing.ResidueField R)).functionField,
        (∃ a b : Work.SpecLin.Core.chartTensor R W, b ∉ N ∧
            x * Work.SpecLin.Alt.Up.chartTensorRedMap R W hW b
              = Work.SpecLin.Alt.Up.chartTensorRedMap R W hW a)
          ↔ 0 ≤ (C.baseChange (IsLocalRing.ResidueField R)).ordAt x z) := by
  classical
  haveI hU : IsAffineOpen (C.bcOpens (IsLocalRing.ResidueField R) W) :=
    Work.CurveBasics.BaseChange.isAffineOpen_bcOpens (IsLocalRing.ResidueField R) W hW
  haveI hUne : Nonempty (C.bcOpens (IsLocalRing.ResidueField R) W) :=
    Work.CurveBasics.Curve.bcOpens_nonempty C (IsLocalRing.ResidueField R) W
  -- the map from the relative chart to the chart ring of the special fibre
  let ψ : Work.SpecLin.Core.chartTensor R W →+* fibreSections R W :=
    Work.SpecLin.Alt.Up.chartTensorRedSectionsMap R W hW
  -- its two factors
  let tMap : Γ(C.left, W) ⊗[K] R →+* Γ(C.left, W) ⊗[K] (IsLocalRing.ResidueField R) :=
    (Algebra.TensorProduct.map (AlgHom.id K Γ(C.left, W))
      (IsScalarTower.toAlgHom K R (IsLocalRing.ResidueField R))).toRingHom
  let sLift : Γ(C.left, W) ⊗[K] (IsLocalRing.ResidueField R) →+* fibreSections R W :=
    Work.CurveBasics.Curve.BCSquare.sectionsLift (Work.CurveBasics.Curve.bcSquare C (IsLocalRing.ResidueField R)) W hW
  have hψfac : ψ = sLift.comp tMap := rfl
  have hres_surj : Function.Surjective (algebraMap R (IsLocalRing.ResidueField R)) := by
    rw [IsLocalRing.ResidueField.algebraMap_eq]
    exact IsLocalRing.residue_surjective
  have hκsurj : Function.Surjective (IsScalarTower.toAlgHom K R (IsLocalRing.ResidueField R)) :=
    fun y => let ⟨r, hr⟩ := hres_surj y; ⟨r, hr⟩
  have htMap_surj : Function.Surjective tMap :=
    Algebra.TensorProduct.map_surjective (AlgHom.id K Γ(C.left, W))
      (IsScalarTower.toAlgHom K R (IsLocalRing.ResidueField R))
      Function.surjective_id hκsurj
  have hsLift_surj : Function.Surjective sLift :=
    Work.SpecLin.Alt.Up.sectionsLift_surjective K (IsLocalRing.ResidueField R)
      (Work.CurveBasics.Curve.bcSquare C (IsLocalRing.ResidueField R)) W hW
  have hsLift_inj : Function.Injective sLift :=
    Work.CurveBasics.Curve.BCSquare.sectionsLift_injective (Work.CurveBasics.Curve.bcSquare C (IsLocalRing.ResidueField R)) W hW
  have hψ_surj : Function.Surjective ψ := by
    rw [hψfac]
    exact hsLift_surj.comp htMap_surj
  -- the kernel of the tensor projection is the fibre prime
  have hkerT : RingHom.ker tMap = Work.SpecLin.Core.chartFibrePrime R W := by
    have hkerres : RingHom.ker (IsScalarTower.toAlgHom K R (IsLocalRing.ResidueField R))
        = IsLocalRing.maximalIdeal R := by
      change RingHom.ker (algebraMap R (IsLocalRing.ResidueField R)) = IsLocalRing.maximalIdeal R
      rw [IsLocalRing.ResidueField.algebraMap_eq, IsLocalRing.ker_residue]
    have h := Algebra.TensorProduct.lTensor_ker (R := K) (A := Γ(C.left, W))
      (IsScalarTower.toAlgHom K R (IsLocalRing.ResidueField R)) hκsurj
    rw [hkerres] at h
    change RingHom.ker (Algebra.TensorProduct.map (AlgHom.id K Γ(C.left, W))
      (IsScalarTower.toAlgHom K R (IsLocalRing.ResidueField R))) = _
    rw [h, Work.SpecLin.Core.chartFibrePrime]
  have hkerψ : RingHom.ker ψ = Work.SpecLin.Core.chartFibrePrime R W := by
    apply le_antisymm
    · intro b hb
      have h1 : sLift (tMap b) = 0 := by
        have h2 : ψ b = 0 := RingHom.mem_ker.mp hb
        rw [hψfac] at h2
        simpa using h2
      have h3 : tMap b = 0 := hsLift_inj (by simpa using h1)
      have h4 : b ∈ RingHom.ker tMap := RingHom.mem_ker.mpr h3
      rwa [hkerT] at h4
    · intro b hb
      have h3 : tMap b = 0 := by
        have h4 : b ∈ RingHom.ker tMap := by rwa [hkerT]
        exact RingHom.mem_ker.mp h4
      rw [hψfac, RingHom.mem_ker]
      simp [h3]
  have hψ_le : RingHom.ker ψ ≤ N := by
    rw [hkerψ]
    exact hPN
  -- the maximal ideal of the special-fibre chart ring
  let m : Ideal (fibreSections R W) := Ideal.map ψ N
  have hψN : ∀ b : Work.SpecLin.Core.chartTensor R W, ψ b ∈ m ↔ ∃ y ∈ N, ψ y = ψ b := by
    intro b
    exact Ideal.mem_map_iff_of_surjective ψ hψ_surj
  have hker_g : RingHom.ker ((Ideal.Quotient.mk m).comp ψ) = N := by
    apply le_antisymm
    · intro b hb
      have hbm : ψ b ∈ m := by
        have h1 : ((Ideal.Quotient.mk m).comp ψ) b = 0 := RingHom.mem_ker.mp hb
        exact Ideal.Quotient.eq_zero_iff_mem.mp h1
      obtain ⟨y, hyN, hy⟩ := (Ideal.mem_map_iff_of_surjective ψ hψ_surj).mp hbm
      have hzy : b - y ∈ RingHom.ker ψ := by
        rw [RingHom.mem_ker, map_sub, hy, sub_self]
      have hbN : b - y ∈ N := hψ_le hzy
      have := N.add_mem hbN hyN
      simpa using this
    · intro b hb
      rw [RingHom.mem_ker]
      show (Ideal.Quotient.mk m) (ψ b) = 0
      rw [Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.mem_map_of_mem ψ hb
  have hmmax : m.IsMaximal := by
    rw [Ideal.Quotient.maximal_ideal_iff_isField_quotient]
    have hquot : (Work.SpecLin.Core.chartTensor R W ⧸ N) ≃+* (fibreSections R W ⧸ m) :=
      (Ideal.quotEquivOfEq (I := N)
        (J := RingHom.ker ((Ideal.Quotient.mk m).comp ψ)) hker_g.symm).trans
        (RingHom.quotientKerEquivOfSurjective
          ((Ideal.Quotient.mk_surjective).comp hψ_surj))
    have hBN : IsField (Work.SpecLin.Core.chartTensor R W ⧸ N) :=
      (Ideal.Quotient.maximal_ideal_iff_isField_quotient N).mp inferInstance
    exact (MulEquiv.isField_congr hquot.symm.toMulEquiv).mpr hBN
  haveI hmprime : m.IsPrime := hmmax.isPrime
  have hm_ne_bot : m ≠ ⊥ := by
    intro hbot
    haveI : IsField (fibreSections R W) := by
      have h1 : IsField (fibreSections R W ⧸ (⊥ : Ideal (fibreSections R W))) :=
        (Ideal.Quotient.maximal_ideal_iff_isField_quotient _).mp (hbot ▸ hmmax)
      have e : (fibreSections R W ⧸ (⊥ : Ideal (fibreSections R W))) ≃+* fibreSections R W :=
        (Ideal.quotEquivOfEq (I := ⊥)
          (J := RingHom.ker (RingHom.id (fibreSections R W)))
          (by ext x; simp [RingHom.mem_ker])).trans
          (RingHom.quotientKerEquivOfSurjective (f := RingHom.id (fibreSections R W))
            Function.surjective_id)
      exact (MulEquiv.isField_congr e.symm.toMulEquiv).mpr h1
    exact not_isField_chartSections (C.baseChange (IsLocalRing.ResidueField R))
      (C.bcOpens (IsLocalRing.ResidueField R) W) hU ‹IsField (fibreSections R W)›
  let qm : PrimeSpectrum (fibreSections R W) := ⟨m, hmprime⟩
  let z : (C.baseChange (IsLocalRing.ResidueField R)).left := hU.fromSpec qm
  have hz_mem : z ∈ C.bcOpens (IsLocalRing.ResidueField R) W := by
    have h : z ∈ Set.range hU.fromSpec := ⟨qm, rfl⟩
    rwa [hU.range_fromSpec] at h
  have hz_closed : IsClosed ({z} : Set (C.baseChange (IsLocalRing.ResidueField R)).left) :=
    isClosed_fromSpec_of_ne_bot (C.baseChange (IsLocalRing.ResidueField R))
      (C.bcOpens (IsLocalRing.ResidueField R) W) hU qm (by
        have h : qm.asIdeal = m := rfl
        rw [h]; exact hm_ne_bot)
  refine ⟨⟨z, hz_closed⟩, hz_mem, fun x => ?_⟩
  letI : Algebra (Work.SpecLin.Core.chartTensor R W) (fibreSections R W) := ψ.toAlgebra
  letI : Algebra (Work.SpecLin.Core.chartTensor R W)
      (C.baseChange (IsLocalRing.ResidueField R)).functionField :=
    (Work.SpecLin.Alt.Up.chartTensorRedMap R W hW).toAlgebra
  haveI hST : IsScalarTower (Work.SpecLin.Core.chartTensor R W) (fibreSections R W)
      (C.baseChange (IsLocalRing.ResidueField R)).functionField :=
    IsScalarTower.of_algebraMap_eq (fun b => rfl)
  letI : Algebra (fibreSections R W)
      ((C.baseChange (IsLocalRing.ResidueField R)).left.presheaf.stalk z) :=
    TopCat.Presheaf.algebra_section_stalk
      ((C.baseChange (IsLocalRing.ResidueField R)).left.presheaf) ⟨z, hz_mem⟩
  haveI hloc : IsLocalization.AtPrime
      ((C.baseChange (IsLocalRing.ResidueField R)).left.presheaf.stalk z) m :=
    hU.isLocalization_stalk' qm hz_mem
  haveI hST2 : IsScalarTower (fibreSections R W)
      ((C.baseChange (IsLocalRing.ResidueField R)).left.presheaf.stalk z)
      (C.baseChange (IsLocalRing.ResidueField R)).functionField :=
    functionField_isScalarTower ((C.baseChange (IsLocalRing.ResidueField R)).left)
      (C.bcOpens (IsLocalRing.ResidueField R) W) ⟨z, hz_mem⟩
  have step1 : (∃ a b : Work.SpecLin.Core.chartTensor R W, b ∉ N ∧
        x * Work.SpecLin.Alt.Up.chartTensorRedMap R W hW b
          = Work.SpecLin.Alt.Up.chartTensorRedMap R W hW a) ↔
      (∃ a b : fibreSections R W, b ∉ m ∧
        x * algebraMap (fibreSections R W)
              (C.baseChange (IsLocalRing.ResidueField R)).functionField b
          = algebraMap (fibreSections R W)
              (C.baseChange (IsLocalRing.ResidueField R)).functionField a) := by
    have h := image_fractionSet_map_of_surjective (φ := ψ) hψ_surj (q := N) hψ_le
      (f := Work.SpecLin.Alt.Up.chartTensorRedMap R W hW)
      (f' := (algebraMap (fibreSections R W)
        (C.baseChange (IsLocalRing.ResidueField R)).functionField))
      (hf := fun a => rfl) x
    simpa using h
  rw [← Work.CurveBasics.BaseChange.mem_range_algebraMap_stalk_iff
    (C.baseChange (IsLocalRing.ResidueField R)) ⟨z, hz_closed⟩ x]
  rw [Work.SpecLin.Alt.mem_range_algebraMap_iff_exists_mul_eq (R := fibreSections R W)
    (S := (C.baseChange (IsLocalRing.ResidueField R)).left.presheaf.stalk z)
    (K := (C.baseChange (IsLocalRing.ResidueField R)).functionField) m x]
  exact step1

end Up
end Work.SpecLin.Alt

