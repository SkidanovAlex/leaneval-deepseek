/-
# The section prime plus the fibre prime is the prime of the section's special-fibre point

For a curve `C` over a field `K`, a `K`-valuation ring `R`, an affine open chart `W ⊆ C`,
an `R`-point `s` of `C` whose image lies in `W` and the relative chart `B = Γ(C,W) ⊗_K R`
with fibre prime `P = m_R·B`, this file computes the image of the ideal
`I ⊔ P` (`I = sectionPrime R W (rgMap R W hW s hs)`) under the reduction map
`ψ = chartTensorRedSectionsMap : B → Γ(C_κ, W_κ)` (`κ = R ⧸ m_R`):

  `Ideal.map ψ (I ⊔ P) = primeIdealOf (ptToPoint (closedPt R ≫ s))`,

i.e. the section prime, reduced modulo the fibre prime, is exactly the prime of the point of
the special fibre at which the section lands.  Together with the "localization ↔ order"
dictionary `exists_mul_eq_iff_ordAt_of_primeIdealOf` and the "recover the prime from its
localization" lemma `recover_prime_of_exists_mul_eq`, this gives the main theorem
`sectionPrime_le_iff_ptPlace_eq_residue` below.
-/
import Mathlib
import Submission.Work.SpecLin.Alt.chartMap
import Submission.Work.SpecLin.Alt.exists_chartTensorFibrePoint
import Submission.Work.SpecLin.Alt.image_fractionSet_map_of_surjective
import Submission.Work.SpecLin.Alt.mem_range_algebraMap_iff_exists_mul_eq
import Submission.Work.SpecLin.Alt.isClosed_fromSpec_of_ne_bot
import Submission.Work.SpecLin.Alt.recover_prime_of_exists_mul_eq
import Submission.Work.SpecLin.Alt.exists_mul_eq_iff_ordAt_of_primeIdealOf
import Submission.Work.SpecLin.Core.sectionPrime_sup_fibrePrime_eq_ker
import Submission.Work.SpecLin.Core.mem_primeIdealOf_ptToPoint_iff
import Submission.Work.CurveBasics.BaseChange.isAffineOpen_bcOpens
import Submission.Work.SpecLin.Alt.chartDictionary

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.style.haveILetI false

universe u

open CategoryTheory Limits AlgebraicGeometry
open scoped TensorProduct

namespace Work.SpecLin.Alt

/-- The reduction map `B = Γ(C,W) ⊗_K R → Γ(C_κ, W_κ)` of the relative chart to the chart of
the special fibre is surjective: it is the composite of the tensor product `id ⊗ (R → κ)` with
the identification `Γ(C,W) ⊗_K κ ≅ Γ(C_κ, W_κ)`. -/
theorem chartTensorRedSectionsMap_surjective {K : Type u} [Field K]
    {C : Work.CurveBasics.Curve K}
    (R : Type u) [CommRing R] [IsDomain R] [ValuationRing R] [Algebra K R]
    (W : C.left.Opens) (hW : AlgebraicGeometry.IsAffineOpen W) [Nonempty W] :
    Function.Surjective (Work.SpecLin.Alt.chartTensorRedSectionsMap (K:=K) (C:=C) R W hW) := by
  have hres_surj : Function.Surjective (algebraMap R (IsLocalRing.ResidueField R)) := by
    rw [IsLocalRing.ResidueField.algebraMap_eq]
    exact IsLocalRing.residue_surjective
  have hκsurj : Function.Surjective
      (IsScalarTower.toAlgHom K R (IsLocalRing.ResidueField R)) :=
    fun y => let ⟨r, hr⟩ := hres_surj y; ⟨r, hr⟩
  unfold Work.SpecLin.Alt.chartTensorRedSectionsMap
  exact (Work.SpecLin.Alt.sectionsLift_surjective K (IsLocalRing.ResidueField R)
      (Work.CurveBasics.Curve.bcSquare C (IsLocalRing.ResidueField R)) W hW).comp
    (Algebra.TensorProduct.map_surjective (AlgHom.id K Γ(C.left, W))
      (IsScalarTower.toAlgHom K R (IsLocalRing.ResidueField R))
      Function.surjective_id hκsurj)

/-- The kernel of the reduction map `Γ(C,W) ⊗_K R → Γ(C_κ, W_κ)` is the fibre prime
`P = m_R·(Γ(C,W) ⊗_K R)`. -/
theorem ker_chartTensorRedSectionsMap {K : Type u} [Field K]
    {C : Work.CurveBasics.Curve K}
    (R : Type u) [CommRing R] [IsDomain R] [ValuationRing R] [Algebra K R]
    (W : C.left.Opens) (hW : AlgebraicGeometry.IsAffineOpen W) [Nonempty W] :
    RingHom.ker (Work.SpecLin.Alt.chartTensorRedSectionsMap (K:=K) (C:=C) R W hW)
      = Work.SpecLin.Core.chartFibrePrime (K:=K) (C:=C) R W := by
  let tMap : Work.SpecLin.Core.chartTensor (K:=K) (C:=C) R W →+*
      (Γ(C.left, W) ⊗[K] IsLocalRing.ResidueField R) :=
    (Algebra.TensorProduct.map (AlgHom.id K Γ(C.left, W))
      (IsScalarTower.toAlgHom K R (IsLocalRing.ResidueField R))).toRingHom
  let sLift : (Γ(C.left, W) ⊗[K] IsLocalRing.ResidueField R) →+*
      Γ((C.baseChange (IsLocalRing.ResidueField R)).left,
        C.bcOpens (IsLocalRing.ResidueField R) W) :=
    Work.CurveBasics.Curve.BCSquare.sectionsLift
      (Work.CurveBasics.Curve.bcSquare C (IsLocalRing.ResidueField R)) W hW
  have hψfac : Work.SpecLin.Alt.chartTensorRedSectionsMap (K:=K) (C:=C) R W hW
      = sLift.comp tMap := rfl
  have hres_surj : Function.Surjective (algebraMap R (IsLocalRing.ResidueField R)) := by
    rw [IsLocalRing.ResidueField.algebraMap_eq]
    exact IsLocalRing.residue_surjective
  have hκsurj : Function.Surjective
      (IsScalarTower.toAlgHom K R (IsLocalRing.ResidueField R)) :=
    fun y => let ⟨r, hr⟩ := hres_surj y; ⟨r, hr⟩
  have hsLift_inj : Function.Injective sLift :=
    Work.CurveBasics.Curve.BCSquare.sectionsLift_injective
      (Work.CurveBasics.Curve.bcSquare C (IsLocalRing.ResidueField R)) W hW
  have hkerT : RingHom.ker tMap = Work.SpecLin.Core.chartFibrePrime (K:=K) (C:=C) R W := by
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
  apply le_antisymm
  · intro b hb
    have h1 : sLift (tMap b) = 0 := by
      have h2 : Work.SpecLin.Alt.chartTensorRedSectionsMap (K:=K) (C:=C) R W hW b = 0 :=
        RingHom.mem_ker.mp hb
      rw [hψfac] at h2
      exact h2
    have h3 : tMap b = 0 := by
      apply hsLift_inj
      rw [h1, map_zero]
    have h4 : b ∈ RingHom.ker tMap := RingHom.mem_ker.mpr h3
    rwa [hkerT] at h4
  · intro b hb
    have h3 : tMap b = 0 := by
      have h4 : b ∈ RingHom.ker tMap := by rwa [hkerT]
      exact RingHom.mem_ker.mp h4
    rw [hψfac, RingHom.mem_ker]
    show sLift (tMap b) = 0
    rw [h3, map_zero]

theorem sectionPrime_sup_chartFibrePrime_map_eq_primeIdealOf {K : Type u} [Field K]
    {C : Work.CurveBasics.Curve K}
    (R : Type u) [CommRing R] [IsDomain R] [ValuationRing R] [Algebra K R]
    (W : C.left.Opens) (hW : AlgebraicGeometry.IsAffineOpen W) [Nonempty W]
    (s : Work.SpecLin.CurvePt C R)
    (hs : Set.range (s.left.base) ⊆ (W : Set C.left)) :
    Ideal.map (Work.SpecLin.Alt.chartTensorRedSectionsMap (K:=K) (C:=C) R W hW)
        (Work.SpecLin.Core.sectionPrime (K:=K) (C:=C) R W
            (Work.SpecLin.Core.rgMap R W hW s hs) ⊔
          Work.SpecLin.Core.chartFibrePrime (K:=K) (C:=C) R W)
      = ((Work.CurveBasics.BaseChange.isAffineOpen_bcOpens (IsLocalRing.ResidueField R) W hW).primeIdealOf
          ⟨Work.SpecLin.ptToPoint (Work.SpecLin.RPt.map
              (IsScalarTower.toAlgHom K R (IsLocalRing.ResidueField R)) s),
            Work.SpecLin.Alt.ptToPoint_closedPt_mem R W s hs⟩).asIdeal := by
  classical
  let S : Type _ := Γ((C.baseChange (IsLocalRing.ResidueField R)).left,
    C.bcOpens (IsLocalRing.ResidueField R) W)
  let app := (Work.CurveBasics.Curve.baseChangeFst C
    (IsLocalRing.ResidueField R)).appLE W (C.bcOpens (IsLocalRing.ResidueField R) W) le_rfl
  set φ := Work.SpecLin.Core.rgMap R W hW s hs with hφ
  set ψ := Work.SpecLin.Alt.chartTensorRedSectionsMap (K:=K) (C:=C) R W hW with hψ
  set hU := Work.CurveBasics.BaseChange.isAffineOpen_bcOpens (IsLocalRing.ResidueField R) W hW with hUdef
  -- Step 1
  have hIP : Work.SpecLin.Core.sectionPrime (K:=K) (C:=C) R W φ ⊔
      Work.SpecLin.Core.chartFibrePrime (K:=K) (C:=C) R W
      = RingHom.ker ((IsLocalRing.residue R).comp
          (Work.SpecLin.Core.evChart (K:=K) (C:=C) R W φ).toRingHom) := by
    have hh := Work.SpecLin.Core.sectionPrime_sup_fibrePrime_eq_ker (K:=K)
      (A := Γ(C.left, W)) (R:=R) φ
    rw [Work.SpecLin.Core.sectionPrime, Work.SpecLin.Core.chartFibrePrime,
      Work.SpecLin.Core.evChart]
    exact hh
  -- Step 2
  have hres_surj : Function.Surjective (algebraMap R (IsLocalRing.ResidueField R)) := by
    rw [IsLocalRing.ResidueField.algebraMap_eq]
    exact IsLocalRing.residue_surjective
  have hκsurj : Function.Surjective (IsScalarTower.toAlgHom K R (IsLocalRing.ResidueField R)) :=
    fun y => let ⟨r, hr⟩ := hres_surj y; ⟨r, hr⟩
  have hψsurj : Function.Surjective ψ := by
    rw [hψ]
    unfold Work.SpecLin.Alt.chartTensorRedSectionsMap
    exact (Work.SpecLin.Alt.sectionsLift_surjective K (IsLocalRing.ResidueField R)
        (Work.CurveBasics.Curve.bcSquare C (IsLocalRing.ResidueField R)) W hW).comp
      (Algebra.TensorProduct.map_surjective (AlgHom.id K Γ(C.left, W))
        (IsScalarTower.toAlgHom K R (IsLocalRing.ResidueField R))
        Function.surjective_id hκsurj)
  -- Step 3
  set p : Work.SpecLin.CurveFPt C (IsLocalRing.ResidueField R) :=
    Work.SpecLin.RPt.map (IsScalarTower.toAlgHom K R (IsLocalRing.ResidueField R)) s with hp
  have hmem : Work.SpecLin.ptToPoint p ∈ C.bcOpens (IsLocalRing.ResidueField R) W :=
    Work.SpecLin.Alt.ptToPoint_closedPt_mem R W s hs
  have hrange : Set.range (Work.SpecLin.ptLeft p).base ⊆ Set.range hU.fromSpec.base := by
    rw [hU.range_fromSpec, Work.SpecLin.Points.range_ptLeft]
    exact Set.singleton_subset_iff.mpr hmem
  set lift := IsOpenImmersion.lift hU.fromSpec (Work.SpecLin.ptLeft p) hrange with hlift
  have hliftfac : lift ≫ hU.fromSpec = Work.SpecLin.ptLeft p :=
    IsOpenImmersion.lift_fac _ _ _
  set γ := (Spec.preimage lift).hom with hγ
  have hγmap : Spec.map (CommRingCat.ofHom γ) = lift := by
    rw [hγ]
    exact Spec.map_preimage lift
  have hfac : Spec.map (CommRingCat.ofHom γ) ≫ hU.fromSpec = Work.SpecLin.ptLeft p := by
    rw [hγmap, hliftfac]
  -- Step 4
  have hpt : Work.SpecLin.ptToPoint p
      = hU.fromSpec (Spec.map (CommRingCat.ofHom γ)
          (IsLocalRing.closedPoint (IsLocalRing.ResidueField R))) := by
    show (Work.SpecLin.ptLeft p).base (IsLocalRing.closedPoint _) = _
    rw [← hfac]
    rfl
  have hprime : (hU.primeIdealOf ⟨Work.SpecLin.ptToPoint p, hmem⟩).asIdeal = RingHom.ker γ := by
    rw [Work.SpecLin.Core.primeIdealOf_eq_of_fromSpec_eq hU γ
      (IsLocalRing.closedPoint (IsLocalRing.ResidueField R)) hmem hpt]
    rw [PrimeSpectrum.comap_asIdeal,
      Work.SpecLin.Core.closedPoint_asIdeal_eq_bot (IsLocalRing.ResidueField R),
      (RingHom.ker_eq_comap_bot γ).symm]
  -- Step 5: κ-linearity of γ
  have hstruct : hU.fromSpec ≫ (C.baseChange (IsLocalRing.ResidueField R)).hom
      = Spec.map (CommRingCat.ofHom (algebraMap (IsLocalRing.ResidueField R) S)) :=
    (Work.CurveBasics.Curve.specMap_algebraMap_sections
      (C.baseChange (IsLocalRing.ResidueField R)) hU).symm
  have h1 : Spec.map (CommRingCat.ofHom γ) ≫
      Spec.map (CommRingCat.ofHom (algebraMap (IsLocalRing.ResidueField R) S))
      = 𝟙 (Spec (CommRingCat.of (IsLocalRing.ResidueField R))) := by
    rw [← hstruct, ← Category.assoc, hfac]
    exact Work.SpecLin.Points.ptLeft_comp_hom p
  have hγlin : γ.comp (algebraMap (IsLocalRing.ResidueField R) S)
      = RingHom.id (IsLocalRing.ResidueField R) := by
    have h3 : CommRingCat.ofHom (γ.comp (algebraMap (IsLocalRing.ResidueField R) S))
        = 𝟙 (CommRingCat.of (IsLocalRing.ResidueField R)) := by
      apply Spec.map_injective
      rw [Spec.map_id]
      rw [← h1]
      rw [← Spec.map_comp (CommRingCat.ofHom (algebraMap (IsLocalRing.ResidueField R) S))
          (CommRingCat.ofHom γ)]
      rw [← CommRingCat.ofHom_comp]
    simpa using congrArg CommRingCat.Hom.hom h3
  -- Step 6: the appLE identity
  have hM : Spec.map app ≫ hW.fromSpec
      = hU.fromSpec ≫ Work.CurveBasics.Curve.baseChangeFst C (IsLocalRing.ResidueField R) :=
    IsAffineOpen.SpecMap_appLE_fromSpec (Work.CurveBasics.Curve.baseChangeFst C
      (IsLocalRing.ResidueField R)) hW hU le_rfl
  have hs_left : Over.Hom.left s = Spec.map (CommRingCat.ofHom
      (Work.SpecLin.Core.rgMapHom R W hW s hs)) ≫ hW.fromSpec :=
    (Work.SpecLin.Core.rgMap_fac R W hW s hs).symm
  have hp_def : p.left = Spec.map (CommRingCat.ofHom
      (algebraMap R (IsLocalRing.ResidueField R))) ≫ Over.Hom.left s := by
    show Over.Hom.left (Work.SpecLin.RPt.map (IsScalarTower.toAlgHom K R
      (IsLocalRing.ResidueField R)) s) = _
    rw [Work.SpecLin.RPt.map, Over.comp_left]
    rfl
  have hp_left : p.left = Spec.map (CommRingCat.ofHom ((IsLocalRing.residue R).comp
      (Work.SpecLin.Core.rgMapHom R W hW s hs))) ≫ hW.fromSpec := by
    rw [hp_def, IsLocalRing.ResidueField.algebraMap_eq, hs_left]
    rw [← Category.assoc, ← Spec.map_comp (CommRingCat.ofHom (Work.SpecLin.Core.rgMapHom R W hW s hs))
      (CommRingCat.ofHom (IsLocalRing.residue R)), ← CommRingCat.ofHom_comp]
  have happLE : γ.comp app.hom
      = (IsLocalRing.residue R).comp (Work.SpecLin.Core.rgMapHom R W hW s hs) := by
    have e1 : Spec.map (CommRingCat.ofHom (γ.comp app.hom))
        = Spec.map (CommRingCat.ofHom γ) ≫ Spec.map app := by
      rw [← Spec.map_comp app (CommRingCat.ofHom γ)]
      congr 1
    have hkey : Spec.map (CommRingCat.ofHom (γ.comp app.hom)) ≫ hW.fromSpec
        = Spec.map (CommRingCat.ofHom ((IsLocalRing.residue R).comp
            (Work.SpecLin.Core.rgMapHom R W hW s hs))) ≫ hW.fromSpec := by
      rw [e1, Category.assoc, hM, ← Category.assoc, hfac, Work.SpecLin.ptLeft_fst]
      exact hp_left
    have hmain : Spec.map (CommRingCat.ofHom (γ.comp app.hom))
        = Spec.map (CommRingCat.ofHom ((IsLocalRing.residue R).comp
            (Work.SpecLin.Core.rgMapHom R W hW s hs))) :=
      (cancel_mono hW.fromSpec).mp hkey
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective hmain)
  -- Step 7: γ ∘ ψ = residue ∘ ev
  have hcomp : γ.comp ψ = (IsLocalRing.residue R).comp
      (Work.SpecLin.Core.evChart (K:=K) (C:=C) R W φ).toRingHom := by
    refine Work.CurveBasics.Curve.BCSquare.ringHom_ext_tensor (C := IsLocalRing.ResidueField R) ?_ ?_
    · intro a
      rw [RingHom.comp_apply, RingHom.comp_apply]
      show γ (ψ (a ⊗ₜ[K] (1 : R))) = IsLocalRing.residue R
        (Work.SpecLin.Core.evChart (K:=K) (C:=C) R W φ (a ⊗ₜ[K] (1 : R)))
      rw [Work.SpecLin.Core.evChart_tmul]
      have hψa : ψ (a ⊗ₜ[K] (1 : R)) = app.hom a := by
        rw [hψ, Work.SpecLin.Alt.chartTensorRedSectionsMap_tmul_one]
        rw [Scheme.Hom.app_eq_appLE]
        rfl
      rw [hψa, show γ (app.hom a) = (γ.comp app.hom) a from rfl, happLE]
      rw [RingHom.comp_apply, hφ, mul_one]
      rfl
    · intro r
      rw [RingHom.comp_apply, RingHom.comp_apply]
      show γ (ψ ((1 : Γ(C.left, W)) ⊗ₜ[K] r)) = IsLocalRing.residue R
        (Work.SpecLin.Core.evChart (K:=K) (C:=C) R W φ ((1 : Γ(C.left, W)) ⊗ₜ[K] r))
      rw [Work.SpecLin.Core.evChart_tmul]
      have hψr : ψ ((1 : Γ(C.left, W)) ⊗ₜ[K] r)
          = algebraMap (IsLocalRing.ResidueField R) S
              (IsScalarTower.toAlgHom K R (IsLocalRing.ResidueField R) r) := by
        rw [hψ]
        unfold Work.SpecLin.Alt.chartTensorRedSectionsMap
        rw [RingHom.comp_apply]
        rw [show (Algebra.TensorProduct.map (AlgHom.id K Γ(C.left, W))
              (IsScalarTower.toAlgHom K R (IsLocalRing.ResidueField R))).toRingHom
                ((1 : Γ(C.left, W)) ⊗ₜ[K] r)
            = (Algebra.TensorProduct.map (AlgHom.id K Γ(C.left, W))
              (IsScalarTower.toAlgHom K R (IsLocalRing.ResidueField R)))
                ((1 : Γ(C.left, W)) ⊗ₜ[K] r) from rfl]
        rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, IsScalarTower.toAlgHom_apply]
        rw [Work.CurveBasics.Curve.BCSquare.sectionsLift_one_tmul]
        rfl
      rw [hψr, show γ (algebraMap (IsLocalRing.ResidueField R) S
            (IsScalarTower.toAlgHom K R (IsLocalRing.ResidueField R) r))
          = (γ.comp (algebraMap (IsLocalRing.ResidueField R) S))
              (IsScalarTower.toAlgHom K R (IsLocalRing.ResidueField R) r) from rfl]
      rw [hγlin, IsScalarTower.toAlgHom_apply, IsLocalRing.ResidueField.algebraMap_eq]
      rw [RingHom.id_apply, map_one, one_mul]
  -- Step 8: conclusion
  have hkercomp : RingHom.ker (γ.comp ψ) = Ideal.comap ψ (RingHom.ker γ) := by
    ext x
    simp only [RingHom.mem_ker, Ideal.mem_comap, RingHom.comp_apply]
  have hmapker : Ideal.map ψ (RingHom.ker (γ.comp ψ)) = RingHom.ker γ := by
    rw [hkercomp]
    exact Ideal.map_comap_of_surjective ψ hψsurj (RingHom.ker γ)
  calc Ideal.map ψ (Work.SpecLin.Core.sectionPrime (K:=K) (C:=C) R W φ ⊔
        Work.SpecLin.Core.chartFibrePrime (K:=K) (C:=C) R W)
      = Ideal.map ψ (RingHom.ker ((IsLocalRing.residue R).comp
          (Work.SpecLin.Core.evChart (K:=K) (C:=C) R W φ).toRingHom)) := by rw [hIP]
    _ = Ideal.map ψ (RingHom.ker (γ.comp ψ)) := by rw [hcomp]
    _ = Ideal.map ψ (Ideal.comap ψ (RingHom.ker γ)) := by rw [hkercomp]
    _ = RingHom.ker γ := hmapker
    _ = (hU.primeIdealOf ⟨Work.SpecLin.ptToPoint p, hmem⟩).asIdeal := hprime.symm

/-- **The section prime reduces to the prime of the section's special-fibre point.** -/
theorem sectionPrime_le_iff_ptPlace_eq_residue {K : Type _} [Field K]
    {C : Work.CurveBasics.Curve K}
    (R : Type _) [CommRing R] [IsDomain R] [ValuationRing R] [Algebra K R]
    (W : C.left.Opens) (hW : AlgebraicGeometry.IsAffineOpen W) [Nonempty W]
    (s : Work.SpecLin.CurvePt C R)
    (hs : Set.range (s.left.base) ⊆ (W : Set C.left))
    (N : Ideal (Work.SpecLin.Core.chartTensor (K := K) (C := C) R W)) [N.IsMaximal]
    (hPN : Work.SpecLin.Core.chartFibrePrime (K := K) (C := C) R W <= N)
    (z : (C.baseChange (IsLocalRing.ResidueField R)).Place)
    (hz : forall x : (C.baseChange (IsLocalRing.ResidueField R)).functionField,
      (exists a b : Work.SpecLin.Core.chartTensor (K := K) (C := C) R W,
          b ∉ N ∧ x * Work.SpecLin.Alt.chartTensorRedMap R W hW b
            = Work.SpecLin.Alt.chartTensorRedMap R W hW a)
        ↔ 0 ≤ (C.baseChange (IsLocalRing.ResidueField R)).ordAt x z) :
    Work.SpecLin.Core.sectionPrime R W (Work.SpecLin.Core.rgMap R W hW s hs) ⊔
        Work.SpecLin.Core.chartFibrePrime (K := K) (C := C) R W = N
      ↔ Work.SpecLin.ptPlace (Work.SpecLin.RPt.map
          (IsScalarTower.toAlgHom K R (IsLocalRing.ResidueField R)) s) = z := by
  classical
  set φ := Work.SpecLin.Core.rgMap R W hW s hs with hφ
  set ψ := Work.SpecLin.Alt.chartTensorRedSectionsMap (K:=K) (C:=C) R W hW with hψ
  set hU := Work.CurveBasics.BaseChange.isAffineOpen_bcOpens (IsLocalRing.ResidueField R) W hW
    with hUdef
  set z' : (C.baseChange (IsLocalRing.ResidueField R)).Place := Work.SpecLin.ptPlace
    (Work.SpecLin.RPt.map (IsScalarTower.toAlgHom K R (IsLocalRing.ResidueField R)) s)
    with hz'
  have hmem : Work.SpecLin.ptToPoint
      (Work.SpecLin.RPt.map (IsScalarTower.toAlgHom K R (IsLocalRing.ResidueField R)) s)
      ∈ C.bcOpens (IsLocalRing.ResidueField R) W :=
    Work.SpecLin.Alt.ptToPoint_closedPt_mem R W s hs
  have hψsurj : Function.Surjective ψ := by
    rw [hψ]; exact chartTensorRedSectionsMap_surjective R W hW
  have hkerψ : RingHom.ker ψ = Work.SpecLin.Core.chartFibrePrime (K:=K) (C:=C) R W := by
    rw [hψ]; exact ker_chartTensorRedSectionsMap R W hW
  have hker_le_N : RingHom.ker ψ ≤ N := by rw [hkerψ]; exact hPN
  have hker_le_N' : RingHom.ker ψ ≤
      (Work.SpecLin.Core.sectionPrime (K:=K) (C:=C) R W φ ⊔
        Work.SpecLin.Core.chartFibrePrime (K:=K) (C:=C) R W) := by
    rw [hkerψ]; exact le_sup_right
  have hcrux : Ideal.map ψ (Work.SpecLin.Core.sectionPrime (K:=K) (C:=C) R W φ ⊔
        Work.SpecLin.Core.chartFibrePrime (K:=K) (C:=C) R W)
      = (hU.primeIdealOf ⟨Work.SpecLin.ptToPoint
          (Work.SpecLin.RPt.map (IsScalarTower.toAlgHom K R (IsLocalRing.ResidueField R)) s),
          hmem⟩).asIdeal := by
    rw [hψ, hφ, hUdef]
    exact sectionPrime_sup_chartFibrePrime_map_eq_primeIdealOf R W hW s hs
  have hα : ∀ x : (C.baseChange (IsLocalRing.ResidueField R)).functionField,
      (∃ a b : Work.SpecLin.Core.chartTensor (K:=K) (C:=C) R W,
          b ∉ Work.SpecLin.Core.sectionPrime (K:=K) (C:=C) R W φ ⊔
              Work.SpecLin.Core.chartFibrePrime (K:=K) (C:=C) R W ∧
          x * Work.SpecLin.Alt.chartTensorRedMap R W hW b
            = Work.SpecLin.Alt.chartTensorRedMap R W hW a)
        ↔ 0 ≤ (C.baseChange (IsLocalRing.ResidueField R)).ordAt x z' := by
    intro x
    rw [Work.SpecLin.Alt.image_fractionSet_map_of_surjective (φ := ψ) hψsurj
      _ hker_le_N' (f := Work.SpecLin.Alt.chartTensorRedMap R W hW)
      (f' := algebraMap (Work.SpecLin.Alt.fibreSections (K:=K) (C:=C) R W) ↑(C.baseChange (IsLocalRing.ResidueField R)).functionField)
      (fun a => rfl) x]
    rw [hcrux]
    exact (Work.SpecLin.Alt.exists_mul_eq_iff_ordAt_of_primeIdealOf
      (C := C.baseChange (IsLocalRing.ResidueField R))
      (C.bcOpens (IsLocalRing.ResidueField R) W) hU z' hmem x)
  have hβ : (∀ x : (C.baseChange (IsLocalRing.ResidueField R)).functionField,
        (∃ a b : Work.SpecLin.Core.chartTensor (K:=K) (C:=C) R W, b ∉ N ∧
            x * Work.SpecLin.Alt.chartTensorRedMap R W hW b
              = Work.SpecLin.Alt.chartTensorRedMap R W hW a)
          ↔ (∃ a b : Work.SpecLin.Core.chartTensor (K:=K) (C:=C) R W,
              b ∉ Work.SpecLin.Core.sectionPrime (K:=K) (C:=C) R W φ ⊔
                  Work.SpecLin.Core.chartFibrePrime (K:=K) (C:=C) R W ∧
              x * Work.SpecLin.Alt.chartTensorRedMap R W hW b
                = Work.SpecLin.Alt.chartTensorRedMap R W hW a)) →
      Work.SpecLin.Core.sectionPrime (K:=K) (C:=C) R W φ ⊔
        Work.SpecLin.Core.chartFibrePrime (K:=K) (C:=C) R W = N := by
    intro hV
    have hW' : ∀ x : (C.baseChange (IsLocalRing.ResidueField R)).functionField,
        (∃ a b : (Work.SpecLin.Alt.fibreSections (K:=K) (C:=C) R W), b ∉ Ideal.map ψ N ∧ x * algebraMap (Work.SpecLin.Alt.fibreSections (K:=K) (C:=C) R W)
            ↑(C.baseChange (IsLocalRing.ResidueField R)).functionField b
          = algebraMap (Work.SpecLin.Alt.fibreSections (K:=K) (C:=C) R W) ↑(C.baseChange (IsLocalRing.ResidueField R)).functionField a)
        ↔ (∃ a b : (Work.SpecLin.Alt.fibreSections (K:=K) (C:=C) R W), b ∉ Ideal.map ψ (Work.SpecLin.Core.sectionPrime (K:=K) (C:=C) R W φ ⊔
              Work.SpecLin.Core.chartFibrePrime (K:=K) (C:=C) R W) ∧
            x * algebraMap (Work.SpecLin.Alt.fibreSections (K:=K) (C:=C) R W)
              ↑(C.baseChange (IsLocalRing.ResidueField R)).functionField b
          = algebraMap (Work.SpecLin.Alt.fibreSections (K:=K) (C:=C) R W) ↑(C.baseChange (IsLocalRing.ResidueField R)).functionField a) := by
      intro x
      exact (Work.SpecLin.Alt.image_fractionSet_map_of_surjective (φ := ψ) hψsurj N hker_le_N
            (f := Work.SpecLin.Alt.chartTensorRedMap R W hW)
            (f' := algebraMap (Work.SpecLin.Alt.fibreSections (K:=K) (C:=C) R W) ↑(C.baseChange (IsLocalRing.ResidueField R)).functionField)
            (fun a => rfl) x).symm.trans
          ((hV x).trans
            (Work.SpecLin.Alt.image_fractionSet_map_of_surjective (φ := ψ) hψsurj _ hker_le_N'
              (f := Work.SpecLin.Alt.chartTensorRedMap R W hW)
              (f' := algebraMap (Work.SpecLin.Alt.fibreSections (K:=K) (C:=C) R W) ↑(C.baseChange (IsLocalRing.ResidueField R)).functionField)
              (fun a => rfl) x))
    haveI : IsFractionRing (Work.SpecLin.Alt.fibreSections (K:=K) (C:=C) R W) ↑(C.baseChange (IsLocalRing.ResidueField R)).functionField :=
      AlgebraicGeometry.functionField_isFractionRing_of_isAffineOpen
        (C.baseChange (IsLocalRing.ResidueField R)).left
        (C.bcOpens (IsLocalRing.ResidueField R) W) hU
    have hmap : Ideal.map ψ N = Ideal.map ψ (Work.SpecLin.Core.sectionPrime (K:=K) (C:=C) R W φ ⊔
        Work.SpecLin.Core.chartFibrePrime (K:=K) (C:=C) R W) :=
      Work.SpecLin.Alt.recover_prime_of_exists_mul_eq
        (algebraMap (Work.SpecLin.Alt.fibreSections (K:=K) (C:=C) R W) ↑(C.baseChange (IsLocalRing.ResidueField R)).functionField)
        (IsFractionRing.injective _ _) hW'
    have h2 := congrArg (Ideal.comap ψ) hmap
    rw [Ideal.comap_map_of_surjective ψ hψsurj N,
      Ideal.comap_map_of_surjective ψ hψsurj
        (Work.SpecLin.Core.sectionPrime (K:=K) (C:=C) R W φ ⊔
          Work.SpecLin.Core.chartFibrePrime (K:=K) (C:=C) R W),
      show Ideal.comap ψ ⊥ = RingHom.ker ψ from (RingHom.ker_eq_comap_bot ψ).symm,
      hkerψ] at h2
    rw [sup_eq_left.mpr hPN, sup_eq_left.mpr le_sup_right] at h2
    exact h2.symm
  constructor
  · intro hN
    have hV : ∀ x : (C.baseChange (IsLocalRing.ResidueField R)).functionField,
        (0 ≤ (C.baseChange (IsLocalRing.ResidueField R)).ordAt x z)
          ↔ (0 ≤ (C.baseChange (IsLocalRing.ResidueField R)).ordAt x z') := by
      intro x
      rw [← hz x, ← hα x, ← hN]
    have hsub : z.valuationSubring = z'.valuationSubring := by
      ext x
      rw [Work.CurveBasics.Place.mem_valuationSubring_iff,
        Work.CurveBasics.Place.mem_valuationSubring_iff]
      exact hV x
    exact (Work.CurveBasics.Place.place_eq_of_valuationSubring_eq
      (C.baseChange (IsLocalRing.ResidueField R)) hsub).symm
  · intro hzz
    have hz'z : z' = z := hz'.trans hzz
    have hV : ∀ x : (C.baseChange (IsLocalRing.ResidueField R)).functionField,
        (∃ a b : Work.SpecLin.Core.chartTensor (K:=K) (C:=C) R W, b ∉ N ∧
            x * Work.SpecLin.Alt.chartTensorRedMap R W hW b
              = Work.SpecLin.Alt.chartTensorRedMap R W hW a)
          ↔ (∃ a b : Work.SpecLin.Core.chartTensor (K:=K) (C:=C) R W,
              b ∉ Work.SpecLin.Core.sectionPrime (K:=K) (C:=C) R W φ ⊔
                  Work.SpecLin.Core.chartFibrePrime (K:=K) (C:=C) R W ∧
              x * Work.SpecLin.Alt.chartTensorRedMap R W hW b
                = Work.SpecLin.Alt.chartTensorRedMap R W hW a) := by
      intro x
      rw [hz x,
        show (0 ≤ (C.baseChange (IsLocalRing.ResidueField R)).ordAt x z)
            ↔ (0 ≤ (C.baseChange (IsLocalRing.ResidueField R)).ordAt x z') from by
          rw [hz'z],
        ← hα x]
    exact hβ hV

end Work.SpecLin.Alt
