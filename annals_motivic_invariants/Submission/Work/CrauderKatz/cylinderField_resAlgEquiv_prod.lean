/-
Copyright (c) 2026 The annals_motivic_invariants team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Work.CrauderKatz
-/
import Mathlib
import Submission.Work.CrauderKatz.Defs
import Submission.Work.CrauderKatz.CylinderChart
import Submission.Work.CrauderKatz.isFractionRing_polynomial_ratFunc
import Submission.Work.CrauderKatz.chartHom_algebraMap

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.CrauderKatz.cylinderField_resAlgEquiv_prod` — the cylinder over `C` has function field `κ(C)(t)`

The `𝕜`-linear presentation of the function field of the cylinder `C ×_𝕜 𝔸¹` as `RatFunc κ(C)`,
the second half of the (F1) inputs `resY`, `resX` of `Work.CrauderKatz.CrauderKatzLink`.

The proof proceeds by exhibiting, for an affine chart `Spec Γ(C,U) ⊆ C` of the curve, the canonical
open immersion `Spec Γ(C,U)[t] ⟶ C ×_𝕜 𝔸¹` ("the cylinder chart" `cylinderChart`) whose global
sections are the polynomial ring `Γ(C,U)[t]`; the chart lemma `isFractionRing_functionField_of_chart`
of `Work.CrauderKatz.CylinderChart` then identifies `Γ(C,U)[t]` as a fraction ring of the function
field of the cylinder, `isFractionRing_polynomial_ratFunc` identifies `RatFunc κ(C)` with a fraction
ring of the same ring, and `IsLocalization.algEquiv` produces the `𝕜`-linear isomorphism.  The
`𝕜`-linearity of the chart lemma is `chartHom_algebraMap`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme CategoryTheory.Limits
open scoped Polynomial TensorProduct

namespace Work.CrauderKatz

noncomputable section

variable {𝕜 : Type} [Field 𝕜]

/-- The structure map of an affine chart, in explicit form. -/
theorem chart_structure_eq (X : Work.Arithmetic.GenOneCurve 𝕜) (U : X.C.Opens)
    (hU : IsAffineOpen U) [Nonempty U] :
    hU.fromSpec ≫ (X.C ↘ Spec (CommRingCat.of 𝕜))
      = Spec.map (CommRingCat.ofHom (((Scheme.ΓSpecIso (CommRingCat.of 𝕜)).inv
          ≫ (X.C ↘ Spec (CommRingCat.of 𝕜)).appLE ⊤ U le_top).hom)) := by
  have h := IsAffineOpen.SpecMap_appLE_fromSpec (X.C ↘ Spec (CommRingCat.of 𝕜))
    (isAffineOpen_top (Spec (CommRingCat.of 𝕜))) hU le_top
  rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv] at h
  rw [← h, ← Spec.map_comp]
  exact congrArg Spec.map (CommRingCat.ofHom_hom _).symm

/-- The structure map of an affine chart. -/
theorem exists_chart_structure (X : Work.Arithmetic.GenOneCurve 𝕜) (U : X.C.Opens)
    (hU : IsAffineOpen U) [Nonempty U] :
    ∃ φ : 𝕜 →+* Γ(X.C, U),
      hU.fromSpec ≫ (X.C ↘ Spec (CommRingCat.of 𝕜)) = Spec.map (CommRingCat.ofHom φ) := by
  refine ⟨((Scheme.ΓSpecIso (CommRingCat.of 𝕜)).inv ≫
    (X.C ↘ Spec (CommRingCat.of 𝕜)).appLE ⊤ U le_top).hom, ?_⟩
  have h := IsAffineOpen.SpecMap_appLE_fromSpec (X.C ↘ Spec (CommRingCat.of 𝕜))
    (isAffineOpen_top (Spec (CommRingCat.of 𝕜))) hU le_top
  rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv] at h
  rw [← h, ← Spec.map_comp]
  exact congrArg Spec.map (CommRingCat.ofHom_hom _).symm

/-- **The canonical chart of the cylinder.** -/
theorem cylinderChart (X : Work.Arithmetic.GenOneCurve 𝕜) (U : X.C.Opens) (hU : IsAffineOpen U)
    [Nonempty U] [Algebra 𝕜 Γ(X.C, U)]
    (hφ : hU.fromSpec ≫ (X.C ↘ Spec (CommRingCat.of 𝕜))
      = Spec.map (CommRingCat.ofHom (algebraMap 𝕜 Γ(X.C, U)))) :
    ∃ z : Spec (CommRingCat.of (Polynomial (Γ(X.C, U)))) ⟶
        pullback (X.C ↘ Spec (CommRingCat.of 𝕜))
          (Spec.map (CommRingCat.ofHom (algebraMap 𝕜 (Polynomial 𝕜)))),
      IsOpenImmersion z ∧
      z ≫ (pullback.fst _ _ ≫ (X.C ↘ Spec (CommRingCat.of 𝕜)))
        = Spec.map (CommRingCat.ofHom (algebraMap 𝕜 (Polynomial (Γ(X.C, U))))) := by
  let g : Spec (CommRingCat.of (Polynomial 𝕜)) ⟶ Spec (CommRingCat.of 𝕜) :=
    Spec.map (CommRingCat.ofHom (algebraMap 𝕜 (Polynomial 𝕜)))
  let Q := pullback (Spec.map (CommRingCat.ofHom (algebraMap 𝕜 Γ(X.C, U)))) g
  let e : Polynomial (Γ(X.C, U)) ≃+* (Γ(X.C, U) ⊗[𝕜] Polynomial 𝕜) :=
    (polyEquivTensor' 𝕜 (Γ(X.C, U))).toRingEquiv
  let w : Spec (CommRingCat.of (Polynomial (Γ(X.C, U)))) ≅ Q :=
    (Scheme.Spec.mapIso (RingEquiv.toCommRingCatIso e).op).symm.trans
      (pullbackSpecIso 𝕜 (Γ(X.C, U)) (Polynomial 𝕜)).symm
  let q : Q ⟶ pullback (X.C ↘ Spec (CommRingCat.of 𝕜)) g :=
    pullback.map (Spec.map (CommRingCat.ofHom (algebraMap 𝕜 Γ(X.C, U)))) g
      (X.C ↘ Spec (CommRingCat.of 𝕜)) g
      hU.fromSpec (𝟙 (Spec (CommRingCat.of (Polynomial 𝕜)))) (𝟙 (Spec (CommRingCat.of 𝕜)))
      (by rw [Category.comp_id]; exact hφ.symm) (by simp)
  refine ⟨w.hom ≫ q, IsOpenImmersion.comp _ _, ?_⟩
  have hq1 : q ≫ pullback.fst (X.C ↘ Spec (CommRingCat.of 𝕜)) g
      = pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap 𝕜 Γ(X.C, U)))) g ≫ hU.fromSpec := by
    simp [q, pullback.map, pullback.lift_fst]
  have hw1 : w.hom ≫ pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap 𝕜 Γ(X.C, U)))) g
      = Spec.map (CommRingCat.ofHom (algebraMap (Γ(X.C, U)) (Polynomial (Γ(X.C, U))))) := by
    have h1 : (Scheme.Spec.mapIso (RingEquiv.toCommRingCatIso e).op).inv =
        Spec.map (CommRingCat.ofHom e.symm) := by
      rw [CategoryTheory.Functor.mapIso_inv]; rfl
    have h2 : (pullbackSpecIso 𝕜 (Γ(X.C, U)) (Polynomial 𝕜)).inv
        ≫ pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap 𝕜 Γ(X.C, U)))) g
        = Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom)) :=
      pullbackSpecIso_inv_fst 𝕜 (Γ(X.C, U)) (Polynomial 𝕜)
    have hes : ∀ a : Γ(X.C, U),
        e.symm (Algebra.TensorProduct.includeLeftRingHom a) = Polynomial.C a := by
      intro a
      show (polyEquivTensor' 𝕜 (Γ(X.C, U))).symm
        (Algebra.TensorProduct.includeLeftRingHom a) = Polynomial.C a
      rw [Algebra.TensorProduct.includeLeftRingHom_apply]
      rw [coe_polyEquivTensor'_symm]
      rw [polyEquivTensor_symm_apply_tmul_eq_smul]
      simp [Polynomial.smul_eq_C_mul]
    simp only [w, Iso.trans_hom, Iso.symm_hom, Category.assoc, h1, h2]
    rw [← Spec.map_comp, Spec.map_injective.eq_iff]
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro a
    simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply, CommRingCat.hom_ofHom]
    change e.symm (Algebra.TensorProduct.includeLeftRingHom a)
      = (algebraMap (↑Γ(X.C, U)) (↑Γ(X.C, U))[X]) a
    rw [← Polynomial.C_eq_algebraMap, hes a]
  calc (w.hom ≫ q) ≫ (pullback.fst (X.C ↘ Spec (CommRingCat.of 𝕜)) g ≫ (X.C ↘ Spec (CommRingCat.of 𝕜)))
      = w.hom ≫ (q ≫ pullback.fst (X.C ↘ Spec (CommRingCat.of 𝕜)) g) ≫ (X.C ↘ Spec (CommRingCat.of 𝕜)) := by
        simp only [Category.assoc]
    _ = (w.hom ≫ pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap 𝕜 Γ(X.C, U)))) g)
          ≫ (hU.fromSpec ≫ (X.C ↘ Spec (CommRingCat.of 𝕜))) := by
        rw [hq1]; simp only [Category.assoc]
    _ = Spec.map (CommRingCat.ofHom (algebraMap 𝕜 (Polynomial (Γ(X.C, U))))) := by
        rw [hw1, hφ, ← Spec.map_comp, Spec.map_injective.eq_iff]
        apply CommRingCat.hom_ext
        apply RingHom.ext
        intro c
        simp


/-- The cylinder theorem, given an affine chart `Spec A[X] ⟶ X × 𝔸¹` of the canonical form. -/
theorem cyl_of_chart {𝕜 : Type} [Field 𝕜] {X : Work.Arithmetic.GenOneCurve 𝕜}
    {A : CommRingCat.{0}} [IsDomain ↥A] [Algebra 𝕜 ↥A] {K : Type} [Field K] [Algebra ↥A K]
    [IsFractionRing ↥A K] {W : Scheme.{0}} [IrreducibleSpace W] [IsIntegral W]
    [W.Over (Spec (CommRingCat.of 𝕜))]
    {Z : Scheme.{0}} [IsAffine Z] [Nonempty Z] [IsIntegral Z]
    (eZ : Z ≅ Spec (CommRingCat.of (Polynomial ↥A)))
    (cRes : 𝕜 →+* K) (hcRes : cRes = (algebraMap ↥A K).comp (algebraMap 𝕜 ↥A))
    (e : W ≅ pullback (X.C ↘ Spec (CommRingCat.of 𝕜))
      (Spec.map (CommRingCat.ofHom (algebraMap 𝕜 (Polynomial 𝕜)))))
    (he : e.hom ≫ (pullback.fst (X.C ↘ Spec (CommRingCat.of 𝕜))
        (Spec.map (CommRingCat.ofHom (algebraMap 𝕜 (Polynomial 𝕜)))) ≫ (X.C ↘ Spec (CommRingCat.of 𝕜)))
      = (W ↘ Spec (CommRingCat.of 𝕜)))
    (z : Z ⟶ pullback (X.C ↘ Spec (CommRingCat.of 𝕜))
          (Spec.map (CommRingCat.ofHom (algebraMap 𝕜 (Polynomial 𝕜)))))
    (hz_imm : IsOpenImmersion z)
    (hzπ : z ≫ (pullback.fst (X.C ↘ Spec (CommRingCat.of 𝕜))
        (Spec.map (CommRingCat.ofHom (algebraMap 𝕜 (Polynomial 𝕜)))) ≫ (X.C ↘ Spec (CommRingCat.of 𝕜)))
      = eZ.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap 𝕜 (Polynomial ↥A)))) :
    ∃ e' : (W.functionField : Type) ≃+* RatFunc K,
      e'.toRingHom.comp (Work.CrauderKatz.functionFieldResMap 𝕜 W) =
        (algebraMap K (RatFunc K)).comp cRes := by
  classical
  -- the projection to `Spec 𝕜`
  let P := pullback (X.C ↘ Spec (CommRingCat.of 𝕜))
    (Spec.map (CommRingCat.ofHom (algebraMap 𝕜 (Polynomial 𝕜))))
  let π : P ⟶ Spec (CommRingCat.of 𝕜) := pullback.fst _ _ ≫ (X.C ↘ Spec (CommRingCat.of 𝕜))
  -- the `𝕜`-structure of the chart ring
  let ψ : 𝕜 →+* Γ(Z, ⊤) := ((Scheme.ΓSpecIso (CommRingCat.of 𝕜)).inv ≫ π.appTop ≫ z.appTop).hom
  have hz : z ≫ π = Z.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom ψ) := by
    have h1 : (z ≫ π) ≫ Spec.map (Scheme.ΓSpecIso (CommRingCat.of 𝕜)).hom
        = Z.isoSpec.hom ≫ Spec.map (π.appTop ≫ z.appTop) := by
      rw [SpecMap_ΓSpecIso_hom, Scheme.isoSpec_hom, Scheme.toSpecΓ_naturality,
        Scheme.Hom.comp_appTop, ← Scheme.isoSpec_hom]
    have h2 : Spec.map (Scheme.ΓSpecIso (CommRingCat.of 𝕜)).hom
        ≫ Spec.map (Scheme.ΓSpecIso (CommRingCat.of 𝕜)).inv
        = 𝟙 (Spec (CommRingCat.of 𝕜)) := by
      rw [← Spec.map_comp, Iso.inv_hom_id, Spec.map_id]
    have h3 : z ≫ π = (z ≫ π) ≫ Spec.map (Scheme.ΓSpecIso (CommRingCat.of 𝕜)).hom
        ≫ Spec.map (Scheme.ΓSpecIso (CommRingCat.of 𝕜)).inv := by
      rw [Category.assoc, h2, Category.comp_id]
    rw [h3, ← Category.assoc, h1, Category.assoc, ← Spec.map_comp]
    refine congrArg (fun t => Z.isoSpec.hom ≫ t) ?_
    exact congrArg Spec.map (CommRingCat.ofHom_hom _).symm
  have hψ : ∀ c : 𝕜, ψ c = (eZ.hom).appTop
      ((Scheme.ΓSpecIso (CommRingCat.of (Polynomial ↥A))).inv
        (algebraMap 𝕜 (Polynomial ↥A) c)) := by
    intro c
    have hψm : CommRingCat.ofHom ψ = CommRingCat.ofHom (algebraMap 𝕜 (Polynomial ↥A))
        ≫ (Scheme.ΓSpecIso (CommRingCat.of (Polynomial ↥A))).inv ≫ (eZ.hom).appTop := by
      have h0 : CommRingCat.ofHom ψ
          = (Scheme.ΓSpecIso (CommRingCat.of 𝕜)).inv ≫ π.appTop ≫ z.appTop :=
        CommRingCat.ofHom_hom _
      rw [h0, ← Scheme.Hom.comp_appTop, hzπ, Scheme.Hom.comp_appTop, ← Category.assoc,
        ← Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap 𝕜 (Polynomial ↥A))),
        Category.assoc]
    have h := RingHom.congr_fun (congrArg CommRingCat.Hom.hom hψm) c
    simpa only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.coe_comp,
      Function.comp_apply] using h
  -- the chart of `W`
  let zW : Z ⟶ W := z ≫ e.inv
  have hzW : zW ≫ (W ↘ Spec (CommRingCat.of 𝕜))
      = Z.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom ψ) := by
    have h1 : e.inv ≫ (W ↘ Spec (CommRingCat.of 𝕜)) = π := by
      rw [← he, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
    rw [show zW ≫ (W ↘ Spec (CommRingCat.of 𝕜)) = z ≫ π from by
      rw [show zW = z ≫ e.inv from rfl, Category.assoc, h1]]
    exact hz
  haveI : IsOpenImmersion zW := IsOpenImmersion.comp _ _
  -- `W`'s function field is a fraction ring of the chart ring
  letI : Algebra Γ(Z, ⊤) (W.functionField : Type) := (Work.CrauderKatz.chartHom zW).toAlgebra
  have hFRW : IsFractionRing Γ(Z, ⊤) (W.functionField : Type) :=
    Work.CrauderKatz.isFractionRing_functionField_of_chart zW
  -- the identification of the chart ring with `A[X]`
  let eΓ : Polynomial ↥A ≃+* Γ(Z, ⊤) := RingEquiv.ofBijective
    (((eZ.hom).appTop.hom).comp ((Scheme.ΓSpecIso (CommRingCat.of (Polynomial ↥A))).inv.hom))
    (by
      have hA : ∀ x : ↥Γ(Z, ⊤), (eZ.hom).appTop ((eZ.inv).appTop x) = x := by
        intro x
        have h3 : (eZ.inv).appTop ≫ (eZ.hom).appTop = 𝟙 (Γ(Z, ⊤)) := by
          rw [← Scheme.Hom.comp_appTop (eZ.hom) (eZ.inv), Iso.hom_inv_id]
          rfl
        simpa using congrArg (fun (f : Γ(Z, ⊤) ⟶ Γ(Z, ⊤)) => f.hom x) h3
      have hB : ∀ x : ↥Γ(Spec (CommRingCat.of (Polynomial ↥A)), ⊤),
          (eZ.inv).appTop ((eZ.hom).appTop x) = x := by
        intro x
        have h3 : (eZ.hom).appTop ≫ (eZ.inv).appTop
            = 𝟙 (Γ(Spec (CommRingCat.of (Polynomial ↥A)), ⊤)) := by
          rw [← Scheme.Hom.comp_appTop (eZ.inv) (eZ.hom), Iso.inv_hom_id]
          rfl
        simpa using congrArg
            (fun (f : Γ(Spec (CommRingCat.of (Polynomial ↥A)), ⊤)
                ⟶ Γ(Spec (CommRingCat.of (Polynomial ↥A)), ⊤)) => f.hom x) h3
      refine Function.bijective_iff_has_inverse.mpr
        ⟨((Scheme.ΓSpecIso (CommRingCat.of (Polynomial ↥A))).hom.hom).comp
          ((eZ.inv).appTop.hom), ?_, ?_⟩
      · intro y
        simp only [RingHom.comp_apply]
        rw [hB]
        exact Iso.inv_hom_id_apply _ _
      · intro z
        simp only [RingHom.comp_apply]
        rw [Iso.hom_inv_id_apply, hA])
  -- the `RatFunc K` side
  let ψR : Polynomial ↥A →+* RatFunc K :=
    (algebraMap (Polynomial K) (RatFunc K)).comp (Polynomial.mapRingHom (algebraMap ↥A K))
  letI : Algebra (Polynomial ↥A) (RatFunc K) := ψR.toAlgebra
  have hFRtower : IsFractionRing (Polynomial ↥A) (RatFunc K) :=
    isFractionRing_polynomial_ratFunc (A := ↥A) (K := K) (fun p => by
      rw [RingHom.algebraMap_toAlgebra]; rfl)
  letI : Algebra Γ(Z, ⊤) (RatFunc K) :=
    ((algebraMap (Polynomial ↥A) (RatFunc K)).comp eΓ.symm.toRingHom).toAlgebra
  have hFRK : IsFractionRing Γ(Z, ⊤) (RatFunc K) := by
    refine isLocalization_of_ringEquiv (R := Polynomial ↥A) (R' := Γ(Z, ⊤)) eΓ
      (nonZeroDivisors (Polynomial ↥A)) (nonZeroDivisors Γ(Z, ⊤)) ?_ ?_
    · intro y
      rw [mem_nonZeroDivisors_iff_ne_zero, mem_nonZeroDivisors_iff_ne_zero]
      exact (Iff.not (RingEquiv.map_eq_zero_iff (f := eΓ.symm) (x := y))).symm
    · intro x
      rw [RingHom.algebraMap_toAlgebra, RingHom.comp_apply]
      exact congrArg ψR (eΓ.symm_apply_apply x)
  refine ⟨(IsLocalization.algEquiv (nonZeroDivisors Γ(Z, ⊤))
    (W.functionField : Type) (RatFunc K)).toRingEquiv, ?_⟩
  apply RingHom.ext
  intro c
  have h1 : (algebraMap Γ(Z, ⊤) (W.functionField : Type)) (ψ c)
      = Work.CrauderKatz.functionFieldResMap 𝕜 W c := by
    rw [RingHom.algebraMap_toAlgebra]
    exact Work.CrauderKatz.chartHom_algebraMap zW ψ hzW c
  have hψ' : eΓ.symm.toRingHom (ψ c) = algebraMap 𝕜 (Polynomial ↥A) c := by
    have hΓ : eΓ (algebraMap 𝕜 (Polynomial ↥A) c) = ψ c := by
      rw [RingEquiv.ofBijective_apply, RingHom.comp_apply]
      exact (hψ c).symm
    rw [← hΓ]
    exact RingEquiv.symm_apply_apply eΓ _
  have h2 : (algebraMap Γ(Z, ⊤) (RatFunc K)) (ψ c)
      = (algebraMap K (RatFunc K)).comp cRes c := by
    rw [RingHom.algebraMap_toAlgebra, RingHom.comp_apply, hψ', hcRes]
    show ψR (Polynomial.C (algebraMap 𝕜 ↥A c))
      = algebraMap K (RatFunc K) (algebraMap ↥A K (algebraMap 𝕜 ↥A c))
    simp only [ψR, RingHom.comp_apply]
    rw [Polynomial.coe_mapRingHom, Polynomial.map_C, Polynomial.C_eq_algebraMap,
      ← IsScalarTower.algebraMap_apply K (Polynomial K) (RatFunc K)]
  have key := (IsLocalization.algEquiv
    (nonZeroDivisors Γ(Z, ⊤)) (W.functionField : Type) (RatFunc K)).commutes (ψ c)
  exact (congrArg (fun x => (IsLocalization.algEquiv
    (nonZeroDivisors Γ(Z, ⊤)) (W.functionField : Type) (RatFunc K)).toRingEquiv.toRingHom x)
    h1.symm).trans (key.trans h2)

/-- The main theorem. -/
theorem cylinderField_resAlgEquiv_prod (𝕜 : Type) [Field 𝕜] (X : Work.Arithmetic.GenOneCurve 𝕜)
    (W : AlgebraicGeometry.Scheme.{0}) [IrreducibleSpace W] [AlgebraicGeometry.IsIntegral W]
    [W.Over (AlgebraicGeometry.Spec (CommRingCat.of 𝕜))]
    (e : W ≅ CategoryTheory.Limits.pullback (X.C ↘ AlgebraicGeometry.Spec (CommRingCat.of 𝕜))
      (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap 𝕜 (Polynomial 𝕜)))))
    (he : CategoryTheory.CategoryStruct.comp e.hom (CategoryTheory.CategoryStruct.comp
        (CategoryTheory.Limits.pullback.fst (X.C ↘ AlgebraicGeometry.Spec (CommRingCat.of 𝕜))
          (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap 𝕜 (Polynomial 𝕜)))))
        (X.C ↘ AlgebraicGeometry.Spec (CommRingCat.of 𝕜))) =
      (W ↘ AlgebraicGeometry.Spec (CommRingCat.of 𝕜))) :
    ∃ e' : (AlgebraicGeometry.Scheme.functionField W : Type) ≃+* Work.CrauderKatz.cylinderField 𝕜 X,
      e'.toRingHom.comp (Work.CrauderKatz.functionFieldResMap 𝕜 W) = Work.CrauderKatz.cylResMap 𝕜 X := by
  classical
  obtain ⟨U, hUmem, hxU, -⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.C.isBasis_affineOpens)
    (show genericPoint X.C ∈ (⊤ : X.C.Opens) from trivial)
  haveI hUne : Nonempty U := ⟨⟨genericPoint X.C, hxU⟩⟩
  have hU : IsAffineOpen U := hUmem
  letI : Algebra 𝕜 ↥(Γ(X.C, U)) :=
    (((Scheme.ΓSpecIso (CommRingCat.of 𝕜)).inv ≫ (X.C ↘ Spec (CommRingCat.of 𝕜)).appLE ⊤ U le_top).hom).toAlgebra
  haveI : IsDomain ↥(Γ(X.C, U)) := inferInstance
  have hφ : hU.fromSpec ≫ (X.C ↘ Spec (CommRingCat.of 𝕜))
      = Spec.map (CommRingCat.ofHom (algebraMap 𝕜 ↥(Γ(X.C, U)))) := by
    rw [RingHom.algebraMap_toAlgebra]
    exact chart_structure_eq (𝕜 := 𝕜) X U hU
  obtain ⟨z, hz_imm, hzπ⟩ := cylinderChart X U hU hφ
  haveI hAK : IsFractionRing ↥(Γ(X.C, U)) (Work.CrauderKatz.curveField 𝕜 X) :=
    functionField_isFractionRing_of_isAffineOpen X.C U hU
  have hcRes : Work.CrauderKatz.curveResMap 𝕜 X
      = (algebraMap ↥(Γ(X.C, U)) (Work.CrauderKatz.curveField 𝕜 X)).comp
        (algebraMap 𝕜 ↥(Γ(X.C, U))) := by
    haveI : Nonempty (⊤ : X.C.Opens) := ⟨⟨genericPoint X.C, trivial⟩⟩
    ext c
    rw [RingHom.comp_apply]
    show (X.C.germToFunctionField (⊤ : X.C.Opens))
        ((X.C ↘ Spec (CommRingCat.of 𝕜)).appTop ((Scheme.ΓSpecIso (CommRingCat.of 𝕜)).inv c))
      = (algebraMap ↥(Γ(X.C, U)) (Work.CrauderKatz.curveField 𝕜 X))
        (algebraMap 𝕜 ↥(Γ(X.C, U)) c)
    rw [RingHom.algebraMap_toAlgebra, RingHom.algebraMap_toAlgebra]
    show (X.C.germToFunctionField (⊤ : X.C.Opens))
        ((X.C ↘ Spec (CommRingCat.of 𝕜)).appTop ((Scheme.ΓSpecIso (CommRingCat.of 𝕜)).inv c))
      = (X.C.germToFunctionField U) (X.C.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op
        ((X.C ↘ Spec (CommRingCat.of 𝕜)).appTop ((Scheme.ΓSpecIso (CommRingCat.of 𝕜)).inv c)))
    exact (TopCat.Presheaf.germ_res_apply X.C.presheaf (homOfLE (le_top : U ≤ ⊤))
      (genericPoint X.C) hxU _).symm
  obtain ⟨e', he'⟩ := cyl_of_chart (X := X) (A := Γ(X.C, U))
    (K := Work.CrauderKatz.curveField 𝕜 X) (Z := Spec (CommRingCat.of (Polynomial ↥(Γ(X.C, U)))))
    (Iso.refl _) (Work.CrauderKatz.curveResMap 𝕜 X) hcRes e he z hz_imm (by simpa using hzπ)
  exact ⟨e', he'⟩

end

end Work.CrauderKatz
