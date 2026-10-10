import Mathlib
import Submission.Work.K3Inputs.Defs
import Submission.Work.CrauderKatz.cylinderField_resAlgEquiv_prod

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.K3Inputs.cylFieldAlgEquiv` — the function field of `X ×_𝕜 𝔸¹` for an arbitrary
integral `𝕜`-scheme `X`

`Work.CrauderKatz.cyl_of_chart` and `Work.CrauderKatz.cylinderChart` are stated for the
underlying scheme `X.C` of a genus-one curve `X : GenOneCurve 𝕜`; their proofs use nothing
about `X` except the structure morphism `X.C ↘ Spec 𝕜`.  The two lemmas below,
`cyl_of_chart_gen` and `cylinderChart_gen`, are the verbatim generalisations to an arbitrary
scheme `D` over `Spec 𝕜` (with `[IrreducibleSpace D]` where the genus-one statement gets it from
the `Variety` structure).  The target `cylFieldAlgEquiv` is then the affine-chart argument of
`Work.CrauderKatz.cylinderField_resAlgEquiv_prod` run with `D = X`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme CategoryTheory.Limits
open scoped Polynomial TensorProduct

namespace Work.K3Inputs

noncomputable section

variable {𝕜 : Type} [Field 𝕜]

/-- **The structure map of an affine chart, in explicit form**, for an arbitrary scheme `D`
over `Spec 𝕜`. -/
theorem chart_structure_eq_gen (D : Scheme.{0}) (U : D.Opens)
    (hU : IsAffineOpen U) [Nonempty U] [D.Over (Spec (CommRingCat.of 𝕜))] :
    hU.fromSpec ≫ (D ↘ Spec (CommRingCat.of 𝕜))
      = Spec.map (CommRingCat.ofHom (((Scheme.ΓSpecIso (CommRingCat.of 𝕜)).inv
          ≫ (D ↘ Spec (CommRingCat.of 𝕜)).appLE ⊤ U le_top).hom)) := by
  have h := IsAffineOpen.SpecMap_appLE_fromSpec (D ↘ Spec (CommRingCat.of 𝕜))
    (isAffineOpen_top (Spec (CommRingCat.of 𝕜))) hU le_top
  rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv] at h
  rw [← h, ← Spec.map_comp]
  exact congrArg Spec.map (CommRingCat.ofHom_hom _).symm


/-- **The canonical chart of the cylinder `D ×_𝕜 𝔸¹`**, for an arbitrary scheme `D` over
`Spec 𝕜` and an affine open `U ⊆ D`: the canonical open immersion
`Spec Γ(D,U)[t] ⟶ D ×_𝕜 𝔸¹` compatible with the projections.  Generalisation of
`Work.CrauderKatz.cylinderChart` (`D` arbitrary instead of the underlying scheme of a
genus-one curve). -/
theorem cylinderChart_gen (D : Scheme.{0}) (U : D.Opens) (hU : IsAffineOpen U)
    [D.Over (Spec (CommRingCat.of 𝕜))] [Nonempty U] [Algebra 𝕜 Γ(D, U)]
    (hφ : hU.fromSpec ≫ (D ↘ Spec (CommRingCat.of 𝕜))
      = Spec.map (CommRingCat.ofHom (algebraMap 𝕜 Γ(D, U)))) :
    ∃ z : Spec (CommRingCat.of (Polynomial (Γ(D, U)))) ⟶
        pullback (D ↘ Spec (CommRingCat.of 𝕜))
          (Spec.map (CommRingCat.ofHom (algebraMap 𝕜 (Polynomial 𝕜)))),
      IsOpenImmersion z ∧
      z ≫ (pullback.fst _ _ ≫ (D ↘ Spec (CommRingCat.of 𝕜)))
        = Spec.map (CommRingCat.ofHom (algebraMap 𝕜 (Polynomial (Γ(D, U))))) := by
  let g : Spec (CommRingCat.of (Polynomial 𝕜)) ⟶ Spec (CommRingCat.of 𝕜) :=
    Spec.map (CommRingCat.ofHom (algebraMap 𝕜 (Polynomial 𝕜)))
  let Q := pullback (Spec.map (CommRingCat.ofHom (algebraMap 𝕜 Γ(D, U)))) g
  let e : Polynomial (Γ(D, U)) ≃+* (Γ(D, U) ⊗[𝕜] Polynomial 𝕜) :=
    (polyEquivTensor' 𝕜 (Γ(D, U))).toRingEquiv
  let w : Spec (CommRingCat.of (Polynomial (Γ(D, U)))) ≅ Q :=
    (Scheme.Spec.mapIso (RingEquiv.toCommRingCatIso e).op).symm.trans
      (pullbackSpecIso 𝕜 (Γ(D, U)) (Polynomial 𝕜)).symm
  let q : Q ⟶ pullback (D ↘ Spec (CommRingCat.of 𝕜)) g :=
    pullback.map (Spec.map (CommRingCat.ofHom (algebraMap 𝕜 Γ(D, U)))) g
      (D ↘ Spec (CommRingCat.of 𝕜)) g
      hU.fromSpec (𝟙 (Spec (CommRingCat.of (Polynomial 𝕜)))) (𝟙 (Spec (CommRingCat.of 𝕜)))
      (by rw [Category.comp_id]; exact hφ.symm) (by simp)
  refine ⟨w.hom ≫ q, IsOpenImmersion.comp _ _, ?_⟩
  have hq1 : q ≫ pullback.fst (D ↘ Spec (CommRingCat.of 𝕜)) g
      = pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap 𝕜 Γ(D, U)))) g ≫ hU.fromSpec := by
    simp [q, pullback.map, pullback.lift_fst]
  have hw1 : w.hom ≫ pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap 𝕜 Γ(D, U)))) g
      = Spec.map (CommRingCat.ofHom (algebraMap (Γ(D, U)) (Polynomial (Γ(D, U))))) := by
    have h1 : (Scheme.Spec.mapIso (RingEquiv.toCommRingCatIso e).op).inv =
        Spec.map (CommRingCat.ofHom e.symm) := by
      rw [CategoryTheory.Functor.mapIso_inv]; rfl
    have h2 : (pullbackSpecIso 𝕜 (Γ(D, U)) (Polynomial 𝕜)).inv
        ≫ pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap 𝕜 Γ(D, U)))) g
        = Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom)) :=
      pullbackSpecIso_inv_fst 𝕜 (Γ(D, U)) (Polynomial 𝕜)
    have hes : ∀ a : Γ(D, U),
        e.symm (Algebra.TensorProduct.includeLeftRingHom a) = Polynomial.C a := by
      intro a
      show (polyEquivTensor' 𝕜 (Γ(D, U))).symm
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
      = (algebraMap (↑Γ(D, U)) (↑Γ(D, U))[X]) a
    rw [← Polynomial.C_eq_algebraMap, hes a]
  calc (w.hom ≫ q) ≫ (pullback.fst (D ↘ Spec (CommRingCat.of 𝕜)) g ≫ (D ↘ Spec (CommRingCat.of 𝕜)))
      = w.hom ≫ (q ≫ pullback.fst (D ↘ Spec (CommRingCat.of 𝕜)) g) ≫ (D ↘ Spec (CommRingCat.of 𝕜)) := by
        simp only [Category.assoc]
    _ = (w.hom ≫ pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap 𝕜 Γ(D, U)))) g)
          ≫ (hU.fromSpec ≫ (D ↘ Spec (CommRingCat.of 𝕜))) := by
        rw [hq1]; simp only [Category.assoc]
    _ = Spec.map (CommRingCat.ofHom (algebraMap 𝕜 (Polynomial (Γ(D, U))))) := by
        rw [hw1, hφ, ← Spec.map_comp, Spec.map_injective.eq_iff]
        apply CommRingCat.hom_ext
        apply RingHom.ext
        intro c
        simp


/-- **The cylinder field theorem, given an affine chart `Spec A[t] ⟶ D ×_𝕜 𝔸¹`** of the
canonical form, for an arbitrary scheme `D` over `Spec 𝕜`.  Generalisation of
`Work.CrauderKatz.cyl_of_chart` (`D` arbitrary instead of the underlying scheme of a
genus-one curve). -/
theorem cyl_of_chart_gen {𝕜 : Type} [Field 𝕜] {D : Scheme.{0}}
    [IrreducibleSpace D] [D.Over (Spec (CommRingCat.of 𝕜))]
    {A : CommRingCat.{0}} [IsDomain ↥A] [Algebra 𝕜 ↥A] {K : Type} [Field K] [Algebra ↥A K]
    [IsFractionRing ↥A K] {W : Scheme.{0}} [IrreducibleSpace W] [IsIntegral W]
    [W.Over (Spec (CommRingCat.of 𝕜))]
    {Z : Scheme.{0}} [IsAffine Z] [Nonempty Z] [IsIntegral Z]
    (eZ : Z ≅ Spec (CommRingCat.of (Polynomial ↥A)))
    (cRes : 𝕜 →+* K) (hcRes : cRes = (algebraMap ↥A K).comp (algebraMap 𝕜 ↥A))
    (e : W ≅ pullback (D ↘ Spec (CommRingCat.of 𝕜))
      (Spec.map (CommRingCat.ofHom (algebraMap 𝕜 (Polynomial 𝕜)))))
    (he : e.hom ≫ (pullback.fst (D ↘ Spec (CommRingCat.of 𝕜))
        (Spec.map (CommRingCat.ofHom (algebraMap 𝕜 (Polynomial 𝕜)))) ≫ (D ↘ Spec (CommRingCat.of 𝕜)))
      = (W ↘ Spec (CommRingCat.of 𝕜)))
    (z : Z ⟶ pullback (D ↘ Spec (CommRingCat.of 𝕜))
          (Spec.map (CommRingCat.ofHom (algebraMap 𝕜 (Polynomial 𝕜)))))
    (hz_imm : IsOpenImmersion z)
    (hzπ : z ≫ (pullback.fst (D ↘ Spec (CommRingCat.of 𝕜))
        (Spec.map (CommRingCat.ofHom (algebraMap 𝕜 (Polynomial 𝕜)))) ≫ (D ↘ Spec (CommRingCat.of 𝕜)))
      = eZ.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap 𝕜 (Polynomial ↥A)))) :
    ∃ e' : (W.functionField : Type) ≃+* RatFunc K,
      e'.toRingHom.comp (Work.CrauderKatz.functionFieldResMap 𝕜 W) =
        (algebraMap K (RatFunc K)).comp cRes := by
  classical
  -- the projection to `Spec 𝕜`
  let P := pullback (D ↘ Spec (CommRingCat.of 𝕜))
    (Spec.map (CommRingCat.ofHom (algebraMap 𝕜 (Polynomial 𝕜))))
  let π : P ⟶ Spec (CommRingCat.of 𝕜) := pullback.fst _ _ ≫ (D ↘ Spec (CommRingCat.of 𝕜))
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
    Work.CrauderKatz.isFractionRing_polynomial_ratFunc (A := ↥A) (K := K) (fun p => by
      rw [RingHom.algebraMap_toAlgebra]; rfl)
  letI : Algebra Γ(Z, ⊤) (RatFunc K) :=
    ((algebraMap (Polynomial ↥A) (RatFunc K)).comp eΓ.symm.toRingHom).toAlgebra
  have hFRK : IsFractionRing Γ(Z, ⊤) (RatFunc K) := by
    refine Work.CrauderKatz.isLocalization_of_ringEquiv (R := Polynomial ↥A) (R' := Γ(Z, ⊤)) eΓ
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


/-- **The function field of the cylinder `X ×_𝕜 𝔸¹` is `κ(X)(t)`, `𝕜`-linearly, for an arbitrary integral `𝕜`-scheme `X`** (the genus-one case being `Work.CrauderKatz.cylinderField_resAlgEquiv_prod`).

`W` is any model of the cylinder `X ×_{Spec 𝕜} Spec 𝕜[t]` — an integral `𝕜`-scheme together with an isomorphism `e` to the fibre product that is compatible with the projections (`he`).  The conclusion says that `κ(W) ≅ RatFunc κ(X)` compatibly with the two structure maps `𝕜 → κ(W)` and `Work.K3Inputs.cylResMap 𝕜 X = 𝕜 → κ(X) → RatFunc κ(X)`.

This is exactly `Work.CrauderKatz.cylinderField_resAlgEquiv_prod` with the genus-one curve `X.C` replaced by an arbitrary integral `𝕜`-scheme `X` (and `curveField 𝕜 X`/`curveResMap 𝕜 X` by `X.functionField`/`functionFieldResMap 𝕜 X`).  Suggested route: copy `Work.CrauderKatz.cyl_of_chart` (its `X.C` is used only through `X.C ↘ Spec 𝕜`) and re-run the affine-chart argument of `Work.CrauderKatz.cylinderField_resAlgEquiv_prod`: pick a nonempty affine open `U ⊆ X` (`AlgebraicGeometry.Scheme.isBasis_affineOpens`), use `IsFractionRing Γ(X,U) κ(X)` (`functionField_isFractionRing_of_isAffineOpen`) and `functionFieldResMap 𝕜 X = (algebraMap Γ(X,U) κ(X)).comp (algebraMap 𝕜 Γ(X,U))` (the `hcRes` computation transfers verbatim).  Nothing about `X` beyond integrality and integrality of `W` is needed. -/
theorem cylFieldAlgEquiv (𝕜 : Type) [Field 𝕜] (X W : AlgebraicGeometry.Scheme)
    [AlgebraicGeometry.IsIntegral X]
    [AlgebraicGeometry.Scheme.Over X (AlgebraicGeometry.Spec (CommRingCat.of 𝕜))]
    [AlgebraicGeometry.IsIntegral W]
    [AlgebraicGeometry.Scheme.Over W (AlgebraicGeometry.Spec (CommRingCat.of 𝕜))]
    (e : CategoryTheory.Iso W (CategoryTheory.Limits.pullback
        (CategoryTheory.over X (AlgebraicGeometry.Spec (CommRingCat.of 𝕜)))
        (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap 𝕜 (Polynomial 𝕜))))))
    (he : CategoryTheory.CategoryStruct.comp e.hom (CategoryTheory.CategoryStruct.comp
        (CategoryTheory.Limits.pullback.fst
          (CategoryTheory.over X (AlgebraicGeometry.Spec (CommRingCat.of 𝕜)))
          (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap 𝕜 (Polynomial 𝕜)))))
        (CategoryTheory.over X (AlgebraicGeometry.Spec (CommRingCat.of 𝕜)))) =
      CategoryTheory.over W (AlgebraicGeometry.Spec (CommRingCat.of 𝕜))) :
    ∃ e' : (W.functionField : Type) ≃+* RatFunc (Work.K3Inputs.funField X),
      e'.toRingHom.comp (Work.CrauderKatz.functionFieldResMap 𝕜 W) =
        Work.K3Inputs.cylResMap 𝕜 X := by
  classical
  obtain ⟨U, hUmem, hxU, -⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens)
    (show genericPoint X ∈ (⊤ : X.Opens) from trivial)
  haveI hUne : Nonempty U := ⟨⟨genericPoint X, hxU⟩⟩
  have hU : IsAffineOpen U := hUmem
  letI : Algebra 𝕜 ↥(Γ(X, U)) :=
    (((Scheme.ΓSpecIso (CommRingCat.of 𝕜)).inv ≫
      (X ↘ Spec (CommRingCat.of 𝕜)).appLE ⊤ U le_top).hom).toAlgebra
  haveI : IsDomain ↥(Γ(X, U)) := inferInstance
  have hφ : hU.fromSpec ≫ (X ↘ Spec (CommRingCat.of 𝕜))
      = Spec.map (CommRingCat.ofHom (algebraMap 𝕜 ↥(Γ(X, U)))) := by
    rw [RingHom.algebraMap_toAlgebra]
    exact chart_structure_eq_gen (𝕜 := 𝕜) X U hU
  obtain ⟨z, hz_imm, hzπ⟩ := cylinderChart_gen X U hU hφ
  haveI hAK : IsFractionRing ↥(Γ(X, U)) (X.functionField : Type) :=
    functionField_isFractionRing_of_isAffineOpen X U hU
  have hcRes : Work.CrauderKatz.functionFieldResMap 𝕜 X
      = (algebraMap ↥(Γ(X, U)) (X.functionField : Type)).comp (algebraMap 𝕜 ↥(Γ(X, U))) := by
    haveI : Nonempty (⊤ : X.Opens) := ⟨⟨genericPoint X, trivial⟩⟩
    ext c
    rw [RingHom.comp_apply]
    show (X.germToFunctionField (⊤ : X.Opens))
        ((X ↘ Spec (CommRingCat.of 𝕜)).appTop ((Scheme.ΓSpecIso (CommRingCat.of 𝕜)).inv c))
      = (algebraMap ↥(Γ(X, U)) (X.functionField : Type))
        (algebraMap 𝕜 ↥(Γ(X, U)) c)
    rw [RingHom.algebraMap_toAlgebra, RingHom.algebraMap_toAlgebra]
    show (X.germToFunctionField (⊤ : X.Opens))
        ((X ↘ Spec (CommRingCat.of 𝕜)).appTop ((Scheme.ΓSpecIso (CommRingCat.of 𝕜)).inv c))
      = (X.germToFunctionField U) (X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op
        ((X ↘ Spec (CommRingCat.of 𝕜)).appTop ((Scheme.ΓSpecIso (CommRingCat.of 𝕜)).inv c)))
    exact (TopCat.Presheaf.germ_res_apply X.presheaf (homOfLE (le_top : U ≤ ⊤))
      (genericPoint X) hxU _).symm
  obtain ⟨e', he'⟩ := cyl_of_chart_gen (D := X) (A := Γ(X, U))
    (K := (X.functionField : Type)) (Z := Spec (CommRingCat.of (Polynomial ↥(Γ(X, U)))))
    (Iso.refl _) (Work.CrauderKatz.functionFieldResMap 𝕜 X) hcRes e he z hz_imm
    (by simpa using hzπ)
  exact ⟨e', he'⟩

end

end Work.K3Inputs
