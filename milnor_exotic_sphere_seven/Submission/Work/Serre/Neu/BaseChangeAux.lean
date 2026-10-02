-- PORTED COPY (neutral island) of `Submission/Work/Serre/BaseChangeAux.lean`.
-- The only changes are: the imports of ratShuffle-island modules are redirected to the
-- copies in `Submission/Work/Serre/Neu/`, and the abbrev `singSSet` is renamed to
-- `singSSetN` (same body) so that this module can coexist with `Work.Serre.E0Defs`,
-- which declares the same name.  Declarations and proofs are unchanged.
import Mathlib
import Submission.Work.Serre.Neu.Defs
import Submission.Work.Serre.ezMap_ezBilR
import Submission.Work.StemsB.RatBaseNaturality
import Submission.Work.KunnethEZ.ezChain_isCycle

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The coefficient change `ℤ → ℚ` on the singular chains, and the comparison `Φ` on generators

This file collects the elementary computation rules for the comparison isomorphism

`Work.StemsB.RatBC.Phi X : C_*(X;ℤ) ⊗[ℤ] ℚ ≅ C_*(X;ℚ)`

on a *generator* of the simplicial chain complex, and its extension to all chains via the
canonical cast `bcCast`.

* `eqToHom_h1_f_id`, `eqToHom_h1_f_apply` — the transport `eqToHom (h1 X)` occurring in `Φ` is the
  identity (the source and target objects are the same, up to unfolding);
* `Psi_gen` — the "reassociation" factor `Ψ` sends `1 ⊗ ι_σ 1` to `ι_σ (1 ⊗ 1)`;
* `coeffIso_gen` — the coefficient factor `coeffIso` sends `ι_σ (1 ⊗ 1)` to `ι_σ 1`;
* `Phi_gen` — **the comparison fixes the generators**: `Φ (1 ⊗ ι_σ 1) = ι_σ 1`;
* `bcCast` — the canonical `ℤ`-linear map `C_*(X;ℤ) → C_*(X;ℚ)` (the identity on the generators),
  with `bcCast_ι`, `bcCast_ι_mor` and the coproduct extensionality `bcCast_ext`;
* `Phi_unit_bcCast` — `Φ (1 ⊗ x) = bcCast x` for every chain `x`.
-/

open CategoryTheory AlgebraicTopology Simplicial Limits MonoidalCategory
open scoped Simplicial TensorProduct

set_option maxHeartbeats 1600000
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Work.Serre

noncomputable section

/-- The product of two simplicial sets, written without the scoped `⊗` notation. -/
abbrev ssProd (X Y : SSet) : SSet := X ⊗ Y

/-- `ℤ` as a module, in the form used by `SSet.chainComplex`. -/
abbrev zcZ : ModuleCat ℤ := ModuleCat.of ℤ ℤ

/-- `ℚ` as a module, in the form used by `SSet.chainComplex`. -/
abbrev zcQ : ModuleCat ℚ := ModuleCat.of ℚ ℚ

/-! ## The transport in `Φ` is the identity -/

/-- The degree-`n` component of the transport `eqToHom (h1 X)` occurring in the definition of `Φ`
is the identity (the two objects are the same chain module, up to unfolding `ChZ`). -/
lemma eqToHom_h1_f_id (X : SSet) (n : ℕ) :
    (HomologicalComplex.Hom.f (eqToHom (Work.StemsB.RatBC.h1 X)) n)
      = 𝟙 ((Work.StemsB.RatBC.FC X).X n) := by
  rw [HomologicalComplex.eqToHom_f]
  have h : congr_fun (congr_arg HomologicalComplex.X (Work.StemsB.RatBC.h1 X)) n
      = (rfl : (Work.StemsB.RatBC.FC X).X n = (Work.StemsB.RatBC.FC X).X n) :=
    Subsingleton.elim _ _
  rw [h, CategoryTheory.eqToHom_refl]

/-- The elementwise form of `eqToHom_h1_f_id`. -/
lemma eqToHom_h1_f_apply (X : SSet) (n : ℕ) (z : (Work.StemsB.RatBC.FC X).X n) :
    (eqToHom (Work.StemsB.RatBC.h1 X)).f n z = z := by
  rw [eqToHom_h1_f_id X n]
  rfl

/-! ## The two factors of `Φ` on generators -/

/-- The component of `sigmaConstObjCompIso` is the canonical isomorphism of coproducts. -/
lemma sigmaConstObjCompIso_hom_app (F : ModuleCat ℤ ⥤ ModuleCat ℚ)
    [∀ (T : Type), PreservesColimitsOfShape (Discrete T) F] (R : ModuleCat ℤ) (T : Type) :
    (Work.StemsB.SphRat.sigmaConstObjCompIso F R).hom.app T
      = (PreservesCoproduct.iso F (fun _ : T => R)).hom := rfl

/-- The canonical isomorphism of coproducts is the inverse of `sigmaComparison`. -/
lemma preservesCoproduct_iso_hom_eq_inv (F : ModuleCat ℤ ⥤ ModuleCat ℚ)
    [∀ (T : Type), PreservesColimitsOfShape (Discrete T) F] (R : ModuleCat ℤ) (T : Type) :
    (PreservesCoproduct.iso F (fun _ : T => R)).hom
      = inv (sigmaComparison F (fun _ : T => R)) := by
  have h2 : inv (sigmaComparison F (fun _ : T => R))
      = (PreservesCoproduct.iso F (fun _ : T => R)).hom := by
    refine IsIso.inv_eq_of_hom_inv_id ?_
    rw [← PreservesCoproduct.inv_hom, Iso.inv_hom_id]
  exact h2.symm

/-- The "reassociation" factor `Ψ` of the comparison sends the generator `1 ⊗ ι_σ 1` to
`ι_σ (1 ⊗ 1)`. -/
lemma Psi_gen (X : SSet) (n : ℕ) (σ : X _⦋n⦌) :
    (HomologicalComplex.Hom.f (Work.StemsB.RatBC.Ψ X) n).hom
        (TensorProduct.tmul ℤ (1 : ℚ) ((X.ιChainComplex (R := zcZ) σ).hom 1))
      = (X.ιChainComplex (R := Work.StemsB.RatBC.IntRat.obj zcZ) σ).hom
          (TensorProduct.tmul ℤ (1 : ℚ) (1 : ℤ)) := by
  rw [Work.StemsB.RatBC.Ψ, AlgebraicTopology.alternatingFaceMapComplex_map_f,
      Work.StemsB.RatBC.β_hom, Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
      sigmaConstObjCompIso_hom_app, preservesCoproduct_iso_hom_eq_inv]
  rw [← ModuleCat.ExtendScalars.map_tmul (f := Int.castRingHom ℚ)
        (g := X.ιChainComplex (R := zcZ) σ)]
  exact congrArg (fun φ => φ.hom (TensorProduct.tmul ℤ (1 : ℚ) (1 : ℤ)))
    (map_ι_comp_inv_sigmaComparison Work.StemsB.RatBC.IntRat
      (fun _ : X.obj (Opposite.op ⦋n⦌) => zcZ) σ)

/-- The component of `sigmaConst.mapIso` is the map induced on coproducts. -/
lemma sigmaConst_mapIso_hom_app (e : (Work.StemsB.RatBC.IntRat.obj zcZ) ≅ zcQ) (S : Type) :
    (Limits.sigmaConst.mapIso e).hom.app S = Limits.Sigma.map (fun _ : S => e.hom) := by
  rw [Functor.mapIso_hom]
  rfl

/-- The coefficient isomorphism `ℤ ⊗[ℤ] ℚ ≅ ℚ` sends `1 ⊗ 1` to `1`. -/
lemma extendScalarsIntRatIso_tmul_one :
    Work.StemsB.SphRat.extendScalarsIntRatIso.hom
        (TensorProduct.tmul ℤ (1 : ℚ) (1 : ℤ)) = 1 := by
  change TensorProduct.rid ℤ ℚ (TensorProduct.tmul ℤ (1 : ℚ) (1 : ℤ)) = 1
  rw [TensorProduct.rid_tmul]
  simp

/-- The coefficient factor `coeffIso` of the comparison sends `ι_σ (1 ⊗ 1)` to `ι_σ 1`. -/
lemma coeffIso_gen (X : SSet) (n : ℕ) (σ : X _⦋n⦌) :
    (HomologicalComplex.Hom.f (Work.StemsB.RatBC.coeffIso X).hom n).hom
        ((X.ιChainComplex (R := Work.StemsB.RatBC.IntRat.obj zcZ) σ).hom
          (TensorProduct.tmul ℤ (1 : ℚ) (1 : ℤ)))
      = (X.ιChainComplex (R := zcQ) σ).hom 1 := by
  rw [Work.StemsB.RatBC.coeffIso_hom, AlgebraicTopology.alternatingFaceMapComplex_map_f,
      Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, sigmaConst_mapIso_hom_app]
  have h := congrArg (fun φ => φ.hom (TensorProduct.tmul ℤ (1 : ℚ) (1 : ℤ)))
      (Sigma.ι_map (fun _ : X.obj (Opposite.op ⦋n⦌) =>
        Work.StemsB.SphRat.extendScalarsIntRatIso.hom) σ)
  rw [ModuleCat.hom_comp, LinearMap.comp_apply] at h
  rw [ModuleCat.hom_comp, LinearMap.comp_apply] at h
  rw [extendScalarsIntRatIso_tmul_one] at h
  exact h

/-- **The comparison `Φ` fixes the generators**: `Φ (1 ⊗ ι_σ 1) = ι_σ 1`. -/
lemma Phi_gen (X : SSet) (n : ℕ) (σ : X _⦋n⦌) :
    (HomologicalComplex.Hom.f (Work.StemsB.RatBC.Phi X).hom n).hom
        (TensorProduct.tmul ℤ (1 : ℚ) ((X.ιChainComplex (R := zcZ) σ).hom 1))
      = (X.ιChainComplex (R := zcQ) σ).hom 1 := by
  rw [Work.StemsB.RatBC.Phi_hom, HomologicalComplex.comp_f, ModuleCat.hom_comp,
      LinearMap.comp_apply]
  rw [Work.StemsB.RatBC.rawIso_hom, HomologicalComplex.comp_f, ModuleCat.hom_comp,
      LinearMap.comp_apply]
  rw [eqToHom_h1_f_apply X n]
  rw [Psi_gen X n σ, coeffIso_gen X n σ]

/-! ## The canonical cast `C_*(X;ℤ) → C_*(X;ℚ)` -/

/-- **The coefficient change `ℤ → ℚ` on the simplicial chains**: the identity on the generators. -/
noncomputable def bcCast (X : SSet) (n : ℕ) :
    (X.chainComplex zcZ).X n ⟶ ModuleCat.of ℤ (↥((X.chainComplex zcQ).X n)) :=
  Cofan.IsColimit.desc (X.isColimitChainComplexXCofan zcZ n)
    (fun x => ModuleCat.ofHom (LinearMap.toSpanSingleton ℤ _
      ((X.ιChainComplex (R := zcQ) x).hom (1 : ℚ))))

/-- The defining property of `bcCast` on the generators. -/
lemma bcCast_ι_mor (X : SSet) (n : ℕ) (x : X _⦋n⦌) :
    X.ιChainComplex (R := zcZ) x ≫ bcCast X n
      = ModuleCat.ofHom (LinearMap.toSpanSingleton ℤ _
          ((X.ιChainComplex (R := zcQ) x).hom (1 : ℚ))) :=
  Cofan.IsColimit.fac (X.isColimitChainComplexXCofan zcZ n) _ x

/-- The value of `bcCast` on a generator. -/
lemma bcCast_ι (X : SSet) (n : ℕ) (x : X _⦋n⦌) :
    (bcCast X n).hom ((X.ιChainComplex (R := zcZ) x).hom (1 : ℤ))
      = (X.ιChainComplex (R := zcQ) x).hom (1 : ℚ) := by
  have h := congrArg (fun (f : zcZ ⟶ ModuleCat.of ℤ
      (↥((X.chainComplex zcQ).X n))) => f.hom (1 : ℤ)) (bcCast_ι_mor X n x)
  simpa using h

/-- Two morphisms out of the `n`-chains of a simplicial set agree when they agree on generators. -/
lemma bcCast_ext (X : SSet) (n : ℕ) {T : ModuleCat ℤ} (f g : (X.chainComplex zcZ).X n ⟶ T)
    (h : ∀ x : X _⦋n⦌, X.ιChainComplex (R := zcZ) x ≫ f = X.ιChainComplex (R := zcZ) x ≫ g) :
    f = g :=
  (X.isColimitChainComplexXCofan zcZ n).hom_ext (fun _ => h _)

/-! ## The comparison on an arbitrary chain -/

/-- `ℚ` as a `ℤ`-module (in the spelling of `ModuleCat.extendScalars`). -/
abbrev ratAsZ : ModuleCat ℤ :=
  (ModuleCat.restrictScalars (Int.castRingHom ℚ)).obj (ModuleCat.of ℚ ℚ)

/-- The degree-`n` component of the comparison, notation. -/
abbrev PhiN (X : SSet) (n : ℕ) := HomologicalComplex.Hom.f (Work.StemsB.RatBC.Phi X).hom n

/-- Additivity of `x ↦ Φ (1 ⊗ x)`. -/
lemma Phi_unit_add (X : SSet) (n : ℕ) (x y : (X.chainComplex zcZ).X n) :
    (PhiN X n).hom (((1 : ℚ) : ↥ratAsZ) ⊗ₜ[ℤ] (x + y))
      = (PhiN X n).hom (((1 : ℚ) : ↥ratAsZ) ⊗ₜ[ℤ] x)
        + (PhiN X n).hom (((1 : ℚ) : ↥ratAsZ) ⊗ₜ[ℤ] y) := by
  rw [TensorProduct.tmul_add, map_add]

/-- The `ZSMul` and `Module ℤ` scalar actions on a `ℤ`-module coincide. -/
lemma zsmul_eq_module_smul (M : Type*) [AddCommGroup M] [Module ℤ M] :
    (ZSMul.toSMul : SMul ℤ M) = (inferInstance : Module ℤ M).toDistribSMul.toSMul := by
  have h : (inferInstance : Module ℤ M) = AddCommGroup.toIntModule M := Subsingleton.elim _ _
  rw [h]
  rfl

/-- `1 ⊗ (c • x) = c • (1 ⊗ x)` for `c : ℤ`. -/
lemma tmul_one_zsmul (X : SSet) (n : ℕ) (c : ℤ) (x : (X.chainComplex zcZ).X n) :
    ((1 : ℚ) : ↥ratAsZ) ⊗ₜ[ℤ] (c • x)
      = c • (((1 : ℚ) : ↥ratAsZ) ⊗ₜ[ℤ] x) := by
  rw [← TensorProduct.mk_apply (R := ℤ) ((1 : ℚ) : ↥ratAsZ) (c • x),
      ← TensorProduct.mk_apply (R := ℤ) ((1 : ℚ) : ↥ratAsZ) x]
  rw [zsmul_eq_module_smul (↑((X.chainComplex zcZ).X n))]
  rw [zsmul_eq_module_smul (ℚ ⊗[ℤ] ↑((X.chainComplex zcZ).X n))]
  exact LinearMap.map_smul
    ((TensorProduct.mk ℤ ↥ratAsZ ↥((X.chainComplex zcZ).X n)) ((1 : ℚ) : ↥ratAsZ)) c x

/-- On a `ℚ`-module the `ℤ`-action is the restriction of the `ℚ`-action. -/
lemma rat_smul_zsmul {M : Type*} [AddCommGroup M] [Module ℚ M] (c : ℤ) (z : M) :
    c • z = (c : ℚ) • z :=
  (Int.cast_smul_eq_zsmul (R := ℚ) c z).symm

/-- `ℤ`-homogeneity of `x ↦ Φ (1 ⊗ x)`. -/
lemma Phi_unit_zsmul (X : SSet) (n : ℕ) (c : ℤ) (x : (X.chainComplex zcZ).X n) :
    (PhiN X n).hom (((1 : ℚ) : ↥ratAsZ) ⊗ₜ[ℤ] (c • x))
      = c • (PhiN X n).hom (((1 : ℚ) : ↥ratAsZ) ⊗ₜ[ℤ] x) := by
  rw [tmul_one_zsmul, rat_smul_zsmul, map_smul, rat_smul_zsmul]

/-- Additivity of `x ↦ Φ (1 ⊗ x)` over a finite sum. -/
lemma Phi_unit_sum (X : SSet) (n : ℕ) {α : Type*} (s : Finset α)
    (f : α → (X.chainComplex zcZ).X n) :
    (PhiN X n).hom (((1 : ℚ) : ↥ratAsZ) ⊗ₜ[ℤ] (∑ a ∈ s, f a))
      = ∑ a ∈ s, (PhiN X n).hom (((1 : ℚ) : ↥ratAsZ) ⊗ₜ[ℤ] f a) := by
  classical
  induction s using Finset.induction with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, TensorProduct.tmul_zero, map_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, Phi_unit_add, ih]

/-- **The comparison on an arbitrary chain**: `Φ (1 ⊗ x) = bcCast x`. -/
lemma Phi_unit_bcCast (X : SSet) (n : ℕ) (x : (X.chainComplex zcZ).X n) :
    (PhiN X n).hom (TensorProduct.tmul ℤ ((1 : ℚ) : ↥ratAsZ) x)
      = (bcCast X n).hom x := by
  conv_lhs => rw [Work.KunnethEZ.chain_eq_sum_gen X n x]
  rw [Phi_unit_sum]
  conv_rhs => rw [Work.KunnethEZ.chain_eq_sum_gen X n x]
  rw [map_sum]
  refine Finset.sum_congr rfl (fun σ _ => ?_)
  rw [map_zsmul, Phi_unit_zsmul, Phi_gen X n σ, bcCast_ι X n σ]

end

end Work.Serre
