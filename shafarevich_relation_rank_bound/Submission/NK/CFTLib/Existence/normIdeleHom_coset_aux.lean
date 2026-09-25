import Mathlib
import Submission.NK.GlobalCFT.Place
import Submission.NK.GlobalCFT.NormFunctorial
import Submission.NK.GlobalCFT.GaloisIdelesAction
import Submission.NK.GlobalCFT.Inclusion.globalCFT_ideleInclusion_exists
import Submission.NK.GlobalCFT.Inclusion.globalCFT_prod_smul_eq_inclusion_normIdeleHom

/-!
# The relative norm is the product of the conjugates (coset form)

For a finite Galois extension `L/K` of number fields, a subgroup `H ≤ Gal(L/K)` with fixed field
`E = L^H`, idèle inclusions `φK : 𝕀 K →* 𝕀 L` and `φE : 𝕀 E →* 𝕀 L` attached to place-below maps
`uK`, `uE`, the relative norm `N_{E/K} z` for `z : 𝕀 E` is the product of the conjugates of
`φE z` over the cosets of `H`.

## Helper lemmas proved in this file

* `NK.CFTLib.Existence.norm_eq_prod_embeddings_of_normal`: for a finite separable extension
  `F/K` contained in a normal extension `Ω/K`, the norm of `x : F` is the product of the images
  of `x` under all `K`-embeddings `F → Ω`.  This is Mathlib's `Algebra.norm_eq_prod_embeddings`
  (which wants an algebraically closed target) transported to a normal target.
-/

namespace NK.CFTLib.Existence

open Polynomial
open NumberField IsDedekindDomain

/-- **The norm is the product of the embeddings into a normal extension.**  If `F/K` is a finite
separable extension and `F → Ω` is an embedding into a finite normal extension `Ω/K`, then
`N_{F/K}(x) = ∏_{σ : F →ₐ[K] Ω} σ x`, the product being taken in `Ω`. -/
theorem norm_eq_prod_embeddings_of_normal {K F Ω : Type*} [Field K] [Field F] [Field Ω]
    [Algebra K F] [Algebra K Ω] [Algebra F Ω] [IsScalarTower K F Ω]
    [FiniteDimensional K F] [Algebra.IsSeparable K F] [Normal K Ω]
    (x : F) : ∏ σ : F →ₐ[K] Ω, σ x = algebraMap K Ω (Algebra.norm K x) := by
  apply (algebraMap Ω (AlgebraicClosure Ω)).injective
  rw [map_prod]
  rw [← IsScalarTower.algebraMap_apply K Ω (AlgebraicClosure Ω)]
  rw [Algebra.norm_eq_prod_embeddings (L := F) K (AlgebraicClosure Ω) x]
  have hinj : Function.Injective
      (fun σ : F →ₐ[K] Ω => (IsScalarTower.toAlgHom K Ω (AlgebraicClosure Ω)).comp σ) := by
    intro a b h
    ext y
    exact (algebraMap Ω (AlgebraicClosure Ω)).injective ((AlgHom.ext_iff.mp h) y)
  have hcard : Nat.card (F →ₐ[K] AlgebraicClosure Ω) ≤ Nat.card (F →ₐ[K] Ω) := by
    rw [AlgHom.natCard_of_splits (F := K) (E := F) (L := AlgebraicClosure Ω)
          (fun _ => IsAlgClosed.splits _)]
    rw [AlgHom.natCard_of_splits (F := K) (E := F) (L := Ω)
          (fun y => by
            rw [← minpoly.algebraMap_eq (algebraMap F Ω).injective y]
            exact (inferInstance : Normal K Ω).splits (algebraMap F Ω y))]
  exact Fintype.prod_bijective
    (fun σ : F →ₐ[K] Ω => (IsScalarTower.toAlgHom K Ω (AlgebraicClosure Ω)).comp σ)
    (hinj.bijective_of_nat_card_le hcard) _ _ (fun _ => rfl)

/-- The unit form of `norm_eq_prod_embeddings_of_normal`. -/
theorem units_norm_eq_prod_algHom {K F Ω : Type*} [Field K] [Field F] [Field Ω]
    [Algebra K F] [Algebra K Ω] [Algebra F Ω] [IsScalarTower K F Ω]
    [FiniteDimensional K F] [Algebra.IsSeparable K F] [Normal K Ω]
    (x : Fˣ) :
    (∏ σ : F →ₐ[K] Ω, Units.map σ.toRingHom.toMonoidHom x) =
      Units.map (algebraMap K Ω).toMonoidHom (Units.map (Algebra.norm K) x) := by
  ext
  simp only [Units.coe_prod, Units.coe_map]
  exact norm_eq_prod_embeddings_of_normal (K := K) (x : F)

open scoped NumberField.LiesOver in
/-- **The completion map on the dense subfield (archimedean case).**  For a tower `E ⊆ L` of
number fields and archimedean places `v` of `E`, `w` of `L` with `w` over `v`, the completion map
`E_v →+* L_w` sends `x ∈ E` to `x ∈ L_w` (via `E → L → L_w`). -/
theorem liesOver_completionMap_algebraMap {E L : Type} [Field E] [Field L] [Algebra E L]
    (w : NumberField.InfinitePlace L) (v : NumberField.InfinitePlace E) [hwv : w.LiesOver v]
    (x : E) :
    NumberField.LiesOver.completionMap (v := v) (w := w) (algebraMap E v.Completion x)
      = algebraMap L w.Completion (algebraMap E L x) := by
  have hST : IsScalarTower E L w.Completion := by
    refine IsScalarTower.of_algebraMap_eq fun a => ?_
    have e2 := NumberField.InfinitePlace.Completion.algebraMap_toCompletion (v := w) (R := L)
      (algebraMap E L a)
    have e3 := NumberField.InfinitePlace.Completion.algebraMap_toCompletion (v := w) (R := E) a
    apply NumberField.InfinitePlace.Completion.ext
    rw [e3, e2, UniformSpace.Completion.algebraMap_def, UniformSpace.Completion.algebraMap_def]
    simp [WithAbs.algebraMap_right_apply]
  rw [← RingHom.algebraMap_toAlgebra (NumberField.LiesOver.completionMap (v := v) (w := w))]
  rw [← IsScalarTower.algebraMap_apply E v.Completion w.Completion x]
  exact IsScalarTower.algebraMap_apply E L w.Completion x

open scoped NumberField.LiesOver in
/-- **The local algebra map on the dense subfield.**  For a tower `K ⊆ E ⊆ L` of number fields and
places `w` of `L` over `v` of `E`, the local algebra map `E_vˣ →* L_wˣ` composed with the
completion `Eˣ →* E_vˣ` is the completion `Eˣ →* L_wˣ`. -/
theorem localAlgebraMapUnits_comp_units_algebraMap {K E L : Type} [Field K] [NumberField K]
    [Field E] [NumberField E] [Field L] [NumberField L] [Algebra K E] [Algebra E L] [Algebra K L]
    [IsScalarTower K E L]
    (w : NK.GlobalCFT.Place L) (v : NK.GlobalCFT.Place E)
    (h : NK.GlobalCFT.Place.LiesOver w v) :
    (NK.GlobalCFT.Place.localAlgebraMapUnits w v h).comp
        (Units.map (algebraMap E (NK.GlobalCFT.Place.localField E v)).toMonoidHom) =
      (Units.map (algebraMap L (NK.GlobalCFT.Place.localField L w)).toMonoidHom).comp
        (Units.map (algebraMap E L).toMonoidHom) := by
  rcases w with w₀ | q <;> rcases v with v₀ | Q
  · haveI : w₀.LiesOver v₀ :=
      (NK.GlobalCFT.Galois.globalCFT_liesOver_ofInfinite_iff w₀ v₀).mp h
    have hmap : NK.GlobalCFT.Place.localAlgebraMapUnits
          (NK.GlobalCFT.Place.ofInfinite w₀) (NK.GlobalCFT.Place.ofInfinite v₀) h
        = Units.map (NumberField.LiesOver.completionMap (v := v₀) (w := w₀)).toMonoidHom := by
      rw [NK.GlobalCFT.Place.localAlgebraMapUnits]
      simp only
      rw [dif_pos (show w₀.LiesOver v₀ from inferInstance)]
    rw [hmap]
    ext x
    simp only [MonoidHom.coe_comp, Function.comp_apply, Units.coe_map]
    exact congrArg (fun t : w₀.Completion => t.toCompletion)
      (liesOver_completionMap_algebraMap w₀ v₀ (↑x : E))
  · exfalso
    rcases (NK.GlobalCFT.Place.liesOver_iff _ _).mp h with
      ⟨w', v', h1, h2, h3⟩ | ⟨q', Q', h1, h2, h3⟩
    · exact NK.GlobalCFT.Place.ofInfinite_ne_ofFinite v' Q h2.symm
    · exact NK.GlobalCFT.Place.ofInfinite_ne_ofFinite w₀ q' h1
  · exfalso
    rcases (NK.GlobalCFT.Place.liesOver_iff _ _).mp h with
      ⟨w', v', h1, h2, h3⟩ | ⟨q', Q', h1, h2, h3⟩
    · exact NK.GlobalCFT.Place.ofInfinite_ne_ofFinite w' q h1.symm
    · exact NK.GlobalCFT.Place.ofInfinite_ne_ofFinite v₀ Q' h2
  · have hqQ : q.asIdeal.LiesOver Q.asIdeal :=
      (NK.GlobalCFT.Galois.globalCFT_liesOver_ofFinite_iff q Q).mp h
    have hmap : NK.GlobalCFT.Place.localAlgebraMapUnits
          (NK.GlobalCFT.Place.ofFinite q) (NK.GlobalCFT.Place.ofFinite Q) h
        = Units.map (Commons.RingTheory.Henselian.adicCompletionMap Q q hqQ).toMonoidHom := by
      rw [NK.GlobalCFT.Place.localAlgebraMapUnits]
      simp only
      rw [dif_pos hqQ]
    rw [hmap]
    ext x
    simp only [MonoidHom.coe_comp, Function.comp_apply, Units.coe_map]
    have harg : (algebraMap E (NK.GlobalCFT.Place.localField E
          (NK.GlobalCFT.Place.ofFinite Q)) (↑x : E))
        = ({ toCompletion := ↑((WithVal.equiv
              (IsDedekindDomain.HeightOneSpectrum.valuation E Q)).symm
              (↑x : E)) } : Q.adicCompletion E) := by
      rw [IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletion]; rfl
    have harg' : (algebraMap L (NK.GlobalCFT.Place.localField L
          (NK.GlobalCFT.Place.ofFinite q)) ((algebraMap E L) (↑x : E)))
        = ({ toCompletion := ↑((WithVal.equiv
              (IsDedekindDomain.HeightOneSpectrum.valuation L q)).symm
              ((algebraMap E L) (↑x : E))) } : q.adicCompletion L) := by
      rw [IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletion]; rfl
    have hkey := Commons.RingTheory.Henselian.adicCompletionMap_apply Q q hqQ (↑x : E)
    refine (congrArg (fun t : Q.adicCompletion E =>
        (Commons.RingTheory.Henselian.adicCompletionMap Q q hqQ t).toCompletion) harg).trans ?_
    refine (congrArg (fun t : q.adicCompletion L => t.toCompletion) hkey).trans ?_
    exact (congrArg (fun t : q.adicCompletion L => t.toCompletion) harg').symm

/-- **The coset bijection `H\G ≃ Hom_K(L^H, L)`.**  For a finite Galois extension `L/K` and a
subgroup `H ≤ Gal(L/K)`, the map sending the class of `r` to the restriction of `r⁻¹` to the fixed
field `L^H` is a bijection onto the `K`-embeddings of `L^H` into `L`.

The direction `r ↦ r⁻¹` is the one compatible with `QuotientGroup.rightRel H` (whose classes are
the left cosets `H r`); with `r ↦ r` one would need `leftRel`. -/
theorem bijective_quotient_restrict_fixedField {K L : Type} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (H : Subgroup (L ≃ₐ[K] L)) :
    Function.Bijective (fun q : Quotient (QuotientGroup.rightRel H) =>
      ((Quotient.out q)⁻¹ : L ≃ₐ[K] L).toAlgHom.comp
        (IntermediateField.fixedField H).val) := by
  classical
  have hN : Normal K L := inferInstance
  let ρ : (L ≃ₐ[K] L) → (↥(IntermediateField.fixedField H) →ₐ[K] L) :=
    fun r => (r⁻¹).toAlgHom.comp (IntermediateField.fixedField H).val
  have hHmem : ∀ (r r' : L ≃ₐ[K] L),
      (∀ y ∈ IntermediateField.fixedField H, (r' * r⁻¹) y = y) → r' * r⁻¹ ∈ H := by
    intro r r' h
    have hh : r' * r⁻¹ ∈ (IntermediateField.fixedField H).fixingSubgroup :=
      (IntermediateField.mem_fixingSubgroup_iff _ _).mpr h
    rwa [IntermediateField.fixingSubgroup_fixedField H] at hh
  have hwd : ∀ r r' : L ≃ₐ[K] L, QuotientGroup.rightRel H r r' → ρ r = ρ r' := by
    intro r r' h
    have hh : r' * r⁻¹ ∈ H := QuotientGroup.rightRel_apply.mp h
    have hmem : (r' * r⁻¹)⁻¹ ∈ H := H.inv_mem hh
    have hfix : ∀ y : L, y ∈ IntermediateField.fixedField H →
        (r' * r⁻¹)⁻¹ y = y :=
      fun y hy => (IntermediateField.mem_fixedField_iff H y).mp hy _ hmem
    have hr'' : r'⁻¹ = r⁻¹ * (r' * r⁻¹)⁻¹ := by group
    ext x
    show (r⁻¹) ((IntermediateField.fixedField H).val x)
        = (r'⁻¹) ((IntermediateField.fixedField H).val x)
    rw [hr'']
    show (r⁻¹) ((IntermediateField.fixedField H).val x)
        = (r⁻¹ * (r' * r⁻¹)⁻¹) ((IntermediateField.fixedField H).val x)
    rw [show ((r⁻¹ * (r' * r⁻¹)⁻¹) : L ≃ₐ[K] L) ((IntermediateField.fixedField H).val x)
        = r⁻¹ (((r' * r⁻¹)⁻¹) ((IntermediateField.fixedField H).val x)) from rfl]
    exact (congrArg (fun t => r⁻¹ t)
      (hfix ((IntermediateField.fixedField H).val x) x.2)).symm
  obtain ⟨ρbar, hρbar⟩ : ∃ ρbar : Quotient (QuotientGroup.rightRel H) →
      (↥(IntermediateField.fixedField H) →ₐ[K] L), ∀ r, ρbar (Quotient.mk'' r) = ρ r :=
    ⟨Quotient.lift ρ hwd, fun r => Quotient.lift_mk ρ hwd r⟩
  have hmap : (fun q : Quotient (QuotientGroup.rightRel H) =>
      ((Quotient.out q)⁻¹ : L ≃ₐ[K] L).toAlgHom.comp (IntermediateField.fixedField H).val) = ρbar := by
    funext q
    conv_rhs => rw [← Quotient.out_eq' q]
    rw [hρbar]
  rw [hmap]
  refine ⟨?_, ?_⟩
  · intro q₁ q₂ h
    have h' : ρ (Quotient.out q₁) = ρ (Quotient.out q₂) := by
      rw [← hρbar (Quotient.out q₁), ← hρbar (Quotient.out q₂), Quotient.out_eq',
        Quotient.out_eq']
      exact h
    have key : Quotient.out q₂ * (Quotient.out q₁)⁻¹ ∈ H :=
      hHmem _ _ (fun y hy => by
        have h2 : (Quotient.out q₁)⁻¹ y = (Quotient.out q₂)⁻¹ y := by
          have := congrArg (fun f : ↥(IntermediateField.fixedField H) →ₐ[K] L => f ⟨y, hy⟩) h'
          simpa [ρ] using this
        show Quotient.out q₂ ((Quotient.out q₁)⁻¹ y) = y
        rw [h2]
        exact (Quotient.out q₂).apply_symm_apply y)
    have hs : Quotient.mk'' (Quotient.out q₁) = Quotient.mk'' (Quotient.out q₂) :=
      Quotient.sound (QuotientGroup.rightRel_apply.mpr key)
    rwa [Quotient.out_eq', Quotient.out_eq'] at hs
  · intro σ
    let s : L →ₐ[K] L := σ.liftNormal L
    have hsbij : Function.Bijective s := AlgHom.normal_bijective K L L s
    let r : L ≃ₐ[K] L := AlgEquiv.ofBijective s hsbij
    have hr : ∀ x : ↥(IntermediateField.fixedField H),
        r ((IntermediateField.fixedField H).val x) = σ x := by
      intro x
      have h1 := AlgHom.liftNormal_commutes σ L x
      simpa [s, r, AlgEquiv.ofBijective_apply] using h1
    refine ⟨Quotient.mk'' r⁻¹, ?_⟩
    show ρbar (Quotient.mk'' r⁻¹) = σ
    rw [hρbar r⁻¹]
    ext x
    show ((r⁻¹)⁻¹) ((IntermediateField.fixedField H).val x) = σ x
    rw [inv_inv]
    exact hr x

/-- **The archimedean local degree sum.**  For an archimedean place `v` of `K`, the sum of the
local degrees `[L_w : K_v]` over the archimedean places `w` of `L` above `v` equals `[L : K]`.
This is the archimedean companion of
`Commons.NumberTheory.NumberField.Completion.sum_finrank_adicCompletion_eq_finrank`; it is a
repackaging of Mathlib's `NumberField.InfinitePlace.sum_inertiaDeg_eq_finrank` together with
`NumberField.InfinitePlace.inertiaDeg_eq_finrank`. -/
theorem sum_finrank_completion_eq_finrank_ofInfinite {K L : Type} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]
    (v : NumberField.InfinitePlace K) :
    (∑ w : {w : NumberField.InfinitePlace L //
        w ∈ NK.GlobalCFT.Place.fiberInfinite (K := K) (L := L) v},
      @Module.finrank (v.Completion) (w.1.Completion) _ _
        (RingHom.toAlgebra (@NumberField.LiesOver.completionMap K L _ _ _ v w.1
          ((NK.GlobalCFT.Place.mem_fiberInfinite (K := K) (L := L)).mp w.2))).toModule)
      = Module.finrank K L := by
  classical
  have h1 : (∑ w : {w : NumberField.InfinitePlace L //
        w ∈ NK.GlobalCFT.Place.fiberInfinite (K := K) (L := L) v},
      @Module.finrank (v.Completion) (w.1.Completion) _ _
        (RingHom.toAlgebra (@NumberField.LiesOver.completionMap K L _ _ _ v w.1
          ((NK.GlobalCFT.Place.mem_fiberInfinite (K := K) (L := L)).mp w.2))).toModule)
      = ∑ w : {w : NumberField.InfinitePlace L //
          w ∈ NK.GlobalCFT.Place.fiberInfinite (K := K) (L := L) v}, v.inertiaDeg w.1 :=
    Finset.sum_congr rfl (fun w _ =>
      (@NumberField.InfinitePlace.inertiaDeg_eq_finrank K L _ _ _ v w.1
        ((NK.GlobalCFT.Place.mem_fiberInfinite (K := K) (L := L)).mp w.2)).symm)
  rw [h1]
  calc (∑ w : {w : NumberField.InfinitePlace L //
          w ∈ NK.GlobalCFT.Place.fiberInfinite (K := K) (L := L) v}, v.inertiaDeg w.1)
      = ∑ w ∈ NK.GlobalCFT.Place.fiberInfinite (K := K) (L := L) v, v.inertiaDeg w :=
        (Finset.sum_subtype _ (fun _ => Iff.rfl) (fun w => v.inertiaDeg w)).symm
    _ = ∑ w ∈ (NumberField.InfinitePlace.placesOver L v).toFinset, v.inertiaDeg w := by
        congr 1
        ext w
        rw [NK.GlobalCFT.Place.mem_fiberInfinite, Set.mem_toFinset]
        rfl
    _ = Module.finrank K L := NumberField.InfinitePlace.sum_inertiaDeg_eq_finrank K L v

end NK.CFTLib.Existence
