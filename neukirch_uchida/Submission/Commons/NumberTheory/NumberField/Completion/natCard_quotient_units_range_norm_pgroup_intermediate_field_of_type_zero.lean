import Mathlib
import Submission.Commons.FieldTheory.Galois.natCard_quotient_units_range_norm_eq_of_ringEquiv
import Submission.Commons.FieldTheory.Galois.isGalois_of_ringEquiv
import Submission.Commons.Algebra.Module.moduleFinite_of_ringEquiv
import Submission.Commons.NumberTheory.NumberField.Completion.exists_type_zero_field_of_finiteDimensional
import Submission.Commons.NumberTheory.NumberField.Completion.exists_adicCompletion_ringEquiv_type_zero

set_option maxHeartbeats 800000
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

namespace Commons.NumberTheory.NumberField.Completion

section UnivTransport
variable {B E B₀ E₀ : Type*} [Field B] [Field E] [Field B₀] [Field E₀]
    [Algebra B E] [Algebra B₀ E₀]

noncomputable def algEquivConjUniv (eB : B ≃+* B₀) (eE : E ≃+* E₀)
    (h : ∀ x : B, eE (algebraMap B E x) = algebraMap B₀ E₀ (eB x)) (σ : E ≃ₐ[B] E) :
    E₀ ≃ₐ[B₀] E₀ :=
  AlgEquiv.ofRingEquiv (f := eE.symm.trans (σ.toRingEquiv.trans eE)) (by
    intro y
    change eE (σ (eE.symm (algebraMap B₀ E₀ y))) = algebraMap B₀ E₀ y
    have hy : algebraMap B₀ E₀ y = eE (algebraMap B E (eB.symm y)) := by
      rw [h (eB.symm y), eB.apply_symm_apply]
    rw [hy, RingEquiv.symm_apply_apply, AlgEquiv.commutes, h (eB.symm y), eB.apply_symm_apply])

noncomputable def algEquivConjSymmUniv (eB : B ≃+* B₀) (eE : E ≃+* E₀)
    (h : ∀ x : B, eE (algebraMap B E x) = algebraMap B₀ E₀ (eB x)) (τ : E₀ ≃ₐ[B₀] E₀) :
    E ≃ₐ[B] E :=
  AlgEquiv.ofRingEquiv (f := eE.trans (τ.toRingEquiv.trans eE.symm)) (by
    intro x
    change eE.symm (τ (eE (algebraMap B E x))) = algebraMap B E x
    rw [h x, AlgEquiv.commutes, ← h x, RingEquiv.symm_apply_apply])

@[simp]
theorem algEquivConjUniv_apply (eB : B ≃+* B₀) (eE : E ≃+* E₀)
    (h : ∀ x : B, eE (algebraMap B E x) = algebraMap B₀ E₀ (eB x)) (σ : E ≃ₐ[B] E) (a : E₀) :
    algEquivConjUniv eB eE h σ a = eE (σ (eE.symm a)) := by
  rw [algEquivConjUniv, AlgEquiv.ofRingEquiv_apply, RingEquiv.trans_apply, RingEquiv.trans_apply]
  rfl

@[simp]
theorem algEquivConjSymmUniv_apply (eB : B ≃+* B₀) (eE : E ≃+* E₀)
    (h : ∀ x : B, eE (algebraMap B E x) = algebraMap B₀ E₀ (eB x)) (τ : E₀ ≃ₐ[B₀] E₀) (a : E) :
    algEquivConjSymmUniv eB eE h τ a = eE.symm (τ (eE a)) := by
  rw [algEquivConjSymmUniv, AlgEquiv.ofRingEquiv_apply, RingEquiv.trans_apply, RingEquiv.trans_apply]
  rfl

theorem algEquivConjSymmUniv_algEquivConjUniv (eB : B ≃+* B₀) (eE : E ≃+* E₀)
    (h : ∀ x : B, eE (algebraMap B E x) = algebraMap B₀ E₀ (eB x)) (σ : E ≃ₐ[B] E) :
    algEquivConjSymmUniv eB eE h (algEquivConjUniv eB eE h σ) = σ := by
  apply AlgEquiv.ext
  intro a
  simp only [algEquivConjSymmUniv_apply, algEquivConjUniv_apply, RingEquiv.symm_apply_apply]

theorem algEquivConjUniv_algEquivConjSymmUniv (eB : B ≃+* B₀) (eE : E ≃+* E₀)
    (h : ∀ x : B, eE (algebraMap B E x) = algebraMap B₀ E₀ (eB x)) (τ : E₀ ≃ₐ[B₀] E₀) :
    algEquivConjUniv eB eE h (algEquivConjSymmUniv eB eE h τ) = τ := by
  apply AlgEquiv.ext
  intro b
  simp only [algEquivConjUniv_apply, algEquivConjSymmUniv_apply, RingEquiv.apply_symm_apply]

noncomputable def algEquivConjEquivUniv (eB : B ≃+* B₀) (eE : E ≃+* E₀)
    (h : ∀ x : B, eE (algebraMap B E x) = algebraMap B₀ E₀ (eB x)) :
    (E ≃ₐ[B] E) ≃ (E₀ ≃ₐ[B₀] E₀) where
  toFun := algEquivConjUniv eB eE h
  invFun := algEquivConjSymmUniv eB eE h
  left_inv := algEquivConjSymmUniv_algEquivConjUniv eB eE h
  right_inv := algEquivConjUniv_algEquivConjSymmUniv eB eE h

theorem algEquivConjUniv_mul (eB : B ≃+* B₀) (eE : E ≃+* E₀)
    (h : ∀ x : B, eE (algebraMap B E x) = algebraMap B₀ E₀ (eB x)) (σ τ : E ≃ₐ[B] E) :
    algEquivConjUniv eB eE h (σ * τ) =
      algEquivConjUniv eB eE h σ * algEquivConjUniv eB eE h τ := by
  apply AlgEquiv.ext
  intro a
  simp only [algEquivConjUniv_apply, AlgEquiv.mul_apply, RingEquiv.symm_apply_apply]

noncomputable def algEquivConjMulEquivUniv (eB : B ≃+* B₀) (eE : E ≃+* E₀)
    (h : ∀ x : B, eE (algebraMap B E x) = algebraMap B₀ E₀ (eB x)) :
    (E ≃ₐ[B] E) ≃* (E₀ ≃ₐ[B₀] E₀) where
  toEquiv := algEquivConjEquivUniv eB eE h
  map_mul' := algEquivConjUniv_mul eB eE h

theorem natCard_algEquiv_eq_of_ringEquiv_univ (eB : B ≃+* B₀) (eE : E ≃+* E₀)
    (h : ∀ x : B, eE (algebraMap B E x) = algebraMap B₀ E₀ (eB x)) :
    Nat.card (E ≃ₐ[B] E) = Nat.card (E₀ ≃ₐ[B₀] E₀) :=
  Nat.card_congr (algEquivConjEquivUniv eB eE h)

theorem isPGroup_algEquiv_of_ringEquiv {p : ℕ} (eB : B ≃+* B₀) (eE : E ≃+* E₀)
    (h : ∀ x : B, eE (algebraMap B E x) = algebraMap B₀ E₀ (eB x))
    (hp : IsPGroup p (E ≃ₐ[B] E)) : IsPGroup p (E₀ ≃ₐ[B₀] E₀) :=
  IsPGroup.of_equiv hp (algEquivConjMulEquivUniv eB eE h)

theorem commute_of_commute_ringEquiv (eB : B ≃+* B₀) (eE : E ≃+* E₀)
    (h : ∀ x : B, eE (algebraMap B E x) = algebraMap B₀ E₀ (eB x))
    (hcomm : ∀ a b : E ≃ₐ[B] E, a * b = b * a) :
    ∀ a b : E₀ ≃ₐ[B₀] E₀, a * b = b * a := by
  intro a b
  have h1 : a * b = algEquivConjMulEquivUniv eB eE h
      ((algEquivConjMulEquivUniv eB eE h).symm a *
        (algEquivConjMulEquivUniv eB eE h).symm b) := by
    rw [map_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
  have h2 : b * a = algEquivConjMulEquivUniv eB eE h
      ((algEquivConjMulEquivUniv eB eE h).symm b *
        (algEquivConjMulEquivUniv eB eE h).symm a) := by
    rw [map_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
  rw [h1, h2, hcomm]

end UnivTransport

theorem isGalois_intermediateFieldOfCommute {B E : Type*} [Field B] [Field E] [Algebra B E]
    [FiniteDimensional B E] [IsGalois B E]
    (hcomm : ∀ a b : E ≃ₐ[B] E, a * b = b * a) (M : IntermediateField B E) :
    IsGalois B ↥M := by
  haveI : IsMulCommutative (E ≃ₐ[B] E) := IsMulCommutative.of_comm hcomm
  haveI : (M.fixingSubgroup).Normal := Subgroup.normal_of_isMulCommutative _
  haveI h : IsGalois B ↥(IntermediateField.fixedField M.fixingSubgroup) :=
    IsGalois.of_fixedField_normal_subgroup M.fixingSubgroup
  exact (IsGalois.fixedField_fixingSubgroup (F := B) (E := E) M) ▸ h

theorem commute_intermediateFieldOfCommute {B E : Type*} [Field B] [Field E] [Algebra B E]
    [FiniteDimensional B E] [IsGalois B E]
    (hcomm : ∀ a b : E ≃ₐ[B] E, a * b = b * a) (M : IntermediateField B E) :
    ∀ a b : ↥M ≃ₐ[B] ↥M, a * b = b * a := by
  haveI : IsMulCommutative (E ≃ₐ[B] E) := IsMulCommutative.of_comm hcomm
  haveI hH : (M.fixingSubgroup).Normal := Subgroup.normal_of_isMulCommutative _
  let e := IsGalois.normalAutEquivQuotient (K := B) (L := E) M.fixingSubgroup
  have hq : ∀ x y : (E ≃ₐ[B] E) ⧸ M.fixingSubgroup, x * y = y * x := by
    intro x y
    obtain ⟨x', rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨y', rfl⟩ := QuotientGroup.mk_surjective y
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hcomm x' y']
  have key : ∀ a b : ↥(IntermediateField.fixedField M.fixingSubgroup) ≃ₐ[B]
      ↥(IntermediateField.fixedField M.fixingSubgroup), a * b = b * a := by
    intro a b
    apply e.symm.injective
    rw [map_mul, map_mul, hq]
  rw [IsGalois.fixedField_fixingSubgroup (F := B) (E := E) M] at key
  exact key

theorem natCard_quotient_units_range_norm_pgroup_intermediate_field_of_type_zero
    (h0 : ∀ {K : Type} [Field K] [NumberField K]
        (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
        {B E : Type} [Field B] [Field E]
        [Algebra (Q.adicCompletion K) B] [Algebra B E] [Algebra (Q.adicCompletion K) E]
        [IsScalarTower (Q.adicCompletion K) B E]
        [FiniteDimensional (Q.adicCompletion K) B] [FiniteDimensional B E]
        [IsGalois B E],
        (∀ a b : E ≃ₐ[B] E, a * b = b * a) →
        ∀ (M : IntermediateField B E) (p : ℕ), IsPGroup p (M ≃ₐ[B] M) →
          Nat.card (Bˣ ⧸ MonoidHom.range (Units.map (Algebra.norm B : M →* B))) =
            Nat.card (M ≃ₐ[B] M)) :
    ∀ {K : Type*} [Field K] [NumberField K]
      (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
      {B E : Type*} [Field B] [Field E]
      [Algebra (Q.adicCompletion K) B] [Algebra B E] [Algebra (Q.adicCompletion K) E]
      [IsScalarTower (Q.adicCompletion K) B E]
      [FiniteDimensional (Q.adicCompletion K) B] [FiniteDimensional B E]
      [IsGalois B E],
      (∀ a b : E ≃ₐ[B] E, a * b = b * a) →
      ∀ (M : IntermediateField B E) (p : ℕ), IsPGroup p (M ≃ₐ[B] M) →
        Nat.card (Bˣ ⧸ MonoidHom.range (Units.map (Algebra.norm B : M →* B))) =
          Nat.card (M ≃ₐ[B] M) := by
  classical
  intro K hKf hKnf Q B E hBf hEf hAlgFB hAlgBE hAlgFE hTower hFdB hFdBE hGalBE hcomm M p hp
  -- ## Step 1: shrink the number field `K` and transport the completion `Q.adicCompletion K`.
  obtain ⟨K₀, hK₀f, hK₀nf, Q₀, ⟨Φ⟩⟩ :=
    Commons.NumberTheory.NumberField.Completion.exists_adicCompletion_ringEquiv_type_zero K Q
  letI : Field K₀ := hK₀f
  letI : NumberField K₀ := hK₀nf
  -- ## Step 2: transport the base `B` to a `Q₀.adicCompletion K₀`-algebra, then shrink it.
  let gB : Q₀.adicCompletion K₀ →+* B :=
    (algebraMap (Q.adicCompletion K) B).comp Φ.symm.toRingHom
  letI : Algebra (Q₀.adicCompletion K₀) B := gB.toAlgebra
  have hFB : ∀ x : Q.adicCompletion K,
      algebraMap (Q₀.adicCompletion K₀) B (Φ x) = algebraMap (Q.adicCompletion K) B x := by
    intro x
    show gB (Φ x) = algebraMap (Q.adicCompletion K) B x
    rw [show gB (Φ x) = algebraMap (Q.adicCompletion K) B (Φ.symm (Φ x)) from rfl,
      Φ.symm_apply_apply]
  have hFB' : ∀ x : Q.adicCompletion K,
      (RingEquiv.refl B) (algebraMap (Q.adicCompletion K) B x)
        = algebraMap (Q₀.adicCompletion K₀) B (Φ x) := fun x => (hFB x).symm
  haveI hFdB₀ : FiniteDimensional (Q₀.adicCompletion K₀) B :=
    Commons.Algebra.Module.moduleFinite_of_ringEquiv Φ (RingEquiv.refl B) hFB'
  obtain ⟨B₀, hB₀f, hB₀a, hB₀fd, ⟨eB⟩⟩ :=
    Commons.NumberTheory.NumberField.Completion.exists_type_zero_field_of_finiteDimensional
      (F := Q₀.adicCompletion K₀) (E := B)
  letI : Field B₀ := hB₀f
  letI : Algebra (Q₀.adicCompletion K₀) B₀ := hB₀a
  letI : FiniteDimensional (Q₀.adicCompletion K₀) B₀ := hB₀fd
  -- ## Step 3: transport the intermediate field `M` along `eB` and shrink it.
  let gM : B₀ →+* ↥M := (algebraMap B ↥M).comp eB.toRingEquiv.symm.toRingHom
  letI : Algebra B₀ ↥M := gM.toAlgebra
  have hBM : ∀ x : B, algebraMap B ↥M x = algebraMap B₀ ↥M (eB.toRingEquiv x) := by
    intro x
    show algebraMap B ↥M x = gM (eB.toRingEquiv x)
    rw [show gM (eB.toRingEquiv x)
        = algebraMap B ↥M (eB.toRingEquiv.symm (eB.toRingEquiv x)) from rfl,
      eB.toRingEquiv.symm_apply_apply]
  have hBM' : ∀ x : B, (RingEquiv.refl ↥M) (algebraMap B ↥M x)
      = algebraMap B₀ ↥M (eB.toRingEquiv x) := fun x => hBM x
  haveI hFdM₀ : FiniteDimensional B₀ ↥M :=
    Commons.Algebra.Module.moduleFinite_of_ringEquiv eB.toRingEquiv (RingEquiv.refl ↥M) hBM'
  haveI hGalBM : IsGalois B ↥M := isGalois_intermediateFieldOfCommute hcomm M
  haveI hGalB₀M : IsGalois B₀ ↥M :=
    Commons.FieldTheory.Galois.isGalois_of_ringEquiv eB.toRingEquiv (RingEquiv.refl ↥M) hBM'
  obtain ⟨M₁, hM₁f, hM₁a, hM₁fd, ⟨eM⟩⟩ :=
    Commons.NumberTheory.NumberField.Completion.exists_type_zero_field_of_finiteDimensional
      (F := B₀) (E := ↥M)
  letI : Field M₁ := hM₁f
  letI : Algebra B₀ M₁ := hM₁a
  letI : FiniteDimensional B₀ M₁ := hM₁fd
  haveI hGalB₀M₁ : IsGalois B₀ M₁ := IsGalois.of_algEquiv eM
  -- the base algebra structure of `M₁` over `Q₀.adicCompletion K₀`, and the tower
  let gM₁ : Q₀.adicCompletion K₀ →+* M₁ :=
    (algebraMap B₀ M₁).comp (algebraMap (Q₀.adicCompletion K₀) B₀)
  letI : Algebra (Q₀.adicCompletion K₀) M₁ := gM₁.toAlgebra
  haveI hTowerM₁ : IsScalarTower (Q₀.adicCompletion K₀) B₀ M₁ :=
    IsScalarTower.of_algebraMap_eq (fun x => rfl)
  -- ## Step 4: transport `hcomm`, `IsPGroup` and the two cardinals.
  have hcommM : ∀ a b : ↥M ≃ₐ[B] ↥M, a * b = b * a :=
    commute_intermediateFieldOfCommute hcomm M
  have hMcompat : ∀ x : B, eM.toRingEquiv (algebraMap B ↥M x) = algebraMap B₀ M₁ (eB.toRingEquiv x) := by
    intro x
    rw [hBM x]
    exact eM.commutes (eB.toRingEquiv x)
  have hcomm₁ : ∀ a b : M₁ ≃ₐ[B₀] M₁, a * b = b * a :=
    commute_of_commute_ringEquiv eB.toRingEquiv eM.toRingEquiv hMcompat hcommM
  have hp₁ : IsPGroup p (M₁ ≃ₐ[B₀] M₁) :=
    isPGroup_algEquiv_of_ringEquiv eB.toRingEquiv eM.toRingEquiv hMcompat hp
  have hp_top : IsPGroup p
      (↥(⊤ : IntermediateField B₀ M₁) ≃ₐ[B₀] ↥(⊤ : IntermediateField B₀ M₁)) :=
    IsPGroup.of_equiv hp₁
      (AlgEquiv.autCongr (IntermediateField.topEquiv (F := B₀) (E := M₁))).symm
  -- ## Step 5: apply the `Type 0` statement at `(K₀, Q₀, B₀, M₁)` and the top intermediate field.
  have hkey := h0 (Q := Q₀) (B := B₀) (E := M₁) hcomm₁ ⊤ p hp_top
  have hquottest : Nat.card (B₀ˣ ⧸ MonoidHom.range (Units.map (Algebra.norm B₀ :
        ↥(⊤ : IntermediateField B₀ M₁) →* B₀)))
      = Nat.card (B₀ˣ ⧸ MonoidHom.range (Units.map (Algebra.norm B₀ : M₁ →* B₀))) := by
    have hcomp : ∀ x : B₀, (IntermediateField.topEquiv (F := B₀) (E := M₁)).toRingEquiv
        (algebraMap B₀ ↥(⊤ : IntermediateField B₀ M₁) x) = algebraMap B₀ M₁ x := by
      intro x
      exact (IntermediateField.topEquiv (F := B₀) (E := M₁)).commutes x
    exact Commons.FieldTheory.Galois.natCard_quotient_units_range_norm_eq_of_ringEquiv
      (B := B₀) (E := ↥(⊤ : IntermediateField B₀ M₁)) (B₀ := B₀) (E₀ := M₁)
      (RingEquiv.refl B₀) (IntermediateField.topEquiv (F := B₀) (E := M₁)).toRingEquiv hcomp
  have hcardtop : Nat.card (↥(⊤ : IntermediateField B₀ M₁) ≃ₐ[B₀]
        ↥(⊤ : IntermediateField B₀ M₁)) = Nat.card (M₁ ≃ₐ[B₀] M₁) :=
    Nat.card_congr (AlgEquiv.autCongr (IntermediateField.topEquiv (F := B₀) (E := M₁))).toEquiv
  -- ## Step 6: transport the two cardinals back to the original universe.
  have hq : Nat.card (Bˣ ⧸ MonoidHom.range (Units.map (Algebra.norm B : M →* B)))
      = Nat.card (B₀ˣ ⧸ MonoidHom.range (Units.map (Algebra.norm B₀ : M₁ →* B₀))) :=
    Commons.FieldTheory.Galois.natCard_quotient_units_range_norm_eq_of_ringEquiv
      eB.toRingEquiv eM.toRingEquiv hMcompat
  have hg : Nat.card (↥M ≃ₐ[B] ↥M) = Nat.card (M₁ ≃ₐ[B₀] M₁) :=
    natCard_algEquiv_eq_of_ringEquiv_univ eB.toRingEquiv eM.toRingEquiv hMcompat
  rw [hq, ← hquottest, hkey, hcardtop, ← hg]

end Commons.NumberTheory.NumberField.Completion
