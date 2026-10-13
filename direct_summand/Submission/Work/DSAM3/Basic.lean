import Submission.Work.DSMap.Mix

/-! # DSAM3: model-level almost mathematics (the AM node of the MIX subtree)

`ModSplit P ε ψ I c` (frozen in `Submission/Work/DSMap/Mix.lean`) says that the base-changed unit
`ε : A → P⁰` admits a `D`-linear splitting `D ⊗_A P⁰ → D ⧸ I` modulo `I`, with value `c`, and
killing `d⁻¹`.  This file records the equivalent **`A`-linear** form `ModSplitA`: by tensor-hom
adjunction (extension of scalars `M ↦ D ⊗_A M` is left adjoint to restriction of scalars), giving
a `D`-linear `s : D ⊗_A P⁰ → D ⧸ I` is the same as giving an `A`-linear `t : P⁰ → D ⧸ I`, and the
conditions translate to `t ∘ d⁻¹ = 0` and `t (ε 1) = c`.

The `A`-form is what makes the transport lemmas (AM1–AM3) trivial: composition of `A`-linear maps.
-/

open scoped TensorProduct
open CategoryTheory

namespace Work.DSAM3

universe a

/-- The `A`-linear (adjoint) form of `ModSplit`: a splitting is an `A`-linear map `P⁰ → D ⧸ I`
killing `d⁻¹ : P⁻¹ → P⁰` and sending the unit `ε 1` to `c`. -/
def ModSplitA {A : Type a} [CommRing A] (P : CochainComplex (ModuleCat.{a} A) ℤ)
    (ε : ModuleCat.of A A ⟶ P.X 0) {D : Type a} [CommRing D] (ψ : A →+* D) (I : Ideal D)
    (c : D) : Prop :=
  letI : Algebra A D := ψ.toAlgebra
  ∃ t : P.X 0 →ₗ[A] D ⧸ I,
    t.comp (P.d (-1) 0).hom = 0 ∧ t (ε.hom 1) = Ideal.Quotient.mk I c

/-- Computation rule for the `D`-linear map out of `D ⊗_A M` attached to an `A`-linear `t`. -/
theorem lift_tmul {A : Type a} [CommRing A] {D : Type a} [CommRing D] [Algebra A D]
    {M : Type a} [AddCommMonoid M] [Module A M] {N : Type a} [AddCommMonoid N] [Module A N]
    [Module D N] [IsScalarTower A D N] (t : M →ₗ[A] N) (x : D) (m : M) :
    (TensorProduct.AlgebraTensorModule.lift
        (A := D) (M := D) (N := M) (P := N)
        ({ toFun := fun d => d • t
           map_add' := fun d₁ d₂ => by simp [add_smul]
           map_smul' := fun d₁ d₂ => by simp [mul_smul] } : D →ₗ[D] (M →ₗ[A] N))) (x ⊗ₜ[A] m)
      = x • t m := by
  rw [TensorProduct.AlgebraTensorModule.lift_apply, TensorProduct.lift.tmul]
  rfl

/-- `ModSplit` is the `A`-linear form `ModSplitA` (tensor-hom adjunction for extension of scalars).
The forward direction is restriction of scalars; the backward direction extends scalars by
`d ⊗ m ↦ d • t m`. -/
theorem modSplit_iff_ModSplitA {A : Type a} [CommRing A] (P : CochainComplex (ModuleCat.{a} A) ℤ)
    (ε : ModuleCat.of A A ⟶ P.X 0) {D : Type a} [CommRing D] (ψ : A →+* D) (I : Ideal D)
    (c : D) : DSMap.Mix.ModSplit P ε ψ I c ↔ ModSplitA P ε ψ I c := by
  letI : Algebra A D := ψ.toAlgebra
  constructor
  · intro h
    obtain ⟨s, hs1, hs2⟩ := h
    refine ⟨(LinearMap.restrictScalars A s).comp (TensorProduct.mk A D (P.X 0) (1 : D)), ?_, ?_⟩
    · ext n
      simp only [LinearMap.comp_apply, LinearMap.zero_apply, TensorProduct.mk_apply,
        LinearMap.restrictScalars_apply]
      rw [← LinearMap.baseChange_tmul (f := (P.d (-1) 0).hom) (a := (1 : D)) (x := n)]
      exact hs1 _
    · simpa only [LinearMap.comp_apply, TensorProduct.mk_apply, LinearMap.restrictScalars_apply]
        using hs2
  · rintro ⟨t, ht1, ht2⟩
    set F : D →ₗ[D] (P.X 0 →ₗ[A] D ⧸ I) :=
      { toFun := fun d => d • t
        map_add' := fun d₁ d₂ => by simp [add_smul]
        map_smul' := fun d₁ d₂ => by simp [mul_smul] } with hF
    refine ⟨TensorProduct.AlgebraTensorModule.lift (A := D) (M := D) (N := P.X 0) (P := D ⧸ I) F,
      ?_, ?_⟩
    · intro y
      refine TensorProduct.inductionOn y (fun x n => ?_) (fun y₁ y₂ h₁ h₂ => ?_)
      · rw [LinearMap.baseChange_tmul, lift_tmul]
        have h0 : t ((P.d (-1) 0).hom n) = 0 := by
          have := LinearMap.congr_fun ht1 n
          simpa using this
        rw [h0, smul_zero]
      · simp only [map_add, h₁, h₂, add_zero]
    · rw [lift_tmul, one_smul, ht2]
