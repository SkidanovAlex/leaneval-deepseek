import Mathlib
import Submission.Work.CY3Stab.Prod.height_map_mvPolynomial

/-!
# `Work.CY3Stab.Prod.isPrime_map_includeRight_tensor`

Primality and contraction properties of the extension `𝔭 · (𝕜[X_σ] ⊗[𝕜] A)` of a prime ideal `𝔭`
of a `𝕜`-algebra `A` to the tensor product `B = 𝕜[X_σ] ⊗[𝕜] A`.

## Mathematical content

Write `S = 𝕜[X_σ]` and `B = S ⊗[𝕜] A`.  The tensor product is a polynomial ring over `A` and, more
importantly for what follows, reducing coefficients modulo `𝔭` realises `B ⧸ (𝔭 · B)` as
`(A ⧸ 𝔭)[X_σ]`:

* `φ : B → S ⊗[𝕜] (A ⧸ 𝔭)`, `s ⊗ a ↦ s ⊗ mk a`, is `Algebra.TensorProduct.map (AlgHom.id) (mkₐ)`;
  by right exactness of the tensor product (`Algebra.TensorProduct.lTensor_ker`) its kernel is
  exactly `𝔭 · B`.
* `S ⊗[𝕜] (A ⧸ 𝔭) ≃ₐ[𝕜] (A ⧸ 𝔭)[X_σ]` is the tensor/`MvPolynomial` identification
  `scalarTensorMvPolynomialAlgEquiv` (composition of `Algebra.TensorProduct.comm` with Mathlib's
  `MvPolynomial.algebraTensorAlgEquiv`); it sends `includeRight c` to `C c` and `includeLeft x` to
  `MvPolynomial.map (algebraMap 𝕜 (A ⧸ 𝔭)) x`.

Composing gives `ψ : B → (A ⧸ 𝔭)[X_σ]` with `RingHom.ker ψ = 𝔭 · B`.  Since `A ⧸ 𝔭` is a domain,
so is `(A ⧸ 𝔭)[X_σ]`, and `𝔭 · B` is prime (`RingHom.ker_isPrime`).  The two contraction statements
follow from the two evaluation formulas: `ψ ∘ includeRight = C ∘ mk` with `C` injective, and
`ψ ∘ includeLeft = map (algebraMap 𝕜 (A ⧸ 𝔭))` with `map` of an injective coefficient map injective
(the residue field of the domain `A ⧸ 𝔭` contains `𝕜`, so `𝕜 → A ⧸ 𝔭` is injective).
-/

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Work.CY3Stab.Prod

open TensorProduct

/-- **The tensor product of the polynomial algebra `𝕜[X_σ]` with an algebra `N` is `N[X_σ]`.**
Explicitly `scalarTensorMvPolynomialAlgEquiv 𝕜 σ N (x ⊗ₜ c) = c • MvPolynomial.map (algebraMap 𝕜 N) x`.

This is Mathlib's `MvPolynomial.algebraTensorAlgEquiv` with the two tensor factors interchanged. -/
noncomputable def scalarTensorMvPolynomialAlgEquiv (𝕜 : Type) [CommSemiring 𝕜] (σ : Type) (N : Type)
    [CommSemiring N] [Algebra 𝕜 N] :
    MvPolynomial σ 𝕜 ⊗[𝕜] N ≃ₐ[𝕜] MvPolynomial σ N :=
  (Algebra.TensorProduct.comm 𝕜 N (MvPolynomial σ 𝕜)).symm.trans
    (AlgEquiv.restrictScalars 𝕜 (MvPolynomial.algebraTensorAlgEquiv 𝕜 N))

/-- `scalarTensorMvPolynomialAlgEquiv` sends `1 ⊗ₜ c` (i.e. `includeRight c`) to the constant
polynomial `C c`. -/
lemma scalarTensorMvPolynomialAlgEquiv_includeRight (𝕜 : Type) [CommSemiring 𝕜] (σ : Type)
    (N : Type) [CommSemiring N] [Algebra 𝕜 N] (c : N) :
    scalarTensorMvPolynomialAlgEquiv 𝕜 σ N
        (Algebra.TensorProduct.includeRight (R := 𝕜) (A := MvPolynomial σ 𝕜) (B := N) c)
      = MvPolynomial.C c := by
  simp only [scalarTensorMvPolynomialAlgEquiv, AlgEquiv.trans_apply,
    AlgEquiv.restrictScalars_apply, Algebra.TensorProduct.comm_symm_tmul,
    Algebra.TensorProduct.includeRight_apply, MvPolynomial.algebraTensorAlgEquiv_tmul, map_one]
  rw [MvPolynomial.smul_eq_C_mul, mul_one]

/-- `scalarTensorMvPolynomialAlgEquiv` sends `x ⊗ₜ 1` (i.e. `includeLeft x`) to the polynomial
obtained from `x` by extending scalars along `𝕜 → N`. -/
lemma scalarTensorMvPolynomialAlgEquiv_includeLeft (𝕜 : Type) [CommSemiring 𝕜] (σ : Type)
    (N : Type) [CommSemiring N] [Algebra 𝕜 N] (x : MvPolynomial σ 𝕜) :
    scalarTensorMvPolynomialAlgEquiv 𝕜 σ N
        (Algebra.TensorProduct.includeLeft (R := 𝕜) (S := 𝕜) (A := MvPolynomial σ 𝕜) (B := N) x)
      = MvPolynomial.map (algebraMap 𝕜 N) x := by
  simp only [scalarTensorMvPolynomialAlgEquiv, AlgEquiv.trans_apply,
    AlgEquiv.restrictScalars_apply, Algebra.TensorProduct.includeLeft_apply,
    Algebra.TensorProduct.comm_symm_tmul, MvPolynomial.algebraTensorAlgEquiv_tmul]
  simp

/-- **Primality and contractions of `𝔭 · (𝕜[X_σ] ⊗[𝕜] A)`.**
For a field `𝕜`, a `𝕜`-algebra `A` and a prime `𝔭 ≤ A`: the extension `𝔭 · (𝕜[X_σ] ⊗[𝕜] A)` of `𝔭`
along `includeRight` is prime, it contracts back to `𝔭` along `includeRight`, and it contracts to
`⊥` along `includeLeft` from `MvPolynomial σ 𝕜`.

Route: `B = 𝕜[X_σ] ⊗[𝕜] A ≅ A[X_σ]` (via `MvPolynomial.algebraTensorAlgEquiv` composed with
`Algebra.TensorProduct.comm`), `𝔭 · B` is the kernel of `B → MvPolynomial σ (A ⧸ 𝔭)` (a polynomial
ring over the domain `A ⧸ 𝔭`), and the contraction statements use that `𝕜[X_σ] → (A ⧸ 𝔭)[X_σ]` and
`A ⧸ 𝔭 → (A ⧸ 𝔭)[X_σ]` are injective.  The corresponding `MvPolynomial`-form lemmas
(`Work.CY3Stab.Prod.isPrime_map_algebraMap`, `comap_map_algebraMap_eq` in
`Submission/Work/CY3Stab/Prod/height_map_mvPolynomial.lean`), or their proofs, may be reused
(that module is `depends_on`). -/
theorem isPrime_map_includeRight_tensor (𝕜 : Type) [Field 𝕜] (σ : Type) (A : Type) [CommRing A]
    [Algebra 𝕜 A] (𝔭 : Ideal A) [𝔭.IsPrime] :
    (Ideal.map (Algebra.TensorProduct.includeRight (R := 𝕜) (A := MvPolynomial σ 𝕜) (B := A)).toRingHom
        𝔭).IsPrime ∧
      (Ideal.map (Algebra.TensorProduct.includeRight (R := 𝕜) (A := MvPolynomial σ 𝕜) (B := A)).toRingHom
        𝔭).comap (Algebra.TensorProduct.includeRight (R := 𝕜) (A := MvPolynomial σ 𝕜) (B := A)).toRingHom = 𝔭 ∧
      (Ideal.map (Algebra.TensorProduct.includeRight (R := 𝕜) (A := MvPolynomial σ 𝕜) (B := A)).toRingHom
        𝔭).comap (Algebra.TensorProduct.includeLeftRingHom (R := 𝕜) (A := MvPolynomial σ 𝕜) (B := A)) = ⊥ := by
  haveI : IsDomain (A ⧸ 𝔭) := Ideal.Quotient.isDomain 𝔭
  have hC : Function.Injective (MvPolynomial.C : (A ⧸ 𝔭) → MvPolynomial σ (A ⧸ 𝔭)) :=
    MvPolynomial.C_injective σ (A ⧸ 𝔭)
  have hmap : Function.Injective (MvPolynomial.map (σ := σ) (algebraMap 𝕜 (A ⧸ 𝔭))) :=
    MvPolynomial.map_injective (σ := σ) _ (FaithfulSMul.algebraMap_injective 𝕜 (A ⧸ 𝔭))
  -- Reduction of the coefficients modulo `𝔭`.
  let φ : MvPolynomial σ 𝕜 ⊗[𝕜] A →ₐ[𝕜] MvPolynomial σ 𝕜 ⊗[𝕜] (A ⧸ 𝔭) :=
    Algebra.TensorProduct.map (AlgHom.id 𝕜 (MvPolynomial σ 𝕜)) (Ideal.Quotient.mkₐ 𝕜 𝔭)
  -- Its kernel is `𝔭 · B`, by right exactness of the tensor product.
  have hkerφ : RingHom.ker φ =
      Ideal.map (Algebra.TensorProduct.includeRight (R := 𝕜) (A := MvPolynomial σ 𝕜) (B := A)).toRingHom 𝔭 := by
    show RingHom.ker (Algebra.TensorProduct.map (AlgHom.id 𝕜 (MvPolynomial σ 𝕜))
        (Ideal.Quotient.mkₐ 𝕜 𝔭)) = _
    rw [Algebra.TensorProduct.lTensor_ker (R := 𝕜) (A := MvPolynomial σ 𝕜) (C := A) (D := A ⧸ 𝔭)
      (g := Ideal.Quotient.mkₐ 𝕜 𝔭) Ideal.Quotient.mk_surjective,
      AlgHom.ker_coe (Ideal.Quotient.mkₐ 𝕜 𝔭), Ideal.Quotient.mkₐ_ker]
    rfl
  -- The composite with `S ⊗[𝕜] (A ⧸ 𝔭) ≅ (A ⧸ 𝔭)[X_σ]`, whose target is a domain.
  let ψ : MvPolynomial σ 𝕜 ⊗[𝕜] A →ₐ[𝕜] MvPolynomial σ (A ⧸ 𝔭) :=
    (scalarTensorMvPolynomialAlgEquiv 𝕜 σ (A ⧸ 𝔭)).toAlgHom.comp φ
  have hkerψ : RingHom.ker ψ = RingHom.ker φ := by
    ext x
    rw [RingHom.mem_ker, RingHom.mem_ker]
    show (scalarTensorMvPolynomialAlgEquiv 𝕜 σ (A ⧸ 𝔭)) (φ x) = 0 ↔ φ x = 0
    rw [← map_zero (scalarTensorMvPolynomialAlgEquiv 𝕜 σ (A ⧸ 𝔭)),
      (scalarTensorMvPolynomialAlgEquiv 𝕜 σ (A ⧸ 𝔭)).injective.eq_iff]
  refine ⟨?_, ?_, ?_⟩
  · -- `𝔭 · B = ker ψ` is prime.
    rw [← hkerφ, ← hkerψ]
    exact RingHom.ker_isPrime ψ
  · -- `(𝔭 · B) ∩ A = 𝔭`, because `A ⧸ 𝔭 → (A ⧸ 𝔭)[X_σ]` is injective.
    ext x
    rw [Ideal.mem_comap, ← hkerφ, RingHom.mem_ker]
    have h1 : φ ((Algebra.TensorProduct.includeRight (R := 𝕜) (A := MvPolynomial σ 𝕜) (B := A)).toRingHom x)
        = (Algebra.TensorProduct.includeRight (R := 𝕜) (A := MvPolynomial σ 𝕜) (B := A ⧸ 𝔭))
            (Ideal.Quotient.mk 𝔭 x) := by
      rw [show (Algebra.TensorProduct.includeRight (R := 𝕜) (A := MvPolynomial σ 𝕜) (B := A)).toRingHom x
          = (Algebra.TensorProduct.includeRight (R := 𝕜) (A := MvPolynomial σ 𝕜) (B := A)) x from rfl]
      exact AlgHom.congr_fun (Algebra.TensorProduct.map_comp_includeRight
        (AlgHom.id 𝕜 (MvPolynomial σ 𝕜)) (Ideal.Quotient.mkₐ 𝕜 𝔭)) x
    rw [h1]
    have hinj : ∀ c : A ⧸ 𝔭,
        ((Algebra.TensorProduct.includeRight (R := 𝕜) (A := MvPolynomial σ 𝕜) (B := A ⧸ 𝔭)) c = 0) ↔
          c = 0 := by
      intro c
      constructor
      · intro h
        have hh := congrArg (scalarTensorMvPolynomialAlgEquiv 𝕜 σ (A ⧸ 𝔭)) h
        rw [map_zero, scalarTensorMvPolynomialAlgEquiv_includeRight] at hh
        exact hC (by simpa using hh)
      · intro h
        rw [h, map_zero]
    rw [hinj, Ideal.Quotient.eq_zero_iff_mem]
  · -- `(𝔭 · B) ∩ 𝕜[X_σ] = ⊥`, because `𝕜[X_σ] → (A ⧸ 𝔭)[X_σ]` is injective.
    ext x
    rw [Ideal.mem_comap, ← hkerφ, RingHom.mem_ker, Ideal.mem_bot]
    have h1 : φ ((Algebra.TensorProduct.includeLeftRingHom (R := 𝕜) (A := MvPolynomial σ 𝕜) (B := A)) x)
        = (Algebra.TensorProduct.includeLeft (R := 𝕜) (S := 𝕜) (A := MvPolynomial σ 𝕜)
            (B := A ⧸ 𝔭)) x := by
      rw [show (Algebra.TensorProduct.includeLeftRingHom (R := 𝕜) (A := MvPolynomial σ 𝕜) (B := A)) x
          = (Algebra.TensorProduct.includeLeft (R := 𝕜) (S := 𝕜) (A := MvPolynomial σ 𝕜)
              (B := A)) x from rfl]
      exact AlgHom.congr_fun (Algebra.TensorProduct.map_comp_includeLeft
        (AlgHom.id 𝕜 (MvPolynomial σ 𝕜)) (Ideal.Quotient.mkₐ 𝕜 𝔭)) x
    rw [h1]
    have hinj : ∀ y : MvPolynomial σ 𝕜,
        ((Algebra.TensorProduct.includeLeft (R := 𝕜) (S := 𝕜) (A := MvPolynomial σ 𝕜)
            (B := A ⧸ 𝔭)) y = 0) ↔ y = 0 := by
      intro y
      constructor
      · intro h
        have hh := congrArg (scalarTensorMvPolynomialAlgEquiv 𝕜 σ (A ⧸ 𝔭)) h
        rw [map_zero, scalarTensorMvPolynomialAlgEquiv_includeLeft] at hh
        exact hmap (by simpa using hh)
      · intro h
        rw [h, map_zero]
    exact hinj x

end Work.CY3Stab.Prod
