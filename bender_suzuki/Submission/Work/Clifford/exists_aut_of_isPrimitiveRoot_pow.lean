import Mathlib

/-!
# `Work.Clifford.exists_aut_of_isPrimitiveRoot_pow`

Given a primitive `n`-th root of unity `ζ : ℂ` and `k` coprime to `n`, there is a ring
automorphism `σ : ℂ ≃+* ℂ` with `σ ζ = ζ ^ k`.

The mathematical content is that `ζ` and `ζ ^ k` are conjugate over `ℚ` (both are roots of the
cyclotomic polynomial `Φₙ`), so there is a `ℚ`-algebra automorphism of `ℚ(ζ)` sending `ζ` to
`ζ ^ k`; this extends to an automorphism of `ℂ` because `ℂ` is an algebraic closure of
`ℚ(ζ)[T]` for a transcendence basis `T` of `ℂ` over `ℚ(ζ)`, and algebraic closures of
isomorphic rings are isomorphic.

The extension step is formalised with `IsAlgClosure.equivOfEquiv`, applied to the (polynomial)
subring `S := ℚ(ζ)[T] ⊆ ℂ`: `ℂ = Frac(S)^alg` is an algebraic closure of `S`, and the automorphism
of `S` sending `ζ ↦ ζ ^ k` and fixing `T` is transported from the coefficient automorphism of
`MvPolynomial ι ℚ(ζ)` via the canonical isomorphism `AlgebraicIndependent.aevalEquiv`.
-/

noncomputable section

open Polynomial

namespace Work.Clifford

theorem exists_aut_of_isPrimitiveRoot_pow {n k : ℕ} (hn : 0 < n) {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ n) (hk : k.Coprime n) :
    ∃ σ : ℂ ≃+* ℂ, σ ζ = ζ ^ k := by
  have hnz : NeZero n := ⟨hn.ne'⟩
  -- The cyclotomic field `A' = ℚ(ζ)` inside `ℂ`.
  let A' : Subalgebra ℚ ℂ := Algebra.adjoin ℚ ({ζ} : Set ℂ)
  have hζm : ζ ∈ A' := Algebra.subset_adjoin (Set.mem_singleton ζ)
  have hζkm : ζ ^ k ∈ A' := Subalgebra.pow_mem _ hζm k
  have hζA' : IsPrimitiveRoot (⟨ζ, hζm⟩ : A') n :=
    (IsPrimitiveRoot.coe_submonoidClass_iff (M := ℂ) (N := A') (ζ := ⟨ζ, hζm⟩)).mp hζ
  have hζk : IsPrimitiveRoot (ζ ^ k) n := hζ.pow_of_coprime k hk
  have hζkA' : IsPrimitiveRoot (⟨ζ ^ k, hζkm⟩ : A') n :=
    (IsPrimitiveRoot.coe_submonoidClass_iff (M := ℂ) (N := A') (ζ := ⟨ζ ^ k, hζkm⟩)).mp hζk
  have hcyc : IsCyclotomicExtension {n} ℚ A' := hζ.adjoin_isCyclotomicExtension ℚ
  have hirr : Irreducible (Polynomial.cyclotomic n ℚ) := Polynomial.cyclotomic.irreducible_rat hn
  have hmin : minpoly ℚ (hζA'.powerBasis ℚ).gen = minpoly ℚ (hζkA'.powerBasis ℚ).gen := by
    rw [IsPrimitiveRoot.powerBasis_gen, IsPrimitiveRoot.powerBasis_gen]
    rw [← hζA'.minpoly_eq_cyclotomic_of_irreducible hirr,
        ← hζkA'.minpoly_eq_cyclotomic_of_irreducible hirr]
  let α : A' ≃ₐ[ℚ] A' := (hζA'.powerBasis ℚ).equivOfMinpoly (hζkA'.powerBasis ℚ) hmin
  have hα : α (⟨ζ, hζm⟩ : A') = ⟨ζ ^ k, hζkm⟩ := by
    have h := PowerBasis.equivOfMinpoly_gen (hζA'.powerBasis ℚ) (hζkA'.powerBasis ℚ) hmin
    rw [IsPrimitiveRoot.powerBasis_gen, IsPrimitiveRoot.powerBasis_gen] at h
    exact h
  -- A transcendence basis `T` of `ℂ` over `ℚ(ζ)`.
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis A' ℂ
  let S : Subalgebra A' ℂ := Algebra.adjoin A' (Set.range (Subtype.val : ↥s → ℂ))
  -- `ℂ` is an algebraic closure of the polynomial ring `S = ℚ(ζ)[T]`.
  have hAlgCl : IsAlgClosure ↥S ℂ :=
    IsAlgClosed.isAlgClosure_of_transcendence_basis (Subtype.val : ↥s → ℂ) hs
  let φ : MvPolynomial ↥s A' ≃ₐ[A'] ↥S := hs.1.aevalEquiv
  let m : MvPolynomial ↥s A' ≃ₐ[ℚ] MvPolynomial ↥s A' := MvPolynomial.mapAlgEquiv ↥s α
  -- Transport `α` to `S` along the identification `S ≅ MvPolynomial ι A'`.
  let β : ↥S ≃+* ↥S := (φ.toRingEquiv).symm.trans (m.toRingEquiv.trans φ.toRingEquiv)
  have hφC : ∀ a : A', ((φ (MvPolynomial.C a) : ↥S) : ℂ) = algebraMap A' ℂ a := by
    intro a
    have h := AlgebraicIndependent.algebraMap_aevalEquiv hs.1 (MvPolynomial.C a)
    simp only [MvPolynomial.aeval_C] at h
    exact h
  have hmC : ∀ a : A', m (MvPolynomial.C a) = MvPolynomial.C (α a) := by
    intro a
    rw [MvPolynomial.mapAlgEquiv_apply, MvPolynomial.map_C]
    rfl
  have hζS : ζ ∈ S := by
    have hmem := Subalgebra.algebraMap_mem S (⟨ζ, hζm⟩ : A')
    simpa using hmem
  have hζkS : ζ ^ k ∈ S := by
    have hmem := Subalgebra.algebraMap_mem S (⟨ζ ^ k, hζkm⟩ : A')
    simpa using hmem
  have hs_eq : (⟨ζ, hζS⟩ : ↥S) = φ (MvPolynomial.C (⟨ζ, hζm⟩ : A')) := by
    apply Subtype.ext
    rw [hφC]
    rfl
  have hβ : β (⟨ζ, hζS⟩ : ↥S) = ⟨ζ ^ k, hζkS⟩ := by
    have hsymm : φ.symm (⟨ζ, hζS⟩ : ↥S) = MvPolynomial.C (⟨ζ, hζm⟩ : A') := by
      rw [hs_eq]
      exact φ.symm_apply_apply _
    calc β (⟨ζ, hζS⟩ : ↥S)
        = φ (m (φ.symm (⟨ζ, hζS⟩ : ↥S))) := rfl
      _ = φ (m (MvPolynomial.C (⟨ζ, hζm⟩ : A'))) := by rw [hsymm]
      _ = φ (MvPolynomial.C (α (⟨ζ, hζm⟩ : A'))) := by rw [hmC]
      _ = φ (MvPolynomial.C (⟨ζ ^ k, hζkm⟩ : A')) := by rw [hα]
      _ = ⟨ζ ^ k, hζkS⟩ := by
            apply Subtype.ext
            rw [hφC]
            rfl
  refine ⟨IsAlgClosure.equivOfEquiv ℂ ℂ β, ?_⟩
  have key := IsAlgClosure.equivOfEquiv_algebraMap (L := ℂ) (M := ℂ) β (⟨ζ, hζS⟩ : ↥S)
  rw [hβ] at key
  simpa using key

end Work.Clifford
