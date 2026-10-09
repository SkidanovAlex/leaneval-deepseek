import Mathlib
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute

open Polynomial

/-- **The field `k(ζ_p)` is finite Galois over `k` of degree coprime to `p`.**

For a prime `p` and a primitive `p`-th root of unity `ζ` in an algebraically closed field `Ω`
over a number field `k`, the intermediate field `k(ζ) ⊆ Ω` is a finite Galois extension of `k`
whose degree divides `p - 1` (hence is coprime to `p`).

Reviewers confirmed the statement and pointed to the Mathlib ingredients:
`IsPrimitiveRoot.intermediateField_adjoin_isCyclotomicExtension` (available since `Ω` is an
algebraic closure, so `Algebra.IsIntegral k Ω`), `IsCyclotomicExtension.isGalois`,
`IsCyclotomicExtension.finiteDimensional`, and `IsPrimitiveRoot.minpoly_dvd_cyclotomic` together
with `Nat.totient p = p - 1` for the coprimality. -/
theorem adjoin_primitiveRoot_isGalois_coprime (p : ℕ) [Fact p.Prime] (k Ω : Type)
    [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) :
    IsGalois k (IntermediateField.adjoin k ({ζ} : Set Ω)) ∧
    FiniteDimensional k (IntermediateField.adjoin k ({ζ} : Set Ω)) ∧
    Nat.Coprime (Module.finrank k (IntermediateField.adjoin k ({ζ} : Set Ω))) p := by
  have hp : p.Prime := Fact.out
  have hppos : 0 < p := hp.pos
  have hpne : NeZero p := ⟨hp.ne_zero⟩
  -- `Ω` is an algebraic closure of `k`, hence algebraic (and so integral) over `k`.
  have hintg : Algebra.IsIntegral k Ω := Algebra.IsAlgebraic.isIntegral
  -- `k(ζ)` is a `{p}`-cyclotomic extension of `k`.
  have hcyclo : IsCyclotomicExtension {p} k (IntermediateField.adjoin k ({ζ} : Set Ω)) :=
    hζ.intermediateField_adjoin_isCyclotomicExtension k
  refine ⟨IsCyclotomicExtension.isGalois {p} k _,
    IsCyclotomicExtension.finiteDimensional {p} k _, ?_⟩
  -- The degree is `natDegree (minpoly k ζ)`, and `minpoly k ζ ∣ cyclotomic p k`,
  -- whose degree is `p.totient = p - 1`.
  have hint : IsIntegral k ζ := hintg.isIntegral ζ
  rw [IntermediateField.adjoin.finrank hint]
  have hdvd : minpoly k ζ ∣ cyclotomic p k := by
    rw [minpoly.dvd_iff]
    rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, Polynomial.map_cyclotomic,
      ← Polynomial.IsRoot.def]
    exact hζ.isRoot_cyclotomic hppos
  have hle : (minpoly k ζ).natDegree ≤ p - 1 := by
    calc (minpoly k ζ).natDegree ≤ (cyclotomic p k).natDegree :=
          Polynomial.natDegree_le_of_dvd hdvd (cyclotomic_ne_zero p k)
      _ = p.totient := Polynomial.natDegree_cyclotomic p k
      _ = p - 1 := Nat.totient_prime hp
  have hpos : 0 < (minpoly k ζ).natDegree := minpoly.natDegree_pos hint
  -- `0 < n ≤ p - 1 < p` with `p` prime forces `n` and `p` to be coprime.
  rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hp]
  intro hd
  have := Nat.le_of_dvd hpos hd
  omega

end Work.SSGRoute
