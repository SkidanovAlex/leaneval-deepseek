import Mathlib
import Submission.Work.Defs.Basic
import Submission.Work.Tower.Chebotarev.Defs
import Submission.Work.Tower.Chebotarev.exists_prime_splits
import Submission.Work.Tower.Chebotarev.isGalois_sup_adjoin_I
import Submission.Work.Tower.Chebotarev.splits_of_algebra
import Submission.Work.Tower.Chebotarev.mod_four_eq_one_of_splits
import Submission.Work.Tower.Chebotarev.splits_to_splitsCompletely

/-!
# The elementary split-prime theorem, with the congruence `q ≡ 1 (mod 4)`

This is the main result of the area: for every finite Galois extension `N/ℚ`, every finite set
`B` of natural numbers and every bound `n`, there is a prime `q > n` with `q ∉ B`, `q ≡ 1 (mod 4)`
which splits completely in `N`.

The proof passes to the compositum `M = N·ℚ(i)` inside `ℂ`: primes splitting completely in `M`
splitting completely in `N` (descent along a finite extension of number fields) and satisfy
`q ≡ 1 (mod 4)` because `i ∈ M` is an algebraic integer whose image in the residue field `𝔽_q`
is a square root of `-1`.  The existence of such a prime in `M` is the elementary
Chebotarev-lite theorem `Work.Tower.exists_prime_splits`.
-/

open NumberField Ideal Polynomial IntermediateField
open scoped Classical nonZeroDivisors NumberField

namespace Work
namespace Tower

/-- For every finite Galois extension `N/ℚ`, every finite set `B` of natural numbers and every
bound `n`, there is a prime `q > n` with `q ∉ B`, `q ≡ 1 (mod 4)`, splitting completely in `N`. -/
theorem exists_prime_split_completely_mod4 (N : Type) [Field N] [NumberField N] [IsGalois ℚ N]
    (B : Finset ℕ) (n : ℕ) :
    ∃ q : ℕ, Nat.Prime q ∧ n < q ∧ q ∉ B ∧ q % 4 = 1 ∧ Work.Defs.SplitsCompletely q N := by
  -- an embedding of `N` into `ℂ`
  let φ : N →ₐ[ℚ] ℂ := IsAlgClosed.lift
  -- the compositum `ℚ(i) · φ(N)` inside `ℂ`, a finite Galois extension of `ℚ`
  let M : IntermediateField ℚ ℂ := ℚ⟮Complex.I⟯ ⊔ φ.fieldRange
  have hIint : IsIntegral ℚ (Complex.I : ℂ) := by
    refine IsIntegral.of_pow (n := 2) (by norm_num) ?_
    rw [Complex.I_sq]
    exact (isIntegral_one : IsIntegral ℚ (1 : ℂ)).neg
  haveI : FiniteDimensional ℚ ↥(ℚ⟮Complex.I⟯ : IntermediateField ℚ ℂ) :=
    adjoin.finiteDimensional hIint
  haveI : FiniteDimensional ℚ ↥φ.fieldRange :=
    (AlgHom.equivFieldRange φ).toLinearEquiv.finiteDimensional
  haveI : FiniteDimensional ℚ ↥M := finiteDimensional_sup _ _
  haveI : NumberField ↥M := ⟨⟩
  haveI : IsGalois ℚ ↥M := Chebotarev.isGalois_sup_adjoin_I φ
  -- the elementary split-prime theorem applied to the compositum, avoiding `2` as well
  obtain ⟨q, hq, hqn, hqB, hqM⟩ := exists_prime_splits ↥M (B ∪ {2}) (max n 4)
  have hnq : n < q := lt_of_le_of_lt (le_max_left n 4) hqn
  have hqB' : q ∉ B := fun h => hqB (by simp [h])
  have hq2 : q ≠ 2 := fun h => hqB (by simp [h])
  -- a prime of `𝓞 ↥M` above `q`
  haveI : Fact (Nat.Prime q) := ⟨hq⟩
  obtain ⟨P⟩ := Ideal.nonempty_primesOver (R := ℤ) (S := 𝓞 ↥M) (Ideal.span {(q : ℤ)})
  have hPprime : P.1.IsPrime := inferInstance
  have hPq : (q : 𝓞 ↥M) ∈ P.1 := by
    have hne : P.1 ≠ ⊤ := hPprime.ne_top
    have hprime : Prime (q : ℤ) := Nat.prime_iff_prime_int.mp hq
    have hlies : P.1.LiesOver (Ideal.span {(q : ℤ)}) := inferInstance
    have := (Ideal.liesOver_span_iff hne hprime).mp hlies
    simpa using this
  -- the algebraic integer `i` of `M`
  let y : ↥(ℚ⟮Complex.I⟯ : IntermediateField ℚ ℂ) := ⟨Complex.I, mem_adjoin_simple_self ℚ Complex.I⟩
  have hysq : y * y = -1 := by
    apply Subtype.ext
    show Complex.I * Complex.I = ((-1 : ↥(ℚ⟮Complex.I⟯ : IntermediateField ℚ ℂ)) : ℂ)
    rw [Subalgebra.coe_neg, Subalgebra.coe_one]
    simpa using Complex.I_mul_I
  let x : ↥M := (IntermediateField.inclusion (le_sup_left : _ ≤ M)) y
  have hxsq : x * x = -1 := by
    have h := congrArg
      (IntermediateField.inclusion (le_sup_left : (ℚ⟮Complex.I⟯ : IntermediateField ℚ ℂ) ≤ M)) hysq
    simpa [map_mul, map_neg, map_one, x] using h
  let u : 𝓞 ↥M := ⟨x, by
    refine IsIntegral.of_pow (n := 2) (by norm_num) ?_
    rw [pow_two, hxsq]
    exact (isIntegral_one : IsIntegral ℤ (1 : ↥M)).neg⟩
  have hu : u * u = -1 := by
    apply Subtype.ext
    change ((u : ↥M) * (u : ↥M) : ↥M) = (-1 : ↥M)
    exact hxsq
  -- `q ≡ 1 (mod 4)` because `-1` is a square in the residue field `𝔽_q`
  have hmod : q % 4 = 1 := Chebotarev.mod_four_eq_one_of_splits hq hq2 hqM hPprime hPq hu
  -- descend from the compositum back to `N`
  let ψ : N →ₐ[ℚ] ↥M := (IntermediateField.inclusion le_sup_right).comp
    (AlgHom.codRestrict φ φ.fieldRange.toSubalgebra fun x => AlgHom.mem_fieldRange.mpr ⟨x, rfl⟩)
  letI : Algebra N ↥M := ψ.toRingHom.toAlgebra
  haveI : IsScalarTower ℚ N ↥M := inferInstance
  haveI : Module.Finite N ↥M := Module.Finite.of_restrictScalars_finite ℚ N ↥M
  have hN : Splits q N := Chebotarev.splits_of_algebra hqM
  exact ⟨q, hq, hnq, hqB', hmod, Chebotarev.splits_to_splitsCompletely hN⟩

end Tower
end Work
