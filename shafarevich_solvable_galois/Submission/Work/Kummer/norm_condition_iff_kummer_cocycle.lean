import Mathlib
import Submission.Work.Kummer.Defs
import Submission.Work.Kummer.exists_algEquiv_div_of_norm_eq_one
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

universe u v

namespace Work.Kummer

/-- **The norm condition is equivalent to the existence of a Kummer cocycle.**

Let `L/K` be a finite cyclic Galois extension of degree `n = [L : K]`, and let `ζ ∈ K` be a
primitive `n`-th root of unity.

Then `ζ` is a norm from `L` to `K` if and only if there are a generator `σ` of `Gal(L/K)`, a unit
`η : Lˣ` whose norm is a primitive `n`-th root of unity, and a unit `y : Lˣ` which is *not* an
`n`-th power and satisfies the cocycle relation `σ y / y = η ^ n`.

The forward implication is Hilbert 90 applied to `η ^ n` (whose norm is `ζ ^ n = 1`): the
resulting `y` with `σ y / y = η ^ n` is never an `n`-th power, because `y = v ^ n` would force
`σ v / v = η · ζ ^ i`, and applying the norm to this equation — the norm is invariant under the
Galois action — would give `ζ = 1`, contradicting `1 < n`.  Conversely, a primitive value
`ζ ^ j = N(η)` with `gcd(j, n) = 1` can be powered to `ζ` itself. -/
theorem norm_condition_iff_kummer_cocycle {K : Type u} {L : Type v} [Field K] [Field L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L] [IsCyclic Gal(L/K)]
    {n : ℕ} [NeZero n] {ζ : K} (hζ : IsPrimitiveRoot ζ n) (hn : Module.finrank K L = n)
    (hnpos : 1 < n) :
    (∃ η : Lˣ, Algebra.norm K (η : L) = ζ) ↔
      ∃ (y : Lˣ) (η : Lˣ) (σ : Gal(L/K)), (∀ x : Gal(L/K), x ∈ Subgroup.zpowers σ) ∧
        (σ : L ≃ₐ[K] L) (y : L) / (y : L) = (η : L) ^ n ∧
        (∀ v : Lˣ, v ^ n ≠ y) ∧
        ∃ j : ℕ, ζ ^ j = Algebra.norm K (η : L) ∧ Nat.Coprime j n := by
  constructor
  · rintro ⟨η, hη⟩
    obtain ⟨σ, hσ⟩ := IsCyclic.exists_generator (α := Gal(L/K))
    have hnorm : Algebra.norm K ((η ^ n : Lˣ) : L) = 1 := by
      rw [Units.val_pow_eq_pow_val, map_pow, hη, hζ.pow_eq_one]
    obtain ⟨y, hy⟩ := exists_algEquiv_div_of_norm_eq_one (K := K) (L := L) hσ hnorm
    refine ⟨y, η, σ, hσ, hy.symm, ?_, 1, ?_, Nat.coprime_one_left n⟩
    · intro v hv
      have hvL : (v : L) ^ n = (y : L) := by
        simpa using congrArg (fun u : Lˣ => (u : L)) hv
      have hdiv : (σ : L ≃ₐ[K] L) (y : L) = (η : L) ^ n * (y : L) :=
        (div_eq_iff (Units.ne_zero y)).mp hy.symm
      -- `σ v / (v η)` is an `n`-th root of unity
      have hkey : ((σ : L ≃ₐ[K] L) (v : L) / ((v : L) * (η : L))) ^ n = 1 := by
        rw [div_pow, mul_pow, ← map_pow, hvL, hdiv]
        rw [mul_comm ((y : L)) ((η : L) ^ n)]
        exact div_self (mul_ne_zero (pow_ne_zero n (Units.ne_zero η)) (Units.ne_zero y))
      have hζL : IsPrimitiveRoot (algebraMap K L ζ) n :=
        hζ.map_of_injective (algebraMap K L).injective
      obtain ⟨i, -, hi⟩ := hζL.eq_pow_of_pow_eq_one hkey
      -- hence `σ v = v · η · ζ ^ i`
      have hvu : (σ : L ≃ₐ[K] L) (v : L) =
          (v : L) * (η : L) * (algebraMap K L ζ) ^ i := by
        have h := (eq_div_iff (mul_ne_zero (Units.ne_zero v) (Units.ne_zero η))).mp hi
        rw [← h]; ring
      -- applying the norm gives `N v · ζ = N v`, whence `ζ = 1`
      have hn2 : Algebra.norm K ((σ : L ≃ₐ[K] L) (v : L)) = Algebra.norm K (v : L) :=
        Algebra.norm_eq_of_algEquiv (σ : L ≃ₐ[K] L) (v : L)
      have hn3 : Algebra.norm K ((v : L) * (η : L) * (algebraMap K L ζ) ^ i)
          = Algebra.norm K (v : L) := by
        rw [← hvu]; exact hn2
      rw [map_mul, map_mul, map_pow, Algebra.norm_algebraMap, hn, hη, hζ.pow_eq_one,
        one_pow, mul_one] at hn3
      have hz : ζ = 1 := by
        refine mul_left_cancel₀ (a := Algebra.norm K (v : L))
          (Algebra.norm_ne_zero_iff.mpr (Units.ne_zero v)) ?_
        simpa using hn3
      exact hζ.ne_one hnpos hz
    · simpa using hη.symm
  · rintro ⟨y, η, σ, hσ, hdiv, hnot, j, hj, hcop⟩
    obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime (x := ζ) (n := j) (by rwa [← hζ.eq_orderOf])
    exact ⟨η ^ m, by rw [Units.val_pow_eq_pow_val, map_pow, ← hj, hm]⟩

end Work.Kummer
