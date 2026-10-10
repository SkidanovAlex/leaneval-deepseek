import Mathlib.NumberTheory.RamificationInertia.Valuation
import Submission.Commons.NumberTheory.NumberField.Completion.exists_unramified_extension_of_inertiaDeg
import Submission.Commons.NumberTheory.NumberField.Completion.isScalarTower_adicCompletion
import Submission.Commons.NumberTheory.NumberField.Completion.liesOver_maximalIdeal_adicCompletionIntegers
import Submission.Commons.NumberTheory.NumberField.Completion.module_finite_adicCompletionIntegers
import Submission.Commons.NumberTheory.NumberField.Completion.natCard_residueField_adicCompletion_eq_pow_inertiaDeg
import Submission.Commons.NumberTheory.NumberField.Completion.val_adicCompletionMap_eq_pow
import Submission.Commons.RingTheory.Henselian.units_mem_pow_of_residue_mem_pow
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# A `p`-th root of a local unit is a local integer

Let `L / K` be an extension of number fields, `Q` a prime of `𝓞 K`, `q` a prime of `𝓞 L` lying
over `Q`, and let `b ∈ Kˣ` be a **local unit at `Q`** (its `Q`-adic valuation is `1`).  If
`α ∈ L` satisfies `α ^ p = b` for a prime `p`, then `α` is integral at `q`.

Mathematically this is immediate from the valuation identity
`v_q (algebraMap K L y) = v_Q (y) ^ e` (`IsDedekindDomain.HeightOneSpectrum.valuation_liesOver`,
combined with `Commons...val_adicCompletionMap_eq_pow`): both sides of `α ^ p = b` are evaluated
in `q.adicCompletion L`, and `v(α) ^ p = v(b) = 1 ^ e = 1` forces `v(α) = 1 ≤ 1` because the value
group `ℤᵐ⁰` has no `p`-torsion (indeed no torsion at all).

This is the input needed to see that a `p`-th root of a local unit is a unit of the local
integers, i.e. that the corresponding Kummer extension is unramified.

The proof is valuation-theoretic and does not use any Galois or Kummer hypothesis beyond
`α ^ p = b`; in particular `p` need only be a prime so that `p ≠ 0`.
-/

set_option linter.style.haveILetI false

open IsDedekindDomain

namespace NK.GlobalCFTdeep.SecondInequality.KummerCase

/-- **A `p`-th root of a local unit is a local integer.**  If `b ∈ Kˣ` is a unit at the prime `Q`
of `𝓞 K` (i.e. `v_Q(b) = 1` in the value group `ℤᵐ⁰`, the normalization used by `Valued.v` on
`Q.adicCompletion K`) and `α ^ p = b` for a prime `p`, then `α` is integral at every prime `q`
of `𝓞 L` lying over `Q`. -/
theorem mem_adicCompletionIntegers_of_pow_eq_unit
    {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] (p : ℕ) (hp : p.Prime)
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (hq : q.asIdeal.LiesOver Q.asIdeal)
    {b : Kˣ} (hb : Valued.v (algebraMap K (Q.adicCompletion K) (b : K)) = 1)
    {α : L} (hα : α ^ p = algebraMap K L (b : K)) :
    algebraMap L (q.adicCompletion L) α ∈ q.adicCompletionIntegers L := by
  haveI : q.asIdeal.LiesOver Q.asIdeal := hq
  -- `b` is a unit at `Q`, read off in the global valuation of `K`
  have hQb : Q.valuation K (b : K) = 1 := by
    rw [← IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation'
      (R := NumberField.RingOfIntegers K) (K := K) Q (b : K)]
    exact hb
  -- hence it is a unit at `q` as well: the `q`-valuation of an element of `K` is a power of its
  -- `Q`-valuation (`valuation_liesOver`), and `1 ^ e = 1`
  have hbq : Valued.v (algebraMap K (q.adicCompletion L) (b : K)) = 1 := by
    have h1 : Valued.v (algebraMap K (q.adicCompletion L) (b : K))
        = q.valuation L (algebraMap K L (b : K)) := by
      rw [IsScalarTower.algebraMap_apply K L (q.adicCompletion L) (b : K)]
      exact IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation'
        (R := NumberField.RingOfIntegers L) (K := L) q (algebraMap K L (b : K))
    rw [h1, ← IsDedekindDomain.HeightOneSpectrum.valuation_liesOver
      (A := NumberField.RingOfIntegers K) (B := NumberField.RingOfIntegers L) L Q q (b : K),
      hQb, one_pow]
  -- the image of `α` in `q.adicCompletion L` satisfies `γ ^ p = (the image of b)`
  have hmap : (algebraMap L (q.adicCompletion L) α) ^ p
      = algebraMap K (q.adicCompletion L) (b : K) := by
    rw [← map_pow, hα]
    exact (IsScalarTower.algebraMap_apply K L (q.adicCompletion L) (b : K)).symm
  -- hence `v α ^ p = v b = 1`
  have hpow : Valued.v (algebraMap L (q.adicCompletion L) α) ^ p = 1 := by
    have h := congrArg Valued.v hmap
    rw [map_pow] at h
    rw [h, hbq]
  -- the value group `ℤᵐ⁰` is torsion free, so `v α ^ p = 1` forces `v α = 1`, in particular
  -- `v α ≤ 1`, which is the desired integrality
  rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers]
  by_contra hle
  rw [not_le] at hle
  have h2 : 1 < Valued.v (algebraMap L (q.adicCompletion L) α) ^ p := one_lt_pow₀ hle hp.ne_zero
  rw [hpow] at h2
  exact lt_irrefl 1 h2

end NK.GlobalCFTdeep.SecondInequality.KummerCase
