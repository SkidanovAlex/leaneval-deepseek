/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The arithmetic input `LocalFieldInputs ℚ 𝔭 p` in the base case `K = ℚ`

For `K = ℚ` the local field is `κ = ℚ_p` (`p` the prime below `𝔭`, i.e. the residue
characteristic), and the two fields of the structure `NK.LocalInputs.LocalFieldInputs` are
discharged as follows.

* `residue_char`: `p ∈ 𝔪_κ` because `v p = exp (-1) < 1` for the normalised valuation of `ℚ_p`
  (`Commons.NumberTheory.NumberField.Completion.val_prime_adicCompletion_rat`); hence the residue
  of `p` vanishes and the residue field `𝓞_κ/𝔪_κ ≅ 𝔽_p` has characteristic `p`.

* `principal_units_card`: `|U¹/(U¹)^p| = p^{d+δ}` with `d = localDegree ℚ 𝔭 = 1`
  (`NK.LocalInputs.Degree.localDegree_rat`) and `δ = 0` for odd `p`
  (`NK.LocalInputs.Zeta.not_exists_isPrimitiveRoot_rat_adic`, i.e. `ζ_p ∉ ℚ_p`), so the right
  hand side is `p`.  The left hand side is the commons' computation
  `Commons.NumberTheory.NumberField.Completion.natCard_KQ_quot_pow` for the group
  `KQ 𝔭 = ker(residue : 𝒪_κˣ → 𝔽_pˣ)`, which is *definitionally* `NK.LocalInputs.principalUnits ℚ 𝔭`.

The key classical input behind the count is the `p`-adic logarithm/`ℤ_p`-structure of the principal
units: `KQ_pow_range_eq_ker` identifies the `p`-th powers of `U¹` with the kernel of the "leading
term" `θ : U¹ → 𝔽_p`, `1 + πu ↦ ū`, which is surjective with kernel `U²`; the powers of `p` in the
binomial expansion make the count collapse, and `|U¹/(U¹)^p| = |𝔽_p| = p` results from
`θ` being surjective.
-/
import Mathlib
import Submission.NK.LocalInputs.Hints
import Submission.NK.LocalInputs.Zeta.not_exists_isPrimitiveRoot_rat_adic
import Submission.NK.LocalInputs.Degree.localDegree_rat
import Submission.NK.LocalInputs.PowerQuotient.natCard_residueUnits_quot_pow_eq_one

namespace NK.LocalInputs.Zeta

open scoped Classical WithZero
open IsDedekindDomain.HeightOneSpectrum

/-- **The arithmetic input `LocalFieldInputs ℚ 𝔭 p` in the base case `K = ℚ`.**

For an odd prime `p` which is the residue characteristic of the finite prime `𝔭` of `ℚ`, the
local field `ℚ_p = 𝔭.adicCompletion ℚ` satisfies the named arithmetic inputs of
`NK.LocalInputs.LocalFieldInputs`: its residue field has characteristic `p`, and
`|U¹/(U¹)^p| = p` (the case `p ^ (localDegree ℚ 𝔭 + zetaIndicator p ℚ_p) = p ^ (1 + 0) = p`). -/
theorem localFieldInputs_rat
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ)) {p : ℕ}
    (hp : p.Prime) (hodd : p ≠ 2)
    (hprim : (Rat.HeightOneSpectrum.primesEquiv 𝔭).1 = p) :
    NK.LocalInputs.LocalFieldInputs ℚ 𝔭 p := by
  -- `p` is the prime below `𝔭`, so that the normalised valuation of `ℚ_p` takes value `exp (-1)`
  -- on `p`, and the residue field has cardinality `p`.
  have hmem : (p : NumberField.RingOfIntegers ℚ) ∈ 𝔭.asIdeal :=
    Commons.NumberTheory.NumberField.mem_of_primesEquiv_eq 𝔭 p hp (Subtype.ext hprim)
  have hvalp : Valued.v (R := 𝔭.adicCompletion ℚ) (Γ₀ := Zstar0)
      ((p : ℚ) : 𝔭.adicCompletion ℚ) = WithZero.exp (-1 : ℤ) :=
    Commons.NumberTheory.NumberField.Completion.val_prime_adicCompletion_rat hp 𝔭 hmem
  have hres : Nat.card (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers ℚ)) = p := by
    rw [Commons.NumberTheory.NumberField.residueCard_adicCompletion_eq_absNorm,
      Commons.NumberTheory.NumberField.Set.absNorm_eq_primesEquiv]
    exact_mod_cast hprim
  refine ⟨hp, ?_, ?_⟩
  · -- `p` lies in the maximal ideal, so the residue field has characteristic `p`.
    have hpm : (p : 𝔭.adicCompletionIntegers ℚ) ∈
        IsLocalRing.maximalIdeal (𝔭.adicCompletionIntegers ℚ) := by
      rw [Commons.NumberTheory.NumberField.adicCompletionIntegers_mem_maximalIdeal_iff_valued_lt_one]
      have hcoe : ((p : 𝔭.adicCompletionIntegers ℚ) : 𝔭.adicCompletion ℚ)
          = ((p : ℚ) : 𝔭.adicCompletion ℚ) := by push_cast; rfl
      rw [hcoe, hvalp, ← WithZero.exp_zero (M := ℤ)]
      exact WithZero.exp_lt_exp.mpr (by norm_num)
    have hpres : (p : IsLocalRing.ResidueField (𝔭.adicCompletionIntegers ℚ)) = 0 := by
      have h1 : IsLocalRing.residue (𝔭.adicCompletionIntegers ℚ)
          (p : 𝔭.adicCompletionIntegers ℚ) = 0 :=
        (IsLocalRing.residue_eq_zero_iff (p : 𝔭.adicCompletionIntegers ℚ)).mpr hpm
      simpa using h1
    exact (CharP.charP_iff_prime_eq_zero hp).mpr hpres
  · -- `|U¹/(U¹)^p| = p`: the commons' count for `KQ 𝔭 = principalUnits ℚ 𝔭`, together with
    -- `localDegree ℚ 𝔭 = 1` and `ζ_p ∉ ℚ_p`.
    have hKQ :=
      Commons.NumberTheory.NumberField.Completion.natCard_KQ_quot_pow 𝔭 p hp hodd hvalp hres
    have hzeta : NK.LocalInputs.zetaIndicator p (𝔭.adicCompletion ℚ) = 0 :=
      (NK.LocalInputs.zetaIndicator_eq_zero_iff p _).mpr
        (NK.LocalInputs.Zeta.not_exists_isPrimitiveRoot_rat_adic 𝔭 hp hodd hprim)
    have hld : NK.LocalInputs.localDegree ℚ 𝔭 = 1 :=
      NK.LocalInputs.Degree.localDegree_rat 𝔭
    rw [show NK.LocalInputs.principalUnits ℚ 𝔭
        = Commons.NumberTheory.NumberField.Completion.KQ 𝔭 from rfl, hKQ, hld, hzeta]
    norm_num

end NK.LocalInputs.Zeta
