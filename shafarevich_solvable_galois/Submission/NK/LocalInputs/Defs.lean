/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# `NK.LocalInputs`: the vocabulary of the local arithmetic inputs

This file fixes the vocabulary in which the local arithmetic inputs of the
Neukirch–Uchida local-invariance chapter are stated.

Throughout, `K` is a number field, `𝔭` a finite prime of `K`, and

  `κ = 𝔭.adicCompletion K`

the corresponding `p`-adic field (with `p` the residue characteristic of `𝔭`).  The
definitions here are

* `primeBelow K 𝔭` — the rational prime `𝔭 ∩ ℤ`, as a height-one prime of `𝓞 ℚ`;
* `localDegree K 𝔭` — the absolute degree `[κ : ℚ_p]` of the completion, computed as the
  `ℚ_p`-dimension of `κ` (i.e. `Module.finrank` over the `p`-adic field `(primeBelow K 𝔭).adicCompletion ℚ`,
  with the algebra structure induced by `adicCompletionMap`);
* `principalUnits K 𝔭` — the group `U¹ = 1 + 𝔪` of principal units of `κ`, as the kernel of the
  residue map on `𝒪_κˣ`;
* `zetaIndicator p κ` — the indicator `δ ∈ {0,1}` of "`ζ_p ∈ κ`".

The definitions are chosen so that the *statements* of the arithmetic inputs (see
`NK.LocalInputs.Inputs`) are unconditional propositions about these objects, with no
`p`-adic field structure theory assumed anywhere.
-/
import Mathlib
import Submission.NK.LocalAnabelian.All
import Submission.Commons.RingTheory.Henselian.adicCompletionMap_liesOver
import Submission.Commons.NumberTheory.NumberField.Completion.mem_ker_units_residue_adicCompletion_iff
import Submission.Commons.NumberTheory.NumberField.Completion.surjective_units_residue_adicCompletion
import Submission.Commons.NumberTheory.NumberField.Completion.natCard_powerQuotient_adicCompletion_rat_units
import Submission.Commons.NumberTheory.NumberField.residueCard_adicCompletion_eq_absNorm
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open scoped Classical
open IsDedekindDomain.HeightOneSpectrum

namespace NK.LocalInputs

noncomputable section

/-- **The rational prime below a finite prime.**  For a finite prime `𝔭` of a number field `K`,
`primeBelow K 𝔭` is the height-one prime ideal `𝔭 ∩ ℤ` of `ℤ = 𝓞 ℚ`; this is the prime `p`
whose `p`-adic completion `ℚ_p` sits inside the completion `K_𝔭`. -/
noncomputable def primeBelow (K : Type*) [Field K] [NumberField K]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ) :=
  IsDedekindDomain.HeightOneSpectrum.ofPrime
    (p := Ideal.under (NumberField.RingOfIntegers ℚ) 𝔭.asIdeal) (by
      refine Ideal.prime_of_isPrime ?_ (inferInstance : (Ideal.under _ 𝔭.asIdeal).IsPrime)
      exact Ideal.under_ne_bot (NumberField.RingOfIntegers ℚ) 𝔭.ne_bot)

/-- The underlying ideal of `primeBelow`. -/
theorem primeBelow_asIdeal (K : Type*) [Field K] [NumberField K]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    (primeBelow K 𝔭).asIdeal = Ideal.under (NumberField.RingOfIntegers ℚ) 𝔭.asIdeal := rfl

/-- The defining property of `primeBelow`: the prime `𝔭` lies over it. -/
theorem primeBelow_liesOver (K : Type*) [Field K] [NumberField K]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    𝔭.asIdeal.LiesOver (primeBelow K 𝔭).asIdeal :=
  Ideal.LiesOver.mk (primeBelow_asIdeal K 𝔭)

/-- The rational prime below `𝔭`, as a natural number (via `Rat.HeightOneSpectrum.primesEquiv`). -/
noncomputable def primeBelowNat (K : Type*) [Field K] [NumberField K]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) : ℕ :=
  (Rat.HeightOneSpectrum.primesEquiv (primeBelow K 𝔭)).1

/-- **The absolute degree `[K_𝔭 : ℚ_p]` of a finite prime.**

`κ = 𝔭.adicCompletion K` is a finite extension of the `p`-adic field `ℚ_p` (where `p` is the
rational prime below `𝔭`), and `localDegree K 𝔭` is its degree, computed as the dimension of `κ`
over `ℚ_p`, using the algebra structure induced by `adicCompletionMap`. -/
noncomputable def localDegree (K : Type*) [Field K] [NumberField K]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) : ℕ :=
  letI := RingHom.toAlgebra
    (Commons.RingTheory.Henselian.adicCompletionMap (primeBelow K 𝔭) 𝔭 (primeBelow_liesOver K 𝔭))
  Module.finrank ((primeBelow K 𝔭).adicCompletion ℚ) (𝔭.adicCompletion K)

/-- **The principal units `U¹ = 1 + 𝔪`** of the local field `κ = K_𝔭`: the kernel of the residue
map on the units of the valuation ring `𝒪_κ`.  Classically `U¹ ≅ ℤ_p^{[κ:ℚ_p]}` when `ζ_p ∉ κ`
and `U¹ ≅ μ_{p^∞}(κ) × ℤ_p^{[κ:ℚ_p]}` in general. -/
noncomputable def principalUnits (K : Type*) [Field K] [NumberField K]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    Subgroup ((𝔭.adicCompletionIntegers K)ˣ) :=
  (Units.map (IsLocalRing.residue (𝔭.adicCompletionIntegers K)).toMonoidHom).ker

/-- The defining property of `principalUnits`: `u ∈ U¹` iff `u - 1` lies in the maximal ideal. -/
theorem mem_principalUnits_iff (K : Type*) [Field K] [NumberField K]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (u : (𝔭.adicCompletionIntegers K)ˣ) :
    u ∈ principalUnits K 𝔭 ↔
      ((u : (𝔭.adicCompletionIntegers K)) - 1) ∈
        IsLocalRing.maximalIdeal (𝔭.adicCompletionIntegers K) :=
  Commons.NumberTheory.NumberField.Completion.mem_ker_units_residue_adicCompletion_iff 𝔭 u

/-- **The indicator `δ` of `ζ_p ∈ κ`**: `1` if `κ` contains a primitive `p`-th root of unity,
`0` otherwise. -/
noncomputable def zetaIndicator (p : ℕ) (κ : Type*) [Field κ] : ℕ :=
  if ∃ ζ : κ, IsPrimitiveRoot ζ p then 1 else 0

/-- `δ` is `0` or `1`. -/
theorem zetaIndicator_le_one (p : ℕ) (κ : Type*) [Field κ] : zetaIndicator p κ ≤ 1 := by
  unfold zetaIndicator
  split <;> omega

/-- `δ = 1` exactly when `κ` contains a primitive `p`-th root of unity. -/
theorem zetaIndicator_eq_one_iff (p : ℕ) (κ : Type*) [Field κ] :
    zetaIndicator p κ = 1 ↔ ∃ ζ : κ, IsPrimitiveRoot ζ p := by
  unfold zetaIndicator
  constructor
  · intro h
    by_contra hc
    rw [if_neg hc] at h
    exact absurd h (by norm_num)
  · intro h
    rw [if_pos h]

/-- `δ = 0` exactly when `κ` contains no primitive `p`-th root of unity. -/
theorem zetaIndicator_eq_zero_iff (p : ℕ) (κ : Type*) [Field κ] :
    zetaIndicator p κ = 0 ↔ ¬ ∃ ζ : κ, IsPrimitiveRoot ζ p := by
  constructor
  · intro h hζ
    rw [(zetaIndicator_eq_one_iff p κ).mpr hζ] at h
    exact one_ne_zero h
  · intro h
    unfold zetaIndicator
    rw [if_neg h]

end

end NK.LocalInputs
