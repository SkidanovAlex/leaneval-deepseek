/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Kummer over `κ^{ur}` in Vahlen–Capelli form: `X ^ n - π` is irreducible for odd `n`

The Kummer-theoretic input of the tamely ramified layer is that a uniformiser `π` of a `p`-adic
field `κ = K_𝔭` has no `n`-th root in the maximal unramified extension `κ^{ur}`
(`Tame/UnramifiedNoPow.lean`, `Tame/no_pow_root_adjoin_primitiveRoot.lean`).

`Tame/Kummer.lean` uses this for *prime* `ℓ ≠ p`: `X ^ ℓ - C π` is irreducible over `κ^{ur}`
because a prime degree can only drop through the existence of a root.

For a **composite** odd `n` the naive statement "no `n`-th root" does *not* formally imply
irreducibility of `X ^ n - C π`: one needs Vahlen–Capelli, which reads (for odd `n`, and `κ^{ur}`
of characteristic `0`)

  `X ^ n - C a` is irreducible over `F` iff `a` is not a `p`-th power in `F` for every prime `p ∣ n`,

Mathlib's `Polynomial.X_pow_sub_C_irreducible_of_odd`.  The point of this file is that the Kummer
input is available at *every* prime, uniformly in the prime, with **no coprimality hypothesis on
`n` against the residue characteristic `p`**: the valuation-theoretic proof of
`no_pow_root_adjoin_primitiveRoot` never uses `(n, p) = 1` — only the auxiliary cyclotomic order
`m` is required to be prime to `p`.

Hence:

* `NK.TameStructureDeep.Tame.pow_ne_uniformizer_of_mem_unramifiedClosure`: for **every** `n ≥ 2`
  (coprime to `p` or not) and every `α ∈ κ^{ur}`, `α ^ n ≠ π`;
* `NK.TameStructureDeep.Tame.irreducible_X_pow_sub_C_unramifiedClosure_odd`: for every **odd**
  `n ≠ 0`, `X ^ n - C π` is irreducible over `κ^{ur}`.

The oddness hypothesis is exactly what Vahlen–Capelli in Mathlib requires (`X ^ n - C a` for even
`n` needs the separate `-4` condition, which is not treated in Mathlib).
-/
import Mathlib
import Submission.NK.TameStructureDeep.Tame.Kummer
import Submission.NK.TameStructureDeep.Tame.UnramifiedNoPow
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open scoped Classical
open Polynomial

namespace NK.TameStructureDeep.Tame

variable {K : Type*} [Field K] [NumberField K]
variable (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))

/-- **No `n`-th root of a uniformiser in `κ^{ur}`, without coprimality hypotheses.**

For every `n ≥ 2` — including `n` divisible by the residue characteristic `p` — and every
`α` in the maximal unramified extension `κ^{ur} = κ(μ_{p'}) ⊆ K'`, `α ^ n ≠ π`.

The proof is the one of `no_pow_root_adjoin_primitiveRoot`: an element of `κ^{ur}` lies in a single
cyclotomic layer `κ⟮ζ_m⟯` with `p ∤ m`, and there `α ^ n = π` would force the valuation
`v(α) = exp (-1/n)`, which is impossible since `κ⟮ζ_m⟯` is unramified over `κ` and `v(π) =
exp (-1)`.  Nothing in that argument uses `Nat.Coprime n p`: the root `α` may have any exponent. -/
theorem pow_ne_uniformizer_of_mem_unramifiedClosure {K' : Type*} [Field K']
    [Algebra (𝔭.adicCompletion K) K'] [IsSepClosure (𝔭.adicCompletion K) K']
    {π : 𝔭.adicCompletionIntegers K} (hπ : IsUniformizerAt 𝔭 π) {n : ℕ} (hn : 2 ≤ n)
    {α : K'} (hα : α ∈ NK.LocalAnabelian.unramifiedClosure (κ := 𝔭.adicCompletion K)
      (K' := K') (resCharAt 𝔭)) :
    α ^ n ≠ algebraMap (𝔭.adicCompletion K) K' (π : 𝔭.adicCompletion K) := by
  have hp : (resCharAt 𝔭).Prime := NK.Mine.prime_ringChar_residueField_adicCompletion 𝔭
  obtain ⟨m, ζ, hm, hζ, hαm⟩ :=
    exists_adjoin_primitiveRoot_of_mem_unramifiedClosure (κ := 𝔭.adicCompletion K) (K' := K')
      hp hα
  exact no_pow_root_adjoin_primitiveRoot 𝔭 hπ hn hm hζ ⟨α, hαm⟩

/-- **Kummer over `κ^{ur}` for odd `n`: `X ^ n - C π` is irreducible.**

By Vahlen–Capelli for odd `n` (`Polynomial.X_pow_sub_C_irreducible_of_odd`) it suffices that `π`
is not a `q`-th power in `κ^{ur}` for every prime `q ∣ n`, which is
`pow_ne_uniformizer_of_mem_unramifiedClosure` — valid at *every* prime `q ≥ 2`, whether or not `q`
equals the residue characteristic: the case `n = q` with `q` a prime divisor of `p` is covered as
well, even though naive Kummer theory over `κ^{ur}` is then unavailable (`μ_q ⊄ κ^{ur}`). -/
theorem irreducible_X_pow_sub_C_unramifiedClosure_odd {K : Type*} [Field K] [NumberField K]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    {π : 𝔭.adicCompletionIntegers K} (hπ : NK.TameStructureDeep.Tame.IsUniformizerAt 𝔭 π)
    {K' : Type*} [Field K'] [Algebra (𝔭.adicCompletion K) K']
    [IsSepClosure (𝔭.adicCompletion K) K'] {n : ℕ} (hn : Odd n) (hn0 : n ≠ 0) :
    Irreducible (Polynomial.X ^ n - Polynomial.C
      (NK.TameStructureDeep.Tame.uniformizerInClosure 𝔭 (K' := K') π)) := by
  refine X_pow_sub_C_irreducible_of_odd hn fun q hq hqn b hb => ?_
  have hb' : (b : K') ^ q = algebraMap (𝔭.adicCompletion K) K' (π : 𝔭.adicCompletion K) := by
    have := congrArg (Subtype.val) hb
    simpa [uniformizerInClosure] using this
  exact pow_ne_uniformizer_of_mem_unramifiedClosure 𝔭 hπ hq.two_le b.2 hb'

end NK.TameStructureDeep.Tame
