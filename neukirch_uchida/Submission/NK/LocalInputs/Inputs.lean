/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The named arithmetic inputs for a `p`-adic completion

This file collects, as `structure`s, the *classical arithmetic facts* about the local field
`κ = K_𝔭` (the `p`-adic completion of a number field at a finite prime) which the local input of
Neukirch–Uchida needs, in the precise form in which the derivation in
`NK.LocalInputs.Instantiation` consumes them.  Nothing here is proved from a `sorry` or a new
axiom: each `structure` is a `Prop`, and every theorem of this chapter takes the relevant
structure as an explicit hypothesis.

The inputs are

* `LocalFieldInputs p K 𝔭` — the *arithmetic* of the local field itself:

  * `residue_char`: `p` is the residue characteristic, i.e. the residue field of `𝒪_κ` has
    characteristic `p`.  Equivalently `p ∈ 𝔪_κ`.  (Reference: trivial, via the residue map.)
  * `principal_units_card`: the structure of the group of principal units
    `U¹ = 1 + 𝔪_κ`: `U¹ ≅ μ_{p^∞}(κ) × ℤ_p^{[κ:ℚ_p]}`, whence
    `|U¹/(U¹)^p| = p^{[κ:ℚ_p] + δ}` with `δ = 1` iff `ζ_p ∈ κ`.
    (Reference: Serre, *Local Fields*, Ch. II §5, Prop. 3 and Cor. to Prop. 5 (the `p`-adic
    logarithm identifies `1 + 𝔪^N` with an additive subgroup of `𝔪_κ ≅ ℤ_p^d`); the case
    `κ = ℚ_p` is the commons' `Commons.NumberTheory.NumberField.Completion.natCard_powerQuotient_adicCompletion_rat_units`
    together with `natCard_ker_unitsValLog_quot_pow`.  A formal proof along
    the lines of `Submission/Work/NumberTheory/NumberField/Completion/probe_count.lean`
    (`PpowRat`, the log/exp bootstrap) generalised from `ℚ_p` to an arbitrary `p`-adic field
    would discharge this; it is not in this workspace.)

* `LocalGaloisInputs p K 𝔭 K'` — the *group theory* of `G_κ = Gal(K'/κ)`, i.e. the structure
  theorems of local Galois theory:

  * `proP_unbounded` and `other_bounded`: Ivanov's Lemma 3.12 (arXiv:1309.3046):
    the `ℓ`-tower rank of `G_κ` is unbounded for `ℓ = p` and bounded for `ℓ ≠ p`.
    (Discharge: the wild inertia `V_κ` is a pro-`p` group and `I_κ/V_κ ≅ ∏_{ℓ≠p}ℤ_ℓ`, so for
    `ℓ ≠ p` the maximal pro-`ℓ` quotient of `G_κ` is the pro-`ℓ` part of `Ẑ ⋉ ∏_{ℓ≠p}ℤ_ℓ`,
    of rank `≤ 2`; for `ℓ = p`, `G_κ^{(p)}` is a Demushkin group of rank `d+2 ≥ 3` (NSW
    (7.5.11)), whose open subgroups have unbounded `p`-Frattini rank and are again absolute
    Galois groups of `p`-adic fields.  Sibling areas: `Submission/Work/LocalTame/`
    (`TameStructureInput`) and `Submission/Work/ProfiniteP/`.)

  * `abelian_rank`: the abelianised pro-`p` part of `G_κ` is `ℤ_p^{d+1}` (no `p`-torsion since
    `p ∤ q-1`), i.e. there are `(p^{d+1+δ} - 1)/(p - 1)` cyclic degree-`p` extensions of `κ`.
    (Discharge: local class field theory, `G_κ^{ab} ≅ κˣ^{∧} = Ẑ × μ_κ × ℤ_p^{d}`, and
    `μ_κ[p] ≅ ℤ/p` iff `ζ_p ∈ κ`.  Sibling area: `Submission/Work/LocalReciprocity/`
    (`LocalReciprocityDatum`, `Invariants.lean`); the transfer along the reciprocity isomorphism
    together with the arithmetic of `κˣ` gives exactly this.)

  * `p_torsion_iff`: the `p`-torsion of `G_κ^{ab}` is `μ_κ[p]`, i.e. non-trivial exactly when
    `ζ_p ∈ κ`.  (Same reference and same discharge as `abelian_rank`.)
-/
import Submission.NK.LocalInputs.Defs
import Submission.NK.LocalAnabelian.All

open scoped Classical
open IsDedekindDomain.HeightOneSpectrum

namespace NK.LocalInputs

noncomputable section

universe u

/-- **The arithmetic inputs for the local field `κ = K_𝔭`.**

`p` is the residue characteristic and the structure of the principal units `U¹ = 1 + 𝔪_κ` is
recorded in the form `|U¹/(U¹)^p| = p^{[κ:ℚ_p] + δ}`.  These are the facts about the *field*
`κ` (no Galois theory). -/
structure LocalFieldInputs (K : Type*) [Field K] [NumberField K]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) (p : ℕ) : Prop where
  /-- `p` is a prime. -/
  hp : p.Prime
  /-- **`p` is the residue characteristic** of `κ = K_𝔭`: the residue field of the valuation ring
  `𝒪_κ` has characteristic `p` (equivalently `p ∈ 𝔪_κ`). -/
  residue_char : CharP (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K)) p
  /-- **The principal units.**  `1 + 𝔪_κ ≅ μ_{p^∞}(κ) × ℤ_p^{[κ : ℚ_p]}`, hence
  `|U¹/(U¹)^p| = p^{[κ : ℚ_p] + δ}` with `δ` the indicator of `ζ_p ∈ κ`.

  For `κ = ℚ_p` this is in the commons (see the module docstring); in general it is the `p`-adic
  logarithm/`ℤ_p^d`-structure of the principal units. -/
  principal_units_card :
    Nat.card (principalUnits K 𝔭 ⧸ (powMonoidHom p).range) =
      p ^ (localDegree K 𝔭 + zetaIndicator p (𝔭.adicCompletion K))

/-- **The local Galois-theoretic inputs for `κ = K_𝔭`.**

`K'` is a separable closure of `κ`, `p` the residue characteristic.  The fields record Ivanov's
detection of the residue characteristic and the local reciprocity computation of `G_κ^{ab}`. -/
structure LocalGaloisInputs (K : Type*) [Field K] [NumberField K]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (K' : Type u) [Field K'] [Algebra (𝔭.adicCompletion K) K']
    [IsSepClosure (𝔭.adicCompletion K) K'] (p : ℕ) : Prop where
  /-- `p` is a prime. -/
  hp : p.Prime
  /-- **Ivanov, Lemma 3.12, the `ℓ = p` case**: the `p`-tower rank of `G_κ` is unbounded. -/
  proP_unbounded : NK.LocalAnabelian.HasUnboundedTowerRank p (Gal(K'/𝔭.adicCompletion K))
  /-- **Ivanov, Lemma 3.12, the `ℓ ≠ p` case**: the `ℓ`-tower rank of `G_κ` is bounded for
  every prime `ℓ ≠ p`. -/
  other_bounded : ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ p →
    ¬ NK.LocalAnabelian.HasUnboundedTowerRank ℓ (Gal(K'/𝔭.adicCompletion K))
  /-- **The abelianised pro-`p` rank** (local reciprocity): the maximal elementary abelian
  `p`-quotient of `G_κ^{ab}` is `(ℤ/p)^{[κ:ℚ_p] + 1 + δ}`. -/
  abelian_rank : NK.LocalAnabelian.HasAbelianFrattiniRank p
    (localDegree K 𝔭 + 1 + zetaIndicator p (𝔭.adicCompletion K)) (Gal(K'/𝔭.adicCompletion K))
  /-- **The `p`-torsion of the abelianisation** is `μ_κ[p]`, hence non-trivial exactly when
  `ζ_p ∈ κ`. -/
  p_torsion_iff : (zetaIndicator p (𝔭.adicCompletion K) = 1) ↔
    NK.LocalAnabelian.HasPTorsionAbelianization p (Gal(K'/𝔭.adicCompletion K))

/-- **Ivanov's detection of the residue characteristic**, from the two tower-rank inputs. -/
theorem residueCharDetectedBy_of_localGaloisInputs {K : Type*} [Field K] [NumberField K]
    {𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)}
    {K' : Type u} [Field K'] [Algebra (𝔭.adicCompletion K) K']
    [IsSepClosure (𝔭.adicCompletion K) K'] {p : ℕ} (h : LocalGaloisInputs K 𝔭 K' p) :
    NK.LocalAnabelian.ResidueCharDetectedBy p (Gal(K'/𝔭.adicCompletion K)) := by
  intro ℓ hℓ
  constructor
  · intro hunb
    by_contra hne
    exact h.other_bounded ℓ hℓ hne hunb
  · rintro rfl
    exact h.proP_unbounded

end

end NK.LocalInputs
