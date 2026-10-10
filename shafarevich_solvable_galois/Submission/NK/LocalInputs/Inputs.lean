import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Submission.NK.LocalInputs.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

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
