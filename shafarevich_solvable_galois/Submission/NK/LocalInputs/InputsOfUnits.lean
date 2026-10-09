/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The Galois inputs of a `p`-adic completion, with the abelian rank *derived*

`NK.LocalInputs.LocalGaloisInputs` (module `Inputs`) assumes the abelianised pro-`p` rank
`HasAbelianFrattiniRank p (d+1+δ) (Gal(K'/κ))` of part (3) of the deliverable.  This module shows
that this field is *not* an independent assumption: it is derived from

* the Lubin–Tate / existence theorem of local class field theory (the input
  `NK.LocalReciprocity.LubinTateInput` isolated by the sibling area
  `Submission/Work/LocalReciprocity/`);
* the fact that index-`p` normal subgroups of `Gal(K'/κ)` are open (Nikolov–Segal: true because
  `Gal(κ̄/κ)` is topologically finitely generated for `p`-adic `κ`);
* **the power-class count of part (1)** (`LocalFieldInputs.principal_units_card`), via
  `NK.LocalInputs.hasFrattiniRank_units_adicCompletion` (`HasFrattiniRank p (d+1+δ) κˣ`) and the
  profinite-completion invariance of the index-`p` count
  (`NK.LocalInputs.CommGroupRank.numIndexSubgroups_profiniteCompletion`).
  No separate hypothesis on the unit group is needed: the `p`-Frattini rank of `κˣ^{∧}` is
  *derived* (`NK.LocalInputs.hasFrattiniRank_completionUnits_adicCompletion`).

This is route (b) of the deliverable, formalised: `LocalGaloisInputsOfUnits` collects exactly
those inputs, and `localGaloisInputs_of_units` / `padicGaloisInputs_of_units` derive
`LocalGaloisInputs` and the instantiation `PadicGaloisInputs` from them.

In the complementary case `δ = 1` (`ζ_p ∈ κ`, e.g. `κ = ℚ_p(ζ_p)`) there is a second route which
does not need Lubin–Tate at all: the Kummer bridge of the sibling chapter
(`NK.LocalAnabelian.hasAbelianFrattiniRank_of_isPrimitiveRoot`) computes the abelian rank from the
power-class count alone, cf. `hasAbelianFrattiniRank_of_isPrimitiveRoot_adicCompletion` below.
-/
import Submission.NK.LocalInputs.Instantiation
import Submission.NK.LocalInputs.AbelianRank.of_lubinTate
import Submission.NK.LocalInputs.CommGroupRank.numIndexSubgroups_profiniteCompletion
import Submission.NK.LocalInputs.PowerQuotient.hasFrattiniRank_units_adicCompletion
import Submission.NK.LocalAnabelian.PadicField.FrattiniRank
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

/-- **The local Galois inputs, with the abelian rank derived rather than assumed.**

In addition to Ivanov's two tower-rank statements (which remain inputs, cf.
`NK.LocalInputs.Inputs`), this structure records

* the Lubin–Tate / existence input of local class field theory,
* openness of index-`p` normal subgroups of `Gal(K'/κ)` (Nikolov–Segal for `p`-adic `κ`),
* the `p`-Frattini rank of the profinite completion of `κˣ`,
* the `p`-torsion of the abelianisation (equivalently of `κˣ^{∧}`, i.e. `μ_κ[p]`).

From these, `NK.LocalInputs.localGaloisInputs_of_units` derives the abelian rank, hence the full
`LocalGaloisInputs`. -/
structure LocalGaloisInputsOfUnits (K : Type*) [Field K] [NumberField K]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (K' : Type u) [Field K'] [Algebra (𝔭.adicCompletion K) K']
    [IsSepClosure (𝔭.adicCompletion K) K'] (p : ℕ) : Prop where
  /-- `p` is a prime. -/
  hp : p.Prime
  /-- **Ivanov, Lemma 3.12, the `ℓ = p` case** (an input: Demushkin/NSW (7.5.11)). -/
  proP_unbounded : NK.LocalAnabelian.HasUnboundedTowerRank p (Gal(K'/𝔭.adicCompletion K))
  /-- **Ivanov, Lemma 3.12, the `ℓ ≠ p` case** (an input: the tame structure, NSW (7.5.7)). -/
  other_bounded : ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ p →
    ¬ NK.LocalAnabelian.HasUnboundedTowerRank ℓ (Gal(K'/𝔭.adicCompletion K))
  /-- **The Lubin–Tate / existence input of local class field theory** (sibling area
  `Submission/Work/LocalReciprocity/`). -/
  lubinTate : NK.LocalReciprocity.LubinTateInput (𝔭.adicCompletion K) K'
  /-- Index-`p` normal subgroups of `Gal(K'/κ)` are open (Nikolov–Segal). -/
  open_of_index_prime : ∀ H : Subgroup (Gal(K'/𝔭.adicCompletion K)), H.index = p → H.Normal →
    IsOpen (H : Set (Gal(K'/𝔭.adicCompletion K)))
  /-- **The `p`-torsion of the abelianisation** is `μ_κ[p]`, i.e. is non-trivial exactly when
  `ζ_p ∈ κ`. -/
  p_torsion_iff : (zetaIndicator p (𝔭.adicCompletion K) = 1) ↔
    NK.LocalAnabelian.HasPTorsionAbelianization p (Gal(K'/𝔭.adicCompletion K))

open NK.LocalAnabelian in
/-- **The `p`-Frattini rank of the profinite completion of `κˣ`**, derived from the arithmetic of
the local field alone: `HasFrattiniRank p (d+1+δ) κˣ^{∧}` follows from
`LocalFieldInputs.principal_units_card` by
`NK.LocalInputs.hasFrattiniRank_units_adicCompletion` (which converts the power-class count into
the `p`-rank of the discrete unit group) and the profinite-completion invariance
`NK.LocalInputs.CommGroupRank.numIndexSubgroups_profiniteCompletion`. -/
theorem hasFrattiniRank_completionUnits_adicCompletion {K : Type*} [Field K] [NumberField K]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) {p : ℕ}
    (hF : LocalFieldInputs K 𝔭 p) :
    HasFrattiniRank p (localDegree K 𝔭 + 1 + zetaIndicator p (𝔭.adicCompletion K))
      (NK.LocalReciprocity.completionUnits (𝔭.adicCompletion K)) := by
  rw [HasFrattiniRank,
    NK.LocalInputs.CommGroupRank.numIndexSubgroups_profiniteCompletion
      (A := (𝔭.adicCompletion K)ˣ) hF.hp]
  exact hasFrattiniRank_units_adicCompletion 𝔭 hF

/-- **The abelian rank is derived**: from the Lubin–Tate input, openness of index-`p` normal
subgroups and the arithmetic of the local field (via the power-class count of part (1)), the
abelianised pro-`p` rank of `Gal(K'/κ)` follows. -/
theorem localGaloisInputs_of_units {K : Type*} [Field K] [NumberField K]
    {𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)}
    {K' : Type u} [Field K'] [Algebra (𝔭.adicCompletion K) K']
    [IsSepClosure (𝔭.adicCompletion K) K'] {p : ℕ}
    (hF : LocalFieldInputs K 𝔭 p) (h : LocalGaloisInputsOfUnits K 𝔭 K' p) :
    LocalGaloisInputs K 𝔭 K' p where
  hp := h.hp
  proP_unbounded := h.proP_unbounded
  other_bounded := h.other_bounded
  abelian_rank := by
    haveI : IsGalois (𝔭.adicCompletion K) K' := IsSepClosure.isGalois
    exact hasAbelianFrattiniRank_of_lubinTate (Classical.choice h.lubinTate)
      h.open_of_index_prime (hasFrattiniRank_completionUnits_adicCompletion 𝔭 hF)
  p_torsion_iff := h.p_torsion_iff

/-- **The instantiation of `PadicGaloisInputs`** from the derived form of the Galois inputs. -/
theorem padicGaloisInputs_of_units {K : Type*} [Field K] [NumberField K]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (K' : Type u) [Field K'] [Algebra (𝔭.adicCompletion K) K']
    [IsSepClosure (𝔭.adicCompletion K) K'] {p : ℕ}
    (hF : LocalFieldInputs K 𝔭 p) (hG : LocalGaloisInputsOfUnits K 𝔭 K' p) :
    NK.LocalAnabelian.PadicGaloisInputs p (localDegree K 𝔭)
      (zetaIndicator p (𝔭.adicCompletion K)) (𝔭.adicCompletion K) K' :=
  padicGaloisInputs_of_localInputs 𝔭 K' hF (localGaloisInputs_of_units hF hG)

/-- **The abelian rank in the Kummer case `ζ_p ∈ κ`**, without any class field theory: when `κ`
contains a primitive `p`-th root of unity the abelian rank follows from the power-class count of
part (1) alone, by the Kummer bridge of the sibling chapter
(`NK.LocalAnabelian.hasAbelianFrattiniRank_of_isPrimitiveRoot`).

Here `δ = 1`, and `localDegree K 𝔭 + 1 + δ = localDegree K 𝔭 + 2`. -/
theorem hasAbelianFrattiniRank_of_isPrimitiveRoot_adicCompletion {K : Type*} [Field K]
    [NumberField K] (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (K' : Type u) [Field K'] [Algebra (𝔭.adicCompletion K) K']
    [IsSepClosure (𝔭.adicCompletion K) K'] {p : ℕ}
    (hF : LocalFieldInputs K 𝔭 p)
    (hζ : ∃ ζ : 𝔭.adicCompletion K, IsPrimitiveRoot ζ p)
    (hclosed : ∀ H : Subgroup (Gal(K'/𝔭.adicCompletion K)), H.index = p → H.Normal →
      IsClosed (H : Set (Gal(K'/𝔭.adicCompletion K)))) :
    NK.LocalAnabelian.HasAbelianFrattiniRank p
      (localDegree K 𝔭 + 1 + zetaIndicator p (𝔭.adicCompletion K))
      (Gal(K'/𝔭.adicCompletion K)) := by
  classical
  obtain ⟨ζ, hζ⟩ := hζ
  have hδ : zetaIndicator p (𝔭.adicCompletion K) = 1 :=
    (zetaIndicator_eq_one_iff p (𝔭.adicCompletion K)).mpr ⟨ζ, hζ⟩
  have hpow : Nat.card (NK.LocalAnabelian.KummerGroup p (𝔭.adicCompletion K)) =
      p ^ (localDegree K 𝔭 + 2) := by
    rw [natCard_KummerGroup_adicCompletion_eq_pow 𝔭 hF, hδ]
  have hne : Nat.card (NK.LocalAnabelian.KummerGroup p (𝔭.adicCompletion K)) ≠ 0 := by
    rw [hpow]
    exact pow_ne_zero _ hF.hp.ne_zero
  haveI : Finite (NK.LocalAnabelian.KummerGroup p (𝔭.adicCompletion K)) :=
    Nat.finite_of_card_ne_zero hne
  have h := NK.LocalAnabelian.hasAbelianFrattiniRank_of_isPrimitiveRoot (κ := 𝔭.adicCompletion K)
    (K' := K') hF.hp hζ hpow hclosed
  simpa only [hδ, Nat.add_assoc, Nat.add_comm 1] using h

end

end NK.LocalInputs
