import Submission.NK.LocalInputs.InputsOfUnits
import Submission.NK.Mine.PlaceCorrespondenceArithmetic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The local Galois inputs of a `p`-adic completion, from the *corrected* reciprocity datum

`Submission/Work/LocalInputs/InputsOfUnits.lean` derives `NK.LocalInputs.LocalGaloisInputs` for a
completion `κ = K_𝔭` from a bundle `LocalGaloisInputsOfUnits` whose field `lubinTate` is
`NK.LocalReciprocity.LubinTateInput κ K'`.  `Submission/Work/LocalCFT/` proved that this datum is
**unsatisfiable** for a `p`-adic field (`NK.LocalCFT.NilpotentObstruction.not_nonempty_localReciprocityDatum_of_galoisQuotient`),
so that derivation is vacuous.

This file re-routes it through the satisfiable replacement `NK.LocalCFT.ArtinReciprocity`
(the Artin map landing in `Gal(κ^{ab}/κ)`), using `NK.Mine.hasAbelianFrattiniRank_of_artinReciprocity`
together with the derived `p`-Frattini rank of `κˣ^{∧}`
(`NK.LocalInputs.hasFrattiniRank_completionUnits_adicCompletion`, whose only input is the
power-class count of the principal units).  The remaining three fields of the bundle
(Ivanov's tower ranks, openness of index-`p` subgroups by Nikolov–Segal, and the `p`-torsion
detection) are unchanged.
-/

namespace NK.Mine

open scoped Classical
open IsDedekindDomain.HeightOneSpectrum

universe u

/-- **The local Galois-theoretic inputs of a `p`-adic completion, with the corrected reciprocity
datum.**  Same as `NK.LocalInputs.LocalGaloisInputsOfUnits`, except that the reciprocity input is
the satisfiable `NK.LocalCFT.ArtinReciprocity` (Artin map into `Gal(κ^{ab}/κ)`) instead of the
empty `NK.LocalReciprocity.LubinTateInput`. -/
structure LocalGaloisInputsOfUnitsCorrected (K : Type*) [Field K] [NumberField K]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (K' : Type u) [Field K'] [Algebra (𝔭.adicCompletion K) K']
    [IsSepClosure (𝔭.adicCompletion K) K'] (p : ℕ) : Prop where
  /-- `p` is a prime. -/
  hp : p.Prime
  /-- **Ivanov, Lemma 3.12, the `ℓ = p` case** (Demushkin / NSW (7.5.11)). -/
  proP_unbounded : NK.LocalAnabelian.HasUnboundedTowerRank p (Gal(K'/𝔭.adicCompletion K))
  /-- **Ivanov, Lemma 3.12, the `ℓ ≠ p` case** (the tame structure, NSW (7.5.7)). -/
  other_bounded : ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ p →
    ¬ NK.LocalAnabelian.HasUnboundedTowerRank ℓ (Gal(K'/𝔭.adicCompletion K))
  /-- **The corrected Lubin–Tate / existence input** of local class field theory: the canonical
  Artin reciprocity datum, whose Artin map lands in `Gal(κ^{ab}/κ)`. -/
  artin : NK.LocalCFT.LubinTateInput (𝔭.adicCompletion K) K'
  /-- Index-`p` normal subgroups of `Gal(K'/κ)` are open (Nikolov–Segal). -/
  open_of_index_prime : ∀ H : Subgroup (Gal(K'/𝔭.adicCompletion K)), H.index = p → H.Normal →
    IsOpen (H : Set (Gal(K'/𝔭.adicCompletion K)))
  /-- **The `p`-torsion of the abelianisation** is `μ_κ[p]`, i.e. is non-trivial exactly when
  `ζ_p ∈ κ`. -/
  p_torsion_iff : (NK.LocalInputs.zetaIndicator p (𝔭.adicCompletion K) = 1) ↔
    NK.LocalAnabelian.HasPTorsionAbelianization p (Gal(K'/𝔭.adicCompletion K))

/-- **The local Galois inputs from the corrected data.**  The abelianised `p`-Frattini rank is
derived from the corrected reciprocity datum and the arithmetic of the local field via
`NK.Mine.hasAbelianFrattiniRank_of_artinReciprocity`; the other three fields are carried over. -/
theorem localGaloisInputs_of_unitsCorrected {K : Type*} [Field K] [NumberField K]
    {𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)}
    {K' : Type u} [Field K'] [Algebra (𝔭.adicCompletion K) K']
    [IsSepClosure (𝔭.adicCompletion K) K'] {p : ℕ}
    (hF : NK.LocalInputs.LocalFieldInputs K 𝔭 p)
    (h : LocalGaloisInputsOfUnitsCorrected K 𝔭 K' p) :
    NK.LocalInputs.LocalGaloisInputs K 𝔭 K' p where
  hp := h.hp
  proP_unbounded := h.proP_unbounded
  other_bounded := h.other_bounded
  abelian_rank :=
    hasAbelianFrattiniRank_of_artinReciprocity (Classical.choice h.artin)
      h.open_of_index_prime
      (NK.LocalInputs.hasFrattiniRank_completionUnits_adicCompletion 𝔭 hF)
  p_torsion_iff := h.p_torsion_iff

/-! ## The `(a)`-chain at the prime `p = 2`

The Brauer/Hasse/Neukirch-criterion chain of `Submission/Work/BrauerHasse/` uses the coefficient
module `Z/p` with the *trivial* action, whereas the classical input is `mu_p = Z/p(1)`.  The two
coincide precisely when `mu_p ⊆ K`, which for `p = 2` is automatic (every field of characteristic
`≠ 2` contains `±1`, and the cyclotomic character is trivial modulo `2`).  Hence at `p = 2` the
whole chain is correct *as stated*: no coefficient twist is needed, and the local input is
available from `NK.LocalCFT.localH2Nonvanishing_two`.

The lemmas below record this: they reduce the `(a)`-chain (CoNF (12.1.9) "if") to the three
classical inputs evaluated at `p = 2`, namely the Kummer/Brauer computation
`NK.LocalCFT.LocalBrauerGroupInput 2`, the Hasse principle (`Sha2Vanishing 2`) and Neukirch's
local finishing step (`LocalDecompositionCriterion 2`), plus the Nikolov–Segal openness of
finite-index subgroups. -/

/-- **The local Brauer input at `p = 2`, for the completion of a number field.**

`NK.BrauerHasse.LocalH2Input 2 K K' κ κ'` (trivial `Z/2`-coefficients) follows from the
Kummer/Brauer computation `LocalBrauerGroupInput 2` — which is the classical
`H²(G_κ, μ_2) = Br(κ)[2] ≅ Z/2`, *unconditional* because `μ_2 ⊆ κ` for every `p`-adic `κ` — and the
Nikolov–Segal openness of finite-index subgroups. -/
theorem localH2Input_two_adicCompletion {K L : Type u} [Field K] [NumberField K] [Field L]
    [Algebra K L] [IsSepClosure K L]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hbr : NK.LocalCFT.LocalBrauerGroupInput 2 (𝔭.adicCompletion K)
      (SeparableClosure (𝔭.adicCompletion K)))
    (hopenH : ∀ H : Subgroup Gal(L/K), IsClosed (H : Set Gal(L/K)) →
      ∀ U : Subgroup ↥H, U.FiniteIndex → IsOpen (U : Set ↥H))
    (hopenκ : ∀ U : Subgroup Gal(SeparableClosure (𝔭.adicCompletion K)/(𝔭.adicCompletion K)),
      U.FiniteIndex → IsOpen (U : Set Gal(SeparableClosure (𝔭.adicCompletion K)/(𝔭.adicCompletion K)))) :
    NK.BrauerHasse.LocalH2Input 2 K L (𝔭.adicCompletion K)
      (SeparableClosure (𝔭.adicCompletion K)) := by
  have h2ne : (2 : 𝔭.adicCompletion K) ≠ 0 := by
    haveI : CharZero (𝔭.adicCompletion K) :=
      Commons.NumberTheory.NumberField.charZero_adicCompletion 𝔭
    exact_mod_cast (by norm_num : (2 : ℚ) ≠ 0)
  exact NK.LocalCFT.localH2Input_of_nonvanishing hopenH hopenκ
    (NK.LocalCFT.localH2Nonvanishing_two hbr h2ne)

/-- **The `(a)`-chain at `p = 2`.**  If the three classical inputs of Neukirch's criterion
(`LocalH2Input`, the Hasse principle, and the local finishing step) are available at `p = 2` for
the completion at every finite prime, then `ϕ` preserves the decomposition groups.  This is
`NK.Mine.preservesDecompositionGroups_of_localGalois` with the auxiliary prime fixed to `2`. -/
theorem preservesDecompositionGroups_of_localData_two {K₁ K₂ K₁' K₂' : Type u} [Field K₁]
    [Field K₂] [Field K₁'] [Field K₂'] [NumberField K₁] [NumberField K₂] [Algebra K₁ K₁']
    [Algebra K₂ K₂'] [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂']
    (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) (he : IsHomeomorph ϕ)
    (h₁ : ∀ (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K₁)),
      NK.BrauerHasse.LocalH2Input 2 K₂ K₂'
        (𝔭.adicCompletion K₁) (SeparableClosure (𝔭.adicCompletion K₁)) ∧
      NK.BrauerHasse.Sha2Vanishing 2 K₂ K₂'
        (𝔭.adicCompletion K₁) (SeparableClosure (𝔭.adicCompletion K₁)) ∧
      NK.BrauerHasse.LocalDecompositionCriterion 2 K₂ K₂'
        (𝔭.adicCompletion K₁) (SeparableClosure (𝔭.adicCompletion K₁)))
    (h₂ : ∀ (𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K₂)),
      NK.BrauerHasse.LocalH2Input 2 K₁ K₁'
        (𝔮.adicCompletion K₂) (SeparableClosure (𝔮.adicCompletion K₂)) ∧
      NK.BrauerHasse.Sha2Vanishing 2 K₁ K₁'
        (𝔮.adicCompletion K₂) (SeparableClosure (𝔮.adicCompletion K₂)) ∧
      NK.BrauerHasse.LocalDecompositionCriterion 2 K₁ K₁'
        (𝔮.adicCompletion K₂) (SeparableClosure (𝔮.adicCompletion K₂))) :
    Submission.NeukirchUchida.PreservesDecompositionGroups ϕ :=
  NK.Mine.preservesDecompositionGroups_of_localGalois ϕ he
    (fun 𝔭 => ⟨2, Nat.prime_two, (h₁ 𝔭).1, (h₁ 𝔭).2.1, (h₁ 𝔭).2.2⟩)
    (fun 𝔮 => ⟨2, Nat.prime_two, (h₂ 𝔮).1, (h₂ 𝔮).2.1, (h₂ 𝔮).2.2⟩)

end NK.Mine
