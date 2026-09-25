import Submission.NK.ResidueFrob.Setup
import Submission.NK.ResidueFrob.Basic
import Submission.NK.ResidueFrob.frobAtLevel_of_primitiveRoot_action
import Submission.NK.ResidueFrob.primeOfLevel_liesOver
import Submission.Commons.NumberTheory.NumberField.orderOf_frobenius_eq_inertiaDeg

/-!
# The residue-field normalisation at a place: "down"

This file proves that a **local Frobenius lift** at a place `A` — an element of `Gal(K'/K)` whose
image under the local/global identification `D_A ≃* Gal(κ̄/κ)` acts on the prime-to-`p` roots of
unity by `ζ ↦ ζ ^ q` (`NK.FrobeniusBridge.localFrobAt`) — restricts, at every finite normal level
`L ⊆ K'`, to an arithmetic Frobenius at the prime `P_L` of `𝓞 L` below `A`
(`NK.FrobeniusBridge.frobAtLevel`, i.e. `NK.Chebotarev.IsFrobAt`).  This is the
`level_of_local` half of the local–global dictionary `NK.FrobeniusBridge.PlaceLevelBridge`, and
it is the residue-field form of the Frobenius normalisation (NSW (12.1.8), Shimizu Lemma 2.1).

Two reductions are involved.

* The identification `NK.FrobeniusBridge.localGaloisEquiv A` is a `Classical.choice` and carries
  no information beyond being an isomorphism; by
  `NK.LocalTame.isFrobeniusLiftOfDecomposition_iff_of_localIso` (which uses the local structure
  input `NK.LocalTame.TameData`) the predicate `IsFrobeniusFor` may instead be read through the
  *explicit* identification `localGaloisEquivAdjoin A`.  There, `IsFrobeniusFor` unwinds to the
  statement that the restriction of the continuous extension of `g` to `M = K_𝔭·K'` acts on the
  roots of unity of `M` by `ζ ↦ ζ ^ q`, which transports along the injection `K' → M` to the roots
  of unity of `K'` (`actsOnRootsOfUnity_of_isFrobeniusFor_localGaloisEquivAdjoin`).
* The resulting hypothesis "`g ζ = ζ ^ q` for every root of unity `ζ ∈ K'` of order prime to `p`"
  implies `NK.FrobeniusBridge.frobAtLevel A L g` by
  `NK.ResidueFrob.frobAtLevel_of_primitiveRoot_action`, applied to a primitive `(#(𝓞L/P_L) - 1)`-st
  root of unity.

The statement of the final theorem carries the hypothesis `ResidueCardMatches A q`: the `q` of the
local data is the cardinality of the residue field of the prime of `K` below `A`.  This is part of
the local structure input (it is what `NK.LocalStructure.ResidueCardRecovery` is *for*): if it is
dropped, `NK.FrobeniusBridge.localFrobAt A g` is satisfied by elements whose residue-field action
is `x ↦ x ^ (q)` for `q = #(𝓞K/𝔭) ^ a`, `a ≠ 1`, and the conclusion fails.  See the `README.md`.
-/

namespace NK.ResidueFrob

open scoped Pointwise Classical

set_option linter.unusedSectionVars false

variable {K : Type*} [Field K] [NumberField K]
variable {K' : Type*} [Field K'] [Algebra K K'] [IsSepClosure K K']

/-- **The residue-field normalisation at a level** (the `level_of_local` half of
`NK.FrobeniusBridge.PlaceLevelBridge`), from the local data: a Frobenius lift at `A`, read
through the identification `NK.FrobeniusBridge.localGaloisEquiv`, restricts to a Frobenius
element at the prime of `𝓞 L` below `A`. -/
theorem level_of_local_of_data (A : NK.FrobeniusBridge.FinitePlaceOf K K') {p q : ℕ}
    (hT : NK.LocalTame.TameData p q (NK.FrobeniusBridge.localField A)
      (NK.FrobeniusBridge.localClosure A))
    (hq : ResidueCardMatches A q)
    (L : IntermediateField K K') [FiniteDimensional K L] [Normal K L] [NumberField ↥L]
    (g : Gal(K'/K))
    (hg : g ∈ Submission.NeukirchUchida.decompositionGroup (K₁ := K) (K₁' := K') A.1)
    (hF : NK.LocalAnabelian.IsFrobeniusFor p q
      (NK.FrobeniusBridge.localGaloisEquiv A ⟨g, hg⟩)) :
    NK.FrobeniusBridge.frobAtLevel A L g := by
  have hF' : NK.LocalAnabelian.IsFrobeniusFor p q (localGaloisEquivAdjoin A ⟨g, hg⟩) :=
    (isFrobeniusFor_localGaloisEquivAdjoin_iff A hT ⟨g, hg⟩).mpr hF
  have hac := actsOnRootsOfUnity_of_isFrobeniusFor_localGaloisEquivAdjoin A hg hF'
  -- the cardinality of the residue field of the level
  set P := NK.Reconstruct.primeOfLevel A.1 L (NK.Reconstruct.comap_level_ne_top A.2 L)
    with hPdef
  set N := Nat.card (NumberField.RingOfIntegers ↥L ⧸ P.asIdeal) with hNdef
  have hcard : N = q ^ (P.asIdeal.inertiaDeg (NumberField.RingOfIntegers K)) := by
    rw [hNdef, hq]
    exact Commons.NumberTheory.NumberField.natCard_residue_eq_pow_inertiaDeg
      (Submission.NeukirchUchida.primeOf A.1 A.2) P (primeOfLevel_liesOver A L)
  haveI hfin : Finite (NumberField.RingOfIntegers ↥L ⧸ P.asIdeal) :=
    Commons.NumberTheory.NumberField.finite_quotient_heightOneSpectrum P
  haveI hfintype : Fintype (NumberField.RingOfIntegers ↥L ⧸ P.asIdeal) := Fintype.ofFinite _
  have hN2 : 2 ≤ N := by
    rw [hNdef, Nat.card_eq_fintype_card]
    exact Fintype.one_lt_card
  have hpq : p ∣ q := by
    obtain ⟨f, hf, hqf⟩ := hT.structure_input.q_eq
    rw [hqf]
    exact dvd_pow_self p hf.ne'
  have hnotdvd : ¬ p ∣ N - 1 := by
    intro hdvd
    have hdvdN : p ∣ N := by
      rcases Nat.eq_zero_or_pos (P.asIdeal.inertiaDeg (NumberField.RingOfIntegers K)) with h0 | hpos
      · rw [hcard, h0, pow_zero] at hN2
        exact absurd hN2 (by norm_num)
      · rw [hcard]
        exact hpq.trans (dvd_pow_self q hpos.ne')
    have hsub : p ∣ N - (N - 1) := Nat.dvd_sub hdvdN hdvd
    have hone : N - (N - 1) = 1 := by omega
    rw [hone] at hsub
    have hle := Nat.le_of_dvd one_pos hsub
    have hp2 : 2 ≤ p := hT.structure_input.hp.two_le
    omega
  refine frobAtLevel_of_primitiveRoot_action A L hq g hg fun ζ hζ => hac _ hnotdvd ζ hζ

end NK.ResidueFrob
