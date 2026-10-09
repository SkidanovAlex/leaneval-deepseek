import Mathlib
import Submission.Work.LocalFields.card_inertiaSubgroup
import Submission.Commons.NumberTheory.NumberField.differentIdeal_eq_top_of_ramificationIdx
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option linter.style.haveILetI false

namespace Work.SSGRoute

open scoped NumberField

/-- The zero ideal of `𝓞 ↥E` has ramification index one over `𝓞 K`: in characteristic zero the
generic point of an integral extension of domains is unramified
(`Algebra.isUnramifiedAt_bot`), and `Ideal.ramificationIdx_eq_one` converts this to the
ramification index.  This is the only prime of `𝓞 ↥E` to which the inertia/tower argument below
does not apply (there is no *nonzero* prime of `𝓞 L` above `⊥`). -/
private theorem ramificationIdx_bot_eq_one_of_intermediateField {K L : Type} [Field K]
    [NumberField K] [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]
    [IsGalois K L] (E : IntermediateField K L) [FiniteDimensional K ↥E] [IsGalois K ↥E] :
    (⊥ : Ideal (𝓞 ↥E)).ramificationIdx (𝓞 K) = 1 := by
  have : Algebra.IsUnramifiedAt (𝓞 K) (⊥ : Ideal (𝓞 ↥E)) := Algebra.isUnramifiedAt_bot
  exact Ideal.ramificationIdx_eq_one (⊥ : Ideal (𝓞 ↥E)) (𝓞 K)

/-- **The heart of the argument: a nonzero prime of `𝓞 ↥E` is unramified over `𝓞 K`.**

Let `Q` be a nonzero prime ideal of `𝓞 ↥E`, `p = Q ∩ 𝓞 K` the prime of `𝓞 K` below it, and
`Q'` a prime of `𝓞 L` above `Q`.  Since `Q ≠ ⊥` the prime `Q'` is nonzero, so the hypothesis
applies to it and gives `I_w ≤ E.fixingSubgroup` for `w = Q'`.  Hence the inertia subgroup of `Q'`
in `Gal(L/K)` is contained in the fixing subgroup of `E`, and transporting it along
`IntermediateField.fixingSubgroupEquiv E` (`Ideal.inertiaEquiv`) identifies
`#I_{Q'}(L/K) = #I_{Q'}(L/E)`; by `Ideal.card_inertia_eq_ramificationIdxIn` (applied to the two
extensions of rings of integers) this says

`e(Q' | 𝓞 K) = e(Q' | 𝓞 ↥E)`.

Multiplicativity of ramification indices in the tower `𝓞 K ⊆ 𝓞 ↥E ⊆ 𝓞 L`
(`Ideal.ramificationIdxIn_mul_ramificationIdxIn`) reads

`e(Q | 𝓞 K) * e(Q' | 𝓞 ↥E) = e(Q' | 𝓞 K)`,

so `e(Q | 𝓞 K) * e(Q' | 𝓞 K) = e(Q' | 𝓞 K)`, and since `e(Q' | 𝓞 K)` is nonzero we conclude
`e(Q | 𝓞 K) = 1`. -/
private theorem ramificationIdx_eq_one_of_ne_bot {K L : Type} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (E : IntermediateField K L) [FiniteDimensional K ↥E] [IsGalois K ↥E]
    (h : ∀ (q' : IsDedekindDomain.HeightOneSpectrum (𝓞 L)),
        Ideal.inertia (L ≃ₐ[K] L) q'.asIdeal ≤ E.fixingSubgroup)
    (Q : Ideal (𝓞 ↥E)) (hQprime : Q.IsPrime) (hQne : Q ≠ ⊥) :
    Q.ramificationIdx (𝓞 K) = 1 := by
  haveI : Q.IsPrime := hQprime
  set p : Ideal (𝓞 K) := Q.under (𝓞 K) with hp
  haveI hpP : p.IsPrime := Ideal.IsPrime.under (𝓞 K) Q
  have hQlies : Q.LiesOver p := Ideal.LiesOver.mk rfl
  haveI : Q.IsMaximal := hQprime.isMaximal hQne
  -- a prime `Q'` of `𝓞 L` above `Q` (maximal, hence nonzero)
  obtain ⟨Q', hQ'max, hQ'lies⟩ :=
    Ideal.exists_maximal_ideal_liesOver_of_isIntegral (R := 𝓞 ↥E) (S := 𝓞 L) Q
  haveI : Q'.IsPrime := hQ'max.isPrime
  haveI : Q'.LiesOver Q := hQ'lies
  have hQ'ne : Q' ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot (A := 𝓞 ↥E) (B := 𝓞 L) hQne Q'
  haveI : Q'.LiesOver p := Ideal.LiesOver.trans Q' Q p
  -- ### The inertia subgroups of `Q'` in `Gal(L/K)` and in `Gal(L/↥E)` have the same cardinality
  have hcard : Nat.card ↥(Ideal.inertia (L ≃ₐ[K] L) Q') =
      Nat.card ↥(Ideal.inertia (L ≃ₐ[↥E] L) Q') := by
    -- the subgroup of `E.fixingSubgroup` cut out by the inertia is the inertia subgroup of
    -- `E.fixingSubgroup`
    have hsub : (Ideal.inertia (L ≃ₐ[K] L) Q').subgroupOf E.fixingSubgroup =
        Ideal.inertia ↥E.fixingSubgroup Q' :=
      AddSubgroup.subgroupOf_inertia Q'.toAddSubgroup E.fixingSubgroup
    -- cutting out does not change the cardinality
    have h1 : Nat.card ↥(Ideal.inertia (L ≃ₐ[K] L) Q') =
        Nat.card ↥((Ideal.inertia (L ≃ₐ[K] L) Q').subgroupOf E.fixingSubgroup) :=
      (Nat.card_congr
        (Subgroup.subgroupOfEquivOfLe (h ⟨Q', hQ'max.isPrime, hQ'ne⟩)).toEquiv).symm
    rw [hsub] at h1
    -- transport along `E.fixingSubgroup ≃* Gal(L/↥E)`, which acts on `𝓞 L` in the same way
    exact h1.trans (Nat.card_congr
      (Ideal.inertiaEquiv Q' (E.fixingSubgroupEquiv) (fun m x => rfl)).toEquiv)
  -- ### Multiplicativity of ramification indices in the tower `𝓞 K ⊆ 𝓞 ↥E ⊆ 𝓞 L`
  have htower : p.ramificationIdxIn (𝓞 ↥E) * Q.ramificationIdxIn (𝓞 L) =
      p.ramificationIdxIn (𝓞 L) :=
    Ideal.ramificationIdxIn_mul_ramificationIdxIn (p := p) (G := ↥E ≃ₐ[K] ↥E) Q (𝓞 L)
      (L ≃ₐ[K] L) (L ≃ₐ[↥E] L)
  rw [Ideal.ramificationIdxIn_eq_ramificationIdx p Q (↥E ≃ₐ[K] ↥E),
    Ideal.ramificationIdxIn_eq_ramificationIdx Q Q' (L ≃ₐ[↥E] L),
    Ideal.ramificationIdxIn_eq_ramificationIdx p Q' (L ≃ₐ[K] L)] at htower
  -- ### `e(Q' | 𝓞 ↥E) = e(Q' | 𝓞 K)` from the equality of inertia cardinalities
  have hcK : Nat.card ↥(Ideal.inertia (L ≃ₐ[K] L) Q') = Q'.ramificationIdx (𝓞 K) := by
    rw [Ideal.card_inertia_eq_ramificationIdxIn (G := L ≃ₐ[K] L) (p := p) Q']
    exact Ideal.ramificationIdxIn_eq_ramificationIdx p Q' (L ≃ₐ[K] L)
  have hcE : Nat.card ↥(Ideal.inertia (L ≃ₐ[↥E] L) Q') = Q'.ramificationIdx (𝓞 ↥E) := by
    rw [Ideal.card_inertia_eq_ramificationIdxIn (G := L ≃ₐ[↥E] L) (p := Q) Q']
    exact Ideal.ramificationIdxIn_eq_ramificationIdx Q Q' (L ≃ₐ[↥E] L)
  have hyx : Q'.ramificationIdx (𝓞 ↥E) = Q'.ramificationIdx (𝓞 K) := by
    rw [← hcE, ← hcK]
    exact hcard.symm
  rw [hyx] at htower
  -- ### Conclusion: `e(Q | 𝓞 K) * x = x` with `x ≠ 0` forces `e(Q | 𝓞 K) = 1`
  exact Nat.eq_of_mul_eq_mul_right (Ideal.ramificationIdx_pos (𝓞 K) Q') (by simpa using htower)

/-- **A Galois subextension whose Galois group contains the inertia groups is unramified at every
finite place.**  For a finite Galois extension `L/K` of number fields and an intermediate field
`E` with `E/K` Galois, if for every nonzero prime `q'` of `𝓞 L` the inertia subgroup of
`Gal(L/K)` at `q'` is contained in `Gal(L/E) = E.fixingSubgroup`, then the relative different
`differentIdeal (𝓞 K) (𝓞 E)` is the unit ideal, i.e. `E/K` is unramified at every finite place.

Route: for a prime `P` of `𝓞 ↥E` pick `q'` of `𝓞 L` above it and let `Q` be the prime of `𝓞 K`
below `P`.  `Ideal.card_inertia_eq_ramificationIdxIn` identifies `Nat.card (Ideal.inertia Gal(L/K)
q'.asIdeal)` with `Q.ramificationIdxIn (𝓞 L)` and hence (via
`Ideal.ramificationIdxIn_eq_ramificationIdx`) with `q'.asIdeal.ramificationIdx (𝓞 K)`; applied to
the extension `L/↥E` (transporting `E.fixingSubgroup ≃* Gal(L/↥E)` along
`IntermediateField.fixingSubgroupEquiv` and `Ideal.inertiaEquiv`) the same cardinality is
`q'.asIdeal.ramificationIdx (𝓞 ↥E)`.  The containment `Ideal.inertia Gal(L/K) q' ≤ E.fixingSubgroup`
identifies the two inertia groups, so these ramification indices agree, and
`Ideal.ramificationIdx_tower` gives `e(q' | 𝓞 K) = e(P | 𝓞 K) * e(q' | 𝓞 ↥E)`; since the second
factor is nonzero, `P.ramificationIdx (𝓞 K) = 1` for every prime `P` of `𝓞 ↥E`, and
`differentIdeal_eq_top_of_ramificationIdx` (in
`Submission.Commons.NumberTheory.NumberField.differentIdeal_eq_top_of_ramificationIdx`) concludes.
The delegate may add whatever imports are needed. -/
theorem e9_caseB_unramified_finite
    {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (E : IntermediateField K L) [FiniteDimensional K ↥E] [IsGalois K ↥E]
    (h : ∀ (q' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L)),
        Ideal.inertia (L ≃ₐ[K] L) q'.asIdeal ≤ E.fixingSubgroup) :
    differentIdeal (NumberField.RingOfIntegers K) (NumberField.RingOfIntegers ↥E) = ⊤ := by
  refine Commons.NumberTheory.NumberField.differentIdeal_eq_top_of_ramificationIdx
    (E := K) (K := ↥E) ?_
  intro Q hQprime
  by_cases hQne : Q = ⊥
  · rw [hQne]
    exact ramificationIdx_bot_eq_one_of_intermediateField E
  · exact ramificationIdx_eq_one_of_ne_bot E h Q hQprime hQne

end Work.SSGRoute
