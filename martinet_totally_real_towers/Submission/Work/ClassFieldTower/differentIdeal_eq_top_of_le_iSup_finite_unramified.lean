import Mathlib
import Submission.Work.ClassFieldTower.Defs

open scoped NumberField

namespace Work.ClassFieldTower

/-- **Unramifiedness is inherited by finite subextensions of a compositum of unramified
extensions.**

Let `F` be a number field and `f i` a family of finite-dimensional Galois number-field
extensions of `F`, each unramified over `F` (i.e. with trivial relative different
`differentIdeal (𝓞 F) (𝓞 ↥(f i)) = ⊤`).  Then any finite-dimensional Galois subextension
`L ≤ ⨆ i, f i` is again unramified over `F`.

The proof has three steps:

* a nonzero prime `Q` of `𝓞 ↥(f i)` cannot divide `differentIdeal (𝓞 F) (𝓞 ↥(f i)) = ⊤`
  (if `⊤ = Q * c` then `⊤ ≤ Q`, so `Q = ⊤`, contradicting primality);
* hence the relative different of each `f i` is supported on the empty set of rational
  primes, and `Commons.NumberTheory.NumberField.differentIdeal_supp_le_iSup_finset` (the
  support version of the statement, with `S = ∅`) shows that every nonzero prime of `𝓞 ↥L`
  fails to divide `differentIdeal (𝓞 F) (𝓞 ↥L)`;
* the prime `⊥` is handled separately: `⊥ ∣ 𝔡` forces `𝔡 = ⊥`, contradicting
  `differentIdeal_ne_bot`.  Now `Commons.NumberTheory.NumberField.differentIdeal_eq_top_of_forall_not_dvd`
  gives `differentIdeal (𝓞 F) (𝓞 ↥L) = ⊤`. -/
theorem differentIdeal_eq_top_of_le_iSup_finite_unramified {F : Type*} [Field F] [NumberField F]
    {ι : Type*} {f : ι → IntermediateField F (AlgebraicClosure F)}
    [∀ i, FiniteDimensional F ↥(f i)] [∀ i, IsGalois F ↥(f i)] [∀ i, NumberField ↥(f i)]
    (hunr : ∀ i,
      differentIdeal (NumberField.RingOfIntegers F) (NumberField.RingOfIntegers ↥(f i)) = ⊤)
    {L : IntermediateField F (AlgebraicClosure F)} [NumberField ↥L]
    [FiniteDimensional F ↥L] [IsGalois F ↥L] (hL : L ≤ ⨆ i, f i) :
    differentIdeal (NumberField.RingOfIntegers F) (NumberField.RingOfIntegers ↥L) = ⊤ := by
  classical
  -- no nonzero prime of `𝓞 ↥(f i)` divides the relative different of `f i`
  have hnod : ∀ i, ∀ Q : Ideal (𝓞 ↥(f i)), Q.IsPrime →
      ¬ Q ∣ differentIdeal (𝓞 F) (𝓞 ↥(f i)) := by
    intro i Q hQ
    rw [hunr i]
    intro h
    obtain ⟨c, hc⟩ := h
    have hle : (⊤ : Ideal (𝓞 ↥(f i))) ≤ Q := by
      rw [hc]
      exact Ideal.mul_le_left
    exact hQ.ne_top (le_antisymm le_top hle)
  -- the corresponding empty support datum
  have hsupp : ∀ i, ∀ P : Ideal (𝓞 ↥(f i)), P.IsPrime → P ≠ ⊥ →
      P ∣ differentIdeal (𝓞 F) (𝓞 ↥(f i)) → ∃ q ∈ (∅ : Finset ℕ),
        P.LiesOver (Ideal.span ({(q : ℤ)} : Set ℤ)) :=
    fun i P hP _ hdvd => absurd hdvd (hnod i P hP)
  -- support transfer along the (possibly infinite) compositum, with `S = ∅`
  have hmain := Commons.NumberTheory.NumberField.differentIdeal_supp_le_iSup_finset
    (F := F) (S := ∅) (f := f) (fun i => inferInstance) (fun i => inferInstance) hsupp hL
  -- conclude `differentIdeal = ⊤` from "no prime divides it"
  refine Commons.NumberTheory.NumberField.differentIdeal_eq_top_of_forall_not_dvd
    (E := F) (K := ↥L) ?_
  intro Q hQ
  by_cases hQbot : Q = ⊥
  · -- the zero ideal: `⊥ ∣ 𝔡` forces `𝔡 = ⊥`, contradicting `differentIdeal_ne_bot`
    rw [hQbot]
    intro h
    obtain ⟨c, hc⟩ := h
    have hbot : differentIdeal (𝓞 F) (𝓞 ↥L) = ⊥ := by
      rw [hc]; simp
    exact differentIdeal_ne_bot hbot
  · intro hdvd
    exact absurd (hmain Q hQ hQbot hdvd) (by simp)

end Work.ClassFieldTower
