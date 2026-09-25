import Mathlib
import Submission.Work.ClassFieldTower.Defs
import Submission.Commons.NumberTheory.NumberField.differentIdeal_eq_top_of_ramificationIdx
import Submission.Commons.NumberTheory.RamificationInertia.ramificationIdx_one_sup

/-!
# The relative different is trivial iff it is trivial after an `F`-algebra isomorphism

If `E` and `E'` are number fields with a common base field `F` and `e : E ≃ₐ[F] E'` is an
`F`-algebra isomorphism, then `differentIdeal (𝓞 F) (𝓞 E) = ⊤` implies
`differentIdeal (𝓞 F) (𝓞 E') = ⊤`.  Equivalently: the property "the extension of `F` is
unramified at every finite prime" is invariant under `F`-algebra isomorphisms.

The proof goes through the ramification indices of the primes: a prime ideal of a ring of
integers divides the relative different if and only if its ramification index is different
from `1`, and ramification indices are preserved by `R`-algebra isomorphisms
(`Commons.NumberTheory.RamificationInertia.ramificationIdx_comap_algEquiv`).  Since a proper
ideal of a Dedekind domain is contained in a maximal ideal, the different is the unit ideal
if and only if no prime ideal `≠ ⊥` divides it.

The two auxiliary facts about ideals of a Dedekind domain are stated in full generality
(`not_dvd_top_of_isPrime`, `eq_top_of_forall_prime_ne_bot_not_dvd`), since the same reduction
is used everywhere a "different is trivial" statement has to be transported.
-/

set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.overlappingInstances false

open scoped Classical
open scoped NumberField
open NumberField

noncomputable section

namespace Work.ClassFieldTower

/-- A prime ideal is not the unit ideal, in particular it does not divide it. -/
private lemma not_dvd_top_of_isPrime {R : Type*} [CommRing R] [IsDedekindDomain R] {Q : Ideal R}
    (hQ : Q.IsPrime) : ¬ Q ∣ (⊤ : Ideal R) := by
  intro hcon
  exact hQ.ne_top (le_antisymm le_top (Ideal.dvd_iff_le.mp hcon))

/-- A nonzero ideal of a Dedekind domain which is not divisible by any prime ideal `≠ ⊥`
is the unit ideal.  (A nonzero proper ideal is contained in a maximal ideal, which is prime
and nonzero because it contains the nonzero ideal.) -/
private lemma eq_top_of_forall_prime_ne_bot_not_dvd {R : Type*} [CommRing R]
    [IsDedekindDomain R] {I : Ideal R} (hI : I ≠ ⊥)
    (h : ∀ Q : Ideal R, Q.IsPrime → Q ≠ ⊥ → ¬ Q ∣ I) : I = ⊤ := by
  by_contra hne
  obtain ⟨M, hMmax, hIM⟩ := Ideal.exists_le_maximal I hne
  have hMne : M ≠ ⊥ := fun hbot => hI (le_bot_iff.mp (hbot ▸ hIM))
  exact h M hMmax.isPrime hMne (Ideal.dvd_iff_le.mpr hIM)

theorem differentIdeal_eq_top_of_algEquiv {F E E' : Type*} [Field F] [NumberField F]
    [Field E] [NumberField E] [Field E'] [NumberField E'] [Algebra F E] [Algebra F E']
    (e : E ≃ₐ[F] E')
    (h : differentIdeal (NumberField.RingOfIntegers F) (NumberField.RingOfIntegers E) = ⊤) :
    differentIdeal (NumberField.RingOfIntegers F) (NumberField.RingOfIntegers E') = ⊤ := by
  -- the isomorphism of rings of integers induced by `e`
  let φ : 𝓞 E ≃ₐ[𝓞 F] 𝓞 E' := NumberField.RingOfIntegers.mapAlgEquiv e
  -- it suffices that no prime ideal `≠ ⊥` of `𝓞 E'` divides the different
  refine eq_top_of_forall_prime_ne_bot_not_dvd
    (I := differentIdeal (𝓞 F) (𝓞 E')) (by exact differentIdeal_ne_bot) ?_
  intro P hP hPne
  -- the prime `Q = P ∩ 𝓞 E` of `𝓞 E`
  let Q : Ideal (𝓞 E) := P.comap φ
  haveI hQprime : Q.IsPrime := Ideal.IsPrime.comap φ
  have hmap : Ideal.map (φ : 𝓞 E →+* 𝓞 E') Q = P :=
    Ideal.map_comap_of_surjective (φ : 𝓞 E →+* 𝓞 E') φ.surjective P
  have hQne : Q ≠ ⊥ := by
    intro hbot
    rw [hbot, Ideal.map_bot] at hmap
    exact hPne hmap.symm
  -- `Q` is unramified over `𝓞 F`, because the different of `E/F` is trivial
  have hQram : Q.ramificationIdx (𝓞 F) = 1 := by
    rw [← Commons.NumberTheory.NumberField.ramificationIdx_one_iff_not_dvd_differentIdeal
      (E := F) (K := E) Q hQprime, h]
    exact not_dvd_top_of_isPrime hQprime
  -- ramification indices are preserved by the isomorphism
  have htrans : Q.ramificationIdx (𝓞 F) = P.ramificationIdx (𝓞 F) :=
    Commons.NumberTheory.RamificationInertia.ramificationIdx_comap_algEquiv
      (P.under (𝓞 F)) (Ideal.under_ne_bot (𝓞 F) (P := P) hPne) φ P
  -- hence `P` is unramified over `𝓞 F`, i.e. it does not divide the different
  rw [Commons.NumberTheory.NumberField.ramificationIdx_one_iff_not_dvd_differentIdeal
    (E := F) (K := E') P hP, ← htrans]
  exact hQram

end Work.ClassFieldTower
