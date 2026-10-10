import Mathlib.Algebra.Order.Ring.Star
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import Submission.Work.SSGRoute.GrunwaldEscapeCore.exists_prime_mem_rayClass
import Submission.Work.SSGRoute.PinnedTwin.card_twoTorsion_range_le
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Existence of an unattained sign pattern at odd primes

Let `K` be a number field, `s` a finite set of height-one primes of `𝓞 K`, none of which
contains `2`, and suppose `rank K + 1 < s.card`.  We show that there is a sign pattern
`ε : HeightOneSpectrum (𝓞 K) → ZMod 2` that is *not* attained by the unit group: for every unit
`u : (𝓞 K)ˣ` there is `q ∈ s` with

`mk (q²) u ≠ mk (q²) (if ε q = 0 then 1 else -1)`.

The proof is a counting (pigeonhole) argument.  The units map to the finite abelian group
`G = ∏_{q ∈ s} (𝓞 K ⧸ q²)ˣ`; the `±1`-valued tuples are the `2`-torsion elements of `G`, and the
number of sign patterns on `s` is `2 ^ s.card`.  Since `card_twoTorsion_range_le` bounds the
`2`-torsion inside the image of the unit group by `2 ^ (rank K + 1) < 2 ^ s.card`, some sign
pattern is missing from the image, which is exactly the claimed statement.

## Main result

* `Work.SSGRoute.PinnedTwin.exists_signPattern_notMem_range`
-/

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open NumberField IsDedekindDomain
open scoped NumberField

namespace Work.SSGRoute.PinnedTwin

section Helpers

variable {K : Type} [Field K] [NumberField K]

/-- The quotient `𝓞 K ⧸ q²` is finite for every height-one prime `q`. -/
private lemma finite_quotient_sq (q : HeightOneSpectrum (𝓞 K)) :
    Finite (𝓞 K ⧸ q.asIdeal ^ 2) := by
  have hne : q.asIdeal ^ 2 ≠ ⊥ := by
    intro h
    rw [pow_two, Ideal.mul_eq_bot] at h
    exact h.elim q.ne_bot q.ne_bot
  exact Ring.HasFiniteQuotients.finiteQuotient hne

/-- The product of the unit groups `(𝓞 K ⧸ q²)ˣ` over the primes `q ∈ s`. -/
private abbrev signGroup (s : Finset (HeightOneSpectrum (𝓞 K))) :=
  (q : ↥s) → (𝓞 K ⧸ (q.1.asIdeal ^ 2))ˣ

/-- The sign unit `±1` attached to `χ : ZMod 2` inside `(𝓞 K)ˣ`. -/
private def signUnit (χ : ZMod 2) : (𝓞 K)ˣ := if χ = 0 then 1 else -1

private lemma signUnit_val (χ : ZMod 2) :
    ((signUnit (K := K) χ : (𝓞 K)ˣ) : 𝓞 K) = if χ = 0 then 1 else -1 := by
  unfold signUnit; split <;> simp

private lemma signUnit_mul_self (χ : ZMod 2) :
    signUnit (K := K) χ * signUnit χ = 1 := by
  unfold signUnit; split <;> simp

/-- In `ZMod 2`, the only nonzero element is `1`. -/
private lemma zmod_two_eq_one : ∀ χ : ZMod 2, χ ≠ 0 → χ = 1 := by
  intro χ hχ
  fin_cases χ
  · exact absurd rfl hχ
  · rfl

/-- The sign pattern, as an element of `signGroup s`. -/
private def signPat (s : Finset (HeightOneSpectrum (𝓞 K))) :
    (↥s → ZMod 2) → signGroup (K := K) s :=
  fun ε q => Units.map (Ideal.Quotient.mk (q.1.asIdeal ^ 2)) (signUnit (K := K) (ε q))

/-- Every sign pattern is `2`-torsion in `signGroup s`. -/
private lemma signPat_mul_self (s : Finset (HeightOneSpectrum (𝓞 K)))
    (ε : ↥s → ZMod 2) :
    signPat (K := K) s ε * signPat (K := K) s ε = 1 := by
  funext q
  simp only [Pi.mul_apply, Pi.one_apply, signPat]
  rw [← map_mul, signUnit_mul_self, map_one]

/-- Distinct sign patterns give distinct elements of `signGroup s`; this is where `2 ∉ q` is
used: in `𝓞 K ⧸ q²` we have `1 ≠ -1`. -/
private lemma signPat_injective (s : Finset (HeightOneSpectrum (𝓞 K)))
    (hs : ∀ q ∈ s, (2 : 𝓞 K) ∉ q.asIdeal) :
    Function.Injective (signPat (K := K) s) := by
  intro ε ε' h
  funext q
  have hq : signPat (K := K) s ε q = signPat (K := K) s ε' q := congrFun h q
  have hv : (Ideal.Quotient.mk (q.1.asIdeal ^ 2)) (if ε q = 0 then (1 : 𝓞 K) else -1)
      = (Ideal.Quotient.mk (q.1.asIdeal ^ 2)) (if ε' q = 0 then (1 : 𝓞 K) else -1) := by
    have := congrArg (fun w : (𝓞 K ⧸ q.1.asIdeal ^ 2)ˣ => (w : 𝓞 K ⧸ q.1.asIdeal ^ 2)) hq
    simpa [signPat, signUnit_val] using this
  rcases eq_or_ne (ε q) 0 with h0 | h0
  · rcases eq_or_ne (ε' q) 0 with h0' | h0'
    · rw [h0, h0']
    · exfalso
      rw [if_pos h0, if_neg h0'] at hv
      have hmem : (2 : 𝓞 K) ∈ q.1.asIdeal ^ 2 := by
        have h := (Ideal.Quotient.eq (I := q.1.asIdeal ^ 2)).mp hv
        convert h using 1
        ring
      exact hs q.1 q.2 (Ideal.pow_le_self (show (2 : ℕ) ≠ 0 by norm_num) hmem)
  · rcases eq_or_ne (ε' q) 0 with h0' | h0'
    · exfalso
      rw [if_pos h0', if_neg h0] at hv
      have hmem : (2 : 𝓞 K) ∈ q.1.asIdeal ^ 2 := by
        have h := (Ideal.Quotient.eq (I := q.1.asIdeal ^ 2)).mp hv.symm
        convert h using 1
        ring
      exact hs q.1 q.2 (Ideal.pow_le_self (show (2 : ℕ) ≠ 0 by norm_num) hmem)
    · rw [zmod_two_eq_one (ε q) h0, zmod_two_eq_one (ε' q) h0']

end Helpers

theorem exists_signPattern_notMem_range {K : Type} [Field K] [NumberField K]
    (s : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))
    (hs : ∀ q ∈ s, (2 : NumberField.RingOfIntegers K) ∉ q.asIdeal)
    (hcard : NumberField.Units.rank K + 1 < s.card) :
    ∃ ε : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K) → ZMod 2,
      (∀ u : (NumberField.RingOfIntegers K)ˣ,
        ∃ q ∈ s,
          Ideal.Quotient.mk (q.asIdeal ^ 2) (u : NumberField.RingOfIntegers K) ≠
            Ideal.Quotient.mk (q.asIdeal ^ 2)
              (if ε q = 0 then (1 : NumberField.RingOfIntegers K) else -1)) := by
  classical
  haveI : ∀ q : ↥s, Finite (𝓞 K ⧸ q.1.asIdeal ^ 2) := fun q => finite_quotient_sq q.1
  haveI : Finite (signGroup (K := K) s) := inferInstance
  haveI : Fintype (signGroup (K := K) s) := Fintype.ofFinite _
  let φ : (𝓞 K)ˣ →* signGroup (K := K) s :=
    MonoidHom.pi fun q => Units.map (Ideal.Quotient.mk (q.1.asIdeal ^ 2))
  -- Some sign pattern is not in the image of the unit group.
  have hex : ∃ ε : ↥s → ZMod 2, signPat (K := K) s ε ∉ φ.range := by
    by_contra hcon
    push Not at hcon
    have hsub : Set.range (signPat (K := K) s) ⊆
        {g : signGroup (K := K) s | g ∈ φ.range ∧ g * g = 1} := by
      rintro g ⟨ε, rfl⟩
      exact ⟨hcon ε, signPat_mul_self s ε⟩
    have h1 : (Set.range (signPat (K := K) s)).ncard = 2 ^ s.card := by
      rw [Set.ncard_range_of_injective (signPat_injective s hs)]
      rw [Nat.card_eq_fintype_card, Fintype.card_fun, ZMod.card, Fintype.card_coe]
    have h2 : (Set.range (signPat (K := K) s)).ncard ≤ 2 ^ (NumberField.Units.rank K + 1) :=
      (Set.ncard_le_ncard hsub).trans (card_twoTorsion_range_le φ)
    have hlt : 2 ^ (NumberField.Units.rank K + 1) < 2 ^ s.card :=
      (Nat.pow_lt_pow_iff_right (by norm_num)).mpr hcard
    have : 2 ^ s.card ≤ 2 ^ (NumberField.Units.rank K + 1) := h1 ▸ h2
    exact absurd this (not_le_of_gt hlt)
  obtain ⟨ε, hε⟩ := hex
  -- Extend `ε` to all places by `0` outside `s` and conclude.
  let E : HeightOneSpectrum (𝓞 K) → ZMod 2 := fun q => if h : q ∈ s then ε ⟨q, h⟩ else 0
  have hE : ∀ q : ↥s, E q.1 = ε q := by
    intro q
    dsimp only [E]
    rw [dif_pos q.2]
  refine ⟨E, ?_⟩
  intro u
  by_contra hcon
  push Not at hcon
  apply hε
  rw [MonoidHom.mem_range]
  refine ⟨u, ?_⟩
  funext q
  apply Units.ext
  simp only [MonoidHom.pi_apply, Units.coe_map, signPat, signUnit_val, φ]
  have hq := hcon q.1 q.2
  rw [hE q] at hq
  exact hq

end Work.SSGRoute.PinnedTwin
