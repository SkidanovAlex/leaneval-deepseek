import Mathlib
import Submission.Work.Fitting.Main

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option linter.unusedVariables false

namespace Work.ThmF.Tools

/-- **Appendix X, the determination of `p`.**

Let `D` be a finite group of odd order acting faithfully on a finite group `E` of exponent
dividing the prime `p`, transitively on `E^#`.  Then `|E|` is a power of `2` (in particular
`p = 2`).

The argument is elementary: `E` is a `p`-group, so `|E| = p ^ n`; the action of `D` on `E^#`
is transitive, so by orbit–stabiliser `|E^#| = |E| - 1` divides the odd number `|D|`, whence
`|E| - 1` is odd and `|E|` is even.  Since `2 ∣ p ^ n` and `p` is prime, `p = 2`. -/
theorem appX_card_E {D E : Type} [Group D] [Finite D] [Group E] [Finite E]
    (hoddD : Odd (Nat.card D)) {p : ℕ} (hp : p.Prime)
    (hEab : ∀ x y : E, x * y = y * x) (hEexp : ∀ x : E, x ^ p = 1)
    (ρ : D →* MulAut E) (hfaith : Function.Injective ρ)
    (htrans : ∀ a b : E, a ≠ 1 → b ≠ 1 → ∃ d : D, ρ d a = b)
    [Nontrivial E] : ∃ k : ℕ, Nat.card E = 2 ^ k := by
  classical
  -- The action of `D` on `E` induced by the homomorphism `ρ` into the automorphisms of `E`.
  letI : MulDistribMulAction D E := MulDistribMulAction.compHom E ρ
  haveI : Fact p.Prime := ⟨hp⟩
  -- Step 1: `E` is a `p`-group, hence `|E| = p ^ n`.
  have hIsP : IsPGroup p E := fun x => ⟨1, by simpa using hEexp x⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hIsP
  -- A nonidentity element, whose orbit under `D` is all of `E^#`.
  obtain ⟨a, ha⟩ : ∃ a : E, a ≠ 1 := exists_ne 1
  have horbit : MulAction.orbit D a = {x : E | x ≠ 1} := by
    ext x
    constructor
    · rintro ⟨d, hd⟩
      rw [← hd]
      intro h
      have h1 : (ρ d) a = (ρ d) 1 := by rw [map_one]; exact h
      exact ha ((ρ d).injective h1)
    · intro hx
      obtain ⟨d, hd⟩ := htrans a x ha hx
      exact ⟨d, hd⟩
  have horbit_card : Nat.card (MulAction.orbit D a) = Nat.card {x : E // x ≠ 1} :=
    Nat.card_congr (Equiv.subtypeEquivRight (fun x => by simp [horbit]))
  -- Step 2: orbit–stabiliser gives `|E^#| ∣ |D|`.
  have hcard : Nat.card D =
      Nat.card (MulAction.orbit D a) * Nat.card (MulAction.stabilizer D a) := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (MulAction.stabilizer D a)]
    congr 1
    exact Nat.card_congr (MulAction.orbitEquivQuotientStabilizer D a).symm
  have hdiv : Nat.card (MulAction.orbit D a) ∣ Nat.card D := ⟨_, hcard⟩
  have hm_dvd : Nat.card {x : E // x ≠ 1} ∣ Nat.card D := by
    rw [← horbit_card]; exact hdiv
  have hm_odd : Odd (Nat.card {x : E // x ≠ 1}) := by
    rw [← Nat.not_even_iff_odd]
    intro hm
    obtain ⟨t, ht⟩ := hm_dvd
    have : Even (Nat.card D) := by rw [ht]; exact hm.mul_right t
    exact (Nat.not_even_iff_odd.mpr hoddD) this
  -- Step 3: `|E| = |E^#| + 1` is even.
  letI : Fintype E := Fintype.ofFinite E
  have hsub : Nat.card {x : E // x ≠ 1} = Nat.card E - 1 := by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    have h := Fintype.card_subtype_compl (fun x : E => x = 1)
    rw [Fintype.card_subtype_eq] at h
    simpa using h
  have hE : Nat.card E = Nat.card {x : E // x ≠ 1} + 1 := by
    have hpos : 0 < Nat.card E := Nat.card_pos
    omega
  have hEvenE : Even (Nat.card E) := by
    rw [hE]
    exact Nat.even_add_one.mpr (Nat.not_even_iff_odd.mpr hm_odd)
  -- Step 4: `2 ∣ |E| = p ^ n` forces `p = 2`.
  have h2dvd : 2 ∣ Nat.card E := even_iff_two_dvd.mp hEvenE
  have hp2 : p = 2 := by
    have h2pn : 2 ∣ p ^ n := by rw [← hn]; exact h2dvd
    have h2p : 2 ∣ p := Nat.prime_two.dvd_of_dvd_pow h2pn
    rcases hp.eq_one_or_self_of_dvd 2 h2p with h | h
    · exact absurd h (by norm_num)
    · exact h.symm
  exact ⟨n, by rw [hn, hp2]⟩

end Work.ThmF.Tools
