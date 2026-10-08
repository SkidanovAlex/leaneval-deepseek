import Mathlib
import Submission.Work.ThmF.ChV3.Chain15

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.ThmF.Prove.step9N2`

Peterfalvi II Ch. V §3, step (9) (arithmetic reduction of the exponent of `|P|`).

Let `p = |P|` be prime, `Q` a complement of `D = H ∩ H^t` in `H`, `V = C_D(t)` and
`W = C_V(K)`.  The order data

* `|H| = |Q| · |D|`,   `|D| = (2^p - 1) · |W| · p`,   `|V| = |W| · p`,

together with `p ∤ |Q|` and `p ∤ |G : H| = |Q| + 1`, force

`|G| = |V| · (|Q| · (|Q| + 1) · (2^p - 1))`,

and Fermat's little theorem in the form `p ∤ 2^p - 1` shows that the second factor is prime
to `p`.  Hence the `p`-adic exponent of `|G|` equals that of `|V|`.
-/

set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false

namespace Work.ThmF.Prove

/-- Fermat's little theorem: for a prime `p`, `p` does not divide `2 ^ p - 1`
(indeed `2 ^ p - 1 ≡ 1 (mod p)`). -/
theorem prime_not_dvd_two_pow_sub_one {p : ℕ} (hp : p.Prime) : ¬ p ∣ 2 ^ p - 1 := by
  intro hdiv
  haveI : Fact p.Prime := ⟨hp⟩
  have h1 : ((2 ^ p - 1 : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hdiv
  have h2 : ((2 ^ p - 1 : ℕ) : ZMod p) = (2 : ZMod p) ^ p - 1 := by
    rw [Nat.cast_sub (show 1 ≤ 2 ^ p from Nat.one_le_two_pow)]
    push_cast
    ring
  have h3 : (2 : ZMod p) ^ p = 2 := ZMod.pow_card 2
  rw [h2, h3] at h1
  have h5 : (2 : ZMod p) - 1 = (1 : ZMod p) := by ring
  rw [h5] at h1
  have h6 : (1 : ZMod p) ≠ 0 := by
    intro h
    have h7 : ((1 : ℕ) : ZMod p) = 0 := by simpa using h
    exact hp.ne_one (Nat.dvd_one.mp ((ZMod.natCast_eq_zero_iff 1 p).mp h7))
  exact h6 h1

theorem step9N2 {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G} {P : Subgroup G}
    (hp : (Nat.card P).Prime) (hpQ : ¬ Nat.card P ∣ Nat.card Q)
    (hG : Nat.card G = (Nat.card Q + 1) * Nat.card ↥H)
    (hH : Nat.card ↥H = Nat.card Q * Nat.card ↥(Submission.Blueprint.twoPoint H t))
    (hD : Nat.card ↥(Submission.Blueprint.twoPoint H t) =
      (2 ^ Nat.card P - 1) * Nat.card ↥(Work.ThmF.W H t) * Nat.card P)
    (hV : Nat.card ↥(Submission.Blueprint.centD H t) = Nat.card ↥(Work.ThmF.W H t) * Nat.card P)
    (hX : ¬ Nat.card P ∣ Nat.card (G ⧸ H)) :
    (Nat.card ↥(Submission.Blueprint.centD H t)).factorization (Nat.card P) =
      (Nat.card G).factorization (Nat.card P) := by
  -- abbreviate `c = 2 ^ |P| - 1`
  set c := 2 ^ Nat.card P - 1 with hc
  -- the index `|G : H|` is `|Q| + 1`
  have hcardH : 0 < Nat.card ↥H := Nat.card_pos
  have hidx : Nat.card (G ⧸ H) = Nat.card Q + 1 := by
    have h1 := Subgroup.card_mul_index H
    rw [Subgroup.index_eq_card] at h1
    rw [hG] at h1
    rw [Nat.mul_comm (Nat.card Q + 1) (Nat.card ↥H)] at h1
    exact Nat.mul_left_cancel hcardH h1
  have hpQ1 : ¬ Nat.card P ∣ Nat.card Q + 1 := by
    rw [← hidx]; exact hX
  have hfermat : ¬ Nat.card P ∣ c := by
    rw [hc]; exact prime_not_dvd_two_pow_sub_one hp
  -- the cofactor of `|V|` is prime to `p`
  have hmain : ¬ Nat.card P ∣ Nat.card Q * (Nat.card Q + 1) * c := by
    intro h
    rcases hp.dvd_mul.mp h with h' | h'
    · rcases hp.dvd_mul.mp h' with h'' | h''
      · exact hpQ h''
      · exact hpQ1 h''
    · exact hfermat h'
  -- `|G| = |V| * (|Q| * (|Q| + 1) * c)`
  have hG' : Nat.card G =
      Nat.card ↥(Submission.Blueprint.centD H t) * (Nat.card Q * (Nat.card Q + 1) * c) := by
    rw [hG, hH, hD, hV]
    ring
  have hVnz : Nat.card ↥(Submission.Blueprint.centD H t) ≠ 0 := Nat.card_pos.ne'
  have hMnz : Nat.card Q * (Nat.card Q + 1) * c ≠ 0 := fun h => hmain (h ▸ dvd_zero _)
  rw [hG', Nat.factorization_mul hVnz hMnz, Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd hmain, add_zero]

end Work.ThmF.Prove
