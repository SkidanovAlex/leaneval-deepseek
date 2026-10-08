import Mathlib
import Submission.Work.ThmF.ChV3.Step16Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.ThmF.ChV3.Prove

/-- **Fermat's little theorem corollary**: for a prime `p`, the prime `p` never divides `2 ^ p - 1`
(indeed `2 ^ p ≡ 2 [ZMOD p]`, so `2 ^ p - 1 ≡ 1 [ZMOD p] ≠ 0`).  This is the arithmetic input that
prevents the factor `2 ^ |P| - 1` from contributing to the `|P|`-part of `|H|`. -/
theorem prime_not_dvd_two_pow_sub_one {p : ℕ} (hp : p.Prime) : ¬ p ∣ 2 ^ p - 1 := by
  intro h
  have h1 : (↑p : ℤ) ∣ ((2 : ℤ) ^ p - 1) := by
    have e : ((2 : ℤ) ^ p - 1) = ((2 ^ p - 1 : ℕ) : ℤ) := by
      rw [Nat.cast_sub Nat.one_le_two_pow]; push_cast; ring
    rw [e]; exact_mod_cast h
  have h2 : (↑p : ℤ) ∣ (2 : ℤ) - (2 : ℤ) ^ p := (Int.ModEq.pow_prime_eq_self hp (2 : ℤ)).dvd
  have h3 : (↑p : ℤ) ∣ 1 := by
    have := Int.dvd_add h2 h1
    simpa using this
  exact hp.not_dvd_one (Int.natCast_dvd_natCast.mp h3)

theorem pPart_H_101 {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t s r : G} {P : Subgroup G}
    (c : Work.ThmF.ChV3.CtxF H Q t s r P)
    (hH : Nat.card ↥H = Nat.card Q * Nat.card ↥(Submission.Blueprint.twoPoint H t))
    (hD : Nat.card ↥(Submission.Blueprint.twoPoint H t) =
      (2 ^ Nat.card P - 1) * Nat.card ↥(Work.ThmF.W H t) * Nat.card P)
    (hQ : ¬ Nat.card P ∣ Nat.card Q) (hW : ¬ Nat.card P ∣ Nat.card ↥(Work.ThmF.W H t)) :
    Work.ThmF.ChV3.pPart (Nat.card P) (Nat.card ↥H) = Nat.card P := by
  have ha : (Nat.card P).Prime := c.P_prime
  -- Non-vanishing of the three factors besides the `|P|`-factor.
  have hb : Nat.card Q ≠ 0 := Nat.card_pos.ne'
  have hw : Nat.card ↥(Work.ThmF.W H t) ≠ 0 := Nat.card_pos.ne'
  have hpa : Nat.card P ≠ 0 := ha.pos.ne'
  -- `2 ^ |P| - 1 > 0` because `|P| ≥ 2`.
  have hd_pos : 0 < 2 ^ Nat.card P - 1 := by
    have h2 : 2 ^ 1 ≤ 2 ^ Nat.card P := Nat.pow_le_pow_right (by norm_num) (by omega)
    simp only [pow_one] at h2; omega
  have hbdw : Nat.card Q * (2 ^ Nat.card P - 1) * Nat.card ↥(Work.ThmF.W H t) ≠ 0 :=
    mul_ne_zero (mul_ne_zero hb hd_pos.ne') hw
  -- `|P|` divides none of the three factors, hence not their product.
  have hnotdvd :
      ¬ Nat.card P ∣ Nat.card Q * (2 ^ Nat.card P - 1) * Nat.card ↥(Work.ThmF.W H t) := by
    intro h
    have h1 : Nat.card P ∣ Nat.card Q * (2 ^ Nat.card P - 1) ∨
        Nat.card P ∣ Nat.card ↥(Work.ThmF.W H t) := ha.dvd_mul.mp h
    rcases h1 with h1 | h1
    · have h2 : Nat.card P ∣ Nat.card Q ∨ Nat.card P ∣ 2 ^ Nat.card P - 1 := ha.dvd_mul.mp h1
      rcases h2 with h2 | h2
      · exact hQ h2
      · exact prime_not_dvd_two_pow_sub_one ha h2
    · exact hW h1
  -- `|H| = (|Q| * (2 ^ |P| - 1) * |W|) * |P|`, and the bracket is not divisible by `|P|`.
  have hmul : Nat.card ↥H =
      (Nat.card Q * (2 ^ Nat.card P - 1) * Nat.card ↥(Work.ThmF.W H t)) * Nat.card P := by
    rw [hH, hD]; ring
  have hfac : (Nat.card ↥H).factorization (Nat.card P) = 1 := by
    rw [hmul, Nat.factorization_mul hbdw hpa, Finsupp.add_apply,
        Nat.factorization_eq_zero_of_not_dvd hnotdvd, Nat.Prime.factorization_self ha]
  simp only [Work.ThmF.ChV3.pPart, hfac, pow_one]

end Work.ThmF.ChV3.Prove
