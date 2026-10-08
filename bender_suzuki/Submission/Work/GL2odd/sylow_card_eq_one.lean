import Mathlib
import Submission.Work.GL2odd.odd_dvd_pm1_sq_mul_pp1_eq_one

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace Work.GL2odd

open Nat

/-- The cardinality of `GL (Fin 2) (ZMod p)` is `p * (p - 1)^2 * (p + 1)`. -/
private theorem card_GL_two (p : ℕ) [Fact p.Prime] :
    Nat.card (GL (Fin 2) (ZMod p)) = p * ((p - 1) ^ 2 * (p + 1)) := by
  have hpge : 2 ≤ p := (Fact.out : p.Prime).two_le
  rw [Matrix.card_GL_field]
  rw [Fin.prod_univ_two]
  rw [ZMod.card]
  simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one]
  have h1 : ((p ^ 2 - 1 : ℕ) : ℤ) = (p : ℤ) ^ 2 - 1 := by
    rw [Nat.cast_sub (by nlinarith : 1 ≤ p ^ 2)]; push_cast; ring
  have h2 : ((p ^ 2 - p : ℕ) : ℤ) = (p : ℤ) ^ 2 - p := by
    rw [Nat.cast_sub (by nlinarith : p ≤ p ^ 2)]; push_cast; ring
  have h3 : ((p - 1 : ℕ) : ℤ) = (p : ℤ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ p)]; push_cast; ring
  apply Nat.cast_injective (R := ℤ)
  push_cast
  rw [h1, h2, h3]
  ring

theorem sylow_card_eq_one {p : ℕ} [Fact p.Prime] (hpodd : Odd p)
    (G : Subgroup (GL (Fin 2) (ZMod p))) (hodd : Odd (Nat.card G)) (hp : p ∣ Nat.card G) :
    Nat.card (Sylow p ↥G) = 1 := by
  haveI : Finite (Sylow p ↥G) := inferInstance
  -- The number `n` of Sylow `p`-subgroups divides `|G|`, hence is odd.
  obtain ⟨P⟩ := Sylow.nonempty (p := p) (G := ↥G)
  have hn_dvd : Nat.card (Sylow p ↥G) ∣ Nat.card ↥G :=
    (Sylow.card_dvd_index P).trans (Subgroup.index_dvd_card (P : Subgroup ↥G))
  have hnodd : Odd (Nat.card (Sylow p ↥G)) := Odd.of_dvd_nat hodd hn_dvd
  -- `n` divides `|GL (Fin 2) (ZMod p)| = p * (p - 1)^2 * (p + 1)`, and `p ∤ n`,
  -- so `n ∣ (p - 1)^2 * (p + 1)`.
  have hn_dvd_pN : Nat.card (Sylow p ↥G) ∣ p * ((p - 1) ^ 2 * (p + 1)) := by
    rw [← card_GL_two p]
    exact hn_dvd.trans (Subgroup.card_subgroup_dvd_card G)
  have hnp : ¬ p ∣ Nat.card (Sylow p ↥G) := not_dvd_card_sylow p ↥G
  have hcop : (Nat.card (Sylow p ↥G)).Coprime p :=
    Nat.coprime_comm.mpr (((Fact.out : p.Prime).coprime_iff_not_dvd).mpr hnp)
  have hn_dvd_N : Nat.card (Sylow p ↥G) ∣ (p - 1) ^ 2 * (p + 1) :=
    hcop.dvd_of_dvd_mul_left hn_dvd_pN
  -- Sylow's third theorem: `n ≡ 1 [MOD p]`.
  have hnmod : Nat.card (Sylow p ↥G) ≡ 1 [MOD p] := card_sylow_modEq_one p ↥G
  exact odd_dvd_pm1_sq_mul_pp1_eq_one (Fact.out : p.Prime) hpodd hnodd hn_dvd_N hnmod

end Work.GL2odd
