import Mathlib

namespace Work.LinnikBurgess

/-- Multiplication by `p ^ 3` after the reduction `ZMod (p ^ m) → ZMod (p ^ e)` is injective,
provided `m + 3 ≤ e`.

The reduction sends `w : ZMod (p ^ m)` to `(w.val : ZMod (p ^ e))` (`ZMod.cast_eq_val`).  If two
images agree after multiplication by `p ^ 3`, then `p ^ e ∣ p ^ 3 * (a.val - b.val)`, hence
`p ^ (e - 3) ∣ a.val - b.val`; both `a.val` and `b.val` are `< p ^ m ≤ p ^ (e - 3)`, so they are
equal. -/
theorem scale_cast_injective {p e m : ℕ} [Fact p.Prime] (hm : m + 3 ≤ e) :
    Function.Injective (fun w : ZMod (p ^ m) =>
      (p : ZMod (p ^ e)) ^ 3 * (ZMod.cast w : ZMod (p ^ e))) := by
  have hp0 : p ≠ 0 := (Fact.out (p := p.Prime)).ne_zero
  have hm3 : m ≤ e - 3 := by omega
  have heq : p ^ e = p ^ 3 * p ^ (e - 3) := by
    rw [← pow_add, show 3 + (e - 3) = e by omega]
  have : NeZero (p ^ m) := ⟨pow_ne_zero m hp0⟩
  have : NeZero (p ^ e) := ⟨pow_ne_zero e hp0⟩
  intro a b hab
  change (p : ZMod (p ^ e)) ^ 3 * (ZMod.cast a : ZMod (p ^ e))
      = (p : ZMod (p ^ e)) ^ 3 * (ZMod.cast b : ZMod (p ^ e)) at hab
  rw [ZMod.cast_eq_val, ZMod.cast_eq_val] at hab
  have h1 : ((p ^ 3 * a.val : ℕ) : ZMod (p ^ e))
      = ((p ^ 3 * b.val : ℕ) : ZMod (p ^ e)) := by
    push_cast
    exact hab
  have hmod : (p ^ 3 * a.val) ≡ (p ^ 3 * b.val) [MOD p ^ e] :=
    (ZMod.natCast_eq_natCast_iff _ _ _).mp h1
  have hmod2 : a.val ≡ b.val [MOD p ^ (e - 3)] := by
    unfold Nat.ModEq at hmod ⊢
    rw [heq, Nat.mul_mod_mul_left, Nat.mul_mod_mul_left] at hmod
    exact Nat.mul_left_cancel (pow_pos (Nat.pos_of_ne_zero hp0) 3) hmod
  have hlt : a.val < p ^ (e - 3) :=
    (ZMod.val_lt a).trans_le (Nat.pow_le_pow_right (Nat.pos_of_ne_zero hp0) hm3)
  have hltb : b.val < p ^ (e - 3) :=
    (ZMod.val_lt b).trans_le (Nat.pow_le_pow_right (Nat.pos_of_ne_zero hp0) hm3)
  have hval : a.val = b.val := by
    unfold Nat.ModEq at hmod2
    rwa [Nat.mod_eq_of_lt hlt, Nat.mod_eq_of_lt hltb] at hmod2
  rw [← ZMod.natCast_zmod_val a, ← ZMod.natCast_zmod_val b, hval]

end Work.LinnikBurgess
