import Mathlib

namespace Work.OROneRel

/-- Bezout with a small coefficient: if `q` is coprime to `p ≥ 2`, the inverse of `q`
modulo `p` lies in `[0, p)` and yields `q * s = p * t + 1` for a natural number `t`. -/
theorem exists_low_bezout (p q : ℕ) (hp : 2 ≤ p) (hcop : Nat.Coprime q p) :
    ∃ s t : ℕ, s < p ∧ q * s = p * t + 1 := by
  have hp0 : NeZero p := ⟨by omega⟩
  refine ⟨(↑q : ZMod p)⁻¹.val, (q * (↑q : ZMod p)⁻¹.val) / p, ZMod.val_lt _, ?_⟩
  have h1 : (((↑q : ZMod p)⁻¹.val : ℕ) : ZMod p) * (q : ZMod p) = 1 :=
    ZMod.val_inv_mul hcop
  have h2 : ((q * (↑q : ZMod p)⁻¹.val : ℕ) : ZMod p) = 1 := by
    rw [Nat.cast_mul, mul_comm]
    exact h1
  have h3 : q * (↑q : ZMod p)⁻¹.val ≡ 1 [MOD p] := by
    rw [← ZMod.natCast_eq_natCast_iff]
    simpa using h2
  have h4 : q * (↑q : ZMod p)⁻¹.val % p = 1 := by
    have hh := h3
    rw [Nat.ModEq] at hh
    rwa [Nat.mod_eq_of_lt (by omega : 1 < p)] at hh
  have h5 := Nat.mod_add_div (q * (↑q : ZMod p)⁻¹.val) p
  rw [h4] at h5
  omega

end Work.OROneRel
