import Mathlib

/-!
# The kernel of the reduction map `(ZMod pᵃ)ˣ →* (ZMod pᵃ⁻¹)ˣ`

For a prime `p` and `2 ≤ a`, the natural reduction
`unitsMap (hd : p ^ (a - 1) ∣ p ^ a) : (ZMod (p ^ a))ˣ →* (ZMod (p ^ (a - 1)))ˣ`
is surjective, and its kernel — the group of "principal units" congruent to `1`
modulo `p ^ (a - 1)` — has cardinality `p`.

The proof is a cardinality count: the first isomorphism theorem gives
`Nat.card ker * Nat.card range = Nat.card G`, surjectivity identifies `range` with
the whole codomain, and Euler's totient formula for prime powers
`Nat.totient_prime_pow` computes both sides.
-/

namespace Commons.NumberTheory.ZMod

theorem card_ker_unitsMap_prime_pow {p a : ℕ} (hp : p.Prime) (ha : 2 ≤ a)
    (hd : p ^ (a - 1) ∣ p ^ a) :
    Nat.card (ZMod.unitsMap hd).ker = p := by
  have hp2 : 2 ≤ p := hp.two_le
  have hpapos : 0 < p ^ a := pow_pos hp.pos a
  have hp1pos : 0 < p ^ (a - 1) := pow_pos hp.pos (a - 1)
  have hNeZeroA : NeZero (p ^ a) := ⟨ne_of_gt hpapos⟩
  have hNeZeroB : NeZero (p ^ (a - 1)) := ⟨ne_of_gt hp1pos⟩
  set f : (ZMod (p ^ a))ˣ →* (ZMod (p ^ (a - 1)))ˣ := ZMod.unitsMap hd with hf
  have hsurj : Function.Surjective f := by
    rw [hf]; exact ZMod.unitsMap_surjective hd
  have hrange : f.range = ⊤ := MonoidHom.range_eq_top.mpr hsurj
  -- First isomorphism theorem: `Nat.card ker * Nat.card range = Nat.card G`.
  have hcard : Nat.card f.ker * Nat.card f.range = Nat.card (ZMod (p ^ a))ˣ := by
    rw [← Subgroup.index_ker f]
    exact Subgroup.card_mul_index f.ker
  have hGa : Nat.card (ZMod (p ^ a))ˣ = p ^ (a - 1) * (p - 1) := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]
    exact Nat.totient_prime_pow hp (by omega)
  have hGb : Nat.card (ZMod (p ^ (a - 1)))ˣ = p ^ (a - 2) * (p - 1) := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient,
      Nat.totient_prime_pow hp (by omega : 0 < a - 1)]
    rw [show (a - 1) - 1 = a - 2 by omega]
  rw [hrange, Subgroup.card_top, hGb, hGa] at hcard
  -- hcard : Nat.card f.ker * (p ^ (a - 2) * (p - 1)) = p ^ (a - 1) * (p - 1)
  have hpos : 0 < p ^ (a - 2) * (p - 1) := by
    apply Nat.mul_pos
    · positivity
    · omega
  have h1 : Nat.card f.ker * (p ^ (a - 2) * (p - 1)) = p * (p ^ (a - 2) * (p - 1)) := by
    rw [hcard]
    have hpow : p ^ (a - 1) = p * p ^ (a - 2) := by
      rw [show a - 1 = (a - 2) + 1 by omega, pow_succ, mul_comm]
    rw [hpow, mul_assoc]
  exact Nat.mul_right_cancel hpos h1

end Commons.NumberTheory.ZMod
