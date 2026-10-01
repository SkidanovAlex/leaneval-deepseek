import Mathlib

set_option linter.style.haveILetI false

/-!
# The kernel of the reduction map `(ZMod pᵉ)ˣ →* (ZMod pᵉ⁻¹)ˣ` consists of `1 + pᵉ⁻¹ · t`

For a prime `p` and `2 ≤ e`, a unit `u` of `ZMod (p ^ e)` whose image under the
natural reduction `ZMod.unitsMap hd : (ZMod (p ^ e))ˣ →* (ZMod (p ^ (e - 1)))ˣ`
is `1` is congruent to `1` modulo `p ^ (e - 1)`; explicitly
`u = 1 + p ^ (e - 1) * t` in `ZMod (p ^ e)` for some `t : ℕ`.

The proof reduces `u` to its natural representative `m = u.val`, observes that the
reduction of `u` is `m` modulo `p ^ (e - 1)`, hence `m ≡ 1 [MOD p ^ (e - 1)]`, and
reads off the division of `m` by `p ^ (e - 1)`.
-/

namespace Work.LinnikBurgess

theorem ddKernelUnitsMap {p e : ℕ} (hp : p.Prime) (he : 2 ≤ e) (hd : p ^ (e - 1) ∣ p ^ e)
    {u : (ZMod (p ^ e))ˣ} (hu : ZMod.unitsMap hd u = 1) :
    ∃ t : ℕ, (u : ZMod (p ^ e)) = ((1 + p ^ (e - 1) * t : ℕ) : ZMod (p ^ e)) := by
  haveI : NeZero (p ^ e) := ⟨(pow_pos hp.pos e).ne'⟩
  -- The reduction of `u` is `1`: coerce `hu` to `ZMod (p ^ (e-1))`.
  have hu_val : ((u : ZMod (p ^ e)).cast : ZMod (p ^ (e - 1))) = 1 := by
    have h1 := congrArg (fun w : (ZMod (p ^ (e - 1)))ˣ => (w : ZMod (p ^ (e - 1)))) hu
    rw [Units.val_one] at h1
    rwa [ZMod.unitsMap_val] at h1
  -- `m` is the canonical representative of `u` in `{0, …, p^e - 1}`.
  set m : ℕ := (u : ZMod (p ^ e)).val with hm
  have hval : ((m : ℕ) : ZMod (p ^ (e - 1))) = 1 := by
    rw [hm]
    rw [← ZMod.cast_eq_val (a := (u : ZMod (p ^ e)))]
    exact hu_val
  have hmod : m ≡ 1 [MOD p ^ (e - 1)] := by
    rw [← ZMod.natCast_eq_natCast_iff m 1 (p ^ (e - 1))]
    simpa using hval
  have hge : 1 < p ^ (e - 1) := by
    have h1 : 1 ≤ e - 1 := by omega
    calc 1 < p := hp.one_lt
      _ = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ (e - 1) := Nat.pow_le_pow_right hp.pos h1
  have hm1 : m % p ^ (e - 1) = 1 := by
    have h2 := hmod
    rw [Nat.ModEq] at h2
    rw [h2, Nat.mod_eq_of_lt hge]
  have hdecomp : m = 1 + p ^ (e - 1) * (m / p ^ (e - 1)) := by
    have h := Nat.div_add_mod m (p ^ (e - 1))
    rw [hm1] at h
    omega
  refine ⟨m / p ^ (e - 1), ?_⟩
  have h1 : (u : ZMod (p ^ e)) = ((m : ℕ) : ZMod (p ^ e)) := by
    rw [hm]
    exact (ZMod.natCast_zmod_val (u : ZMod (p ^ e))).symm
  rw [h1, hdecomp.symm]

end Work.LinnikBurgess
