import Mathlib

namespace Work.L2F.Dihedral

/-- Auxiliary arithmetic fact: if `0 < a < m` and `m ∣ 2 * a`, then `a = m / 2`.
(Such an `a` exists only when `m` is even.) -/
lemma nat_eq_half_of_dvd_two_mul {m a : ℕ} (hm : 0 < m) (ha : a < m) (ha0 : a ≠ 0)
    (hdvd : m ∣ 2 * a) : a = m / 2 := by
  obtain ⟨k, hk⟩ := hdvd
  have hkpos : 0 < k := by
    by_contra h
    have : k = 0 := by omega
    subst this
    rw [Nat.mul_zero] at hk
    omega
  have h2m : 2 * a < 2 * m := Nat.mul_lt_mul_of_pos_left ha (by norm_num)
  have h3 : m * k < m * 2 := by
    rw [hk.symm, Nat.mul_comm m 2]; exact h2m
  have hlt : k < 2 := (Nat.mul_lt_mul_left hm).mp h3
  have hk1 : k = 1 := by omega
  have h2a : 2 * a = m := by rw [hk, hk1, Nat.mul_one]
  omega

lemma zmod_half_of_add_self {m : ℕ} (x : ZMod m) (hx : x + x = 0) (hne : x ≠ 0) :
    x = ((m / 2 : ℕ) : ZMod m) := by
  rcases Nat.eq_zero_or_pos m with hm | hm
  · -- `ZMod 0 = ℤ` is an integral domain of characteristic zero, so `2 * x = 0`
    -- forces `x = 0`, contradicting `hne`.
    subst hm
    have h2 : (2 : ZMod 0) * x = 0 := by rw [two_mul]; exact hx
    have h2ne : (2 : ZMod 0) ≠ 0 := by norm_num
    exact absurd ((mul_eq_zero.mp h2).resolve_left h2ne) hne
  · -- `m > 0`: use the canonical representative `x.val ∈ [0, m)`.
    haveI : NeZero m := ⟨hm.ne'⟩
    have hval_ne : x.val ≠ 0 := fun h => hne ((ZMod.val_eq_zero x).mp h)
    have hcast : ((x.val : ℕ) : ZMod m) = x := ZMod.natCast_zmod_val x
    have hx' : ((2 * x.val : ℕ) : ZMod m) = 0 := by
      rw [Nat.cast_mul, Nat.cast_ofNat, hcast, two_mul]
      exact hx
    have hdvd : m ∣ 2 * x.val := (CharP.cast_eq_zero_iff (ZMod m) m (2 * x.val)).mp hx'
    have hhalf : x.val = m / 2 :=
      nat_eq_half_of_dvd_two_mul hm (ZMod.val_lt x) hval_ne hdvd
    rw [← hcast, hhalf]

end Work.L2F.Dihedral
