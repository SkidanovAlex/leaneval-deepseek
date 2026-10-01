import Mathlib

set_option linter.style.haveILetI false

namespace Commons.NumberTheory.ZMod

/-- Decomposition of a natural number cast into `ZMod (p^(k+1))` according to the
    Euclidean division by `p^k`: `n ≡ n % p^k + p^k * (n / p^k % p)  (mod p^(k+1))`. -/
lemma natCast_decomp (p k n : ℕ) :
    ((n : ℕ) : ZMod (p ^ (k + 1))) =
      ((n % p ^ k : ℕ) : ZMod (p ^ (k + 1))) +
        ((p ^ k : ℕ) : ZMod (p ^ (k + 1))) * ((n / p ^ k % p : ℕ) : ZMod (p ^ (k + 1))) := by
  have h1 : p ^ k * (n / p ^ k) + n % p ^ k = n := Nat.div_add_mod n (p ^ k)
  have h2 : p * (n / p ^ k / p) + n / p ^ k % p = n / p ^ k := Nat.div_add_mod (n / p ^ k) p
  have hpp : ((p ^ k : ℕ) : ZMod (p ^ (k + 1))) * ((p : ℕ) : ZMod (p ^ (k + 1))) = 0 := by
    rw [← Nat.cast_mul, ← Nat.pow_succ p k, ZMod.natCast_self]
  calc ((n : ℕ) : ZMod (p ^ (k + 1)))
      = ((p ^ k * (n / p ^ k) + n % p ^ k : ℕ) : ZMod (p ^ (k + 1))) := by rw [h1]
    _ = ((p ^ k : ℕ) : ZMod (p ^ (k + 1))) * ((n / p ^ k : ℕ) : ZMod (p ^ (k + 1)))
          + ((n % p ^ k : ℕ) : ZMod (p ^ (k + 1))) := by push_cast; ring
    _ = ((p ^ k : ℕ) : ZMod (p ^ (k + 1)))
          * ((p * (n / p ^ k / p) + n / p ^ k % p : ℕ) : ZMod (p ^ (k + 1)))
          + ((n % p ^ k : ℕ) : ZMod (p ^ (k + 1))) := by conv_lhs => rw [← h2]
    _ = (((p ^ k : ℕ) : ZMod (p ^ (k + 1))) * ((p : ℕ) : ZMod (p ^ (k + 1))))
          * ((n / p ^ k / p : ℕ) : ZMod (p ^ (k + 1)))
          + ((p ^ k : ℕ) : ZMod (p ^ (k + 1))) * ((n / p ^ k % p : ℕ) : ZMod (p ^ (k + 1)))
          + ((n % p ^ k : ℕ) : ZMod (p ^ (k + 1))) := by push_cast; ring
    _ = ((n % p ^ k : ℕ) : ZMod (p ^ (k + 1)))
          + ((p ^ k : ℕ) : ZMod (p ^ (k + 1))) * ((n / p ^ k % p : ℕ) : ZMod (p ^ (k + 1))) := by
        rw [hpp]; ring

/-- The "high digit" decomposition `ZMod (p^k) × ZMod p → ZMod (p^(k+1))`,
`(y,t) ↦ y + p^k * t`, is a bijection. -/
lemma digit_decomposition_bijective (p k : ℕ) (hp : 0 < p) :
    Function.Bijective (fun yt : ZMod (p ^ k) × ZMod p =>
      ((yt.1.val : ℕ) : ZMod (p ^ (k + 1))) +
        ((p ^ k : ℕ) : ZMod (p ^ (k + 1))) * ((yt.2.val : ℕ) : ZMod (p ^ (k + 1)))) := by
  have hpne : p ≠ 0 := Nat.pos_iff_ne_zero.mp hp
  haveI : NeZero p := ⟨hpne⟩
  haveI : NeZero (p ^ k) := ⟨pow_ne_zero k hpne⟩
  haveI : NeZero (p ^ (k + 1)) := ⟨pow_ne_zero (k + 1) hpne⟩
  have hpk_pos : 0 < p ^ k := pow_pos hp k
  let f : ZMod (p ^ k) × ZMod p → ZMod (p ^ (k + 1)) := fun yt =>
      ((yt.1.val : ℕ) : ZMod (p ^ (k + 1))) +
        ((p ^ k : ℕ) : ZMod (p ^ (k + 1))) * ((yt.2.val : ℕ) : ZMod (p ^ (k + 1)))
  let g : ZMod (p ^ (k + 1)) → ZMod (p ^ k) × ZMod p := fun a =>
      (((a.val % p ^ k : ℕ) : ZMod (p ^ k)), ((a.val / p ^ k % p : ℕ) : ZMod p))
  change Function.Bijective f
  -- the explicit inverse of `f`
  have hr : Function.RightInverse g f := by
    intro a
    have h1 : ((g a).1.val : ℕ) = a.val % p ^ k := by
      simp only [g, ZMod.val_natCast, Nat.mod_mod]
    have h2 : ((g a).2.val : ℕ) = a.val / p ^ k % p := by
      simp only [g, ZMod.val_natCast, Nat.mod_mod]
    show f (g a) = a
    rw [show f (g a) = ((a.val % p ^ k : ℕ) : ZMod (p ^ (k + 1))) +
        ((p ^ k : ℕ) : ZMod (p ^ (k + 1))) * ((a.val / p ^ k % p : ℕ) : ZMod (p ^ (k + 1))) from by
          simp only [f]; rw [h1, h2]]
    rw [← natCast_decomp p k a.val, ZMod.natCast_zmod_val]
  have hl : Function.LeftInverse g f := by
    intro yt
    obtain ⟨y, t⟩ := yt
    have hy : y.val < p ^ k := ZMod.val_lt y
    have ht : t.val < p := ZMod.val_lt t
    -- the sum `y.val + p^k * t.val` is the canonical representative of `f (y,t)`
    have hb : y.val + p ^ k * t.val < p ^ (k + 1) := by
      have hlt : y.val + p ^ k * t.val < p ^ k * (t.val + 1) := by
        calc y.val + p ^ k * t.val < p ^ k + p ^ k * t.val := Nat.add_lt_add_right hy _
          _ = p ^ k * (t.val + 1) := by ring
      have hle : p ^ k * (t.val + 1) ≤ p ^ k * p :=
        Nat.mul_le_mul_left _ (Nat.succ_le_iff.mpr ht)
      have h := lt_of_lt_of_le hlt hle
      rwa [← Nat.pow_succ p k] at h
    have hA : f (y, t) = ((y.val + p ^ k * t.val : ℕ) : ZMod (p ^ (k + 1))) := by
      simp only [f]; push_cast; ring
    have hAval : (f (y, t)).val = y.val + p ^ k * t.val := by
      rw [hA, ZMod.val_natCast, Nat.mod_eq_of_lt hb]
    have h1 : (f (y, t)).val % p ^ k = y.val := by
      rw [hAval, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hy]
    have h2 : (f (y, t)).val / p ^ k % p = t.val := by
      rw [hAval, Nat.add_mul_div_left y.val t.val hpk_pos, Nat.div_eq_of_lt hy,
        Nat.zero_add, Nat.mod_eq_of_lt ht]
    have hg1 : (g (f (y, t))).1 = y := by
      show (((f (y, t)).val % p ^ k : ℕ) : ZMod (p ^ k)) = y
      rw [h1, ZMod.natCast_zmod_val]
    have hg2 : (g (f (y, t))).2 = t := by
      show (((f (y, t)).val / p ^ k % p : ℕ) : ZMod p) = t
      rw [h2, ZMod.natCast_zmod_val]
    exact Prod.ext hg1 hg2
  exact Function.bijective_iff_has_inverse.mpr ⟨g, hl, hr⟩

end Commons.NumberTheory.ZMod
