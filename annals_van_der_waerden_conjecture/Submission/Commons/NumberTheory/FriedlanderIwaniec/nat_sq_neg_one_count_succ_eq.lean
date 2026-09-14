import Mathlib
import Submission.Commons.NumberTheory.FriedlanderIwaniec.nat_sq_neg_one_lift
import Submission.Commons.NumberTheory.FriedlanderIwaniec.nat_sq_neg_one_lift_unique
import Submission.Commons.NumberTheory.FriedlanderIwaniec.sq_roots_neg_one_count_eq_fin_count

set_option linter.style.haveILetI false

namespace Commons.NumberTheory.FriedlanderIwaniec

/-- The number of solutions of `x ^ 2 + 1 ≡ 0 (mod p ^ k)` does not depend on
`k ≥ 1`, for an odd prime `p`.

The reduction map `ZMod (p ^ (e + 1)) → ZMod (p ^ e)` is a bijection on the
root sets: it is injective because two roots in `[0, p ^ (e + 1))` with the same
residue mod `p ^ e` coincide (`nat_sq_neg_one_lift_unique`), and surjective by
Hensel lifting (`nat_sq_neg_one_lift`). -/
lemma nat_sq_neg_one_count_succ_eq {p e : ℕ} (hp : p.Prime) (hpodd : p ≠ 2) (he : 1 ≤ e) :
    ({x : Fin (p ^ (e + 1)) | p ^ (e + 1) ∣ (x : ℕ) ^ 2 + 1}.ncard) =
      ({x : Fin (p ^ e) | p ^ e ∣ (x : ℕ) ^ 2 + 1}.ncard) := by
  classical
  have hA : 0 < p ^ (e + 1) := pow_pos hp.pos _
  have hB : 0 < p ^ e := pow_pos hp.pos _
  haveI : NeZero (p ^ (e + 1)) := ⟨pow_ne_zero _ hp.ne_zero⟩
  haveI : NeZero (p ^ e) := ⟨pow_ne_zero _ hp.ne_zero⟩
  rw [← sq_roots_neg_one_count_eq_fin_count (n := p ^ (e + 1)) hA,
      ← sq_roots_neg_one_count_eq_fin_count (n := p ^ e) hB]
  have hdvd : p ^ e ∣ p ^ (e + 1) := pow_dvd_pow p (Nat.le_succ e)
  let f : ZMod (p ^ (e + 1)) →+* ZMod (p ^ e) := ZMod.castHom hdvd (ZMod (p ^ e))
  have hf_apply : ∀ a : ZMod (p ^ (e + 1)),
      f a = (a.val : ZMod (p ^ e)) := by
    intro a
    conv_lhs => rw [← ZMod.natCast_zmod_val a]
    exact map_natCast f a.val
  refine Set.ncard_congr (fun a _ => f a) ?_ ?_ ?_
  · intro a ha
    show (f a) ^ 2 = -1
    rw [← map_pow, ha, map_neg, map_one]
  · intro a b ha hb hab
    have hmodeq : a.val % p ^ e = b.val % p ^ e := by
      have h : (a.val : ZMod (p ^ e)) = (b.val : ZMod (p ^ e)) := by
        rw [← hf_apply a, ← hf_apply b, hab]
      exact (ZMod.natCast_eq_natCast_iff' a.val b.val (p ^ e)).mp h
    have hroota : p ^ (e + 1) ∣ a.val ^ 2 + 1 := by
      have h : ((a.val ^ 2 + 1 : ℕ) : ZMod (p ^ (e + 1))) = 0 := by
        rw [Nat.cast_add, Nat.cast_pow, Nat.cast_one, ZMod.natCast_zmod_val, ha]
        ring
      exact (ZMod.natCast_eq_zero_iff (a.val ^ 2 + 1) (p ^ (e + 1))).mp h
    have hrootb : p ^ (e + 1) ∣ b.val ^ 2 + 1 := by
      have h : ((b.val ^ 2 + 1 : ℕ) : ZMod (p ^ (e + 1))) = 0 := by
        rw [Nat.cast_add, Nat.cast_pow, Nat.cast_one, ZMod.natCast_zmod_val, hb]
        ring
      exact (ZMod.natCast_eq_zero_iff (b.val ^ 2 + 1) (p ^ (e + 1))).mp h
    exact ZMod.val_injective _ (nat_sq_neg_one_lift_unique hp hpodd he
      (ZMod.val_lt a) (ZMod.val_lt b) hroota hrootb hmodeq)
  · intro b hb
    have hrootb : p ^ e ∣ b.val ^ 2 + 1 := by
      have h : ((b.val ^ 2 + 1 : ℕ) : ZMod (p ^ e)) = 0 := by
        rw [Nat.cast_add, Nat.cast_pow, Nat.cast_one, ZMod.natCast_zmod_val, hb]
        ring
      exact (ZMod.natCast_eq_zero_iff (b.val ^ 2 + 1) (p ^ e)).mp h
    obtain ⟨y, hy_lt, hy_mod, hy_root⟩ :=
      nat_sq_neg_one_lift hp hpodd he (ZMod.val_lt b) hrootb
    refine ⟨(y : ZMod (p ^ (e + 1))), ?_, ?_⟩
    · show (y : ZMod (p ^ (e + 1))) ^ 2 = -1
      rw [eq_neg_iff_add_eq_zero]
      have h : ((y ^ 2 + 1 : ℕ) : ZMod (p ^ (e + 1))) = 0 :=
        (ZMod.natCast_eq_zero_iff (y ^ 2 + 1) (p ^ (e + 1))).mpr hy_root
      push_cast at h
      exact h
    · have hf_y : f (y : ZMod (p ^ (e + 1))) = (y : ZMod (p ^ e)) := map_natCast f y
      rw [hf_y, ← ZMod.natCast_zmod_val b]
      apply (ZMod.natCast_eq_natCast_iff' y b.val (p ^ e)).mpr
      rw [hy_mod, Nat.mod_eq_of_lt (ZMod.val_lt b)]

end Commons.NumberTheory.FriedlanderIwaniec
