import Mathlib
import Submission.Work.SynFFT.defs

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Work.SynFFT

open HvdH

/-! ## Helper lemmas about one butterfly stage `lvlN` and the level composition `levels`

These are the elementary unfolding facts for Lemma 3.2 / Proposition 3.3 of the paper:
the two outputs of a butterfly that reads a block of length `m` and its shift-invariance
when the array is translated by a multiple of `m` (resp. by a multiple of `m / 2 ^ j`). -/

/-- The "sum" output of one butterfly stage: for `u < t/2`, position `u` carries
`(a u + a (u + t/2)) / 2`. -/
lemma lvlN_apply_low (r : ℕ) (sgn : ℤ) (t : ℕ) (a : Arr r) (u : ℕ) (h : u < t / 2) :
    lvlN r t sgn a u = fun c => (a u c + a (u + t / 2) c) / 2 := by
  have hut : u < t := lt_of_lt_of_le h (Nat.div_le_self t 2)
  have hmod : u % t = u := Nat.mod_eq_of_lt hut
  unfold lvlN
  funext c
  rw [hmod, ite_eq_left h]

/-- The "difference" output of one butterfly stage: for `u < t/2`, position `u + t/2`
carries `y^{sgn·(2r/t)·u} (a u - a (u + t/2)) / 2`. -/
lemma lvlN_apply_high (r : ℕ) (sgn : ℤ) (t : ℕ) (a : Arr r) (u : ℕ) (h : u < t / 2) :
    lvlN r t sgn a (u + t / 2) = fun c =>
      yMul r (sgn * (((2 * r / t) * u : ℕ) : ℤ))
        (fun c' => (a u c' - a (u + t / 2) c') / 2) c := by
  have hh : u + t / 2 < t := by omega
  have hmod : (u + t / 2) % t = u + t / 2 := Nat.mod_eq_of_lt hh
  have hsub : (u + t / 2) - t / 2 = u := by omega
  unfold lvlN
  funext c
  rw [hmod, hsub, ite_eq_right (by omega)]

/-- A butterfly stage commutes with translation of the array by a multiple of its block
size `m`. -/
lemma lvlN_shift_add (r : ℕ) (m : ℕ) (sgn : ℤ) (S : ℕ) (a : Arr r) (hS : m ∣ S) :
    lvlN r m sgn (fun p => a (p + S)) = fun q => lvlN r m sgn a (q + S) := by
  funext q c
  unfold lvlN
  have hmod : (q + S) % m = q % m := by
    obtain ⟨k, hk⟩ := hS
    rw [hk, Nat.add_mul_mod_self_left]
  rw [hmod]
  by_cases hc : q % m < m / 2
  · rw [ite_eq_left hc, ite_eq_left hc]
    simp only [show q + m / 2 + S = q + S + m / 2 from by omega]
  · rw [ite_eq_right hc, ite_eq_right hc]
    have hge : m / 2 ≤ q := le_trans (Nat.le_of_not_lt hc) (Nat.mod_le q m)
    have hsub : q - m / 2 + S = q + S - m / 2 := by omega
    simp only [hsub]

/-- The composition `levels` of the stages of sizes `m, m/2, …, m/2^{k-1}` commutes with a
translation by `S`, provided `m / 2 ^ j ∣ S` for every `j < k`. -/
lemma levels_shift_add (r : ℕ) (sgn : ℤ) (m S k : ℕ) (a : Arr r)
    (h : ∀ j < k, m / 2 ^ j ∣ S) :
    levels r sgn m k (fun p => a (p + S)) = fun q => levels r sgn m k a (q + S) := by
  induction k generalizing m S a with
  | zero => rfl
  | succ k ih =>
    show levels r sgn (m / 2) k (lvlN r m sgn (fun p => a (p + S))) =
         fun q => levels r sgn (m / 2) k (lvlN r m sgn a) (q + S)
    have hshift : lvlN r m sgn (fun p => a (p + S)) = fun q => lvlN r m sgn a (q + S) :=
      lvlN_shift_add r m sgn S a (by simpa using h 0 (Nat.zero_lt_succ k))
    rw [hshift]
    refine ih (m / 2) S (lvlN r m sgn a) (fun j hj => ?_)
    have hjj : m / 2 ^ (j + 1) = (m / 2) / 2 ^ j := by
      rw [Nat.div_div_eq_div_mul, pow_succ']
    rw [← hjj]
    exact h (j + 1) (by omega)

theorem lvlNLevelsLib (r : ℕ) (sgn : ℤ) :
    (∀ (t : ℕ) (a : Arr r) (u : ℕ), u < t / 2 →
      lvlN r t sgn a u = fun c => (a u c + a (u + t / 2) c) / 2) ∧
    (∀ (t : ℕ) (a : Arr r) (u : ℕ), u < t / 2 →
      lvlN r t sgn a (u + t / 2) = fun c =>
        HvdH.yMul r (sgn * (((2 * r / t) * u : ℕ) : ℤ))
          (fun c' => (a u c' - a (u + t / 2) c') / 2) c) ∧
    (∀ (m S : ℕ) (a : Arr r), m ∣ S →
      lvlN r m sgn (fun p => a (p + S)) = fun q => lvlN r m sgn a (q + S)) ∧
    (∀ (m S k : ℕ) (a : Arr r), (∀ j < k, m / 2 ^ j ∣ S) →
      levels r sgn m k (fun p => a (p + S)) = fun q => levels r sgn m k a (q + S)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro t a u h
    exact lvlN_apply_low r sgn t a u h
  · intro t a u h
    exact lvlN_apply_high r sgn t a u h
  · intro m S a hS
    exact lvlN_shift_add r m sgn S a hS
  · intro m S k a h
    exact levels_shift_add r sgn m S k a h

end Work.SynFFT
