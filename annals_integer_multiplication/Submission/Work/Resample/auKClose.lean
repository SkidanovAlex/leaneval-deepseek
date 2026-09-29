import Mathlib
import Submission.Work.Resample.auDefs

namespace Work.Resample

/-- Rounded-division bound: for `t ≥ 1`, `t · ⌊(2ks+t)/(2t)⌋` differs from `sk` by at most `t`.
Auxiliary arithmetic core, stated for `ℤ` so that the casts are transparent. -/
theorem auKClose_aux (a b c : ℤ) (ha : 1 ≤ a) (h1 : 2 * c ≤ 2 * b + a)
    (h2 : 2 * b + a < 2 * c + 2 * a) : |c - b| ≤ a := by
  rw [abs_le]
  constructor
  · have h : 2 * (b - c) < a := by omega
    have h' : b - c ≤ a / 2 := (Int.le_ediv_iff_mul_le (by norm_num)).mpr (by omega)
    have h'' : a / 2 ≤ a := Int.ediv_le_self (2 : ℤ) (by omega)
    omega
  · have h' : c - b ≤ a / 2 := (Int.le_ediv_iff_mul_le (by norm_num)).mpr (by omega)
    have h'' : a / 2 ≤ a := Int.ediv_le_self (2 : ℤ) (by omega)
    omega

theorem auKClose (s t k : ℕ) (ht : 1 ≤ t) :
    |(t : ℤ) * ( Work.Resample.auK s t k : ℤ) - (s : ℤ) * (k : ℤ)| ≤ (t : ℤ) := by
  have hb : 0 < 2 * t := by omega
  simp only [auK]
  set A : ℕ := (2 * k * s + t) / (2 * t) with hAdef
  have h1 : A * (2 * t) ≤ 2 * k * s + t := by
    rw [hAdef]; exact Nat.div_mul_le_self _ _
  have h2 : 2 * k * s + t < (A + 1) * (2 * t) := by
    rw [hAdef]
    exact (Nat.div_lt_iff_lt_mul hb).mp (Nat.lt_succ_self _)
  have h1z : 2 * ((t : ℤ) * (A : ℤ)) ≤ 2 * ((k : ℤ) * (s : ℤ)) + (t : ℤ) := by
    have h := Nat.cast_le (α := ℤ).mpr h1
    rw [show ((A * (2 * t) : ℕ) : ℤ) = 2 * ((t : ℤ) * (A : ℤ)) by push_cast; ring,
        show ((2 * k * s + t : ℕ) : ℤ) = 2 * ((k : ℤ) * (s : ℤ)) + (t : ℤ) by
          push_cast; ring] at h
    exact h
  have h2z : 2 * ((k : ℤ) * (s : ℤ)) + (t : ℤ) < 2 * ((t : ℤ) * (A : ℤ)) + 2 * (t : ℤ) := by
    have h := Nat.cast_lt (α := ℤ).mpr h2
    rw [show (((A + 1) * (2 * t) : ℕ) : ℤ) = 2 * ((t : ℤ) * (A : ℤ)) + 2 * (t : ℤ) by
          push_cast; ring,
        show ((2 * k * s + t : ℕ) : ℤ) = 2 * ((k : ℤ) * (s : ℤ)) + (t : ℤ) by
          push_cast; ring] at h
    exact h
  have hgoal : |(t : ℤ) * (A : ℤ) - (k : ℤ) * (s : ℤ)| ≤ (t : ℤ) :=
    auKClose_aux (t : ℤ) ((k : ℤ) * (s : ℤ)) ((t : ℤ) * (A : ℤ)) (by exact_mod_cast ht)
      h1z h2z
  simpa only [mul_comm (s : ℤ) (k : ℤ)] using hgoal

end Work.Resample
