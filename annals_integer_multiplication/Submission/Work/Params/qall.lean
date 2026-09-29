import Mathlib
import Submission.Work.Params.basic

/-! `Q = ∏_{k<d} (2Fk+1)(2Fk-1) ≡ 1 (mod F)`; `F = (d-1)!`. -/

set_option autoImplicit false

namespace Work.Params

open HvdH

theorem Ffac_mul_sub_one {m : ℕ} (hm : 1 ≤ m) : Ffac * m - 1 ≡ Ffac - 1 [MOD Ffac] := by
  rw [Nat.modEq_iff_dvd]
  have hle : 1 ≤ Ffac * m :=
    Nat.one_le_iff_ne_zero.mpr (Nat.pos_iff_ne_zero.mp (Nat.mul_pos Ffac_pos (lt_of_lt_of_le Nat.zero_lt_one hm)))
  have h1 : ((Ffac * m - 1 : ℕ) : ℤ) = (Ffac : ℤ) * m - 1 := by
    rw [Nat.cast_sub hle, Nat.cast_mul, Nat.cast_one]
  have h2 : ((Ffac - 1 : ℕ) : ℤ) = (Ffac : ℤ) - 1 := by
    rw [Nat.cast_sub Ffac_one_le, Nat.cast_one]
  rw [h1, h2]
  have h3 : (Ffac : ℤ) - 1 - ((Ffac : ℤ) * m - 1) = (Ffac : ℤ) * ((1:ℤ) - (m:ℤ)) := by ring
  rw [h3]
  exact ⟨((1:ℤ) - (m:ℤ)), by ring⟩

theorem Ffac_sq_modEq_one : (Ffac - 1) ^ 2 ≡ 1 [MOD Ffac] := by
  rw [pow_two, Nat.modEq_iff_dvd, Nat.cast_one]
  have h1 : ((Ffac - 1 : ℕ) : ℤ) = (Ffac : ℤ) - 1 := by
    rw [Nat.cast_sub Ffac_one_le, Nat.cast_one]
  have hh : (1:ℤ) - (((Ffac - 1) * (Ffac - 1) : ℕ) : ℤ) = ((2:ℤ) - (Ffac:ℤ)) * (Ffac : ℤ) := by
    rw [Nat.cast_mul, h1]; ring
  rw [hh]
  exact ⟨((2:ℤ) - (Ffac:ℤ)), by ring⟩

theorem Ffac_pow_modEq_one : (Ffac - 1) ^ (D - 1) ≡ 1 [MOD Ffac] := by
  have hD : D - 1 = 2 * 864 := by decide
  rw [hD, pow_mul]
  have hp : ((Ffac - 1) ^ 2) ^ 864 ≡ (1:ℕ) ^ 864 [MOD Ffac] :=
    Nat.ModEq.pow 864 Ffac_sq_modEq_one
  rw [one_pow] at hp
  exact hp

theorem factor_modEq (j : ℕ) :
    (2 * Ffac * (j+1) + 1) * (2 * Ffac * (j+1) - 1) ≡ Ffac - 1 [MOD Ffac] := by
  have e1 : (2 * Ffac * (j+1) + 1) ≡ 1 [MOD Ffac] := by
    have h0 : 2 * Ffac * (j+1) ≡ 0 [MOD Ffac] :=
      Nat.modEq_zero_iff_dvd.mpr ⟨2*(j+1), by ring⟩
    have hA := Nat.ModEq.add h0 (Nat.ModEq.refl 1)
    rw [Nat.zero_add] at hA
    exact hA
  have e2 : (2 * Ffac * (j+1) - 1) ≡ Ffac - 1 [MOD Ffac] := by
    have heq : 2 * Ffac * (j+1) - 1 = Ffac * (2 * (j+1)) - 1 := by ring
    rw [heq]
    exact Ffac_mul_sub_one (by omega : 1 ≤ 2 * (j+1))
  have hm := Nat.ModEq.mul e1 e2
  rw [Nat.one_mul] at hm
  exact hm

theorem Qall_modEq_one : Qall ≡ 1 [MOD Ffac] := by
  have hg : ∀ j ∈ List.range (D-1),
      (2 * Ffac * (j+1) + 1) * (2 * Ffac * (j+1) - 1) ≡ (Ffac - 1) [MOD Ffac] :=
    fun j _ => factor_modEq j
  unfold Qall
  have h1 := List.prod_map_modEq hg
  have h2 : (List.map (fun _ => Ffac - 1) (List.range (D-1))).prod = (Ffac - 1) ^ (D - 1) := by
    rw [List.map_const', List.length_range, List.prod_replicate]
  rw [h2] at h1
  exact h1.trans Ffac_pow_modEq_one

/-- `F` is a multiple of `d!`, in particular of every prime `≤ d`. -/
theorem dvd_Ffac_of_le {m : ℕ} (hm0 : 0 < m) (hm : m ≤ D - 1) : m ∣ Ffac := by
  unfold Ffac
  exact Nat.dvd_factorial hm0 hm

end Work.Params
