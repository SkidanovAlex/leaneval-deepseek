import Mathlib
import Submission.Work.SynFFT.defs

/-!
# `yMul` on a single coefficient (`getD` form)

Explicit evaluation of `HvdH.yMul r e a j` for `|e| ≤ r`: multiplication by `y^e` in
`ℂ[y]/(y^r+1)` shifts the coefficient index by `-e` modulo `r`, the wrap-around contributing the
sign `-1` (the relation `y^r = -1`).  Precisely, with `f = (-e).fmod r`:

* `e + f = 0` (no sign) when `-r ≤ e ≤ 0`, and `e + f = -r` (sign `-1`) when `0 < e ≤ r`;
* the index is `(j + f.toNat) mod r`, and the branch `j + f.toNat ≥ r` returns `-vget a (...)`
  (the `y^r = -1`) — which, together with the first sign, reproduces the quotient ring relation.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Work.SynFFT

open HvdH

theorem yMulGetD (r : ℕ) (hr : 0 < r) (e : ℤ) (he : |e| ≤ (r : ℤ)) (a : Fin r → ℂ) (j : Fin r) :
    HvdH.yMul r e a j =
      (if e + (-e).fmod (r : ℤ) = 0 then (1 : ℂ) else -1) *
        (if (j : ℕ) + ((-e).fmod (r : ℤ)).toNat < r
          then HvdH.vget a ((j : ℕ) + ((-e).fmod (r : ℤ)).toNat)
          else -HvdH.vget a ((j : ℕ) + ((-e).fmod (r : ℤ)).toNat - r)) := by
  have hrZ : (0:ℤ) < (r:ℤ) := by exact_mod_cast hr
  have hRne : (r:ℤ) ≠ 0 := ne_of_gt hrZ
  have hElow : -(r:ℤ) ≤ -e := by have h := le_abs_self e; linarith
  have hEup : -e ≤ (r:ℤ) := by have h := neg_abs_le e; linarith
  set f : ℤ := (-e).fmod (r:ℤ) with hfdef
  set s : ℕ := f.toNat with hsdef
  set m : ℕ := (j:ℕ) + s with hmdef
  have hf_emod : f = (-e) % (r:ℤ) := by rw [hfdef, Int.fmod_eq_emod_of_nonneg _ (le_of_lt hrZ)]
  have hf0 : 0 ≤ f := by rw [hf_emod]; exact Int.emod_nonneg _ hRne
  have hfR : f < (r:ℤ) := by rw [hf_emod]; exact Int.emod_lt_of_pos _ hrZ
  have hscast : (s:ℤ) = f := by rw [hsdef]; exact Int.toNat_of_nonneg hf0
  have hsr : s < r := by rw [hsdef, Int.toNat_lt' hr]; exact hfR
  have hmcast : (m:ℤ) = (j:ℤ) + f := by rw [hmdef]; push_cast; rw [hscast]
  have hm2r : m < 2 * r := by rw [hmdef]; have := j.isLt; omega
  have hE0 : Even (0:ℤ) := by rw [Int.even_iff]; norm_num
  have hE1 : ¬ Even (1:ℤ) := by rw [Int.even_iff]; norm_num
  have hEm1 : ¬ Even (-1:ℤ) := by rw [Int.even_iff]; norm_num
  have hEm2 : Even (-2:ℤ) := by rw [Int.even_iff]; norm_num
  have hem : f + (r:ℤ) * ((-e)/(r:ℤ)) = -e := by
    have h := Int.emod_add_mul_ediv (-e) (r:ℤ); rw [← hf_emod] at h; exact h
  have hk1 : (-e)/(r:ℤ) = -1 ∨ (-e)/(r:ℤ) = 0 ∨ (-e)/(r:ℤ) = 1 := by
    rcases lt_trichotomy (-e) 0 with hlt | heq | hgt
    · left
      have h1 : 0 ≤ -e + (r:ℤ) := by linarith
      have h2 : -e + (r:ℤ) < (r:ℤ) := by linarith
      have hkey' : (-e) = (-e + (r:ℤ)) + (-1) * (r:ℤ) := by ring
      rw [hkey', Int.add_mul_ediv_right _ _ hRne, Int.ediv_eq_zero_of_lt h1 h2]
      ring
    · right; left; rw [heq, Int.zero_ediv]
    · rcases lt_or_eq_of_le hEup with hElt | hEeq
      · right; left; exact Int.ediv_eq_zero_of_lt (le_of_lt hgt) hElt
      · right; right; rw [hEeq, Int.ediv_self hRne]
  have hc : e + f = (r:ℤ) ∨ e + f = 0 ∨ e + f = -(r:ℤ) := by
    have hef : e + f = -((r:ℤ) * ((-e)/(r:ℤ))) := by linarith [hem]
    rcases hk1 with hk | hk | hk
    · left; rw [hk] at hef; ring_nf at hef; exact hef
    · right; left; rw [hk] at hef; ring_nf at hef; exact hef
    · right; right; rw [hk] at hef; ring_nf at hef; exact hef
  have hem' : -e = f + ((-e)/(r:ℤ)) * (r:ℤ) := by
    calc -e = f + (r:ℤ) * ((-e)/(r:ℤ)) := hem.symm
      _ = f + ((-e)/(r:ℤ)) * (r:ℤ) := by ring
  have hkey : (j:ℤ) - e = (m:ℤ) + ((-e)/(r:ℤ)) * (r:ℤ) := by
    have h1 : (j:ℤ) - e = (j:ℤ) + (-e) := by ring
    rw [h1, hmcast]
    conv_lhs => rw [hem']
    ring
  have hA : ((j:ℤ) - e) % (r:ℤ) = ((m:ℤ)) % (r:ℤ) := by
    rw [hkey, Int.add_mul_emod_self_right]
  have hAtoNat : (((j:ℤ) - e) % (r:ℤ)).toNat = m % r := by
    rw [hA, ← Int.natCast_emod, Int.toNat_natCast]
  have hqval : (((j:ℤ) - e) % (r:ℤ) + e - (j:ℤ)) / (r:ℤ) = (e+f)/(r:ℤ) - (m:ℤ)/(r:ℤ) := by
    have hAe : ((j:ℤ) - e) % (r:ℤ) = (m:ℤ) - (r:ℤ) * ((m:ℤ)/(r:ℤ)) := by
      rw [hA]; have hh := Int.emod_add_mul_ediv (m:ℤ) (r:ℤ); linarith
    have hnum : ((j:ℤ) - e) % (r:ℤ) + e - (j:ℤ) = (e+f) - (r:ℤ)*((m:ℤ)/(r:ℤ)) := by
      have h1 : ((j:ℤ) - e) % (r:ℤ) + e - (j:ℤ)
          = ((m:ℤ) - (j:ℤ)) + e - ((r:ℤ)*((m:ℤ)/(r:ℤ))) := by rw [hAe]; ring
      have h2 : (m:ℤ) - (j:ℤ) = f := by rw [hmcast]; ring
      rw [h1, h2]; ring
    rw [hnum]
    have h1 : (e+f) - (r:ℤ)*((m:ℤ)/(r:ℤ)) = (e+f) + (-((m:ℤ)/(r:ℤ))) * (r:ℤ) := by ring
    rw [h1, Int.add_mul_ediv_right _ _ hRne]; ring
  rw [HvdH.yMul]
  rw [hAtoNat, hqval]
  rcases lt_or_ge m r with hm | hm
  · have hη : (m:ℤ)/(r:ℤ) = 0 := Int.ediv_eq_zero_of_lt (by positivity) (by exact_mod_cast hm)
    have hmr : m % r = m := Nat.mod_eq_of_lt hm
    rw [hη, sub_zero, hmr, ite_eq_left hm]
    have hsgn : (if Even ((e+f)/(r:ℤ)) then (1:ℂ) else -1) = (if e+f = 0 then (1:ℂ) else -1) := by
      rcases hc with h | h | h
      · rw [h, Int.ediv_self hRne, ite_eq_right hE1, ite_eq_right hRne]
      · rw [h, Int.zero_ediv, ite_eq_left hE0, ite_eq_left rfl]
      · rw [h, Int.neg_ediv_of_dvd (dvd_refl (r:ℤ)), Int.ediv_self hRne, ite_eq_right hEm1,
          ite_eq_right (by linarith : ¬ ((-(r:ℤ)) = 0))]
    rw [hsgn]
  · have hη : (m:ℤ)/(r:ℤ) = 1 := by
      have hmr : ((m - r : ℕ) : ℤ) = (m:ℤ) - (r:ℤ) := Nat.cast_sub hm
      have hlt : m - r < r := by omega
      have h1 : (m:ℤ) = ((m - r : ℕ) : ℤ) + (r:ℤ) := by rw [hmr]; ring
      rw [h1]
      have hz : ((m - r : ℕ) : ℤ) / (r:ℤ) = 0 :=
        Int.ediv_eq_zero_of_lt (by positivity) (by exact_mod_cast hlt)
      rw [show ((m - r : ℕ) : ℤ) + (r:ℤ) = ((m - r : ℕ) : ℤ) + 1 * (r:ℤ) by ring,
        Int.add_mul_ediv_right _ _ hRne, hz]
      ring
    have hmr : m % r = m - r := by
      rw [Nat.mod_eq_sub_mod hm, Nat.mod_eq_of_lt (by omega)]
    rw [hη, hmr, ite_eq_right (not_lt.mpr hm)]
    have hsgn : (if Even ((e+f)/(r:ℤ) - 1) then (1:ℂ) else -1)
        = -(if e+f = 0 then (1:ℂ) else -1) := by
      rcases hc with h | h | h
      · rw [h, Int.ediv_self hRne, show (1:ℤ) - 1 = 0 by ring, ite_eq_left hE0, ite_eq_right hRne]
        try ring
      · rw [h, Int.zero_ediv, show (0:ℤ) - 1 = -1 by ring, ite_eq_right hEm1, ite_eq_left rfl]
        try ring
      · rw [h, Int.neg_ediv_of_dvd (dvd_refl (r:ℤ)), Int.ediv_self hRne,
          show (-1:ℤ) - 1 = -2 by ring, ite_eq_left hEm2,
          ite_eq_right (by linarith : ¬ ((-(r:ℤ)) = 0))]
        try ring
    rw [hsgn]; ring

end Work.SynFFT
