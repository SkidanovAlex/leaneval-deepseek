import Mathlib

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotC2.TransAux

/- General degree obstruction: if `natDegree b ≤ 1` and `natDegree c = 3`, then the
Weierstrass-style equation `p² + b·p·q - c·q² = 0` has no solution with `q ≠ 0`.

The proof factors the left-hand side as `p·(p + b·q) = c·q²` and compares `natDegree`
of both sides: writing `n = natDegree p`, `m = natDegree q`, `β = natDegree b ≤ 1`,
the identity reads `n + N = 3 + 2m` where `N = natDegree (p + b·q)`.
Since `N ≤ max n (β + m)`, splitting on the comparison of `n` with `β + m` gives a
contradiction in every case. -/
open Polynomial in
theorem aux_no_root {L : Type*} [Field L] (b c : L[X]) (hb : natDegree b ≤ 1)
    (hc : natDegree c = 3) (p q : L[X]) (hq : q ≠ 0) :
    p ^ 2 + b * p * q - c * q ^ 2 ≠ 0 := by
  intro h
  have hc_ne : c ≠ 0 := by intro hz; rw [hz] at hc; simp at hc
  have h1 : p ^ 2 + b * p * q = c * q ^ 2 := sub_eq_zero.mp h
  have hq2_ne : q ^ 2 ≠ 0 := pow_ne_zero 2 hq
  have hp_ne : p ≠ 0 := by
    intro hp
    have hz : c * q ^ 2 = 0 := by rw [← h1, hp]; ring
    exact (mul_ne_zero hc_ne hq2_ne) hz
  have hfac : p * (p + b * q) = c * q ^ 2 := by rw [← h1]; ring
  have hpq_ne : p + b * q ≠ 0 := by
    intro hz
    have : c * q ^ 2 = 0 := by rw [← hfac, hz, mul_zero]
    exact (mul_ne_zero hc_ne hq2_ne) this
  have h2 : natDegree p + natDegree (p + b * q) = 3 + 2 * natDegree q := by
    have hd := congrArg natDegree hfac
    rw [natDegree_mul hp_ne hpq_ne, natDegree_mul hc_ne hq2_ne, pow_two,
        natDegree_mul hq hq, hc] at hd
    omega
  by_cases hb0 : b = 0
  · rw [hb0, zero_mul, add_zero] at h2
    omega
  · have hbq : natDegree (b * q) = natDegree b + natDegree q := natDegree_mul hb0 hq
    rcases lt_trichotomy (natDegree p) (natDegree b + natDegree q) with hlt | heq | hgt
    · have hN : natDegree (p + b * q) = natDegree (b * q) :=
        natDegree_add_eq_right_of_natDegree_lt (by rwa [hbq])
      rw [hN, hbq] at h2
      omega
    · have hN : natDegree (p + b * q) ≤ natDegree p := by
        calc natDegree (p + b * q) ≤ max (natDegree p) (natDegree (b * q)) := natDegree_add_le _ _
          _ = max (natDegree p) (natDegree b + natDegree q) := by rw [hbq]
          _ = natDegree p := by rw [heq, max_self]
      omega
    · have hN : natDegree (p + b * q) = natDegree p :=
        natDegree_add_eq_left_of_natDegree_lt (by rwa [hbq])
      rw [hN] at h2
      omega

open Polynomial in
theorem NoRoot {L : Type*} [Field L] (a1 a3 a2 a4 a6 : L) (p q : L[X]) (hq : q ≠ 0) :
    p ^ 2 + (C a1 * X + C a3) * p * q - (X ^ 3 + C a2 * X ^ 2 + C a4 * X + C a6) * q ^ 2 ≠ 0 := by
  have hb : natDegree (C a1 * X + C a3 : L[X]) ≤ 1 := by
    calc natDegree (C a1 * X + C a3) ≤ max (natDegree (C a1 * X)) (natDegree (C a3)) :=
          natDegree_add_le _ _
      _ ≤ max 1 0 := by
          gcongr
          · exact (natDegree_mul_le (p := C a1) (q := X)).trans (by simp)
          · simp
      _ = 1 := by norm_num
  have hc : natDegree (X ^ 3 + C a2 * X ^ 2 + C a4 * X + C a6 : L[X]) = 3 := by
    compute_degree <;> norm_num
  exact aux_no_root (C a1 * X + C a3) (X ^ 3 + C a2 * X ^ 2 + C a4 * X + C a6) hb hc p q hq

end Work.MotC2.TransAux
