import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Computability.Reduce
import Mathlib.Data.Int.Star
import Mathlib.Tactic.LinearCombination
import Submission.Work.FTS.PhiStar.FamLopAux.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.FlatWAux

set_option autoImplicit false

/-
# The three-term coefficient identity for `famC`

`famC k = (3/2)_k / k!` is the coefficient sequence of `(1 - z)^{-3/2}`, defined in
`Submission/Work/FTS/PhiStar/FamLopAux/Defs.lean` as

`famC k = (∏_{i<k} (3/2 + i)) / k!`  for `k ≥ 0`  (and `0` for `k < 0`).

The present lemma is the **pairwise** coefficient identity: for integers `u, v ≥ 0` with
`u + v = n + 2`,

`(n+2)·c u·c v - ((2n+5)/2)·(c u·c (v-1) + c (u-1)·c v) + (n+3)·c (u-1)·c (v-1) = 0`,

equivalently (writing `s = u + v = n + 2`)

`(u+v)·c u·c v = ((2(u+v)+1)/2)·(c (u-1)·c v + c u·c (v-1)) - (u+v+1)·c (u-1)·c (v-1)`.

This is the pointwise algebraic input to the three-term recurrence of the trigonometric
Gegenbauer sums `famTrig`; it is exactly the statement that the product of the generating
series `Σ c u·z^u` with itself satisfies the degree-`s` ODE inherited from
`2(1-z)f' = 3f` on each bidegree `(u,v)`.

## Proof

Everything is derived here from the definition of `famC`, so the module is self-contained
(it only imports the definitions).

* `famC_ratio_nat`: the defining ratio `c (m+1) = c m · (m + 3/2)/(m + 1)`, from
  `Finset.prod_range_succ` and `Nat.factorial_succ`.
* `key_boundary`: the degenerate instance `(n+2)·c (n+2) = ((2n+5)/2)·c (n+1)`, an immediate
  consequence of the ratio at `m = n+1`.
* `key_core`: the genuinely two-variable case: after `field_simp` it is the polynomial
  identity (in `m, k : ℕ`, `s := m + k + 2`, `r_m := (m + 3/2)/(m + 1)`,
  `r_k := (k + 3/2)/(k + 1)`)

  `s·r_m·r_k - ((2s+1)/2)·(r_m + r_k) + (s+1) = 0`,

  which is the "room" computation `-¼(1/u + 1/v) + (u+v)/(4uv) = 0` with `u = m+1`,
  `v = k + 1` (here `r_j = 1 + 1/(2(j+1))`).
* The main theorem distinguishes `u = 0`, `v = 0`, and `u, v ≥ 1`; in the last case we write
  `u = m+1`, `v = k+1` and substitute the defining ratio twice.

An equivalent form of the identity (multiplied by `2` and rearranged) is available in
`Work.FTS.PhiStar.FamLopAux.famC_ident` (`FamLopAux/TrigGegen.lean`), proved for arbitrary
integers `j`, `l`; the proof below does not use it, so that this module needs neither that
file nor its (larger) import cone.
-/

/-! ## Elementary facts about `famC`, from the definition -/

private lemma famC_one_zero : famC (0 : ℤ) = 1 := by
  rw [famC]
  norm_num

private lemma famC_eq_zero_of_neg {k : ℤ} (hk : k < 0) : famC k = 0 := by
  rw [famC, if_neg (by omega)]

/-- The defining ratio of the coefficients: `c (m+1) = c m · (m + 3/2)/(m + 1)`. -/
private lemma famC_ratio_nat (m : ℕ) :
    famC ((m : ℤ) + 1) = famC (m : ℤ) * (((m : ℝ) + 3 / 2) / ((m : ℝ) + 1)) := by
  have h1 : (((m : ℤ) + 1).toNat) = m + 1 := by simp
  have h2 : ((m : ℤ).toNat) = m := by simp
  rw [famC, famC,
    if_pos (by omega : (0 : ℤ) ≤ (m : ℤ) + 1), if_pos (by omega : (0 : ℤ) ≤ (m : ℤ)),
    h1, h2, Finset.prod_range_succ, Nat.factorial_succ]
  push_cast
  field_simp
  ring

/-! ## The two algebraic keys -/

/-- Degenerate instance (one index `0`): `(n+2)·c (n+2) = ((2n+5)/2)·c (n+1)`. -/
private lemma key_boundary (n : ℕ) :
    ((n : ℝ) + 2) * famC ((n : ℤ) + 2) - ((2 * (n : ℝ) + 5) / 2) * famC ((n : ℤ) + 1) = 0 := by
  have h := famC_ratio_nat (n + 1)
  have h1 : (((n + 1 : ℕ) : ℤ) + 1) = (n : ℤ) + 2 := by push_cast; ring
  have h2 : (((n + 1 : ℕ) : ℤ)) = (n : ℤ) + 1 := by push_cast; ring
  rw [h1, h2] at h
  rw [h]
  push_cast
  field_simp
  ring

/-- The two-variable rational identity, with `r_j := (j + 3/2)/(j + 1) = 1 + 1/(2(j+1))`:
`(m+k+2)·r_m·r_k - ((2(m+k)+5)/2)·(r_m + r_k) + (m+k+3) = 0`. -/
private lemma key_core (m k : ℕ) :
    ((m : ℝ) + (k : ℝ) + 2) * (((m : ℝ) + 3 / 2) / ((m : ℝ) + 1))
        * (((k : ℝ) + 3 / 2) / ((k : ℝ) + 1))
      - ((2 * ((m : ℝ) + (k : ℝ)) + 5) / 2)
        * ((((m : ℝ) + 3 / 2) / ((m : ℝ) + 1)) + (((k : ℝ) + 3 / 2) / ((k : ℝ) + 1)))
      + ((m : ℝ) + (k : ℝ) + 3) = 0 := by
  field_simp
  ring

/-! ## The theorem -/

theorem famC_coeff_int (n : ℕ) (u v : ℤ) (hu : 0 ≤ u) (hv : 0 ≤ v) (h : u + v = (n : ℤ) + 2) :
    ((n : ℝ) + 2) * Work.FTS.PhiStar.famC u * Work.FTS.PhiStar.famC v
      - ((2 * (n : ℝ) + 5) / 2) * (Work.FTS.PhiStar.famC u * Work.FTS.PhiStar.famC (v - 1)
          + Work.FTS.PhiStar.famC (u - 1) * Work.FTS.PhiStar.famC v)
      + ((n : ℝ) + 3) * Work.FTS.PhiStar.famC (u - 1) * Work.FTS.PhiStar.famC (v - 1) = 0 := by
  rcases lt_or_eq_of_le hu with hu | hu
  · rcases lt_or_eq_of_le hv with hv | hv
    · -- `1 ≤ u` and `1 ≤ v`: write `u = m+1`, `v = k+1` and use the defining ratio
      obtain ⟨m, hm⟩ : ∃ m : ℕ, u = (m : ℤ) + 1 :=
        ⟨(u - 1).toNat, by rw [Int.toNat_of_nonneg (by omega)]; omega⟩
      obtain ⟨k, hk⟩ : ∃ k : ℕ, v = (k : ℤ) + 1 :=
        ⟨(v - 1).toNat, by rw [Int.toNat_of_nonneg (by omega)]; omega⟩
      have hn : (n : ℝ) = (m : ℝ) + (k : ℝ) := by
        have hz : (n : ℤ) = (m : ℤ) + (k : ℤ) := by omega
        exact_mod_cast hz
      rw [hm, hk, hn,
        show ((m : ℤ) + 1) - 1 = (m : ℤ) by ring,
        show ((k : ℤ) + 1) - 1 = (k : ℤ) by ring,
        famC_ratio_nat m, famC_ratio_nat k]
      linear_combination (famC (m : ℤ) * famC (k : ℤ)) * key_core m k
    · -- `v = 0`: only the boundary term survives
      have hv0 : v = 0 := hv.symm
      subst hv0
      have hu_eq : u = (n : ℤ) + 2 := by omega
      subst hu_eq
      rw [famC_one_zero, famC_eq_zero_of_neg (by norm_num : ((0 : ℤ) - 1) < 0),
        show ((n : ℤ) + 2) - 1 = (n : ℤ) + 1 by ring]
      simpa using key_boundary n
  · -- `u = 0`: symmetric
    have hu0 : u = 0 := hu.symm
    subst hu0
    have hv_eq : v = (n : ℤ) + 2 := by omega
    subst hv_eq
    rw [famC_one_zero, famC_eq_zero_of_neg (by norm_num : ((0 : ℤ) - 1) < 0),
      show ((n : ℤ) + 2) - 1 = (n : ℤ) + 1 by ring]
    simpa [mul_add, mul_comm, mul_left_comm, mul_assoc] using key_boundary n

end Work.FTS.PhiStar.FlatWAux
