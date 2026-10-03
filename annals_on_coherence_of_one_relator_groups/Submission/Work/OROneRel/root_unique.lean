/-
Copyright: subproject `OROneRel` -- one-relator combinatorics (node N2) of the
formalisation of Jaikin-Zapirain--Linton, "On the coherence of one-relator groups
and their group algebras".

# Uniqueness of the root of a non-proper-power element of a free group

An element `u` of a group is *not a proper power* (in the sense of `IsProperPower`) if it admits
no expression `u = w ^ k` with `k ≥ 2`.  In a free group every non-trivial element `r` has a
unique "root" `u` which is not a proper power, and `r = u ^ l` determines `l` uniquely as well.

Here we derive this from two ingredients:

* `exists_common_power`: if `u ^ l = v ^ m` with `l, m ≥ 1` then `u` and `v` are powers of a
  common element `w`;
* torsion-freeness of a free group (`IsMulTorsionFree (FreeGroup α)`), which makes `n ↦ x ^ n`
  injective on `ℕ` as soon as `x ≠ 1`.

Note that the degenerate case `u = 1` is excluded by the hypothesis `¬ IsProperPower u`, since
`1 = 1 ^ 2` *is* a proper power; this is exactly the edge case in which the exponent would not be
unique.
-/
import Mathlib
import Submission.Work.OROneRel.Basic
import Submission.Work.OROneRel.exists_common_power

namespace Work.OROneRel

universe u

theorem root_unique {α : Type u} {r u v : FreeGroup α} {l m : ℕ} (hl : 1 ≤ l) (hm : 1 ≤ m)
    (hru : r = u ^ l) (hrv : r = v ^ m) (hu : ¬ Work.OROneRel.IsProperPower u)
    (hv : ¬ Work.OROneRel.IsProperPower v) : u = v ∧ l = m := by
  have h : u ^ l = v ^ m := by rw [← hru, hrv]
  -- Common root: `u = w ^ a`, `v = w ^ b` with `a, b ≥ 1`.
  obtain ⟨w, a, b, ha, hb, hua, hvb⟩ := exists_common_power hl hm h
  -- `u` is not a proper power, so it cannot be a power with exponent `≥ 2`.
  have ha1 : a = 1 := by
    by_contra hne
    exact hu ⟨w, a, by omega, hua⟩
  have hb1 : b = 1 := by
    by_contra hne
    exact hv ⟨w, b, by omega, hvb⟩
  have huv : u = v := by rw [hua, hvb, ha1, hb1]
  subst huv
  refine ⟨rfl, ?_⟩
  -- `u ≠ 1` because `1 = 1 ^ 2` is a proper power.
  have hu1 : u ≠ 1 := fun h1 => hu ⟨1, 2, le_rfl, by rw [h1]; simp⟩
  -- A free group is torsion-free, and `u ≠ 1`, so `u` has infinite order.
  have horder : orderOf u = 0 := by
    rw [orderOf_eq_zero_iff']
    intro n hn hcon
    exact absurd ((pow_eq_one_iff_right hu1).mp hcon) (by omega)
  exact (pow_inj_iff_of_orderOf_eq_zero (x := u) horder).mp h

end Work.OROneRel
