import Mathlib
import Submission.Work.BrauerSuzuki.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# A four-group from two involutions whose product has power-of-two order

The main result of this file,
`Work.BrauerSuzuki.Group.hasFourGroup_of_two_involutions`, is the elementary group-theoretic
fact underlying every reduction that produces a Klein four-group:

> If `u ≠ v` are two involutions of a group `G` and `u * v` has order `2 ^ k` with `k ≥ 1`
> (i.e. `u * v` has *even* order), then `G` contains a four-group.

The proof is the classical one.  Put `z = u * v` and let `w = z ^ (2 ^ (k - 1))` be the
unique involution of the cyclic group `⟨z⟩` (it has order `2` because `2 ^ k` is the order of
`z`).  Since `u * z * u⁻¹ = (u * v)⁻¹` and `v * z * v⁻¹ = (u * v)⁻¹`, conjugating the power
`w` of `z` by `u` and by `v` inverts it; as `w` is an involution this says that both `u` and
`v` commute with `w`.  Hence either `w ≠ u`, and `u`, `w` are two commuting involutions, or
`w = u`, in which case `v` commutes with `u = w` and `u`, `v` themselves work.

Nothing here needs `G` to be finite: only that `u * v` has finite order. -/

namespace Work.BrauerSuzuki.Group

/-- **Two distinct involutions whose product has even order generate a four-group** (in the
weak sense of `HasFourGroup`: the group contains two distinct commuting involutions).

`u * v` having order `2 ^ k` with `k ≥ 1` is exactly the hypothesis that `u * v` has even
order; the conclusion `HasFourGroup G` is then the existence of the Klein four-group
`{1, u, w, u * w}` with `w = (u * v) ^ (2 ^ (k - 1))`. -/
theorem hasFourGroup_of_two_involutions {G : Type*} [Group G] {u v : G}
    (hu : orderOf u = 2) (hv : orderOf v = 2) (hne : u ≠ v)
    (h : ∃ k : ℕ, 1 ≤ k ∧ orderOf (u * v) = 2 ^ k) :
    Submission.Blueprint.HasFourGroup G := by
  obtain ⟨k, hk1, hkord⟩ := h
  -- `u` and `v` are involutions.
  have hu2 : u * u = 1 := by
    have hh := pow_orderOf_eq_one u
    rw [hu] at hh
    simpa [pow_two] using hh
  have hv2 : v * v = 1 := by
    have hh := pow_orderOf_eq_one v
    rw [hv] at hh
    simpa [pow_two] using hh
  have huinv : u⁻¹ = u := inv_eq_of_mul_eq_one_left hu2
  have hvinv : v⁻¹ = v := inv_eq_of_mul_eq_one_left hv2
  -- `z = u * v` has order `2 ^ k`.
  have hzpow : (u * v) ^ (2 ^ k) = 1 := by
    rw [← hkord]; exact pow_orderOf_eq_one (u * v)
  have hk2 : 2 ^ (k - 1) * 2 = 2 ^ k := by
    nth_rewrite 2 [← Nat.sub_add_cancel hk1]
    rw [pow_succ]
  -- `w` is the unique involution of `⟨z⟩`.
  let w : G := (u * v) ^ (2 ^ (k - 1))
  have hw2 : w ^ 2 = 1 := by
    show ((u * v) ^ (2 ^ (k - 1))) ^ 2 = 1
    rw [← pow_mul, hk2, hzpow]
  have hwne : w ≠ 1 := by
    intro hw1
    have hdvd : 2 ^ k ∣ 2 ^ (k - 1) := by
      rw [← hkord, orderOf_dvd_iff_pow_eq_one]
      exact hw1
    have hle : 2 ^ k ≤ 2 ^ (k - 1) := Nat.le_of_dvd (by positivity) hdvd
    have hk_le : k ≤ k - 1 := (Nat.pow_le_pow_iff_right (by norm_num)).mp hle
    omega
  have hword : orderOf w = 2 := orderOf_eq_prime (p := 2) hw2 hwne
  have hww : w * w = 1 := by rw [← pow_two]; exact hw2
  have hw_inv : w⁻¹ = w := inv_eq_of_mul_eq_one_left hww
  -- Conjugation by `u` (resp. `v`) inverts `u * v`.
  have huzu : u * (u * v) * u⁻¹ = (u * v)⁻¹ := by
    rw [mul_inv_rev, hvinv, huinv, ← mul_assoc, hu2, one_mul]
  have hvzv : v * (u * v) * v⁻¹ = (u * v)⁻¹ := by
    rw [mul_inv_rev, hvinv, huinv, ← mul_assoc, mul_assoc, hv2, mul_one]
  -- hence conjugation by `u` (resp. `v`) inverts every power of `u * v`, in particular `w`.
  have hconj : ∀ c : G, c * (u * v) * c⁻¹ = (u * v)⁻¹ → c * w * c⁻¹ = w⁻¹ := by
    intro c hc
    have hcz : MulAut.conj c (u * v) = (u * v)⁻¹ := by
      rw [MulAut.conj_apply]; exact hc
    have hh : MulAut.conj c w = w⁻¹ := by
      show MulAut.conj c ((u * v) ^ (2 ^ (k - 1))) = ((u * v) ^ (2 ^ (k - 1)))⁻¹
      rw [map_pow, hcz, inv_pow]
    simpa [MulAut.conj_apply] using hh
  -- as `w` is an involution, `u` and `v` commute with it.
  have huw : u * w = w * u := by
    have hh := hconj u huzu
    rw [hw_inv] at hh
    calc u * w = u * w * u⁻¹ * u := by group
      _ = w * u := by rw [hh]
  have hvw : v * w = w * v := by
    have hh := hconj v hvzv
    rw [hw_inv] at hh
    calc v * w = v * w * v⁻¹ * v := by group
      _ = w * v := by rw [hh]
  -- either `w ≠ u`, giving the commuting involutions `u`, `w`, or `w = u`, in which case
  -- `v` commutes with `u = w` and `u`, `v` themselves are the required pair.
  by_cases hwu : w = u
  · rw [hwu] at hvw
    exact ⟨u, v, hu, hv, hne, hvw.symm⟩
  · exact ⟨u, w, hu, hword, fun hh => hwu hh.symm, huw⟩

end Work.BrauerSuzuki.Group
