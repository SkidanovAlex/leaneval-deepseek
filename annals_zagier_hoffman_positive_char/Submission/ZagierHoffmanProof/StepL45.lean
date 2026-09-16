import Submission.ZagierHoffmanProof.StepM3

set_option autoImplicit false
set_option maxHeartbeats 100000000
open scoped BigOperators

/-!
# Step L45: the admissibility collapse at weight = level

For a tuple of weight exactly `k`, `k`-admissibility and `(k−1)`-admissibility
coincide (`kAdm_weight_iff_sub_one`): the only way they could differ is an entry
`> q` at position `k−1`, impossible when `weight = k` (if the depth reaches `k−1`
then it is `k` and weight `= k` forces all entries to be `1`), or the forbidden
depth-`≤ k` q-ended form with depth exactly `k`, whose last entry would be `1 ≠ q`.
Consequences used by the Prop-3.2 recursion analysis (PLAN SESSION 186): a weight-`k`
tuple that is `¬k`-admissible is automatically `¬(k−1)`-admissible — so at exact
weight = level the MAIN recursion's hard inputs do not exist and theorem-A(w)'s
hard inputs are routed to the level-`w−1` theorem.
-/

namespace ZagierHoffmanPositiveChar

/-- A tuple whose weight equals its depth has all entries `1`. -/
lemma weight_eq_depth_all_one (r : ℕ) (s : Fin r → ℕ+) (hw : weight r s = r) :
    ∀ i : Fin r, (s i : ℕ) = 1 := by
  classical
  intro i
  by_contra hne
  have hgt : 1 < (s i : ℕ) := by
    have hpos : 0 < (s i : ℕ) := (s i).pos
    omega
  have hsum : (∑ j : Fin r, (1 : ℕ)) < (∑ j : Fin r, ((s j : ℕ))) := by
    apply Finset.sum_lt_sum
    · intro x hx
      have hpos : 0 < (s x : ℕ) := (s x).pos
      omega
    · refine ⟨i, Finset.mem_univ i, hgt⟩
  have hsum' : r < weight r s := by
    simpa [weight] using hsum
  omega

/-- `(k−1)`-admissible and weight `k` implies `k`-admissible (q ≥ 2). -/
lemma kAdm_sub_one_weight_eq (q : ℕ) {r k : ℕ} (s : Fin r → ℕ+) (hk : 1 ≤ k)
    (hq : 2 ≤ q) (hw : weight r s = k) (hadm : kAdmissible q s (k - 1)) :
    kAdmissible q s k := by
  constructor
  · intro x hx
    by_cases hxr : x < r
    · by_cases hxkm : x < k - 1
      · have h := hadm.1 x hxkm
        simpa [pad0_of_lt s hxr] using h
      · have hxk1 : x = k - 1 := by omega
        subst x
        have hdep : r = k := by
          apply le_antisymm
          · have hge := weight_ge_depth r s
            omega
          · omega
        have hw' : weight r s = r := by simpa [hdep] using hw
        have hall := weight_eq_depth_all_one r s hw'
        have hle : (s ⟨k - 1, by omega⟩ : ℕ) ≤ q := by
          have hone := hall ⟨k - 1, by omega⟩
          rw [hone]
          omega
        simpa [pad0_of_lt s hxr] using hle
    · have hge : r ≤ x := le_of_not_gt hxr
      rw [pad0_of_ge s hge]
      exact Nat.zero_le q
  · intro hc2
    rcases hc2 with ⟨hr1, hrk, hall, hlast⟩
    by_cases hrk1 : r ≤ k - 1
    · -- depth ≤ k−1: the witness also violates (k−1)-admissibility
      apply hadm.2
      exact ⟨hr1, hrk1, hall, hlast⟩
    · -- depth = k: the last entry is 1 (weight = depth), contradiction with q ≥ 2
      have hdep : r = k := by omega
      have hw' : weight r s = r := by simpa [hdep] using hw
      have hall1 := weight_eq_depth_all_one r s hw'
      have hlast1 : (s ⟨r - 1, by omega⟩ : ℕ) = 1 := hall1 ⟨r - 1, by omega⟩
      have hq1 : q ≠ 1 := by omega
      apply hq1
      rw [← hlast]
      exact hlast1

/-- ★ For a tuple of weight exactly `k` (k ≥ 1, q ≥ 2): `k`-admissible iff
`(k−1)`-admissible. -/
lemma kAdm_weight_iff_sub_one (q : ℕ) {r k : ℕ} (s : Fin r → ℕ+) (hk : 1 ≤ k)
    (hq : 2 ≤ q) (hw : weight r s = k) :
    kAdmissible q s k ↔ kAdmissible q s (k - 1) := by
  constructor
  · intro hadm
    constructor
    · intro x hx
      have hxk : x < k := by omega
      exact hadm.1 x hxk
    · intro hc2
      rcases hc2 with ⟨hr1, hrk1, hall, hlast⟩
      apply hadm.2
      exact ⟨hr1, (by omega : r ≤ k), hall, hlast⟩
  · intro hadm
    exact kAdm_sub_one_weight_eq q s hk hq hw hadm

/-- A weight-`k` tuple that is not `k`-admissible is not `(k−1)`-admissible either. -/
lemma not_kAdm_weight_of_not_kAdm_sub_one (q : ℕ) {r k : ℕ} (s : Fin r → ℕ+) (hk : 1 ≤ k)
    (hq : 2 ≤ q) (hw : weight r s = k) (hnot : ¬ kAdmissible q s k) :
    ¬ kAdmissible q s (k - 1) := by
  intro hadm
  exact hnot ((kAdm_weight_iff_sub_one q s hk hq hw).mpr hadm)

end ZagierHoffmanPositiveChar
