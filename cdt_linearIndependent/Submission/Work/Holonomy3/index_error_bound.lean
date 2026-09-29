import Mathlib
import Submission.Work.Holonomy3.seed_helpers

namespace Work.Holonomy3

open Submission.CDT.Discrepancy

/-! ## Counting helpers for monotone configurations

For a nondecreasing configuration `t : Fin d → ℝ` the indices of the points strictly below `t j`
are among `0, …, j-1`, and the points `t 0, …, t j` all lie in `[0, u)` for every `u > t j`. -/

/-- The indices `i` of `Fin d` with `i < j` number exactly `j.val`. -/
lemma card_filter_lt_fin {d : ℕ} (j : Fin d) :
    (Finset.univ.filter (fun i : Fin d => i < j)).card = j.val := by
  rw [show (Finset.univ.filter (fun i : Fin d => i < j)) = Finset.Iio j from by
    ext i; simp [Finset.mem_Iio]]
  exact Fin.card_Iio j

/-- The indices `i` of `Fin d` with `i ≤ j` number exactly `j.val + 1`. -/
lemma card_filter_le_fin {d : ℕ} (j : Fin d) :
    (Finset.univ.filter (fun i : Fin d => i ≤ j)).card = j.val + 1 := by
  rw [show (Finset.univ.filter (fun i : Fin d => i ≤ j)) = Finset.Iic j from by
    ext i; simp [Finset.mem_Iic]]
  exact Fin.card_Iic j

/-- The points strictly below `t j` occupy indices strictly below `j`. -/
lemma cnt_zero_le_of_monotone {d : ℕ} {t : Fin d → ℝ} (ht : ∀ j, 0 ≤ t j) (hmono : Monotone t)
    (j : Fin d) : cnt t 0 (t j) ≤ j.val := by
  rw [cnt_zero_eq_card_filter_lt ht (t j)]
  calc (Finset.univ.filter (fun i : Fin d => t i < t j)).card
      ≤ (Finset.univ.filter (fun i : Fin d => i < j)).card := by
        apply Finset.card_le_card
        intro i hi
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
        by_contra h
        exact absurd (hmono (not_lt.mp h)) (not_le.mpr hi)
    _ = j.val := card_filter_lt_fin j

/-- The `j.val + 1` points `t 0, …, t j` all lie in `[0, u)` as soon as `u > t j`. -/
lemma cnt_zero_ge_of_monotone {d : ℕ} {t : Fin d → ℝ} (ht : ∀ j, 0 ≤ t j) (hmono : Monotone t)
    (j : Fin d) {u : ℝ} (hju : t j < u) : j.val + 1 ≤ cnt t 0 u := by
  rw [cnt_zero_eq_card_filter_lt ht u]
  calc j.val + 1 = (Finset.univ.filter (fun i : Fin d => i ≤ j)).card := (card_filter_le_fin j).symm
    _ ≤ (Finset.univ.filter (fun i : Fin d => t i < u)).card := by
        apply Finset.card_le_card
        intro i hi
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
        exact lt_of_le_of_lt (hmono hi) hju

/-- **The lower bound from the discrepancy.**  If `t j < u ≤ 1` then `u ≥ (j+1)/d - ε`. -/
lemma value_lower_bound {d : ℕ} (hd : 0 < d) (t : Fin d → ℝ) (ht : ∀ j, t j ∈ Set.Icc 0 1)
    (hmono : Monotone t) {ε : ℝ} (hdisc : Submission.CDT.Discrepancy.disc t ≤ ε)
    (j : Fin d) {u : ℝ} (hju : t j < u) (hu1 : u ≤ 1) :
    ((j : ℝ) + 1) / (d : ℝ) - ε ≤ u := by
  have hdR : (0:ℝ) < (d:ℝ) := by exact_mod_cast hd
  have hu0 : 0 ≤ u := le_trans (ht j).1 (le_of_lt hju)
  have hcnt : j.val + 1 ≤ cnt t 0 u := cnt_zero_ge_of_monotone (fun i => (ht i).1) hmono j hju
  have hcntR : ((j:ℝ) + 1) ≤ (cnt t 0 u : ℝ) := by
    have h : ((j.val + 1 : ℕ) : ℝ) ≤ (cnt t 0 u : ℝ) := by exact_mod_cast hcnt
    push_cast at h
    linarith
  have hb := abs_cnt_sub_le t hu0 hu1 hdisc
  have h3 : ((j:ℝ) + 1) - (d:ℝ) * ε ≤ u * (d:ℝ) := by
    have hmc : u * (d:ℝ) = (d:ℝ) * u := mul_comm _ _
    have := (abs_le.mp hb).2
    linarith
  calc ((j:ℝ)+1)/(d:ℝ) - ε = (((j:ℝ)+1) - (d:ℝ)*ε)/(d:ℝ) := by field_simp
    _ ≤ u := (div_le_iff₀ hdR).mpr h3

/-- **Index/value bound from the box discrepancy.**  If `t : Fin d → ℝ` is nondecreasing with all
values in `[0,1]` and box discrepancy `≤ ε`, then the `j`-th value of `t` differs from the equidistant
value `j/d` by at most `ε + 1/d`.  Upper half: the points strictly below `t j` are among the first `j`
indices, so `cnt t 0 (t j) ≤ j` and `|cnt t 0 (t j) - d·t j| ≤ d·ε` gives `t j ≤ j/d + ε`.  Lower
half: for every `s > 0` the `j+1` points `t 0, …, t j` lie in `[0, t j + s)`, so (for `t j + s ≤ 1`)
`d(t j + s) ≥ (j+1) - d·ε`; letting `s → 0` and treating `t j + s > 1` separately gives
`t j ≥ (j+1)/d - ε ≥ j/d - ε - 1/d`. -/
theorem index_error_bound {d : ℕ} (hd : 0 < d) (t : Fin d → ℝ) (ht : ∀ j, t j ∈ Set.Icc 0 1)
    (hmono : Monotone t) {ε : ℝ} (hε : 0 ≤ ε)
    (hdisc : Submission.CDT.Discrepancy.disc t ≤ ε) (j : Fin d) :
    |t j - (j : ℝ) / (d : ℝ)| ≤ ε + 1 / (d : ℝ) := by
  have hdR : (0:ℝ) < (d:ℝ) := by exact_mod_cast hd
  have h1d : (0:ℝ) ≤ 1 / (d:ℝ) := by positivity
  have hsplit : ((j:ℝ) + 1) / (d:ℝ) = (j:ℝ) / (d:ℝ) + 1 / (d:ℝ) := by rw [add_div]
  rw [abs_le]
  constructor
  · -- lower half: `j/d - ε - 1/d ≤ t j`
    have key : ∀ δ : ℝ, 0 < δ → (j:ℝ)/(d:ℝ) - ε - 1/(d:ℝ) ≤ t j + δ := by
      intro δ hδ
      rcases eq_or_lt_of_le (ht j).2 with htj | htj
      · -- `t j = 1`: then `t j` dominates `(j+1)/d ≥ j/d + 1/d`
        have hle : ((j:ℝ) + 1) / (d:ℝ) ≤ 1 := by
          rw [div_le_one hdR]
          have hcast : ((j:ℝ) + 1) = ((j.val + 1 : ℕ) : ℝ) := by push_cast; ring
          rw [hcast]
          exact_mod_cast (Nat.succ_le_of_lt j.isLt)
        rw [htj]
        linarith
      · -- `t j < 1`: test the discrepancy on `[0, t j + s)` with a small `s > 0`
        have hmin_pos : 0 < min (δ/2) ((1 - t j)/2) :=
          lt_min (by linarith) (by linarith)
        have hsle : min (δ/2) ((1 - t j)/2) ≤ δ/2 := min_le_left _ _
        have hsle' : min (δ/2) ((1 - t j)/2) ≤ (1 - t j)/2 := min_le_right _ _
        have hju : t j < t j + min (δ/2) ((1 - t j)/2) := by linarith
        have hu1 : t j + min (δ/2) ((1 - t j)/2) ≤ 1 := by linarith
        have hb := value_lower_bound hd t ht hmono hdisc j hju hu1
        linarith
    have := le_of_forall_pos_le_add key
    linarith
  · -- upper half: `t j - j/d ≤ ε + 1/d`
    have hcell : cnt t 0 (t j) ≤ j.val := cnt_zero_le_of_monotone (fun i => (ht i).1) hmono j
    have hb := abs_cnt_sub_le t (ht j).1 (ht j).2 hdisc
    have hcntR : (cnt t 0 (t j) : ℝ) ≤ (j:ℝ) := by
      have h : (cnt t 0 (t j) : ℝ) ≤ (j.val : ℝ) := by exact_mod_cast hcell
      simpa using h
    have h3 : (d:ℝ) * t j ≤ (j:ℝ) + (d:ℝ) * ε := by
      have := (abs_le.mp hb).1
      linarith
    have h5 : t j ≤ ((j:ℝ) + (d:ℝ) * ε) / (d:ℝ) := (le_div_iff₀ hdR).mpr (by linarith)
    have h6 : ((j:ℝ) + (d:ℝ) * ε) / (d:ℝ) = (j:ℝ)/(d:ℝ) + ε := by field_simp
    linarith

end Work.Holonomy3
