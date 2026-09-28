import Mathlib

/-!
# Core arithmetic (log form) for the per-cell estimate `hi_cell_arith`

With `a = log A`, `b = log B`, `d = log Δ`, `m = log M` the per-cell estimate reduces, in each
of the cases (case `Δ ≤ B` / case `Δ ≥ B`) and branches (`2Δ ≤ (2M)^53` / `(2M)^53 ≤ 2Δ`),
to exhibiting an index `k ∈ {4,…,67}` satisfying two explicit *linear* inequalities `c1…`, `c2…`
in `(a,b,d,m)`.  This file proves those linear facts, using only the standing hypotheses
`10⁶ ≤ b`, `log b ≤ b/400 + 400`, `b - log b ≤ a`, `a/20 ≤ d`, `d ≤ log 48 + 2b - a`, `0 ≤ m`,
`m ≤ a` and the branch condition.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Work.HP.MDEstimates.hiparts

/-! ## The eight per-case linear conditions -/

/-- Case `Δ ≤ B`, branch `2Δ ≤ (2M)^53`, first (`T1`) part. -/
def hc_c1AP (k : ℕ) (a b d : ℝ) : Prop :=
  (1/32 - (k:ℝ)) * a + (2*(k:ℝ) - 3.999 + 1/1000) * b + (3 - (k:ℝ)) * d ≤ 1900

/-- Case `Δ ≤ B`, branch `2Δ ≤ (2M)^53`, second (`T2`) part. -/
def hc_c2AP (k : ℕ) (a b d m : ℝ) : Prop :=
  ((k:ℝ) + 31/32) * a + ((67:ℝ) - (k:ℝ)) * m - (4.001 + 1/1000) * b - 3 * d ≥ -1900

/-- Case `Δ ≤ B`, branch `(2M)^53 ≤ 2Δ`, first part. -/
def hc_c1AQ (k : ℕ) (a b d m : ℝ) : Prop :=
  (1/32 - (k:ℝ)) * a + (2*(k:ℝ) - 3.999 + 1/1000) * b + (2 - (k:ℝ)) * d + 53 * m ≤ 1900

/-- Case `Δ ≤ B`, branch `(2M)^53 ≤ 2Δ`, second part. -/
def hc_c2AQ (k : ℕ) (a b d m : ℝ) : Prop :=
  ((k:ℝ) + 31/32) * a + (14 - (k:ℝ)) * m - (4.001 + 1/1000) * b - 2 * d ≥ -1900

/-- Case `B ≤ Δ`, branch `2Δ ≤ (2M)^53`, first part. -/
def hc_c1BP (a b d : ℝ) : Prop :=
  -5.96875 * a + (6.501 + 1/1000) * b - 1.5 * d ≤ 1900

/-- Case `B ≤ Δ`, branch `2Δ ≤ (2M)^53`, second part. -/
def hc_c2BP (a b d m : ℝ) : Prop :=
  6.96875 * a + 61 * m - (2.501 + 1/1000) * b - 4.5 * d ≥ -1900

/-- Case `B ≤ Δ`, branch `(2M)^53 ≤ 2Δ`, first part. -/
def hc_c1BQ (a b d m : ℝ) : Prop :=
  -5.96875 * a + (6.501 + 1/1000) * b - 2.5 * d + 53 * m ≤ 1900

/-- Case `B ≤ Δ`, branch `(2M)^53 ≤ 2Δ`, second part. -/
def hc_c2BQ (a b d m : ℝ) : Prop :=
  6.96875 * a + 8 * m - (2.501 + 1/1000) * b - 3.5 * d ≥ -1900

/-! ## Elementary bounds on `log 2` and `log 48` -/

lemma hc_log_two_le_one : Real.log 2 ≤ 1 := by
  have h := Real.log_le_sub_one_of_pos (show (0:ℝ) < 2 by norm_num)
  linarith

lemma hc_log_fortyeight_le : Real.log 48 ≤ 47 := by
  have h := Real.log_le_sub_one_of_pos (show (0:ℝ) < 48 by norm_num)
  linarith

/-! ## Unpacking helpers -/

lemma c1AP_unpack {k : ℕ} {a b d : ℝ} (h : hc_c1AP k a b d) :
    (1/32 - (k:ℝ)) * a + (2*(k:ℝ) - 3.999 + 1/1000) * b + (3 - (k:ℝ)) * d ≤ 1900 := h

lemma c2AP_unpack {k : ℕ} {a b d m : ℝ} (h : hc_c2AP k a b d m) :
    ((k:ℝ) + 31/32) * a + ((67:ℝ) - (k:ℝ)) * m - (4.001 + 1/1000) * b - 3 * d ≥ -1900 := h

lemma c1AQ_unpack {k : ℕ} {a b d m : ℝ} (h : hc_c1AQ k a b d m) :
    (1/32 - (k:ℝ)) * a + (2*(k:ℝ) - 3.999 + 1/1000) * b + (2 - (k:ℝ)) * d + 53 * m ≤ 1900 := h

lemma c2AQ_unpack {k : ℕ} {a b d m : ℝ} (h : hc_c2AQ k a b d m) :
    ((k:ℝ) + 31/32) * a + (14 - (k:ℝ)) * m - (4.001 + 1/1000) * b - 2 * d ≥ -1900 := h

lemma c1BP_unpack {a b d : ℝ} (h : hc_c1BP a b d) :
    -5.96875 * a + (6.501 + 1/1000) * b - 1.5 * d ≤ 1900 := h

lemma c2BP_unpack {a b d m : ℝ} (h : hc_c2BP a b d m) :
    6.96875 * a + 61 * m - (2.501 + 1/1000) * b - 4.5 * d ≥ -1900 := h

lemma c1BQ_unpack {a b d m : ℝ} (h : hc_c1BQ a b d m) :
    -5.96875 * a + (6.501 + 1/1000) * b - 2.5 * d + 53 * m ≤ 1900 := h

lemma c2BQ_unpack {a b d m : ℝ} (h : hc_c2BQ a b d m) :
    6.96875 * a + 8 * m - (2.501 + 1/1000) * b - 3.5 * d ≥ -1900 := h

/-! ## Case `Δ ≤ B`, branch `2Δ ≤ (2M)^53` -/

lemma hc_derive_c1AP_4 (a b d : ℝ) (hb : (1000000:ℝ) ≤ b) (ha : b - Real.log b ≤ a)
    (hl : Real.log b ≤ b / 400 + 400) (hd : a / 20 ≤ d) : hc_c1AP 4 a b d := by
  unfold hc_c1AP; norm_num; linarith

lemma hc_derive_c1AP_5 (a b d m : ℝ) (hb : (1000000:ℝ) ≤ b) (ha : b - Real.log b ≤ a)
    (hl : Real.log b ≤ b / 400 + 400) (hd : a / 20 ≤ d) (hm : 0 ≤ m)
    (hbr : d ≤ 53 * m + 52 * Real.log 2) (h4 : ¬ hc_c2AP 4 a b d m) : hc_c1AP 5 a b d := by
  have h4' := h4
  simp only [hc_c2AP] at h4'
  norm_num at h4'
  have hg := hc_log_two_le_one
  have hg0 : (0:ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  unfold hc_c1AP; norm_num; linarith

lemma hc_derive_c1AP_6 (a b d m : ℝ) (hb : (1000000:ℝ) ≤ b) (ha : b - Real.log b ≤ a)
    (hl : Real.log b ≤ b / 400 + 400) (hd : a / 20 ≤ d) (hm : 0 ≤ m)
    (hbr : d ≤ 53 * m + 52 * Real.log 2) (h5 : ¬ hc_c2AP 5 a b d m) : hc_c1AP 6 a b d := by
  have h5' := h5
  simp only [hc_c2AP] at h5'
  norm_num at h5'
  have hg := hc_log_two_le_one
  have hg0 : (0:ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  unfold hc_c1AP; norm_num; linarith

lemma hc_derive_c1AP_67 (a b d m : ℝ) (hb : (1000000:ℝ) ≤ b) (ha : b - Real.log b ≤ a)
    (hl : Real.log b ≤ b / 400 + 400) (hd : a / 20 ≤ d) (hm : 0 ≤ m)
    (hbr : d ≤ 53 * m + 52 * Real.log 2) (h6 : ¬ hc_c2AP 6 a b d m) : hc_c1AP 67 a b d := by
  have h6' := h6
  simp only [hc_c2AP] at h6'
  norm_num at h6'
  have hg := hc_log_two_le_one
  have hg0 : (0:ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  unfold hc_c1AP; norm_num; linarith

lemma hc_derive_c2AP_67 (a b d m : ℝ) (hb : (1000000:ℝ) ≤ b) (ha : b - Real.log b ≤ a)
    (hl : Real.log b ≤ b / 400 + 400) (hm : 0 ≤ m) (h5b : d ≤ Real.log 48 + 2 * b - a) :
    hc_c2AP 67 a b d m := by
  have hH := hc_log_fortyeight_le
  unfold hc_c2AP; norm_num; linarith

/-! ## Case `Δ ≤ B`, branch `(2M)^53 ≤ 2Δ`

In this branch `53 m ≤ d - 52 log 2`, which bounds `m` *above* — exactly what the first
(`T1`) conditions, which carry `+ 53 m`, need. -/

lemma hc_derive_c1AQ_4 (a b d m : ℝ) (hb : (1000000:ℝ) ≤ b) (ha : b - Real.log b ≤ a)
    (hl : Real.log b ≤ b / 400 + 400) (hd : a / 20 ≤ d) (hm : 0 ≤ m)
    (hbr : 53 * m + 52 * Real.log 2 ≤ d) : hc_c1AQ 4 a b d m := by
  have hg := hc_log_two_le_one
  have hg0 : (0:ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  unfold hc_c1AQ; norm_num; linarith

lemma hc_derive_c1AQ_5 (a b d m : ℝ) (hb : (1000000:ℝ) ≤ b) (ha : b - Real.log b ≤ a)
    (hl : Real.log b ≤ b / 400 + 400) (hd : a / 20 ≤ d) (hm : 0 ≤ m)
    (hbr : 53 * m + 52 * Real.log 2 ≤ d) (h4 : ¬ hc_c2AQ 4 a b d m) : hc_c1AQ 5 a b d m := by
  have h4' := h4
  simp only [hc_c2AQ] at h4'
  norm_num at h4'
  have hg0 : (0:ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  unfold hc_c1AQ; norm_num; linarith

lemma hc_derive_c1AQ_6 (a b d m : ℝ) (hb : (1000000:ℝ) ≤ b) (ha : b - Real.log b ≤ a)
    (hl : Real.log b ≤ b / 400 + 400) (hd : a / 20 ≤ d) (hm : 0 ≤ m)
    (hbr : 53 * m + 52 * Real.log 2 ≤ d) (h5 : ¬ hc_c2AQ 5 a b d m) : hc_c1AQ 6 a b d m := by
  have h5' := h5
  simp only [hc_c2AQ] at h5'
  norm_num at h5'
  have hg0 : (0:ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  unfold hc_c1AQ; norm_num; linarith

lemma hc_derive_c1AQ_67 (a b d m : ℝ) (hb : (1000000:ℝ) ≤ b) (ha : b - Real.log b ≤ a)
    (hl : Real.log b ≤ b / 400 + 400) (hd : a / 20 ≤ d) (hm : 0 ≤ m)
    (hbr : 53 * m + 52 * Real.log 2 ≤ d) (h5b : d ≤ Real.log 48 + 2 * b - a)
    (h6 : ¬ hc_c2AQ 6 a b d m) : hc_c1AQ 67 a b d m := by
  have h6' := h6
  simp only [hc_c2AQ] at h6'
  norm_num at h6'
  have hg := hc_log_two_le_one
  have hg0 : (0:ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hH := hc_log_fortyeight_le
  unfold hc_c1AQ; norm_num; linarith

lemma hc_derive_c2AQ_67 (a b d m : ℝ) (hb : (1000000:ℝ) ≤ b) (ha : b - Real.log b ≤ a)
    (hl : Real.log b ≤ b / 400 + 400) (hm : 0 ≤ m) (hbr : 53 * m + 52 * Real.log 2 ≤ d)
    (h5b : d ≤ Real.log 48 + 2 * b - a) : hc_c2AQ 67 a b d m := by
  have hg := hc_log_two_le_one
  have hg0 : (0:ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hH := hc_log_fortyeight_le
  unfold hc_c2AQ; norm_num; linarith

/-! ## Case `B ≤ Δ` -/

lemma hc_derive_c1BP (a b d : ℝ) (hb : (1000000:ℝ) ≤ b) (ha : b - Real.log b ≤ a)
    (hl : Real.log b ≤ b / 400 + 400) (hcB : b ≤ d) : hc_c1BP a b d := by
  unfold hc_c1BP; norm_num; linarith

lemma hc_derive_c2BP (a b d m : ℝ) (hb : (1000000:ℝ) ≤ b) (ha : b - Real.log b ≤ a)
    (hl : Real.log b ≤ b / 400 + 400) (hm : 0 ≤ m) (hcB : b ≤ d)
    (hbr : d ≤ 53 * m + 52 * Real.log 2) (h5b : d ≤ Real.log 48 + 2 * b - a) :
    hc_c2BP a b d m := by
  have hg := hc_log_two_le_one
  have hg0 : (0:ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hH := hc_log_fortyeight_le
  unfold hc_c2BP; norm_num; linarith

lemma hc_derive_c1BQ (a b d m : ℝ) (hb : (1000000:ℝ) ≤ b) (ha : b - Real.log b ≤ a)
    (hl : Real.log b ≤ b / 400 + 400) (hcB : b ≤ d) (hbr : 53 * m + 52 * Real.log 2 ≤ d) :
    hc_c1BQ a b d m := by
  have hg := hc_log_two_le_one
  have hg0 : (0:ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  unfold hc_c1BQ; norm_num; linarith

lemma hc_derive_c2BQ (a b d m : ℝ) (hb : (1000000:ℝ) ≤ b) (ha : b - Real.log b ≤ a)
    (hl : Real.log b ≤ b / 400 + 400) (hm : 0 ≤ m) (h5b : d ≤ Real.log 48 + 2 * b - a) :
    hc_c2BQ a b d m := by
  have hH := hc_log_fortyeight_le
  unfold hc_c2BQ; norm_num; linarith

/-! ## The four case lemmas -/

theorem hc_core_AP (a b d m : ℝ) (hb : (1000000:ℝ) ≤ b) (ha : b - Real.log b ≤ a)
    (hl : Real.log b ≤ b / 400 + 400) (hd : a / 20 ≤ d) (hm : 0 ≤ m)
    (h5b : d ≤ Real.log 48 + 2 * b - a) (hbr : d ≤ 53 * m + 52 * Real.log 2) :
    ∃ k ∈ Finset.Icc 4 67, hc_c1AP k a b d ∧ hc_c2AP k a b d m := by
  by_cases h4 : hc_c2AP 4 a b d m
  · exact ⟨4, by norm_num [Finset.mem_Icc], hc_derive_c1AP_4 a b d hb ha hl hd, h4⟩
  · by_cases h5 : hc_c2AP 5 a b d m
    · exact ⟨5, by norm_num [Finset.mem_Icc], hc_derive_c1AP_5 a b d m hb ha hl hd hm hbr h4, h5⟩
    · by_cases h6 : hc_c2AP 6 a b d m
      · exact ⟨6, by norm_num [Finset.mem_Icc], hc_derive_c1AP_6 a b d m hb ha hl hd hm hbr h5, h6⟩
      · exact ⟨67, by norm_num [Finset.mem_Icc], hc_derive_c1AP_67 a b d m hb ha hl hd hm hbr h6,
          hc_derive_c2AP_67 a b d m hb ha hl hm h5b⟩

theorem hc_core_AQ (a b d m : ℝ) (hb : (1000000:ℝ) ≤ b) (ha : b - Real.log b ≤ a)
    (hl : Real.log b ≤ b / 400 + 400) (hd : a / 20 ≤ d) (hm : 0 ≤ m)
    (h5b : d ≤ Real.log 48 + 2 * b - a) (hbr : 53 * m + 52 * Real.log 2 ≤ d) :
    ∃ k ∈ Finset.Icc 4 67, hc_c1AQ k a b d m ∧ hc_c2AQ k a b d m := by
  by_cases h4 : hc_c2AQ 4 a b d m
  · exact ⟨4, by norm_num [Finset.mem_Icc], hc_derive_c1AQ_4 a b d m hb ha hl hd hm hbr, h4⟩
  · by_cases h5 : hc_c2AQ 5 a b d m
    · exact ⟨5, by norm_num [Finset.mem_Icc], hc_derive_c1AQ_5 a b d m hb ha hl hd hm hbr h4, h5⟩
    · by_cases h6 : hc_c2AQ 6 a b d m
      · exact ⟨6, by norm_num [Finset.mem_Icc], hc_derive_c1AQ_6 a b d m hb ha hl hd hm hbr h5, h6⟩
      · exact ⟨67, by norm_num [Finset.mem_Icc],
          hc_derive_c1AQ_67 a b d m hb ha hl hd hm hbr h5b h6,
          hc_derive_c2AQ_67 a b d m hb ha hl hm hbr h5b⟩

theorem hc_core_BP (a b d m : ℝ) (hb : (1000000:ℝ) ≤ b) (ha : b - Real.log b ≤ a)
    (hl : Real.log b ≤ b / 400 + 400) (hm : 0 ≤ m) (hcB : b ≤ d)
    (h5b : d ≤ Real.log 48 + 2 * b - a) (hbr : d ≤ 53 * m + 52 * Real.log 2) :
    hc_c1BP a b d ∧ hc_c2BP a b d m :=
  ⟨hc_derive_c1BP a b d hb ha hl hcB, hc_derive_c2BP a b d m hb ha hl hm hcB hbr h5b⟩

theorem hc_core_BQ (a b d m : ℝ) (hb : (1000000:ℝ) ≤ b) (ha : b - Real.log b ≤ a)
    (hl : Real.log b ≤ b / 400 + 400) (hm : 0 ≤ m) (hcB : b ≤ d)
    (h5b : d ≤ Real.log 48 + 2 * b - a) (hbr : 53 * m + 52 * Real.log 2 ≤ d) :
    hc_c1BQ a b d m ∧ hc_c2BQ a b d m :=
  ⟨hc_derive_c1BQ a b d m hb ha hl hcB hbr, hc_derive_c2BQ a b d m hb ha hl hm h5b⟩

end Work.HP.MDEstimates.hiparts
