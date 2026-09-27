import Mathlib
import Submission.Work.Geo.Prism.Defs

/-!
# The elementary stretch `str` of `ℝ`

API for `Work.Geo.Prism.str`, the total function

`str a b c t = t + (c - b) * clamp01 ((t - a) / (b - a))`,  `clamp01 x = min 1 (max 0 x)`.

For `a < b` and `a < c` this is the piecewise linear map of `ℝ` which is the identity on
`(-∞, a]`, maps `[a, b]` linearly onto `[a, c]`, and translates `[b, ∞)` by `c - b`; it is
a bijection with inverse `str a c b` (`str_inv_left`, `str_inv_right`), and
`str a b c '' Icc a b = Icc a c` (`str_image_Icc`).

Warning: `str` is *not* jointly continuous in all four variables.  It is discontinuous at
`(a, b, c, t)` with `a = b` and `c ≠ b` (the "jump" of a stretch of zero length; e.g.
`str 0 ε 1 ε = 1 → 1` while `str 0 0 1 0 = 0`).  What is true, and is what the prism
construction uses, is `str_continuousAt` (continuity at points with `a ≠ b`) together with
the unconditional bound `str_dist_le : |str a b c t - t| ≤ |c - b|`, which shows that the
map collapses to the identity uniformly as the "amplitude" `c - b` tends to `0`.
-/

open Set Metric
open scoped Topology
open Classical

namespace Work.Geo.Prism

/-- `str a b c` is continuous at every point with `a ≠ b`. -/
theorem str_continuousAt {X : Type*} [TopologicalSpace X] {f g h k : X → ℝ} {x : X}
    (hf : ContinuousAt f x) (hg : ContinuousAt g x) (hh : ContinuousAt h x)
    (hk : ContinuousAt k x) (hne : g x ≠ f x) :
    ContinuousAt (fun y => str (f y) (g y) (h y) (k y)) x := by
  have h0 : g x - f x ≠ 0 := sub_ne_zero.mpr hne
  unfold str clamp01
  fun_prop (disch := assumption)

/-- `str a b c` fixes everything at or below `a` (for `a ≤ b`). -/
theorem str_self_of_le {a b c t : ℝ} (hab : a ≤ b) (h : t ≤ a) : str a b c t = t := by
  have hq : (t - a) / (b - a) ≤ 0 := by
    rcases eq_or_lt_of_le hab with h' | h'
    · subst h'; simp
    · exact div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
  unfold str clamp01
  rw [max_eq_left hq, min_eq_right (by norm_num : (0 : ℝ) ≤ 1)]
  ring

/-- `str a b b` is the identity (zero amplitude). -/
theorem str_self_of_eq (a b t : ℝ) : str a b b t = t := by
  unfold str clamp01
  ring

/-- `str a a c` is the identity (zero length). -/
theorem str_self_of_same (a c t : ℝ) : str a a c t = t := by
  unfold str clamp01
  simp

/-- Above `b` (for `a < b`), `str a b c` is the translation by `c - b`. -/
theorem str_eq_of_ge {a b c t : ℝ} (hab : a < b) (h : b ≤ t) : str a b c t = t + (c - b) := by
  have hq : 1 ≤ (t - a) / (b - a) := by
    rw [le_div_iff₀ (by linarith : (0 : ℝ) < b - a)]; linarith
  unfold str clamp01
  rw [max_eq_right (by linarith), min_eq_left hq]
  ring_nf

/-- Between `a` and `b`, `str a b c` is the linear interpolation from `a` to `c`. -/
theorem str_eq_between {a b c t : ℝ} (hab : a < b) (h₁ : a ≤ t) (h₂ : t ≤ b) :
    str a b c t = a + (t - a) * (c - a) / (b - a) := by
  have hq0 : 0 ≤ (t - a) / (b - a) := div_nonneg (by linarith) (by linarith)
  have hq1 : (t - a) / (b - a) ≤ 1 := by
    rw [div_le_one (by linarith : (0 : ℝ) < b - a)]; linarith
  unfold str clamp01
  rw [max_eq_right hq0, min_eq_right hq1]
  have hne : b - a ≠ 0 := by linarith
  field_simp
  ring

/-- The value of `str` is never farther from `t` than the "amplitude" `|c - b|`. -/
theorem str_dist_le (a b c t : ℝ) : |str a b c t - t| ≤ |c - b| := by
  have key : ∀ x : ℝ, |min 1 (max 0 x)| ≤ 1 := by
    intro x
    rw [abs_of_nonneg (le_min (by norm_num) (le_max_left _ _))]
    exact min_le_left _ _
  unfold str clamp01
  rw [add_sub_cancel_left, abs_mul]
  calc |c - b| * |min 1 (max 0 ((t - a) / (b - a)))| ≤ |c - b| * 1 := by
        gcongr
        exact key _
    _ = |c - b| := by ring

/-- `str a c b` is a left inverse of `str a b c` when `a < b` and `a < c`. -/
theorem str_inv_left {a b c : ℝ} (hab : a < b) (hac : a < c) (t : ℝ) :
    str a c b (str a b c t) = t := by
  rcases le_or_gt t a with h | h
  · rw [str_self_of_le (le_of_lt hab) h, str_self_of_le (le_of_lt hac) h]
  rcases le_or_gt b t with h2 | h2
  · rw [str_eq_of_ge hab h2, str_eq_of_ge hac (by linarith : c ≤ t + (c - b))]
    ring
  · have hu₁ : a ≤ a + (t - a) * (c - a) / (b - a) := by
      have : 0 ≤ (t - a) * (c - a) / (b - a) :=
        div_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)
      linarith
    have hu₂ : a + (t - a) * (c - a) / (b - a) ≤ c := by
      have hq1 : (t - a) / (b - a) ≤ 1 := by
        rw [div_le_one (by linarith : (0 : ℝ) < b - a)]; linarith
      have heq : (t - a) * (c - a) / (b - a) = ((t - a) / (b - a)) * (c - a) := by ring
      rw [heq]
      nlinarith [hq1, sub_pos.mpr hac]
    rw [str_eq_between hab (le_of_lt h) (le_of_lt h2), str_eq_between hac hu₁ hu₂]
    have hne1 : b - a ≠ 0 := by linarith
    have hne2 : c - a ≠ 0 := by linarith
    field_simp
    ring

/-- `str a c b` is a right inverse of `str a b c` when `a < b` and `a < c`. -/
theorem str_inv_right {a b c : ℝ} (hab : a < b) (hac : a < c) (t : ℝ) :
    str a b c (str a c b t) = t :=
  str_inv_left hac hab t

/-- `str a c b` is a two-sided inverse of `str a b c`. -/
theorem str_inv {a b c : ℝ} (hab : a < b) (hac : a < c) (t : ℝ) :
    str a c b (str a b c t) = t ∧ str a b c (str a c b t) = t :=
  ⟨str_inv_left hab hac t, str_inv_right hab hac t⟩

/-- `str a b c` maps the interval `[a, b]` onto the interval `[a, c]` (for `a < b`, `a < c`). -/
theorem str_image_Icc {a b c : ℝ} (hab : a < b) (hac : a < c) :
    str a b c '' Icc a b = Icc a c := by
  have hb : a ≤ b := le_of_lt hab
  have hc : a ≤ c := le_of_lt hac
  have inner : ∀ t ∈ Icc a b, str a b c t ∈ Icc a c := by
    intro t ht
    rw [mem_Icc] at ht
    have hq0 : 0 ≤ (t - a) / (b - a) := div_nonneg (by linarith [ht.1]) (by linarith)
    have hq1 : (t - a) / (b - a) ≤ 1 := by
      rw [div_le_one (by linarith : (0 : ℝ) < b - a)]; linarith [ht.2]
    have heq : (t - a) * (c - a) / (b - a) = ((t - a) / (b - a)) * (c - a) := by ring
    rw [mem_Icc]
    rcases eq_or_lt_of_le ht.1 with h | h
    · have hta : t = a := h.symm
      subst hta
      rw [str_self_of_le hb le_rfl]
      exact ⟨le_rfl, hc⟩
    · rw [str_eq_between hab ht.1 ht.2, heq]
      constructor
      · have : 0 ≤ ((t - a) / (b - a)) * (c - a) := mul_nonneg hq0 (by linarith)
        linarith
      · nlinarith [hq1, sub_pos.mpr hac]
  refine Subset.antisymm ?_ ?_
  · rintro u ⟨t, ht, rfl⟩
    exact inner t ht
  · intro u hu
    rw [mem_Icc] at hu
    refine ⟨str a c b u, ?_, str_inv_right hab hac u⟩
    have hq0 : 0 ≤ (u - a) / (c - a) := div_nonneg (by linarith [hu.1]) (by linarith)
    have hq1 : (u - a) / (c - a) ≤ 1 := by
      rw [div_le_one (by linarith : (0 : ℝ) < c - a)]; linarith [hu.2]
    have heq : (u - a) * (b - a) / (c - a) = ((u - a) / (c - a)) * (b - a) := by ring
    rw [mem_Icc]
    rcases eq_or_lt_of_le hu.1 with h | h
    · have hua : u = a := h.symm
      rw [hua, str_self_of_le (le_of_lt hac) le_rfl]
      exact ⟨le_rfl, le_of_lt hab⟩
    · rw [str_eq_between hac hu.1 hu.2, heq]
      constructor
      · have : 0 ≤ ((u - a) / (c - a)) * (b - a) := mul_nonneg hq0 (by linarith)
        linarith
      · nlinarith [hq1, sub_pos.mpr hab]

end Work.Geo.Prism
