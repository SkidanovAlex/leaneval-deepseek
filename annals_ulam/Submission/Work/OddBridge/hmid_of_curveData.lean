import Mathlib
import Submission.Work.OddBridge.Defs

/-!
# Positivity of the radicand `ψ` on the whole slope window, from the curve data

The odd-case construction needs `ψ_s(t) = semicircle t ^ 2 - L(s,t) ^ 2 > 0` on the
section window `t ∈ [-1/√2, 1/√2]`, uniformly over the slopes `s` used by the
Volterra/Abel machinery.  The `CurveData` supplies exactly the numerical
information needed:

* `|h s| ≤ 1/100` for every `s` (`CurveData.close_h`), and
* `support h ⊆ [1 - 2τ, 1 - τ] = [4/5, 9/10]`, so `h` vanishes for `s > 9/10`.

Writing `L(s,t) = s t + h s` and `semicircle t ^ 2 = 1 - t ^ 2` for `|t| ≤ 1`, the
radicand is `1 - t ^ 2 - (s t + h s) ^ 2`, and the two cases are:

* `s ≤ 9/10`: then `|s t + h s| ≤ (9/10)(5/7) + 1/100 = 9/14 + 1/100`, while
  `t ^ 2 ≤ p ^ 2 = 1/2 ≤ 25/49`, and `(9/14 + 1/100) ^ 2 < 1/2 ≤ 1 - t ^ 2`; the
  numerical pinning `p = 1/√2 ≤ 5/7` is what makes the estimate come out strictly.
* `s > 9/10`: then `h s = 0` and `1 - t ^ 2 - (s t) ^ 2 > 0` because `s < 1`
  (respectively `t ^ 2 < 1/2` when `s = 1`).

The two conclusions differ only in the closed/open status of the windows: on the
closed `t`-window the slope `s = 1` must be excluded (at `s = 1`, `t = ±1/√2` the
radicand vanishes), and on the closed slope window `s = 1` the `t`-window must be
open.
-/

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

namespace Work.OddBridge

open Work.OddVolterra
open Commons.Geometry.Ulam

noncomputable section

/-- The radicand is positive for slopes `s ≤ 9/10` (where only the pointwise bound
`|h s| ≤ 1/100` is used) and `|t| ≤ 5/7`: then `|s t + h s| ≤ 9/14 + 1/100` and
`(9/14 + 1/100) ^ 2 < 1/2 ≤ 1 - t ^ 2`. -/
private lemma psi_core_lo {s t : ℝ} {h : ℝ → ℝ} (hs0 : 0 ≤ s) (hs : s ≤ 9 / 10)
    (hH : |h s| ≤ 1 / 100) (ht : |t| ≤ 5 / 7) (ht2 : t ^ 2 ≤ 1 / 2) :
    0 < 1 - t ^ 2 - (s * t + h s) ^ 2 := by
  have hsabs : |s| ≤ 9 / 10 := by rw [abs_of_nonneg hs0]; exact hs
  have habs : |s * t + h s| ≤ 9 / 14 + 1 / 100 := by
    calc |s * t + h s| ≤ |s * t| + |h s| := abs_add_le _ _
      _ = |s| * |t| + |h s| := by rw [abs_mul]
      _ ≤ (9 / 10) * (5 / 7) + 1 / 100 :=
          add_le_add (mul_le_mul hsabs ht (abs_nonneg _) (by norm_num)) hH
      _ = 9 / 14 + 1 / 100 := by norm_num
  have h1 : (s * t + h s) ^ 2 ≤ (9 / 14 + 1 / 100) ^ 2 := by
    rw [sq_le_sq, abs_of_pos (by norm_num : (0 : ℝ) < 9 / 14 + 1 / 100)]
    exact habs
  have h2 : (9 / 14 + 1 / 100 : ℝ) ^ 2 < 1 / 2 := by norm_num
  nlinarith [h1, h2, ht2, sq_nonneg t]

/-- The radicand is positive for slopes `s > 9/10`, where `h s = 0`, and `s < 1`. -/
private lemma psi_core_hi {s t : ℝ} {h : ℝ → ℝ} (hsz : h s = 0) (hs0 : 0 < s)
    (hs1 : s < 1) (ht2 : t ^ 2 ≤ 1 / 2) : 0 < 1 - t ^ 2 - (s * t + h s) ^ 2 := by
  rw [hsz, add_zero]
  by_cases ht0 : t = 0
  · subst ht0; norm_num
  · have htpos : 0 < t ^ 2 := by positivity
    have hs2 : s ^ 2 < 1 := by nlinarith
    nlinarith [htpos, ht2, hs2]

/-- The radicand is positive for slopes `s > 9/10`, where `h s = 0`, when `s = 1`
is allowed but the `t`-window is open (`t ^ 2 < 1/2`). -/
private lemma psi_core_hi_le {s t : ℝ} {h : ℝ → ℝ} (hsz : h s = 0) (hs0 : 0 < s)
    (hs1 : s ≤ 1) (ht2 : t ^ 2 < 1 / 2) : 0 < 1 - t ^ 2 - (s * t + h s) ^ 2 := by
  rw [hsz, add_zero]
  have hs2 : s ^ 2 ≤ 1 := by nlinarith
  nlinarith [ht2, hs2, sq_nonneg t]

/-- `1/√2 = profileX 1 ≤ 5/7`; the rational upper bound for `1/√2` used by
`psi_core_lo`. -/
private lemma profileX_one_le {P : ℝ} (hP : P = Commons.Geometry.Ulam.profileX 1) :
    P ≤ 5 / 7 := by
  subst hP
  have hp2 : (Commons.Geometry.Ulam.profileX 1) ^ 2 = (1 : ℝ) / 2 := by
    rw [Commons.Geometry.Ulam.profileX_sq]; norm_num
  nlinarith [sq_nonneg (Commons.Geometry.Ulam.profileX 1 - 5 / 7)]

theorem hmid_of_curveData (n : ℕ) {h x y : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hhsupp : Function.support h ⊆ Set.Icc (1 - 2 * Work.OddVolterra.tau) (1 - Work.OddVolterra.tau))
    (hdata : Work.OddVolterra.CurveData n h x y) :
    (∀ s ∈ Set.Ioo (0 : ℝ) 1, ∀ t ∈ Set.Icc (-(Commons.Geometry.Ulam.profileX 1)) (Commons.Geometry.Ulam.profileX 1),
      0 < Work.OddVolterra.psi h Commons.Geometry.Ulam.semicircle s t) ∧
    (∀ s ∈ Set.Ioc (0 : ℝ) 1, ∀ t ∈ Set.Ioo (-(Commons.Geometry.Ulam.profileX 1)) (Commons.Geometry.Ulam.profileX 1),
      0 < Work.OddVolterra.psi h Commons.Geometry.Ulam.semicircle s t) := by
  have hp_pos : 0 < Commons.Geometry.Ulam.profileX 1 :=
    Commons.Geometry.Ulam.profileX_pos 1 (by norm_num)
  have hp_sq : (Commons.Geometry.Ulam.profileX 1) ^ 2 = (1 : ℝ) / 2 := by
    rw [Commons.Geometry.Ulam.profileX_sq]; norm_num
  have hp57 : Commons.Geometry.Ulam.profileX 1 ≤ 5 / 7 := profileX_one_le rfl
  have hbound : ∀ s : ℝ, |h s| ≤ 1 / 100 := fun s => (hdata.close_h s).1
  -- `h` vanishes strictly above the support window `[4/5, 9/10]`.
  have hzero_hi : ∀ z : ℝ, 9 / 10 < z → h z = 0 := by
    intro z hz
    by_contra hne
    have hmem := hhsupp hne
    have h2 : z ≤ 1 - Work.OddVolterra.tau := hmem.2
    rw [Work.OddVolterra.tau] at h2
    norm_num at h2
    linarith
  constructor
  · intro s hs t ht
    have hs0 : 0 < s := hs.1
    have hs1 : s < 1 := hs.2
    have htabs_p : |t| ≤ Commons.Geometry.Ulam.profileX 1 := by
      rw [abs_le]; exact ⟨by linarith [ht.1], ht.2⟩
    have htabs : |t| ≤ 5 / 7 := le_trans htabs_p hp57
    have ht2 : t ^ 2 ≤ 1 / 2 := by
      have h' : |t| ≤ |Commons.Geometry.Ulam.profileX 1| := by
        rwa [abs_of_pos hp_pos]
      have := (sq_le_sq).mpr h'
      rw [hp_sq] at this
      exact this
    have ht_Icc : t ∈ Set.Icc (-1 : ℝ) 1 := by
      obtain ⟨h1, h2⟩ := abs_le.mp htabs
      constructor <;> linarith
    rw [Work.OddVolterra.psi, Work.OddVolterra.line,
      Commons.Geometry.Ulam.semicircle_sq_of_mem_Icc ht_Icc]
    rcases le_or_gt s (9 / 10) with hcase | hcase
    · exact psi_core_lo (le_of_lt hs0) hcase (hbound s) htabs ht2
    · exact psi_core_hi (hzero_hi s hcase) hs0 hs1 ht2
  · intro s hs t ht
    have hs0 : 0 < s := hs.1
    have hs1 : s ≤ 1 := hs.2
    have htabs_p : |t| < Commons.Geometry.Ulam.profileX 1 := by
      rw [abs_lt]; exact ⟨by linarith [ht.1], ht.2⟩
    have htabs : |t| ≤ 5 / 7 := le_of_lt (lt_of_lt_of_le htabs_p hp57)
    have ht2 : t ^ 2 < 1 / 2 := by
      have h' : |t| < |Commons.Geometry.Ulam.profileX 1| := by
        rwa [abs_of_pos hp_pos]
      have := (sq_lt_sq).mpr h'
      rw [hp_sq] at this
      exact this
    have ht_Icc : t ∈ Set.Icc (-1 : ℝ) 1 := by
      obtain ⟨h1, h2⟩ := abs_le.mp htabs
      constructor <;> linarith
    rw [Work.OddVolterra.psi, Work.OddVolterra.line,
      Commons.Geometry.Ulam.semicircle_sq_of_mem_Icc ht_Icc]
    rcases le_or_gt s (9 / 10) with hcase | hcase
    · exact psi_core_lo (le_of_lt hs0) hcase (hbound s) htabs (le_of_lt ht2)
    · exact psi_core_hi_le (hzero_hi s hcase) hs0 hs1 ht2

end

end Work.OddBridge
