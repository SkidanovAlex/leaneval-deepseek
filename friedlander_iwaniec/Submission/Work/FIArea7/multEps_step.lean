import Mathlib
import Submission.Work.FIPlan.Interface
import Submission.Work.FIArea7.FIsymbols

namespace Work.FIArea7

/-- **Step-function threshold for a linear inequality on `ℤ`.**

For fixed integers `M`, `K` the truth value of `M * v < K` is constant on `v ≤ t` and constant
on `t < v` for a suitable integer `t`: the set `{v | M * v < K}` is a down-set when `M > 0`, an
up-set when `M < 0`, and the whole line or empty when `M = 0`.  This is the arithmetic content
of the statement that the branch condition `w.re * z.re > w.im * z.im` of `MultEps`, read along
`z = ⟨r, b + L v⟩`, changes sign at most once. -/
lemma exists_step_threshold (M K : ℤ) :
    ∃ t : ℤ, ∀ v v' : ℤ, ((v ≤ t ∧ v' ≤ t) ∨ (t < v ∧ t < v')) →
      (M * v < K ↔ M * v' < K) := by
  rcases lt_trichotomy M 0 with hM | hM | hM
  · -- `M < 0`: the set `{v | M v < K}` is `{v | t < v}` with `t = (-K)/(-M)`
    have hpos : 0 < -M := by omega
    refine ⟨(-K) / (-M), ?_⟩
    intro v v' hv'
    have key : ∀ v : ℤ, (M * v < K) ↔ ((-K) / (-M) < v) := by
      intro v
      rw [Int.ediv_lt_iff_lt_mul hpos]
      rw [mul_comm v (-M), neg_mul]
      omega
    rw [key v, key v']
    rcases hv' with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact iff_of_false (not_lt.mpr h1) (not_lt.mpr h2)
    · exact iff_of_true h1 h2
  · -- `M = 0`: the truth value is independent of `v`
    subst hM
    exact ⟨0, fun v v' _ => by simp⟩
  · -- `M > 0`: the set `{v | M v < K}` is `{v | v ≤ t}` with `t = (K-1)/M`
    have hpos : 0 < M := hM
    refine ⟨(K - 1) / M, ?_⟩
    intro v v' hv'
    have key : ∀ v : ℤ, (M * v < K) ↔ (v ≤ (K - 1) / M) := by
      intro v
      rw [Int.le_ediv_iff_mul_le hpos]
      rw [mul_comm v M]
      omega
    rw [key v, key v']
    rcases hv' with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact iff_of_true h1 h2
    · exact iff_of_false (not_le.mpr h1) (not_le.mpr h2)

/-- **The multiplier sign `ε(w,z)` of (20.5)/(20.6) is a step function of `s`.**  For fixed `w`,
`r`, `b`, `L`, the function `v ↦ MultEps w ⟨r, b + L v⟩` takes at most two values: the branch
condition `w.re * z.re > w.im * z.im` is linear in `v` (hence changes sign at most once) and both
Hilbert-symbol factors depend only on the *signs* of `z.re = r` and `w.im`, which are fixed.
Used in *FI* §22 to apply summation by parts to the sector character on sub-segments on which `ε`
is constant (the `≤ 2` sub-segments cost nothing). -/
theorem multEps_step (w : GaussianInt) (r b L : ℤ) :
    ∃ t : ℤ, ∀ v v' : ℤ,
      ((v ≤ t ∧ v' ≤ t) ∨ (t < v ∧ t < v')) →
      Work.FIArea7.MultEps w ⟨r, b + L * v⟩ = Work.FIArea7.MultEps w ⟨r, b + L * v'⟩ := by
  obtain ⟨t, ht⟩ := exists_step_threshold (w.im * L) (w.re * r - w.im * b)
  refine ⟨t, ?_⟩
  intro v v' hv'
  have hiff := ht v v' hv'
  -- `MultEps` reads off `z = ⟨r, b + L v⟩` only through the branch condition and the two
  -- Hilbert factors, which are constants on `v`.
  have hfun : ∀ v : ℤ,
      MultEps w ⟨r, b + L * v⟩
        = (if w.re * r > w.im * (b + L * v)
           then HilbertInf w.re w.im * HilbertInf r (-w.im)
           else HilbertInf w.re w.im * HilbertInf (-r) w.im) := by
    intro v; rfl
  rw [hfun v, hfun v']
  by_cases h : w.im * L * v < w.re * r - w.im * b
  · have hp : w.re * r > w.im * (b + L * v) := by nlinarith [h]
    have hp' : w.re * r > w.im * (b + L * v') := by nlinarith [hiff.mp h]
    rw [if_pos hp, if_pos hp']
  · have hp : ¬ (w.re * r > w.im * (b + L * v)) := by
      intro hc; exact h (by nlinarith [hc])
    have hp' : ¬ (w.re * r > w.im * (b + L * v')) := by
      intro hc; exact h (hiff.mpr (by nlinarith [hc]))
    rw [if_neg hp, if_neg hp']

end Work.FIArea7
