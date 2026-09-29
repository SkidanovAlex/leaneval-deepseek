import Mathlib
import Submission.Work.CNum.Hfun_defs
import Submission.Work.CNum.cterm_deriv
import Submission.Work.CNum.cterm_bounds
import Submission.Work.CNum.sum_bound
import Submission.Work.CNum.Hfun_chord

namespace Work.CNum



/-- `KfunDeriv2` is bounded above by `3200` (mirror of `KfunDeriv2_ge`). -/
lemma KfunDeriv2_le (φ : ℝ) : KfunDeriv2 φ ≤ 3200 := by
  have hsum : Summable (fun n : ℕ => ctermDeriv2 (n + 1) φ) := by
    refine Summable.of_norm_bounded summable_ub (fun n => ?_)
    have h := (cterm_bounds (n + 1) (by omega) φ).2
    rw [Real.norm_eq_abs]
    simpa [ub] using h
  have hle : (∑' n : ℕ, ctermDeriv2 (n + 1) φ) ≤ ∑' n : ℕ, ub n :=
    Summable.tsum_le_tsum (fun n => by
      have h := (cterm_bounds (n + 1) (by omega) φ).2
      calc ctermDeriv2 (n + 1) φ ≤ |ctermDeriv2 (n + 1) φ| := le_abs_self _
        _ ≤ ub n := by simpa [ub] using h) hsum summable_ub
  rw [KfunDeriv2]
  exact le_trans hle sum_bound

/-- **Lower chord bound for `Hfun`.**  `Hfun` lies above the chord of its endpoint values,
up to `400 (b-a)²`.  `Hfun_chord` (the upper bound) applied to `-Hfun`. -/
theorem Hfun_chord_lower {a b : ℝ} (hab : a ≤ b) :
    ∀ φ ∈ Set.Icc a b, min (Hfun a) (Hfun b) - 400 * (b - a) ^ 2 ≤ Hfun φ := by
  intro φ hφ
  have h := chord hab (g := fun x => -Hfun x) (g' := fun x => -KfunDeriv x)
      (g'' := fun x => -KfunDeriv2 x) (fun x => (hasDerivAt_Hfun x).neg)
      (fun x => (hasDerivAt_KfunDeriv x).neg) (fun x => by
        rw [neg_le_neg_iff]; exact KfunDeriv2_le x) φ hφ
  rw [max_neg_neg] at h
  linarith

end Work.CNum
