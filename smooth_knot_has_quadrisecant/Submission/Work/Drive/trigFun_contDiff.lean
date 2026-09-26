import Mathlib
import Submission.Work.Drive.trigFun

namespace Work.Drive

/-- Every trigonometric sum `t ↦ Σ_k cos (k t) • c_k + sin (k t) • d_k` (`k : ℤ`) with coefficients
in a real normed space is **analytic** (`ContDiff ℝ ⊤`, where `⊤ = ω`) on `ℝ`.
Route: `Work.Drive.TrigFun.toFun` is a `Finsupp.sum`; `change` to the unfolded `Finset.sum` form
(`rw [TrigFun.toFun]` fails), and use `Real.contDiff_cos`/`Real.contDiff_sin` composed with
`t ↦ (k:ℝ) * t`, `ContDiff.smul_const` (a scalar function times a constant vector) and
`ContDiff.sum`/`ContDiff.add`. -/
theorem trigFun_contDiff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (P : Work.Drive.TrigFun E) : ContDiff ℝ ⊤ P.toFun := by
  -- unfold `toFun` and the two `Finsupp.sum`s into `Finset.sum`s
  change ContDiff ℝ ⊤ (fun t : ℝ =>
    P.c.sum (fun k v => Real.cos ((k : ℝ) * t) • v) +
    P.d.sum (fun k v => Real.sin ((k : ℝ) * t) • v))
  change ContDiff ℝ ⊤ (fun t : ℝ =>
    (P.c.support.sum (fun k => Real.cos ((k : ℝ) * t) • P.c k)) +
    (P.d.support.sum (fun k => Real.sin ((k : ℝ) * t) • P.d k)))
  refine ContDiff.add ?_ ?_
  · exact ContDiff.sum (fun i _ => ContDiff.smul_const (Real.contDiff_cos.comp
      (contDiff_const.mul contDiff_id)) _)
  · exact ContDiff.sum (fun i _ => ContDiff.smul_const (Real.contDiff_sin.comp
      (contDiff_const.mul contDiff_id)) _)

end Work.Drive
