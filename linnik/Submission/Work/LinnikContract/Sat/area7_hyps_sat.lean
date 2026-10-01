import Mathlib
import Submission.Work.LinnikContract.Pre

namespace Work.LinnikContract.Sat

/-- Non-degeneracy of the hypothesis list of AREA 7 (`Assembly`) and record of the numerical
margins of §4.  The threshold `(3/10)^2 - η` in the conclusion of `Assembly` is strictly positive
for every `η < (3/10)^2`, so the conclusion of `Assembly` is a genuine gap and not a tautology; and
the recorded numerical data of §4.1 are consistent: the worst normalised total of HB Lemma 15.1 at
`L = 11/2`, `K = 3/10` with HB's tables is `9944/10000` (margin `56/10000`), and with every λ-bound
lowered by the safety margin `0.001` — which is what the frozen `rows15` does — it is `9956/10000`
(margin `44/10000`); each total plus its margin is `1`.

Prover notes: `norm_num` throughout (mind the parentheses: the square of `3/10`, i.e. `9/100`,
must be written `((3:ℝ)/10)^2` and *not* `(3:ℝ)/10^2 = 3/100`).  No `native_decide`. -/
theorem area7_hyps_sat :
    (∀ η : ℝ, 0 < η → η < ((3:ℝ)/10)^2 → 0 < ((3:ℝ)/10)^2 - η) ∧
    (0 < ((3:ℝ)/10)^2 - (56:ℝ)/10000) ∧
    (0 < ((3:ℝ)/10)^2 - (44:ℝ)/10000) ∧
    ((9944:ℝ)/10000 + (56:ℝ)/10000 = 1) ∧
    ((9956:ℝ)/10000 + (44:ℝ)/10000 = 1) ∧
    ((9944:ℝ)/10000 < 1) ∧ ((9956:ℝ)/10000 < 1) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro η _ hη
    linarith
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num

end Work.LinnikContract.Sat
