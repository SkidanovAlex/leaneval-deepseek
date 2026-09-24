import ChallengeDeps
import Submission.Helpers
import Submission.Work.GM.Assembly.keyprop_of_parts
import Submission.Work.GM.HB.hb_statement
import Submission.Work.GM.Trace.trace_statement
import Submission.Work.GM.S2.s2_of_hb
import Submission.Work.GM.S3.s3_of_affine
import Submission.Work.GM.Energy.energy_of_hb
import Submission.Work.GM.Affine.affine_statement
import Submission.LargeValues.Endgame

open LargeValueEstimates
open Asymptotics Complex

set_option autoImplicit false

namespace Submission

theorem theorem_1_1 : ∃ o : ℝ → ℝ, o =o[Filter.atTop] (1 : ℝ → ℝ) ∧
    ∀ (b : ℕ → ℂ) (_hb : ∀ n, ‖b n‖ ≤ 1) (N : ℕ) (V : ℝ) (T : ℝ) (R : ℕ) (t : Fin R → ℝ),
    N > 0 → V > 0 → T > 1 → -- these assumptions are necessary but not stated in the paper
    (∀ i j, i ≠ j → |t i - t j| ≥ 1) → (∀ i, t i ∈ Set.Icc 0 T) →
    (∀ r, ‖∑ n ∈ Finset.Icc N (2 * N), b n * n ^ (I * t r)‖ ≥ V) →
    R ≤ T ^ (o T) * bound N V T :=
  Submission.LargeValues.theorem_1_1_of_keyprop
    (Work.GM.Assembly.keyprop_of_parts Work.GM.Trace.trace_statement
      (Work.GM.S2.s2_of_hb Work.GM.HB.hb_statement)
      (Work.GM.S3.s3_of_affine Work.GM.Affine.affine_statement)
      (Work.GM.Energy.energy_of_hb Work.GM.HB.hb_statement))

end Submission
