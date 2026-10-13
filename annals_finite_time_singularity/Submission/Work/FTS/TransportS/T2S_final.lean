/-
Copyright: work module for the Elgindi finite-time singularity project.

# `T2S` assembled from its inputs

`Work.FTS.TransportS.T2S_of_pieces` reduces the frozen `T2S` to six inputs.  Three of them are
proved in this workspace and are imported here:

* `T2SupG` — `T2SupG_proof` (proved in `T2S.lean`, from the proved
  `Work.FTS.H2.T2Qaux.supQ_T2Q`);
* `T2Slice` — `Submission/Work/FTS/TransportS/t2Slice.lean` (proved);
* `T2Hard` — `Submission/Work/FTS/TransportS/t2Hard.lean` (proved);
* `T2Aesm` — `Submission/Work/FTS/TransportS/t2Aesm.lean` (proved).

The remaining two (`T2SupF`, `T2Easy`) are taken as hypotheses here, so that this module is
`sorry`-free; their (in-flight) proofs live at
`Submission/Work/FTS/TransportS/t2SupF.lean` and `.../t2Easy.lean`.
-/
import Mathlib.Analysis.Real.Sqrt
import Submission.Work.FTS.TransportS.T2S
import Submission.Work.FTS.TransportS.t2Slice
import Submission.Work.FTS.TransportS.t2Hard
import Submission.Work.FTS.TransportS.t2Aesm

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.TransportS

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-- **The frozen `T2S` from `T2SupF` and `T2Easy`.**  All the other inputs of `T2S_of_pieces`
are proved in the workspace. -/
theorem T2S_of_two (hF : T2SupF) (hEasy : T2Easy) :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (f g : Fn), 0 < α → α ≤ 1 → T2SF α f → T2SG α g →
      |Work.FTS.H2.H4Pair α (fun z θ => f z θ * Work.Spaces.Dz g z θ) g|
        ≤ C / Real.sqrt (Work.Spaces.gam α - 1)
            * (Work.FTS.Nonlin.Xn α f + Work.FTS.VocabO.CoefTh 1 f)
            * Work.FTS.Nonlin.Xn α g ^ 2 :=
  T2S_of_pieces hF T2SupG_proof t2Slice hEasy t2Hard t2Aesm

end Work.FTS.TransportS
