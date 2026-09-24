import Mathlib
import Submission.GM.Interfaces
import Submission.Work.GM.S3.Base
import Submission.Work.GM.S3.Defs
import Submission.Work.GM.S3.Statements
import Submission.Work.GM.S3.R_l2
import Submission.Work.GM.S3.R_l4
import Submission.Work.GM.S3.lemma84_relaxed
import Submission.Work.GM.S3.Gen.cellstatements
import Submission.Work.GM.S3.Gen.S30g_le_cell
import Submission.Work.GM.S3.Gen.S3_le_cellSum
import Submission.Work.GM.S3.Gen.s3_of_cellSum_of

/-! Guidance from the project lead (the requester):

This is a whole AREA (GM §§7, 8, 10: Props 7.1, 7.2, Lemmas 8.2–8.4, Prop 10.1), assuming
Prop 9.1 as the hypothesis `hAff : AffineStatement`.  Paper: `REFS/GuthMaynard_2405.20552.txt`,
Sections 7, 8, 10.

The area is assembled in `Submission/Work/GM/S3/Gen/` (see `Gen/NOTES_cell_route.md`,
`Gen/NOTES_final_assembly.md` and `ROADMAP.md`):

* `Gen.S3_le_cellSum` — GM 7.2 in *cell* form: every truncation triple is estimated with the
  per-`m` bound `norm_Iterm_le_Rtilde_of_domain` at the smoothing **matched to its own second
  coordinate**, which turns the truncated sum into a sum over cells with three independent dyadic
  windows `idx1 (Mdy i) × idxM (Mdy j) × idxM (Mdy k)`.  No comparison of two lattices is needed,
  so no equidistribution input is required (the single-box strict factor-two box of
  `Prop72RelaxedStatement` would need one; see `NOTES_prop72_relaxed_reduction.md`).
* `Gen.S30g_le_cell` — the §10 pipeline run per cell (two Cauchy–Schwarz steps
  `Gen.S30g_le_cauchy`, `Gen.S32g_le_cauchy`, the two recognitions `Gen.S33g_le_affine`,
  `Gen.S34g_le_affine` of the `a₁`/`a₂` factors as `affineSum` integrals, then GM 9.1): with
  `Mbig = Mdy j`, `S30g ≤ C N^ε (Mbig³|W|^{3/2} + Mbig²|W|^{1/2} E(W)^{1/2})`.
* `Gen.s3_of_cellSum_of` — the final assembly: `Spart 3 = TRUNC + O(N^{-20})`
  (`s3_tail_noclash`), `TRUNC ≤ C N^δ · cellSum + …`, each cell bounded as above, and the geometric
  bookkeeping of the `O(log N)` cells.
-/

namespace Work.GM.S3

/-- GM §§7, 8, 10 (Props 7.1, 7.2, Lemmas 8.2–8.4, Prop 10.1), assuming GM Prop 9.1;
see `Submission/GM/Interfaces.lean`. -/
theorem s3_of_affine (hAff : Submission.GM.AffineStatement) : Submission.GM.S3Statement :=
  Work.GM.S3.Gen.s3_of_cellSum_of hAff Work.GM.S3.lemma84_relaxed
    (Work.GM.S3.Gen.S30g_le_cell hAff Work.GM.S3.lemma84_relaxed)
    Work.GM.S3.Gen.S3_le_cellSum

end Work.GM.S3
