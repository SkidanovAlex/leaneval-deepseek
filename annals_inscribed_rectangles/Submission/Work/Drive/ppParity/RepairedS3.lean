import Submission.Work.Drive.ppParity.StripDefs
import Submission.Work.Drive.ppParity.piece_data_pp_strip
import Submission.Work.Drive.ppParity.exists_ppReg_shift_strip_of_pieces_fixed

/-!
# **The repaired S3 — `Work.Drive.exists_ppReg_shift_strip`**

The capstone of the collar repair (`Submission/Work/Drive/PPPARITY_COLLAR_DEFECT.md`): the intrinsic
pair Sard in the form that is *consistent* and *usable in the intended regime*, i.e. with

* `hwne` restricted to the **active strip** `δ < ftS · < 1 - δ` (the weight can, and must, vanish on
  the closed collar `ftS · ≤ δ`, `1 - δ ≤ ftS ·`, where the perturbation is inactive),
* **closed** collars `s ≤ δ → w s = 0`, `1 - δ ≤ s → w s = 0`,
* `hregBase` at the *base* meets in the closed collar (the honesty hypothesis), and
* the same covering condition `hKcover` on the closed slab of the box.

It is proved by instantiating the per-piece bundle `Work.Drive.PieceDataStrip` of the repaired
assembly `Work.Drive.ppParity.exists_ppReg_shift_strip_of_pieces_fixed` with the proved restricted
localized pair Sard `Work.Drive.ppParity.piece_data_pp_strip` (whose own proof runs the *relaxed*
Sard `Work.Drive.ppParity.exists_forall_good_face_and_notMem_family_rel` — the one new deep ingredient
of the repair — with the surjectivity input restricted to the active strip, the off-strip regularity
supplied by the relaxed Sard's `hregOff`, and the collar-adjacent layers handled by the proved
`ppIntrinsic.ppRegAt_local` / `PPRegAt_ppShift_of_collarBoundary`).

Compare with `Work.Drive.exists_ppReg_shift` (`ppParity/Assembly.lean`), which is the *strict-collar*
form with the unrestricted `hwne`: its hypotheses are unsatisfiable for `δ ∈ (0, 1/2]`
(`ppParity/CollarDefect.lean`), so the present statement is the one the design can instantiate.
-/

namespace Work.Drive

open scoped Manifold ContDiff Topology
open Manifold Set

noncomputable section

attribute [local instance] Work.Drive.cappingCharted Work.Drive.isManifold_cappingCharted
  Work.Drive.t2Space_cappingSpace Work.Drive.projCharted

/-- **The repaired S3**, in the form of the `Prop` `Work.Drive.ExistsPPRegShiftStrip`. -/
theorem exists_ppReg_shift_strip (Q : ℂ → CappingSpace)
    (E E' : ℝ → EuclideanSpace ℝ (Fin 2) → CappingSpace)
    (V W : EuclideanSpace ℝ (Fin 3) → CappingSpace)
    (Ξ : EuclideanSpace ℝ (Fin 4) → CappingSpace → CappingSpace) (w : ℝ → ℝ) :
    ExistsPPRegShiftStrip Q E E' V W Ξ w := by
  intro hE hE' hV hW hw hΞ K hK δ hδ hwne hKcover hwleft hwright hregBase ε hε
  exact ppParity.exists_ppReg_shift_strip_of_pieces_fixed Ξ hΞ.1 hΞ.2.1 hΞ.2.2 w hw hδ
    hE hE' hV hW K hK hwne hKcover hwleft hwright hregBase
    (fun p p' => ppParity.piece_data_pp_strip Ξ hΞ.2.1 hΞ.1 w hw hδ hE hE' hV hW hwleft hwright
      hregBase p p') ε hε

end

end Work.Drive
