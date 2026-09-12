import Submission.Work.SpliceDeck
import Submission.Work.UncContinuity

open OptimalMoebius Topology Filter
open scoped BigOperators Matrix Topology Metric
set_option autoImplicit false
set_option maxHeartbeats 800000
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-!
# Prop main0 — the `BandFoliation` instance and the T-pattern

Assembling the continuous bend foliation of the band from the spliced
chord family:
* `chord := spliceChord hf ha` (total, all heights),
* `centre := spliceChord_centre`,
* `deck := spliceChord_deck` (LAYER 4, PROVED in `SpliceDeck`),
* `cont_left/right := continuous_spliceA1/B1` (LAYER 3, PROVED in
  `UncContinuity`),
* `preBend := spliceChord_preBend`.

Then `lemmaT_tpattern` (PROVED, `FoliationInterface`) yields the T-pattern:
two distinct centreline heights `y`, `y+δ` (`0 < δ < a`) with perpendicular
image directions and coplanar midpoint displacement.

Build: `lake build Submission.Work.BandFoliationInstance` (rc=0 target).
-/

noncomputable section
namespace Submission

open Submission.PaperBand

/-- **The continuous bend foliation of the band** (Schwartz's Prop
main0): the spliced chord family, with its centre, deck symmetry,
continuous endpoint heights and isometric pre-bends, is a
`BandFoliation`. -/
theorem bandFoliation_exists {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) : Nonempty (BandFoliation a f hf) := by
  refine ⟨?_⟩
  exact
  { chord := spliceChord hf ha
    centre := fun y => spliceChord_centre hf ha y
    deck := fun y => spliceChord_deck hf ha y
    cont_left := by
      show Continuous (fun y : ℝ => ((spliceChord hf ha y).A 1 : ℝ))
      simpa [spliceA1] using continuous_spliceA1 hf ha
    cont_right := by
      show Continuous (fun y : ℝ => ((spliceChord hf ha y).B 1 : ℝ))
      simpa [spliceB1] using continuous_spliceB1 hf ha
    preBend := fun y => spliceChord_preBend hf ha y }

/-- **The T-pattern** (Lemma T of the paper, f-relative form): there are
two distinct centreline heights `y` and `y + δ`, `0 < δ < a`, whose image
leaf directions are perpendicular and whose image midpoints' displacement
is coplanar with them. -/
theorem tpattern_exists {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) :
    ∃ y : ℝ, ∃ δ : ℝ, 0 < δ ∧ δ < a ∧
      (WithLp.ofLp (BandFoliation.imageDir (Classical.choice (bandFoliation_exists hf ha)) y) ⬝ᵥ
         WithLp.ofLp (BandFoliation.imageDir (Classical.choice (bandFoliation_exists hf ha)) (y + δ)) = 0) ∧
      (WithLp.ofLp (BandFoliation.imageMid (Classical.choice (bandFoliation_exists hf ha)) y -
          BandFoliation.imageMid (Classical.choice (bandFoliation_exists hf ha)) (y + δ)) ⬝ᵥ
         (WithLp.ofLp (BandFoliation.imageDir (Classical.choice (bandFoliation_exists hf ha)) y) ⨯₃
           WithLp.ofLp (BandFoliation.imageDir (Classical.choice (bandFoliation_exists hf ha)) (y + δ))) = 0) :=
  lemmaT_tpattern hf ha (Classical.choice (bandFoliation_exists hf ha))

end Submission
