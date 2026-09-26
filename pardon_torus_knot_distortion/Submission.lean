import ChallengeDeps
import Submission.Helpers
import Submission.Basic
import Submission.Work.Core.Torus
import Submission.Extract
import Submission.Work.Distortion.length_diameter
import Submission.Work.Distortion.length_ge_twice_diam
import Submission.Work.Core.torusMap_eq_iff
import Submission.Work.StandardCurve.injOn_coprime
import Submission.Work.StandardCurve.distortion_bound
import Submission.Work.Geometry.box_halving
import Submission.Work.Geometry.diameter_systole
import Submission.Work.StandardCurve.knot_instance
import Submission.Work.Distortion.reparam_invariance
import Submission.Work.Distortion.one_le_distortion
import Submission.RatioBound
import Submission.CoreSetup
import Submission.Work.CoreSetup.essential_diam_lower_bound
import Submission.Work.CoreTopology.All
import Submission.Box
import Submission.Shrink
import Submission.Assemble
import Submission.Iterate
import Submission.SmallCase
import Submission.Work.BoxShrink.ledger
import Submission.Work.Drive.Mono.pardon_unconditional_mono

/-!
# Pardon's lower bound for the distortion of torus knots

The challenge (`Submission.pardon_torus_knot_distortion`) is Pardon's theorem in the smooth
setting: for coprime `p, q > 0`, every smooth knot in the isotopy class of the standard
`(p,q)`-torus curve has distortion at least `min(p,q)/160`.

The proof is assembled in three layers:

* `Submission.theorem_of_core` (`Submission/Assemble.lean`) reduces the challenge to
  `Submission.CoreStatement`, the statement that no knot in the class can satisfy the *strict*
  distortion bound `distortionRatio < min p q / 160` for all pairs of distinct parameters;
* `Submission.CoreStatement_of_boxShrink` (`Submission/Shrink.lean`) reduces `CoreStatement` to
  the single geometric input `Submission.BoxShrinkStatement` --- Pardon's "one sweep and one
  double bubble shrinks a box": a box whose intersection with the embedded torus contains an
  essential curve can be replaced, under the distortion hypothesis, by a box of size
  `shrinkFactor * r` (`shrinkFactor = 2^{-1/3}(1+ε) + ε/2 < 1`, `ε = 2/13`) with the same
  property.  Everything else in that reduction is proved: the extrinsic systole
  (`systole_of_psiHomeo`), the existence of a large starting box (`exists_start_of_psiHomeo`)
  and the combinatorial iteration (`Submission.shrink_contradiction`);
* the geometric input itself is Pardon's argument (Annals 174 (2011), §2--3): the integral
  geometry of the sweep of boxes, Pardon's `mustbeinessential` (the innermost-disc obstruction)
  and the `spherefamily`/`doublebubble` persistence along the `2`-surgery family, together with
  the elementary geometry of the halving (`Submission.halfBox_upper_subset`,
  `Submission.halfBox_lower_subset`).
-/

open LeanEval.KnotTheory.PardonDistortion
open Set
open scoped ENNReal

namespace Submission

theorem pardon_torus_knot_distortion (p q : ℕ) (hp : 0 < p) (hq : 0 < q) (hc : Nat.Coprime p q)
    (K : Knot)
    (hclass : ∃ Φ : AmbientIsotopy, ∃ σ : CircleReparam,
      ∀ t, Φ.H 1 (K.curve t) = standardTorusCurve p q (σ.f t)) :
    (1 / 160 : ℝ≥0∞) * (Nat.min p q : ℝ≥0∞) ≤ distortion K := by
  exact Work.Drive.Mono.pardon_unconditional_mono p q hp hq hc K hclass

end Submission
