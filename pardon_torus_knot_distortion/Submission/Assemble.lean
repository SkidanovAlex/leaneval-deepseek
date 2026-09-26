import ChallengeDeps
import Submission.Basic
import Submission.Extract
import Submission.Work.Distortion.length_diameter
import Submission.Work.Distortion.length_ge_twice_diam
import Submission.Work.Core.torusMap_eq_iff
import Submission.Work.StandardCurve.injOn_coprime

/-!
# Reduction of the challenge to the "core" statement

The whole mathematical content of Pardon's theorem, in the smooth setting of this
benchmark, is the following *core statement*: it is impossible for a knot in the
isotopy class of the standard `(p,q)`-torus curve to satisfy the distortion bound
  `intrinsicDistance s t / dist (curve s) (curve t) < min p q / 160`
for *all* pairs of distinct parameters.

Everything else --- passing from that statement about distortion ratios to the
statement about the extended-nonnegative-real supremum `distortion K` --- is pure
bookkeeping, done here.

The core statement is what the geometric/topological development
(`Submission/Work/TorusCover`, `Submission/Work/Sweep`,
`Submission/Work/CoreTopology`) is designed to establish:

* the *sweep* (integral geometry) shows that for every ball there is a concentric
  sphere meeting the curve in at most `C * d` points, where `d` is the distortion
  bound, and similarly for a cutting plane;
* the *topological core* shows that a sphere meeting the curve in fewer than
  `I(F,beta) = min p q` points, together with its cutting disk, can be used to
  shrink a ball that contains an essential loop of the torus `F` on which the
  curve lies;
* the *extrinsic systole* (covering space of the parametrised torus) shows that a
  ball containing an essential loop has radius bounded below by a positive
  constant;
* iterating the shrink gives balls of arbitrarily small radius containing
  essential loops, a contradiction.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set
open scoped ENNReal

namespace Submission

/-- **The core statement.**  A knot in the (orientation preserving) ambient
isotopy class of the standard `(p,q)`-torus curve cannot satisfy the distortion
bound with constant `min p q / 160`. -/
def CoreStatement : Prop :=
  ∀ (p q : ℕ) (_hp : 0 < p) (_hq : 0 < q) (_hc : Nat.Coprime p q) (K : Knot)
    (_hclass : ∃ Φ : AmbientIsotopy, ∃ σ : CircleReparam,
      ∀ t, Φ.H 1 (K.curve t) = standardTorusCurve p q (σ.f t)),
    (∀ s ∈ Set.Ico (0 : ℝ) (2 * Real.pi), ∀ t ∈ Set.Ico (0 : ℝ) (2 * Real.pi),
      s ≠ t → distortionRatio K s t < (1 / 160 : ℝ) * (Nat.min p q : ℝ)) → False

/-- **Reduction of the challenge to the core statement.**  If the core statement
holds then every knot in the isotopy class of the standard `(p,q)`-torus curve has
distortion at least `min p q / 160`. -/
theorem theorem_of_core (hcore : CoreStatement) (p q : ℕ) (hp : 0 < p) (hq : 0 < q)
    (hc : Nat.Coprime p q) (K : Knot)
    (hclass : ∃ Φ : AmbientIsotopy, ∃ σ : CircleReparam,
      ∀ t, Φ.H 1 (K.curve t) = standardTorusCurve p q (σ.f t)) :
    (1 / 160 : ℝ≥0∞) * (Nat.min p q : ℝ≥0∞) ≤ distortion K := by
  by_contra hlt
  have hlt0 : distortion K < (1 / 160 : ℝ≥0∞) * (Nat.min p q : ℝ≥0∞) := not_le.mp hlt
  have hlt' : distortion K < ENNReal.ofReal ((1 / 160 : ℝ) * (Nat.min p q : ℝ)) := by
    rwa [coe_160_mul (Nat.min p q)] at hlt0
  refine hcore p q hp hq hc K hclass ?_
  intro s hs t ht hst
  have hmem : ENNReal.ofReal (distortionRatio K s t) ≤ distortion K :=
    le_distortion_of_pair K hs ht hst
  have h2 : ENNReal.ofReal (distortionRatio K s t) <
      ENNReal.ofReal ((1 / 160 : ℝ) * (Nat.min p q : ℝ)) := lt_of_le_of_lt hmem hlt'
  exact (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mp h2

end Submission
