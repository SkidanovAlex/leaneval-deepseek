import Mathlib
import Submission.Work.Drive.N2.orientationFlipDefs

/-!
# Labelled configurations of round circles (the vocabulary of the collar family)

The collar construction of the compact `n = 2` movie draws every connected component of a regular
level set as a *round circle* placed by a label: a centre, a radius and a phase.  This file fixes that
vocabulary:

* `Work.Drive.N2.RoundConfig m` — the labels of `m` round circles (`pos`, `rad > 0`, `phase`);
* `RoundConfig.circle D i t` — the point of the `i`-th circle at parameter `t`
  (`pos i + rad i • roundPic (phase i + 2 π t)`, so the first coordinate of the parameter is
  `phase i` and the circle is travelled once when `t` runs over `[0,1]`);
* `RoundConfig.Disjoint D` — the `m` circles are pairwise disjoint.

The point of the labelling is that the *agreement* rows of `Work.Drive.N2.levelSeparatingMap_of_blocks`
only compare neighbouring blocks: the labels `(λ_i, ϑ_i)` of a band are transported to the next band
through the collar at the critical value between them, and the collar's isotopy is the path of
configurations produced by `Work.Drive.N2.exists_roundConfig_path` (the placement moves: raise, slide,
descend, together with the radius and phase interpolation).
-/

namespace Work.Drive.N2

open scoped Manifold ContDiff Topology

noncomputable section

/-- The labels of `m` round circles in `ℝ³`: centre, positive radius and phase. -/
structure RoundConfig (m : ℕ) where
  /-- the centre of each circle -/
  pos : Fin m → EuclideanSpace ℝ (Fin 3)
  /-- the radius of each circle -/
  rad : Fin m → ℝ
  /-- the radii are positive -/
  hrad : ∀ i : Fin m, 0 < rad i
  /-- the phase of each circle: the parameter of the first coordinate axis point -/
  phase : Fin m → ℝ

namespace RoundConfig

variable {m : ℕ}

/-- The point of the `i`-th circle at parameter `t`: `pos i + rad i • roundPic (phase i + 2 π t)`. -/
def circle (D : RoundConfig m) (i : Fin m) (t : ℝ) :
    EuclideanSpace ℝ (Fin 3) :=
  D.pos i + D.rad i • roundPic (D.phase i + 2 * Real.pi * t)

/-- The `m` circles of a configuration are pairwise disjoint. -/
def Disjoint (D : RoundConfig m) : Prop :=
  ∀ i j : Fin m, i ≠ j → ∀ s t : ℝ, D.circle i s ≠ D.circle j t

end RoundConfig

end

end Work.Drive.N2
