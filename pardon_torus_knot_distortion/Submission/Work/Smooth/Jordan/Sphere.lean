import Submission.Work.Smooth.Jordan.Family

/-!
# Schoenflies on a surface: two complementary discs bounded by a curve

For a simple closed curve `c` on a set `A ⊆ ℝ³` (in the application, the round `2`-sphere
`Metric.sphere (0 : R3) 1` or the boundary `{y | Submission.boxNorm c σ y = s}` of Pardon's box),
the classical Jordan–Schoenflies theorem on the `2`-sphere states that `A` is the union of two
closed discs whose intersection is exactly the curve: `SphereSchoenflies A c`.

This is the form in which the separation theory of a sphere is consumed by the innermost-disc
arguments (each curve of `S ∩ F` bounds a disc *inside* `S`), and it is transported along
homeomorphisms of `ℝ³` (`SphereSchoenflies.map_homeomorph`), which is how the theorem for the round
sphere gives it for the box boundary along the explicit homeomorphism
`Work.Topology.SphereSlicing.homeomorph_BoxSphere`.
-/

open Set
open Classical
open LeanEval.KnotTheory.PardonDistortion

namespace Work.Smooth.Jordan

noncomputable section

/-- **Jordan–Schoenflies on a set `A ⊆ ℝ³`**: the simple closed curve `c` in `A` is the common
boundary of two embedded closed discs in `A` which cover `A` and meet exactly in the curve. -/
structure SphereSchoenflies (A : Set R3) (c : ℝ → R3) where
  /-- the curve is a simple closed curve in `A` -/
  simple : IsSimpleClosedCurveOn A c
  /-- one of the two discs -/
  e : C(Disc, R3)
  /-- the other one -/
  e' : C(Disc, R3)
  /-- the first disc is embedded -/
  inj : Function.Injective e
  /-- the second disc is embedded -/
  inj' : Function.Injective e'
  /-- the boundary of the first disc is the curve -/
  boundary : ∀ θ : ℝ, e (circlePoint θ) = c θ
  /-- the boundary of the second disc is the curve -/
  boundary' : ∀ θ : ℝ, e' (circlePoint θ) = c θ
  /-- the first disc lies in `A` -/
  mem : ∀ z : Disc, e z ∈ A
  /-- the second disc lies in `A` -/
  mem' : ∀ z : Disc, e' z ∈ A
  /-- the two discs cover `A` -/
  cover : Set.range e ∪ Set.range e' = A
  /-- they meet exactly in the curve -/
  meet : Set.range e ∩ Set.range e' = Set.range c

namespace SphereSchoenflies

variable {A : Set R3} {c : ℝ → R3}

/-- The first disc bounds the curve. -/
theorem isSpanningDisc_left (h : SphereSchoenflies A c) : IsSpanningDiscOn A c h.e :=
  ⟨h.inj, h.boundary, h.mem⟩

/-- The second disc bounds the curve. -/
theorem isSpanningDisc_right (h : SphereSchoenflies A c) : IsSpanningDiscOn A c h.e' :=
  ⟨h.inj', h.boundary', h.mem'⟩

/-- The curve bounds an embedded disc in `A`. -/
theorem boundsDisc (h : SphereSchoenflies A c) :
    ∃ e : C(Disc, R3), IsSpanningDiscOn A c e :=
  ⟨h.e, h.isSpanningDisc_left⟩

end SphereSchoenflies

/-- **Schoenflies on a set `A ⊆ ℝ³`**: every simple closed curve in `A` bounds two complementary
embedded discs.  This is the classical input of the sphere side of the chapter. -/
def SchoenfliesOnInput (A : Set R3) : Prop :=
  ∀ c : ℝ → R3, IsSimpleClosedCurveOn A c → Nonempty (SphereSchoenflies A c)

/-- The round unit `2`-sphere `S² ⊆ ℝ³`. -/
def RoundSphere : Set R3 := Metric.sphere (0 : R3) 1

@[simp] theorem mem_RoundSphere {x : R3} : x ∈ RoundSphere ↔ ‖x‖ = 1 := by
  simp [RoundSphere]

end

end Work.Smooth.Jordan
