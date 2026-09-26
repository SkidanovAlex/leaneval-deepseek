import Mathlib
import Submission.Work.Drive.Mono.BoxGen
import Submission.Work.Drive.Mono.JunctionGenC

/-!
# The box genericity `BoxGenE` of the junction route, with a generic centre

`Work.Drive.Mono.BoxGen` is the pointwise general position of the box sphere at the level, and
`Work.Drive.Mono.ae_boxGen` proves it for almost every level.  The junction route needs more:

* `Work.Drive.Mono.VertEdgeFinite` — the surface meets the **vertical** edge lines of the box
  (pinned `σ 0`- and `σ 1`-coordinates, direction `e_{σ 2}`) in finitely many points.  Its role is to
  make `Work.Drive.Mono.EdgeFree` true: the horizontal edges are at height `± boxSide 2 * s`, hence
  at distance at least `s − ε r` from the cutting plane, while the (finitely many) heights of the
  vertical edge points are avoidable by `u` (`Mono/NOTES_LEAD_junctionGen.md` §2, §0.5).
* `Work.Drive.Mono.FaceCrossReg` — the face planes `i = 0, 1` cross the flat plane
  `{y (σ 2) = c (σ 2) + u}` transversally on the surface (a pair Sard condition on `(s, u)`);
* `Work.Drive.Mono.FaceNoBend` — a *vertical-tangent* crossing of the box trace `Γ` with that plane
  is a double zero of the vertical-tangent determinant (`Mono/NOTES_LEAD_junctionGen.md` §3).  This
  is what makes clause (a) of the junction bundle true at almost every level `u` (the `CFree` clause
  of the earlier design was wrong: a bent vertical crossing forces a critical point of `ℓ` on `Γ`
  inside the slab).
* `Work.Drive.Mono.BoxGenE` — the conjunction of `BoxGen`, `VertEdgeFinite` and
  `FaceCrossReg ∧ FaceNoBend` for almost every `u`.

The generic-centre device is `Work.Drive.Mono.diagVec`: shifting the centre along the diagonal
`c' = c + τ • diagVec` moves the vertical edge *rays* of the box, so that the bad configurations (a
flat `C^∞` patch of the surface in the vertical plane through a vertical edge, `NOTES_H381_edgeArc_OBSTRUCTION.md` §5)
become a null set of `τ`.
-/

open LeanEval.KnotTheory.PardonDistortion
open MeasureTheory Set
open scoped ENNReal

namespace Work.Drive.Mono

noncomputable section

/-- The diagonal vector of `ℝ³` (all coordinates `1`), used for the generic shift of the box
centre. -/
def diagVec : R3 := ∑ i : Fin 3, EuclideanSpace.single i (1 : ℝ)

/-- **The vertical edge locus is finite**: the surface meets the box edge lines of direction
`e_{σ 2}` (pinned `σ 0`- and `σ 1`-coordinates) in finitely many points. -/
def VertEdgeFinite (ψ : Submission.Diffeo) (c : R3) (σ : Equiv.Perm (Fin 3)) (s : ℝ) : Prop :=
  {z : R3 | z ∈ (Work.Drive.EpsSphere.torusOf ψ).carrier ∧
    |z (σ 0) - c (σ 0)| = Submission.boxSide 0 * s ∧
    |z (σ 1) - c (σ 1)| = Submission.boxSide 1 * s}.Finite

/-- **Pair regularity of the face crossing**: the face planes `i = 0, 1` cross the flat plane
`{y (σ 2) = c (σ 2) + u}` transversally on the surface. -/
def FaceCrossReg (ψ : Submission.Diffeo) (c : R3) (σ : Equiv.Perm (Fin 3)) (s u : ℝ) : Prop :=
  ∀ i : Fin 3, i ≠ 2 → ∀ ε : ℝ, (ε = 1 ∨ ε = -1) → ∀ p : ℝ × ℝ,
    (Work.BoxShrink.Pinch.par ψ p) (σ i) = c (σ i) + ε * Submission.boxSide i * s →
    (Work.BoxShrink.Pinch.par ψ p) (σ 2) = c (σ 2) + u →
    (fderiv ℝ (fun q : ℝ × ℝ => ((Work.BoxShrink.Pinch.par ψ q) (σ i),
        (Work.BoxShrink.Pinch.par ψ q) (σ 2))) p).IsInvertible

/-- The determinant `det [d (y_{σ i} ∘ par), d (y_{σ j} ∘ par)]`: it vanishes exactly where the face
curve `Γ_i` has a vertical tangent (a tangent direction in the `σ 2`-coordinate). -/
def faceVertDet (ψ : Submission.Diffeo) (σ : Equiv.Perm (Fin 3)) (i j : Fin 3) (p : ℝ × ℝ) : ℝ :=
  fderiv ℝ (fun q => (Work.BoxShrink.Pinch.par ψ q) (σ i)) p (1, 0) *
      fderiv ℝ (fun q => (Work.BoxShrink.Pinch.par ψ q) (σ j)) p (0, 1) -
    fderiv ℝ (fun q => (Work.BoxShrink.Pinch.par ψ q) (σ i)) p (0, 1) *
      fderiv ℝ (fun q => (Work.BoxShrink.Pinch.par ψ q) (σ j)) p (1, 0)

/-- The tangent field of the face curve: the Hamiltonian field of `y_{σ i} ∘ par`. -/
def faceTangent (ψ : Submission.Diffeo) (σ : Equiv.Perm (Fin 3)) (i : Fin 3) (p : ℝ × ℝ) : ℝ × ℝ :=
  (-(fderiv ℝ (fun q => (Work.BoxShrink.Pinch.par ψ q) (σ i)) p (0, 1)),
    fderiv ℝ (fun q => (Work.BoxShrink.Pinch.par ψ q) (σ i)) p (1, 0))

/-- **No bend**: a vertical-tangent crossing of the box trace `Γ` with the flat plane
`{y (σ 2) = c (σ 2) + u}` is a *double* zero of the vertical-tangent determinant — i.e. the trace
crosses the plane with curvature, not as a straight vertical line. -/
def FaceNoBend (ψ : Submission.Diffeo) (c : R3) (σ : Equiv.Perm (Fin 3)) (s u : ℝ) : Prop :=
  ∀ i j : Fin 3, i ≠ 2 → j ≠ 2 → i ≠ j → ∀ ε : ℝ, (ε = 1 ∨ ε = -1) → ∀ p : ℝ × ℝ,
    (Work.BoxShrink.Pinch.par ψ p) (σ i) = c (σ i) + ε * Submission.boxSide i * s →
    (Work.BoxShrink.Pinch.par ψ p) (σ 2) = c (σ 2) + u →
    faceVertDet ψ σ i j p = 0 → fderiv ℝ (faceVertDet ψ σ i j) p (faceTangent ψ σ i p) = 0

/-- **Triple-point transversality** (project lead, message of 2026-09-26 08:5x; see
`Submission/Work/Drive/Final/NOTES_tripleGatesCorrected_REFUTED.md`): at every triple point — a point
of the surface on a box *face* `{y (σ i) = c (σ i) + ε boxSide i * s}` **and** on a slab face
`{⟪v,·⟫ = a + η h}` — the two face curves meet transversally, i.e. the pair
`((y (σ i)) ∘ par, ⟪v,·⟫ ∘ par)` has invertible derivative there.

This is the missing hypothesis of `Work.Drive.Final.tripleGatesCorrected` (a flat `C^∞` oscillation
of the slab face against a box face makes infinitely many notches).  It is a.e. in `h` at fixed
`(s, u, v)`: the pair is `C^∞` and `2π`-periodic, its critical values are null
(`Work.Smooth.BoxGeneric.Sard.criticalValues_null_of_contDiffTwo_periodic_pair`), and the pinned point
`(c (σ i) + ε boxSide i * s, ⟪v,c⟫ + u + η h)` is affine in `h` with slope `η ≠ 0`, so for a.e. `h`
it is not a critical value. -/
def SlabBoxCrossReg (ψ : Submission.Diffeo) (c : R3) (σ : Equiv.Perm (Fin 3)) (s : ℝ) (v : R3)
    (a h : ℝ) : Prop :=
  ∀ i : Fin 3, i ≠ 2 → ∀ ε : ℝ, (ε = 1 ∨ ε = -1) → ∀ η : ℝ, (η = 1 ∨ η = -1) →
    ∀ p : ℝ × ℝ,
      (Work.BoxShrink.Pinch.par ψ p) (σ i) = c (σ i) + ε * Submission.boxSide i * s →
      inner ℝ v (Work.BoxShrink.Pinch.par ψ p) = a + η * h →
      (fderiv ℝ (fun q : ℝ × ℝ => ((Work.BoxShrink.Pinch.par ψ q) (σ i),
          inner ℝ v (Work.BoxShrink.Pinch.par ψ q))) p).IsInvertible

/-- **The box genericity of the junction route**: `BoxGen`, the finiteness of the vertical edge
locus, and, for almost every cutting level `u`, the pair regularity of the face crossing and the
absence of a bend at a vertical-tangent crossing. -/
def BoxGenE (ψ : Submission.Diffeo) (c : R3) (σ : Equiv.Perm (Fin 3)) (s : ℝ) : Prop :=
  BoxGen ψ c σ s ∧ VertEdgeFinite ψ c σ s ∧
    ∀ᵐ u ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
      FaceCrossReg ψ c σ s u ∧ FaceNoBend ψ c σ s u

end

end Work.Drive.Mono
