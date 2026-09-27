import Mathlib
import Submission.Work.Drive.endsParity
import Submission.Work.Drive.meet32_bordism_invariance

/-!
# The class-triple count of a triple of class maps of the square

`Work.Drive.classTripleSet P` (`Submission/Work/Drive/endsParity.lean`) is the set of triples of
*class coordinates* of a triple of plane presentations at which the three projective classes agree;
its cardinality is the mod-`2` degree input `n_{-λ}` of the ends clause (Hugelmeyer's "`x³ ≠ 0` in
`H^*(ℝP³; ℤ/2) = ℤ/2[x]/(x⁴)`").

This file isolates the count from the plane presentations, so that the *bordism* invariance of the
mod-`2` triple intersection number (the `3 + 2 + 2` engine
`Work.Drive.even_ncard_meet32_encoded`) can be applied to the class maps alone:

* `Work.Drive.classCount f` — the set of triples of points of the unit square at which the three maps
  `f 0, f 1, f 2 : ℝ² → ℝP³` take the same value;
* `Work.Drive.classTripleSet_eq_classCount` — `classTripleSet P` is `classCount` of the three class
  maps `planeClassMap (P k)`;
* `Work.Drive.mk3t`, `Work.Drive.sliceChain`, `Work.Drive.homotopyChain` — the three-and-two-
  dimensional bookkeeping of a chain of the shape "time is the third parameter", which is what the
  encoding `Work.Drive.encodedChains` (`Submission/Work/Drive/meet32_bordism_invariance.lean`) needs.
-/

namespace Work.Drive

open scoped Manifold ContDiff

noncomputable section

/-- **The class-triple set of a triple of maps of the unit square into `ℝP³`**: the triples of
parameters at which the three maps take the same value. -/
def classCount (f : Fin 3 → EuclideanSpace ℝ (Fin 2) → Projectivization ℝ (Eucl 3)) :
    Set (Fin 3 → EuclideanSpace ℝ (Fin 2)) :=
  {y | (∀ k, y k ∈ Submission.Drive.unitBox 1) ∧ (∀ k, f k (y k) = f 0 (y 0))}

@[simp] lemma mem_classCount {f : Fin 3 → EuclideanSpace ℝ (Fin 2) → Projectivization ℝ (Eucl 3)}
    {y : Fin 3 → EuclideanSpace ℝ (Fin 2)} :
    y ∈ classCount f ↔ (∀ k, y k ∈ Submission.Drive.unitBox 1) ∧
      (∀ k, f k (y k) = f 0 (y 0)) := Iff.rfl

/-- **The class-triple set of a triple of plane presentations is the class-triple set of its class
maps**: no information about the presentations except the three projective classes enters the count. -/
theorem classTripleSet_eq_classCount
    (P : Fin 3 → EuclideanSpace ℝ (Fin 2) → CappingSpace) :
    classTripleSet P = classCount (fun k => planeClassMap (P k)) := rfl

/-- **The point of `ℝ³` with the two surface coordinates of `y` and the time coordinate `t`.**  This
is the coordinate convention of the encoding: the *third* coordinate is the time. -/
def mk3t (y : EuclideanSpace ℝ (Fin 2)) (t : ℝ) : EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 ![y 0, y 1, t]

@[simp] lemma mk3t_zero (y : EuclideanSpace ℝ (Fin 2)) (t : ℝ) : mk3t y t 0 = y 0 := rfl
@[simp] lemma mk3t_one (y : EuclideanSpace ℝ (Fin 2)) (t : ℝ) : mk3t y t 1 = y 1 := rfl
@[simp] lemma mk3t_two (y : EuclideanSpace ℝ (Fin 2)) (t : ℝ) : mk3t y t 2 = t := rfl

/-- **The time-`t` slice of a chain `W : ℝ³ → ℝP³`**, as a map of the square. -/
def sliceChain (W : EuclideanSpace ℝ (Fin 3) → Projectivization ℝ (Eucl 3)) (t : ℝ) :
    EuclideanSpace ℝ (Fin 2) → Projectivization ℝ (Eucl 3) :=
  fun y => W (mk3t y t)

/-- **The chain of a homotopy of class maps**: the time is the third parameter.  At `x 2 = 0` it is
`H (0, ·)` and at `x 2 = 1` it is `H (1, ·)`. -/
def homotopyChain {M : Type*} (H : ℝ × EuclideanSpace ℝ (Fin 2) → M) :
    EuclideanSpace ℝ (Fin 3) → M :=
  fun x => H (x 2, pt2 (x 0) (x 1))

@[simp] lemma sliceChain_eq (W : EuclideanSpace ℝ (Fin 3) → Projectivization ℝ (Eucl 3)) (t : ℝ) :
    sliceChain W t = fun y => W (mk3t y t) := rfl

end

end Work.Drive
