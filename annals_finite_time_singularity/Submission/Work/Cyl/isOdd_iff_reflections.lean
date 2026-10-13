import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.Cyl.Coords
import Submission.Work.Cyl.Frame
import Submission.Work.Cyl.Basic
import Submission.Work.Cyl.FieldDeriv

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Cyl

/-!
# `IsOdd` as three reflection identities

`FiniteTimeSingularity.IsOdd u` is stated componentwise: for each coordinate `i`, the `i`-th
component of `u` is odd in coordinate `i` and even in the other two coordinates.  Since a vector
of `ℝ³` is exactly its three coordinates, this is the same as saying that `u` intertwines each
coordinate reflection of the *argument* with the corresponding reflection (sign flip) of the
*value*:

* `refl0`/`flip0` — reflection in the first coordinate,
* `refl1`/`flip1` — reflection in the second coordinate,
* `reflZ`/`flipZ` — reflection in the axial coordinate.

The proof is purely componentwise: writing `x = !₂[x₀, x₁, x₂]` turns each of the reflection
identities into the corresponding parity statement about the slices `t ↦ u !₂[t, x₁, x₂]`, and
conversely.
-/

/-- Every vector of `ℝ³` is the vector of its three coordinates.  This is the only bookkeeping
needed to compare the slice form of `IsOdd` with the reflection form. -/
private lemma vec3_eta (x : R3) : (!₂[x 0, x 1, x 2] : R3) = x := by
  ext i; fin_cases i <;> simp

theorem isOdd_iff_reflections (u : Work.Cyl.R3 → Work.Cyl.R3) :
    FiniteTimeSingularity.IsOdd u ↔
      (∀ x, u (Work.Cyl.refl0 x) = Work.Cyl.flip0 (u x)) ∧
        (∀ x, u (Work.Cyl.refl1 x) = Work.Cyl.flip1 (u x)) ∧
          (∀ x, u (Work.Cyl.reflZ x) = Work.Cyl.flipZ (u x)) := by
  constructor
  · -- **Forward.**  Read the reflection identities off the coordinatewise parity hypotheses.
    intro h
    refine ⟨?_, ?_, ?_⟩
    · intro x
      ext i
      fin_cases i <;> simp only [refl0, flip0]
      · have h1 : (u !₂[-x 0, x 1, x 2]) 0 = -(u !₂[x 0, x 1, x 2]) 0 :=
          (h.1 (x 1) (x 2)).1 (x 0)
        rw [vec3_eta x] at h1; simpa using h1
      · have h1 : (u !₂[-x 0, x 1, x 2]) 1 = (u !₂[x 0, x 1, x 2]) 1 :=
          (h.1 (x 1) (x 2)).2.1 (x 0)
        rw [vec3_eta x] at h1; simpa using h1
      · have h1 : (u !₂[-x 0, x 1, x 2]) 2 = (u !₂[x 0, x 1, x 2]) 2 :=
          (h.1 (x 1) (x 2)).2.2 (x 0)
        rw [vec3_eta x] at h1; simpa using h1
    · intro x
      ext i
      fin_cases i <;> simp only [refl1, flip1]
      · have h1 : (u !₂[x 0, -x 1, x 2]) 0 = (u !₂[x 0, x 1, x 2]) 0 :=
          (h.2.1 (x 0) (x 2)).1 (x 1)
        rw [vec3_eta x] at h1; simpa using h1
      · have h1 : (u !₂[x 0, -x 1, x 2]) 1 = -(u !₂[x 0, x 1, x 2]) 1 :=
          (h.2.1 (x 0) (x 2)).2.1 (x 1)
        rw [vec3_eta x] at h1; simpa using h1
      · have h1 : (u !₂[x 0, -x 1, x 2]) 2 = (u !₂[x 0, x 1, x 2]) 2 :=
          (h.2.1 (x 0) (x 2)).2.2 (x 1)
        rw [vec3_eta x] at h1; simpa using h1
    · intro x
      ext i
      fin_cases i <;> simp only [reflZ, flipZ]
      · have h1 : (u !₂[x 0, x 1, -x 2]) 0 = (u !₂[x 0, x 1, x 2]) 0 :=
          (h.2.2 (x 0) (x 1)).1 (x 2)
        rw [vec3_eta x] at h1; simpa using h1
      · have h1 : (u !₂[x 0, x 1, -x 2]) 1 = (u !₂[x 0, x 1, x 2]) 1 :=
          (h.2.2 (x 0) (x 1)).2.1 (x 2)
        rw [vec3_eta x] at h1; simpa using h1
      · have h1 : (u !₂[x 0, x 1, -x 2]) 2 = -(u !₂[x 0, x 1, x 2]) 2 :=
          (h.2.2 (x 0) (x 1)).2.2 (x 2)
        rw [vec3_eta x] at h1; simpa using h1
  · -- **Backward.**  Assemble the coordinatewise parity from the three reflection identities.
    rintro ⟨hr0, hr1, hrz⟩
    refine ⟨?_, ?_, ?_⟩
    · intro x₁ x₂
      refine ⟨?_, ?_, ?_⟩
      · intro t
        have h := congrArg (fun v : R3 => v 0) (hr0 (!₂[t, x₁, x₂]))
        simpa [refl0, flip0] using h
      · intro t
        have h := congrArg (fun v : R3 => v 1) (hr0 (!₂[t, x₁, x₂]))
        simpa [refl0, flip0] using h
      · intro t
        have h := congrArg (fun v : R3 => v 2) (hr0 (!₂[t, x₁, x₂]))
        simpa [refl0, flip0] using h
    · intro x₀ x₂
      refine ⟨?_, ?_, ?_⟩
      · intro t
        have h := congrArg (fun v : R3 => v 0) (hr1 (!₂[x₀, t, x₂]))
        simpa [refl1, flip1] using h
      · intro t
        have h := congrArg (fun v : R3 => v 1) (hr1 (!₂[x₀, t, x₂]))
        simpa [refl1, flip1] using h
      · intro t
        have h := congrArg (fun v : R3 => v 2) (hr1 (!₂[x₀, t, x₂]))
        simpa [refl1, flip1] using h
    · intro x₀ x₁
      refine ⟨?_, ?_, ?_⟩
      · intro t
        have h := congrArg (fun v : R3 => v 0) (hrz (!₂[x₀, x₁, t]))
        simpa [reflZ, flipZ] using h
      · intro t
        have h := congrArg (fun v : R3 => v 1) (hrz (!₂[x₀, x₁, t]))
        simpa [reflZ, flipZ] using h
      · intro t
        have h := congrArg (fun v : R3 => v 2) (hrz (!₂[x₀, x₁, t]))
        simpa [reflZ, flipZ] using h

end Work.Cyl
