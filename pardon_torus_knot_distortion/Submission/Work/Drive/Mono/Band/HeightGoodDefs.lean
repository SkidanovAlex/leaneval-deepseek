import Mathlib
import Submission.Work.Drive.Mono.BoxWidth
import Submission.Work.Drive.EpsForm.goodHeight_exists
import Submission.Work.Drive.Generic.ae_height_morse

/-!
# "Good" height directions of the parametrised torus

For `n : R3`, write `heightIn ψ n = fun q => ⟪n, par ψ q⟫` for the height in the direction `n`, read
in the parameter plane of the parametrisation `par ψ (x,y) = ψ (torusMap x y)`.

`Work.Drive.Mono.Band.HeightGood ψ n` says that this height is

* **Morse** — the Hessian is injective at every critical point, and
* **injectively valued** — two critical points with the same value have the same image on the
  surface (i.e. differ by a period of the parametrisation).

These are the first two clauses of Pardon's tilt genericity without the box restriction, so they
hold on *every* parameter, and they are the form in which `Work.Drive.EpsForm.goodHeight_exists`
produces them.
-/

namespace Work.Drive.Mono.Band

open LeanEval.KnotTheory.PardonDistortion

noncomputable section

/-- The height in direction `n` of the parametrised surface, read in the parameter plane. -/
abbrev heightIn (ψ : Submission.Diffeo) (n : R3) : ℝ × ℝ → ℝ :=
  fun q => inner ℝ n (Work.BoxShrink.Pinch.par ψ q)

/-- **The good directions.**  The height in the direction `n` is Morse and has injectively valued
critical points (modulo the periods of the parametrisation). -/
def HeightGood (ψ : Submission.Diffeo) (n : R3) : Prop :=
  (∀ p : ℝ × ℝ, fderiv ℝ (heightIn ψ n) p = 0 →
    Function.Injective (fderiv ℝ (fderiv ℝ (heightIn ψ n)) p)) ∧
  (∀ p p' : ℝ × ℝ, fderiv ℝ (heightIn ψ n) p = 0 → fderiv ℝ (heightIn ψ n) p' = 0 →
    heightIn ψ n p = heightIn ψ n p' →
    Work.BoxShrink.Pinch.par ψ p = Work.BoxShrink.Pinch.par ψ p')

theorem heightIn_eq_heightOf (ψ : Submission.Diffeo) (n : R3) :
    heightIn ψ n = Work.Drive.EpsForm.heightOf ψ n := rfl

theorem heightIn_contDiff_two (ψ : Submission.Diffeo) (n : R3) :
    ContDiff ℝ 2 (heightIn ψ n) :=
  Work.Drive.EpsForm.heightOf_contDiff_two ψ n

theorem heightIn_contDiff (ψ : Submission.Diffeo) (n : R3) :
    ContDiff ℝ (⊤ : ℕ∞) (heightIn ψ n) :=
  Work.Drive.EpsForm.heightOf_contDiff ψ n

end

end Work.Drive.Mono.Band
