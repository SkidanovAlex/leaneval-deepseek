/-
  WilE6 (area E6): the assembly of the closure half of `E6_fiber_closure`.

  * `exists_cubeSaturated` (delegated, `Submission.Work.WilE6.exists_cubeSaturated`) re-presents
    a `SemiPf` so that every basic set already lies inside the cube — this is needed because
    `cl(cubeC q ∩ S) ≠ cubeC q ∩ cl(S)` in general.
  * `E6_closure_cubeSaturated` (delegated, `Submission.Work.WilE6.E6_closure_cubeSaturated`) is
    the closure half for a cube-saturated presentation, from the frozen E3b and E4.

  The composition below is the closure half of the frozen `E6_fiber_closure`; once the two parts
  are available it specialises to

      theorem E6_closure_proved (hE3b : ...) (hE4 : ...) (F : ℕ) : ∃ a b, ∀ p q (X : SemiPf (p+q)),
        X.fmt ≤ F → ∃ Y : SemiPf (p + q), Y.fmt ≤ a ∧ Y.deg ≤ b.eval X.deg ∧
          Y.set = fiberClosure X.set

  with the two leading hypotheses copied verbatim from
  `Submission/Work/Wilkies/E/Spec.lean` (`E3_taylor_closure`, `E4_sa_fiber_closure`).
  The frontier conjunct `Y'.set = fiberClosure X.set \ X.set` is NOT covered here; see
  `NOTES.md` for the obstruction (it needs an effective complement / cell count, which is in
  neither E3b nor E4).
-/
import Submission.Work.WilE6.Base
import Submission.Work.WilE6.CritSA
import Submission.Work.WilE6.Closure

set_option autoImplicit false
noncomputable section
open Classical Topology
namespace Work.WilE6
open WilkiesConjecture WilkiesDesign WilkiesDesign.E

/-- `Polynomial.eval` at a natural number is monotone for polynomials with coefficients in `ℕ`.
This is what lets the two polynomial bounds (cube saturation, then closure) be composed. -/
theorem polynomial_eval_mono (p : Polynomial ℕ) : Monotone fun n : ℕ => p.eval n := by
  intro a b hab
  induction p using Polynomial.induction_on' with
  | monomial n c =>
      simp only [Polynomial.eval_monomial]
      exact Nat.mul_le_mul_left c (Nat.pow_le_pow_left hab n)
  | add p q hp hq => simpa [Polynomial.eval_add] using add_le_add hp hq

/-- **The closure half of `E6_fiber_closure`.**  From the cube-saturation step and the
cube-saturated closure step (both per format `F`) we get the closure half of the frozen
statement: a `SemiPf` `Y` with `Y.set = fiberClosure X.set`, format and degree bounded
as required. -/
theorem E6_closure_proved_of_parts (F : ℕ)
    (hsat : ∃ b : Polynomial ℕ, ∀ (k : ℕ) (X : SemiPf k), X.fmt ≤ F →
      ∃ X' : SemiPf k, X'.fmt ≤ F ∧ X'.deg ≤ b.eval X.deg ∧ X'.set = X.set ∧
        (∀ B ∈ X'.basics, ∀ z : Fin k → ℝ, B.holds X'.c z → z ∈ cubeC k))
    (hclos : ∃ (a : ℕ) (b : Polynomial ℕ), ∀ (p q : ℕ) (X : SemiPf (p + q)), X.fmt ≤ F →
      (∀ B ∈ X.basics, ∀ z : Fin (p + q) → ℝ, B.holds X.c z → z ∈ cubeC (p + q)) →
      ∃ Y : SemiPf (p + q), Y.fmt ≤ a ∧ Y.deg ≤ b.eval X.deg ∧ Y.set = fiberClosure X.set) :
    ∃ (a : ℕ) (b : Polynomial ℕ), ∀ (p q : ℕ) (X : SemiPf (p + q)), X.fmt ≤ F →
      ∃ Y : SemiPf (p + q), Y.fmt ≤ a ∧ Y.deg ≤ b.eval X.deg ∧ Y.set = fiberClosure X.set := by
  obtain ⟨b₁, hb₁⟩ := hsat
  obtain ⟨a₂, b₂, hb₂⟩ := hclos
  refine ⟨a₂, b₂.comp b₁, fun p q X hfmt => ?_⟩
  obtain ⟨X', hX'fmt, hX'deg, hX'set, hX'sat⟩ := hb₁ (p + q) X hfmt
  obtain ⟨Y, hYfmt, hYdeg, hYset⟩ := hb₂ p q X' hX'fmt hX'sat
  refine ⟨Y, hYfmt, ?_, ?_⟩
  · have hcomp : b₂.eval (b₁.eval X.deg) = (b₂.comp b₁).eval X.deg := by
      rw [Polynomial.eval_comp]
    calc Y.deg ≤ b₂.eval X'.deg := hYdeg
      _ ≤ b₂.eval (b₁.eval X.deg) := polynomial_eval_mono b₂ hX'deg
      _ = (b₂.comp b₁).eval X.deg := hcomp
  · rw [hYset, hX'set]

end Work.WilE6
