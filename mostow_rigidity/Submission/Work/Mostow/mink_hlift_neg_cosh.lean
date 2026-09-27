import Mathlib
import Submission.Work.Mostow.Hyper

/-!
# The Minkowski pairing of two chart points is `−cosh` of the hyperbolic distance

`Hyper.mink_hlift` gives `⟨hlift u, hlift v⟩ = ⟪u,v⟫ − tpart u * tpart v` and
`hdist u v = arcosh (tpart u * tpart v − ⟪u,v⟫)`, so the claim is
`Real.cosh (Real.arcosh (cc u v)) = cc u v` with `cc u v = tpart u * tpart v − ⟪u,v⟫ ≥ 1`.

The only content is `1 ≤ cc u v`: by Cauchy–Schwarz `⟪u,v⟫ ≤ ‖u‖‖v‖` and
`tpart u * tpart v = √((1+‖u‖²)(1+‖v‖²)) ≥ 1 + ‖u‖‖v‖`, since
`(1+‖u‖²)(1+‖v‖²) − (1+‖u‖‖v‖)² = (‖u‖ − ‖v‖)² ≥ 0`.
-/

namespace Work.Mostow

theorem mink_hlift_neg_cosh {n : ℕ} (u v : Submission.Mostow.E n) :
    Submission.Mostow.Hyper.mink (Submission.Mostow.hlift u) (Submission.Mostow.hlift v)
      = -Real.cosh (Submission.Mostow.hdist u v) := by
  have hcc : (1 : ℝ) ≤
      Submission.Mostow.tpart u * Submission.Mostow.tpart v - inner ℝ u v := by
    have h1 : inner ℝ u v ≤ ‖u‖ * ‖v‖ := real_inner_le_norm u v
    have h2 : 1 + ‖u‖ * ‖v‖ ≤ Submission.Mostow.tpart u * Submission.Mostow.tpart v := by
      have ha : Submission.Mostow.tpart u * Submission.Mostow.tpart v =
          Real.sqrt ((1 + ‖u‖ ^ 2) * (1 + ‖v‖ ^ 2)) := by
        rw [Submission.Mostow.tpart, Submission.Mostow.tpart,
          Real.sqrt_mul (by nlinarith [sq_nonneg ‖u‖])]
      rw [ha]
      apply Real.le_sqrt_of_sq_le
      nlinarith [sq_nonneg (‖u‖ - ‖v‖)]
    linarith
  rw [Submission.Mostow.Hyper.mink_hlift]
  rw [show Submission.Mostow.hdist u v =
      Real.arcosh (Submission.Mostow.tpart u * Submission.Mostow.tpart v - inner ℝ u v)
        from rfl,
    Real.cosh_arcosh hcc]
  ring

end Work.Mostow
