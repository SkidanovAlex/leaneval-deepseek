import Mathlib
import Submission.Work.WilE9.Psi.psi_psig_algebra
import Submission.Work.WilE9.Psi.psig_pos

namespace Work.WilE9.Sharp

/-- **Uniqueness of the ψ-branch on the circle.**  The point `(ψ x, psig x)` lies on the unit
circle, and any pair `(y, w)` with `w > 0`, `y = x·w` and `y² + w² = 1` is *that* point.  Indeed
`y = x·w` forces `w²(1 + x²) = 1`, and `psig x² (1 + x²) = 1` by `psi_psig_algebra`, so
`w² = psig x²`; positivity of both then gives `w = psig x`, and `y = x·w = x·psig x = psi x`. -/
theorem circle_branch {x y w : ℝ} (hw : 0 < w) (hy : y = x * w) (h : y ^ 2 + w ^ 2 = 1) :
    w = Work.WilE9.psig x ∧ y = WilkiesDesign.E.psi x := by
  obtain ⟨hpsi, hpsig, -⟩ := Work.WilE9.Psi.psi_psig_algebra x
  have hpw : 0 < Work.WilE9.psig x := Work.WilE9.Psi.psig_pos x
  have hc : (1 + x ^ 2) ≠ 0 := by positivity
  -- The circle relation together with `y = x·w` gives `w²(1+x²) = 1`.
  have hy2 : y ^ 2 = x ^ 2 * w ^ 2 := by rw [hy]; ring
  have h1 : w ^ 2 * (1 + x ^ 2) = 1 := by nlinarith [hy2, h]
  -- Hence `w² = psig x²`.
  have hw2 : w ^ 2 = Work.WilE9.psig x ^ 2 := by
    apply mul_right_cancel₀ hc
    rw [h1, hpsig]
  -- Positivity upgrades the square equality to equality.
  have hwx : w = Work.WilE9.psig x := by
    have hfac : (w - Work.WilE9.psig x) * (w + Work.WilE9.psig x) = 0 := by nlinarith [hw2]
    have hpos : 0 < w + Work.WilE9.psig x := by linarith
    rcases mul_eq_zero.mp hfac with h' | h'
    · linarith
    · linarith
  refine ⟨hwx, ?_⟩
  rw [hpsi, hy, hwx]

end Work.WilE9.Sharp
