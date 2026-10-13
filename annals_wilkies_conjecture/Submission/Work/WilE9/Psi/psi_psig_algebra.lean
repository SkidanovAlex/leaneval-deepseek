import Mathlib
import Submission.Work.WilE9.Defs
import Submission.Work.WilE9.Psi.psi_sq_add_psig_sq
import Submission.Work.WilE9.Psi.psig_pos

namespace Work.WilE9.Psi

/-- **The auxiliary `w`-coordinate of `ψ` is algebraic.**  With `w := psig x` one has
`ψ x = x·w`, `w² (1 + x²) = 1` (so `w = (1+x²)^{-1/2}` is the algebraic square root), and
`w = √(1 - ψ x²)`, whence every `ψ`-factor of a derivative, e.g.
`deriv ψ x = w³ = (1 - ψ x²)^{3/2}`, is a polynomially-bounded algebraic function of the pair
`(ψ x, w)`.  These are the relations by which the auxiliary coordinates of the `ψ`-transport are
tied to the graph coordinate `ψ x` in a semi-Pfaffian description. -/
theorem psi_psig_algebra (x : ℝ) :
    WilkiesDesign.E.psi x = x * Work.WilE9.psig x ∧
      Work.WilE9.psig x ^ 2 * (1 + x ^ 2) = 1 ∧
      Work.WilE9.psig x = Real.sqrt (1 - WilkiesDesign.E.psi x ^ 2) := by
  have hpos : 0 < 1 + x ^ 2 := by positivity
  have hsqrt_ne : Real.sqrt (1 + x ^ 2) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hpos)
  have hsq : Real.sqrt (1 + x ^ 2) ^ 2 = 1 + x ^ 2 := Real.sq_sqrt (le_of_lt hpos)
  have hpsig_pos : 0 < Work.WilE9.psig x := psig_pos x
  have hcirc := psi_sq_add_psig_sq x
  refine ⟨?_, ?_, ?_⟩
  · unfold WilkiesDesign.E.psi Work.WilE9.psig
    field_simp
  · unfold Work.WilE9.psig
    field_simp
    nlinarith [hsq]
  · have h2 : 1 - WilkiesDesign.E.psi x ^ 2 = Work.WilE9.psig x ^ 2 := by linarith
    rw [h2, Real.sqrt_sq_eq_abs, abs_of_pos hpsig_pos]

end Work.WilE9.Psi
