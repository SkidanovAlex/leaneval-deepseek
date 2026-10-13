import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.EllipticEst.AngAWeak.SRSAux.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.AngAWeak.SRSAux

/-- The amplitude `Wn u = u / sin 2θ` has derivative `Bflux u θ / (cos θ · (sin 2θ)²)`, which is
the quotient rule for `u` against the kernel element `sin 2θ` (the factor `cos θ` cancels between
the definition of `Bflux` and the denominator). -/
theorem WnDeriv {u : ℝ → ℝ}
    (hsm : ContDiffOn ℝ 1 u (Set.Ioo (0 : ℝ) (Real.pi / 2)))
    {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    HasDerivAt (Work.FTS.EllipticEst.AngAWeak.Wn u)
      (Work.FTS.EllipticEst.AngAWeak.Bflux u θ / (Real.cos θ * (Real.sin (2 * θ)) ^ 2)) θ := by
  -- differentiability of `u` at the interior point `θ`
  have hderiv : HasDerivAt u (deriv u θ) θ := by
    have hd : DifferentiableOn ℝ u (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
      hsm.differentiableOn (by norm_num)
    exact (hd.differentiableAt (isOpen_Ioo.mem_nhds hθ)).hasDerivAt
  -- derivative of the denominator `θ ↦ sin (2θ)`
  have hsin : HasDerivAt (fun x : ℝ => Real.sin (2 * x)) (2 * Real.cos (2 * θ)) θ := by
    have h2 : HasDerivAt (fun x : ℝ => 2 * x) 2 θ := by
      simpa using (hasDerivAt_id θ).const_mul (2 : ℝ)
    have h3 : HasDerivAt (fun x : ℝ => Real.sin (2 * x)) (Real.cos (2 * θ) * 2) θ :=
      (Real.hasDerivAt_sin (2 * θ)).comp θ h2
    rw [show (2 : ℝ) * Real.cos (2 * θ) = Real.cos (2 * θ) * 2 by ring]
    exact h3
  have hne : Real.sin (2 * θ) ≠ 0 := by
    apply ne_of_gt
    apply Real.sin_pos_of_pos_of_lt_pi
    · linarith [hθ.1, Real.pi_pos]
    · linarith [hθ.2, Real.pi_pos]
  have h := hderiv.div hsin hne
  have hc : Real.cos θ ≠ 0 := by
    apply ne_of_gt
    exact Real.cos_pos_of_mem_Ioo
      ⟨by linarith [hθ.1, Real.pi_pos], by linarith [hθ.2, Real.pi_pos]⟩
  rw [show Work.FTS.EllipticEst.AngAWeak.Wn u = u / (fun x : ℝ => Real.sin (2 * x)) by
        funext x; rfl]
  rw [show Work.FTS.EllipticEst.AngAWeak.Bflux u θ / (Real.cos θ * (Real.sin (2 * θ)) ^ 2)
        = ((deriv u θ * Real.sin (2 * θ) - u θ * (2 * Real.cos (2 * θ)))
            / (Real.sin (2 * θ)) ^ 2) by
      rw [Work.FTS.EllipticEst.AngAWeak.Bflux]
      rw [mul_div_mul_left _ _ hc]]
  exact h

end Work.FTS.EllipticEst.AngAWeak.SRSAux
