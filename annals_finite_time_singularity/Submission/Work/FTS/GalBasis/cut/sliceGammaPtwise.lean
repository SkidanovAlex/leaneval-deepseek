import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Topology.Algebra.Module.ModuleTopology

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.GalBasis.cut

/-- The two `rpow` power identities used below, for `s = sin (2θ)` with `s > 0`:
`s ^ (2 - γ) = s * s ^ (1 - γ)` and `s ^ (-γ) = s ^ (1 - γ) / s`. -/
theorem sin_rpow_shift {γ θ : ℝ} (h : 0 < Real.sin (2 * θ)) :
    (Real.sin (2 * θ)) ^ (2 - γ) = Real.sin (2 * θ) * (Real.sin (2 * θ)) ^ (1 - γ) ∧
      (Real.sin (2 * θ)) ^ (-γ) = (Real.sin (2 * θ)) ^ (1 - γ) / Real.sin (2 * θ) := by
  have hne : Real.sin (2 * θ) ≠ 0 := ne_of_gt h
  have h2 : (Real.sin (2 * θ)) ^ (2 - γ)
      = Real.sin (2 * θ) * (Real.sin (2 * θ)) ^ (1 - γ) := by
    rw [show (2 : ℝ) - γ = 1 + (1 - γ) by ring, Real.rpow_add h, Real.rpow_one]
  have h1 : (Real.sin (2 * θ)) ^ (1 - γ) = (Real.sin (2 * θ)) ^ (-γ) * Real.sin (2 * θ) := by
    rw [show (1 : ℝ) - γ = (-γ) + 1 by ring, Real.rpow_add h, Real.rpow_one]
  exact ⟨h2, by rw [eq_div_iff hne]; exact h1.symm⟩

theorem sliceGammaPtwise {γ b θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    HasDerivAt (fun t => -2 * b * Real.cos (2 * t) * (Real.sin (2 * t)) ^ (1 - γ))
      (4 * b * (Real.sin (2 * θ)) ^ (2 - γ) + 4 * b * (γ - 1) * (Real.cos (2 * θ)) ^ 2
        * (Real.sin (2 * θ)) ^ (-γ)) θ ∧
    (4 * b * (Real.sin (2 * θ)) ^ (2 - γ) + 4 * b * (γ - 1) * (Real.cos (2 * θ)) ^ 2
        * (Real.sin (2 * θ)) ^ (-γ)
      - (-2 * b * Real.cos (2 * θ) / (Real.sin (2 * θ)))
          * (-2 * b * Real.cos (2 * θ) * (Real.sin (2 * θ)) ^ (1 - γ))
      = (4 * b * (Real.sin (2 * θ)) ^ 2 + 4 * b * (γ - 1 - b) * (Real.cos (2 * θ)) ^ 2)
          * (Real.sin (2 * θ)) ^ (-γ)) ∧
    (-2 * b * Real.cos (2 * θ) * (Real.sin (2 * θ)) ^ (1 - γ)
      = (-2 * b * Real.cos (2 * θ) / (Real.sin (2 * θ))) * (Real.sin (2 * θ)) ^ (2 - γ)) := by
  obtain ⟨hθ0, hθ1⟩ := hθ
  have h2θ0 : 0 < 2 * θ := by linarith
  have h2θ1 : 2 * θ < Real.pi := by linarith
  have hsin : 0 < Real.sin (2 * θ) := Real.sin_pos_of_pos_of_lt_pi h2θ0 h2θ1
  have hsinne : Real.sin (2 * θ) ≠ 0 := ne_of_gt hsin
  obtain ⟨hs2, hs0⟩ := sin_rpow_shift (γ := γ) hsin
  refine ⟨?_, ?_, ?_⟩
  · -- differentiability of `t ↦ -2 b cos (2t) sin (2t) ^ (1 - γ)` at `θ`
    have hlin : HasDerivAt (fun t : ℝ => 2 * t) 2 θ := by
      simpa using (hasDerivAt_id θ).const_mul (2 : ℝ)
    have hcos_d : HasDerivAt (fun t : ℝ => Real.cos (2 * t)) (-Real.sin (2 * θ) * 2) θ :=
      (Real.hasDerivAt_cos (2 * θ)).comp θ hlin
    have hsin_d : HasDerivAt (fun t : ℝ => Real.sin (2 * t)) (Real.cos (2 * θ) * 2) θ :=
      (Real.hasDerivAt_sin (2 * θ)).comp θ hlin
    have hrpow : HasDerivAt (fun t : ℝ => (Real.sin (2 * t)) ^ (1 - γ))
        ((Real.cos (2 * θ) * 2) * (1 - γ) * (Real.sin (2 * θ)) ^ ((1 - γ) - 1)) θ :=
      hsin_d.rpow_const (Or.inl hsinne)
    have hcc : HasDerivAt (fun t : ℝ => -2 * b * Real.cos (2 * t))
        (-2 * b * (-Real.sin (2 * θ) * 2)) θ := hcos_d.const_mul (-2 * b)
    have hmul := hcc.mul hrpow
    have hval : (-2 * b * (-Real.sin (2 * θ) * 2)) * (Real.sin (2 * θ)) ^ (1 - γ)
        + (-2 * b * Real.cos (2 * θ))
            * ((Real.cos (2 * θ) * 2) * (1 - γ) * (Real.sin (2 * θ)) ^ ((1 - γ) - 1))
        = 4 * b * (Real.sin (2 * θ)) ^ (2 - γ) + 4 * b * (γ - 1) * (Real.cos (2 * θ)) ^ 2
          * (Real.sin (2 * θ)) ^ (-γ) := by
      rw [show (1 : ℝ) - γ - 1 = -γ by ring, hs2]
      ring
    exact hmul.congr_deriv hval
  · -- the cancellation of the `b ^ 2` term
    rw [hs2, hs0]
    field_simp
    ring
  · -- the exponent shift in the quadratic term
    rw [hs2]
    field_simp

end Work.FTS.GalBasis.cut
