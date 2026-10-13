import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.Construction.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_RegExport.RXT.SysAux

/-- `(sin (2·))' = 2 cos (2·)`, the only calculus input of the closed forms below. -/
private lemma deriv_sin_two (θ : ℝ) : deriv (fun θ' => Real.sin (2 * θ')) θ = 2 * Real.cos (2 * θ) := by
  have h1 : HasDerivAt (fun θ' : ℝ => Real.sin (2 * θ')) (Real.cos (2 * θ) * 2) θ :=
    (Real.hasDerivAt_sin (2 * θ)).comp θ (hasDerivAt_const_mul (x := θ) (2 : ℝ))
  rw [h1.deriv]; ring

/-- The three closed forms of the operators `V`, `U`, `R` (of `Work.Construction`) applied to the
singular part `Θ αG F = (1/(4αG))·sin 2θ·L₁₂(F)(z)`, on the open quadrant
`z > 0, 0 < θ < π/2` (where `cos θ ≠ 0`), given the index-raising identity
`z ∂_z L₁₂(F) = -𝔽K(F)` (hypothesis `hL12d`, which the callers supply from the integral form of
`L₁₂`).  These are the identities that let `Vz7`, `Vθ7`, `cs7` be written with the `Θ`-part in
closed form. -/
theorem Theta_ops {αG : ℝ} (hα : 0 < αG) {F : ℝ → ℝ → ℝ}
    (hL12d : ∀ z : ℝ, 0 < z →
      z * deriv (fun z' => Work.Construction.L12 F z') z = -Work.Construction.FK F z) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      (2 * αG * Work.Construction.Vop (Work.Construction.Theta αG F) z θ
          = Work.Construction.c2m θ * Work.Construction.L12 F z) ∧
      (2 * Work.Construction.Uop αG (Work.Construction.Theta αG F) z θ
          = -(3 / (2 * αG)) * Real.sin (2 * θ) * Work.Construction.L12 F z
            + (1 / 2) * Real.sin (2 * θ) * Work.Construction.FK F z) ∧
      (-2 * Work.Construction.Rop αG (Work.Construction.Theta αG F) z θ
          = -(Work.Construction.L12 F z) / αG + (Real.sin θ) ^ 2 * Work.Construction.FK F z) := by
  intro z θ hz hθ hθ2
  -- `cos θ ≠ 0` on the open quadrant, so `tan θ = sin θ / cos θ` may be used.
  have hcos : Real.cos θ ≠ 0 := by
    have h := Real.cos_pos_of_mem_Ioo (show θ ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) from
      ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩)
    exact ne_of_gt h
  have hzne : z ≠ 0 := ne_of_gt hz
  -- `hL12d` in the form `∂_z L₁₂(F)(z) = -𝔽K(F)(z)/z`, in which every occurrence of the
  -- radial derivative can be eliminated.
  have hLd : deriv (fun z' => Work.Construction.L12 F z') z
      = -Work.Construction.FK F z / z := by
    rw [eq_div_iff hzne, mul_comm]
    exact hL12d z hz
  -- `∂_θ Θ = (1/(4αG))·L₁₂(F)·2cos 2θ`
  have hpth : Work.Spaces.pth (Work.Construction.Theta αG F) z θ
      = (1 / (4 * αG)) * (2 * Real.cos (2 * θ)) * Work.Construction.L12 F z := by
    show deriv (fun θ' => Work.Construction.Theta αG F z θ') θ = _
    have h1 : (fun θ' => Work.Construction.Theta αG F z θ')
        = fun θ' => ((1 / (4 * αG)) * Work.Construction.L12 F z) * Real.sin (2 * θ') := by
      funext θ'
      simp only [Work.Construction.Theta, Work.Construction.s2]
      ring
    rw [h1, deriv_const_mul_field, deriv_sin_two]
    ring
  -- `∂_z Θ = (1/(4αG))·sin 2θ·∂_z L₁₂(F)`, and the hypothesis removes `∂_z L₁₂(F)`.
  have hpz : Work.Spaces.pz (Work.Construction.Theta αG F) z θ
      = (1 / (4 * αG)) * Real.sin (2 * θ) * (-Work.Construction.FK F z / z) := by
    show deriv (fun z' => Work.Construction.Theta αG F z' θ) z = _
    have h1 : (fun z' => Work.Construction.Theta αG F z' θ)
        = fun z' => ((1 / (4 * αG)) * Real.sin (2 * θ)) * Work.Construction.L12 F z' := by
      funext z'
      simp only [Work.Construction.Theta, Work.Construction.s2]
    rw [h1, deriv_const_mul_field, hLd]
  refine ⟨?_, ?_, ?_⟩
  -- `V(Θ) = ∂_θΘ - tan θ·Θ`: `2αG·V(Θ) = L₁₂(F)·(cos 2θ - sin²θ) = c2m θ·L₁₂(F)`.
  · simp only [Work.Construction.Vop, hpth, Work.Construction.Theta, Work.Construction.s2,
      Work.Construction.c2m, Real.tan_eq_sin_div_cos]
    rw [Real.sin_two_mul, Real.cos_two_mul']
    field_simp
    ring
  -- `U(Θ) = -3Θ - αG·z·∂_zΘ`; substituting `z ∂_z L₁₂(F) = -𝔽K(F)` gives the second form.
  · simp only [Work.Construction.Uop, hpz, Work.Construction.Theta, Work.Construction.s2]
    field_simp
    ring
  -- `ℛ(Θ) = (2 sin θ·Θ + αG sin θ·z ∂_zΘ + cos θ·∂_θΘ)/cos θ`, and
  -- `sin θ·sin 2θ + cos θ·cos 2θ = cos θ`, whence `-2ℛ(Θ) = -L₁₂(F)/αG + sin²θ·𝔽K(F)`.
  · simp only [Work.Construction.Rop, hpth, hpz, Work.Construction.Theta, Work.Construction.s2]
    rw [Real.sin_two_mul, Real.cos_two_mul']
    field_simp
    rw [Real.sin_sq]
    ring

end Work.FTS_RegExport.RXT.SysAux
