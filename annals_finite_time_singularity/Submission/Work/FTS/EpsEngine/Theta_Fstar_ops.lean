import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.Construction.Defs
import Submission.Work.Construction.L12_Fstar_eq
import Submission.Work.FTS.Nonlinear.FstarPkg.FK_Fstar
import Submission.Work.FTS_RegExport.RXT.SysAux.Theta_ops

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Topology

namespace Work.FTS.EpsEngine

/-- The three closed forms of the singular part `Theta α F_*` of the star profile, at the level of
the operators `Rop`, `Uop`, `Vop` of `Work.Construction`, on the open quadrant:
`Rop α (Theta α F_*) = 1/(1+z) − α sin²θ z/(1+z)²`,
`Vop (Theta α F_*) = c2m θ/(1+z)`,
`Uop α (Theta α F_*)/sin 2θ = −3/(2(1+z)) + α z/(2(1+z)²)`.
The values at `z = 0` are `1`, `c2m θ` and `−3/2` respectively.

They follow from `Work.FTS_RegExport.RXT.SysAux.Theta_ops`
(`-2·Rop α (Theta α F) = -L₁₂(F)/α + sin²θ·𝔽K(F)`, `2α·Vop (Theta α F) = L₁₂(F)·c2m θ`,
`2·Uop α (Theta α F) = -(3/(2α))sin2θ L₁₂(F) + (1/2)sin2θ·𝔽K(F)`) at `F = F_*`, together with
`Work.Construction.L12_Fstar_eq` (`L₁₂(F_*) z = 2α/(1+z)`) and
`Work.FTS.Nonlinear.FstarPkg.FK_Fstar` (`𝔽K(F_*) z = α·(2z/(1+z)²)`). -/
theorem Theta_Fstar_ops {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    (∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Construction.Rop α (Work.Construction.Theta α (Work.Construction.Fstar α)) z θ
        = 1 / (1 + z) - α * (Real.sin θ) ^ 2 * z / (1 + z) ^ 2) ∧
    (∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Construction.Vop (Work.Construction.Theta α (Work.Construction.Fstar α)) z θ
        = Work.Construction.c2m θ / (1 + z)) ∧
    (∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Construction.Uop α (Work.Construction.Theta α (Work.Construction.Fstar α)) z θ
          / Work.Construction.s2 θ
        = -(3 / (2 * (1 + z))) + α * z / (2 * (1 + z) ^ 2)) := by
  -- The index-raising identity `z ∂_z L₁₂(F_*) = -𝔽K(F_*)` required by `Theta_ops`.  Since
  -- `L₁₂(F_*)` is *exactly* `2α/(1+z)` on `[0,∞)`, its derivative there is elementary.
  have hL12d : ∀ z : ℝ, 0 < z →
      z * deriv (fun z' => Work.Construction.L12 (Work.Construction.Fstar α) z') z
        = -Work.Construction.FK (Work.Construction.Fstar α) z := by
    intro z hz
    have heq : (fun z' : ℝ => Work.Construction.L12 (Work.Construction.Fstar α) z')
        =ᶠ[𝓝 z] (fun z' : ℝ => 2 * α / (1 + z')) := by
      filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
      exact Work.Construction.L12_Fstar_eq hα hα1 (le_of_lt hz')
    rw [heq.deriv_eq]
    have hd : HasDerivAt (fun z' : ℝ => (1 + z')⁻¹) (-((1 + z) ^ 2)⁻¹) z := by
      have h1 : HasDerivAt (fun z' : ℝ => 1 + z') 1 z := by
        simpa using (hasDerivAt_id z).const_add (1 : ℝ)
      have h2 := h1.inv (by positivity : (1 : ℝ) + z ≠ 0)
      convert h2 using 1
      ring
    have hderiv : deriv (fun z' : ℝ => 2 * α / (1 + z')) z = -2 * α / (1 + z) ^ 2 := by
      rw [show (fun z' : ℝ => 2 * α / (1 + z')) = fun z' => 2 * α * (1 + z')⁻¹ from by
        funext z'; ring]
      rw [deriv_const_mul_field, hd.deriv]
      ring
    rw [hderiv, Work.FTS.Nonlinear.FstarPkg.FK_Fstar hα hα1]
    field_simp
  have hmain := Work.FTS_RegExport.RXT.SysAux.Theta_ops (αG := α) hα hL12d
  refine ⟨?_, ?_, ?_⟩
  · -- `Rop`: `-2·Rop(Θ) = -L₁₂(F_*)/α + sin²θ·𝔽K(F_*) = -2(1/(1+z) - α sin²θ z/(1+z)²)`.
    intro z θ hz hθ hθ2
    have h := (hmain z θ hz hθ hθ2).2.2
    rw [Work.Construction.L12_Fstar_eq hα hα1 (le_of_lt hz),
        Work.FTS.Nonlinear.FstarPkg.FK_Fstar hα hα1] at h
    have hαne : α ≠ 0 := ne_of_gt hα
    have h1z : (1 : ℝ) + z ≠ 0 := by positivity
    have key : -(2 * α / (1 + z)) / α + (Real.sin θ) ^ 2 * (α * (2 * z / (1 + z) ^ 2))
        = -2 * (1 / (1 + z) - α * (Real.sin θ) ^ 2 * z / (1 + z) ^ 2) := by
      field_simp
      ring
    rw [key] at h
    linarith
  · -- `Vop`: `2α·Vop(Θ) = c2m θ·L₁₂(F_*) = 2α·(c2m θ/(1+z))`.
    intro z θ hz hθ hθ2
    have h := (hmain z θ hz hθ hθ2).1
    rw [Work.Construction.L12_Fstar_eq hα hα1 (le_of_lt hz)] at h
    have key : Work.Construction.c2m θ * (2 * α / (1 + z))
        = 2 * α * (Work.Construction.c2m θ / (1 + z)) := by ring
    rw [key] at h
    exact mul_left_cancel₀ (by positivity : (2 : ℝ) * α ≠ 0) h
  · -- `Uop`: `2·Uop(Θ) = 2 sin 2θ·(-3/(2(1+z)) + α z/(2(1+z)²))`; divide by `sin 2θ > 0`.
    intro z θ hz hθ hθ2
    have h := (hmain z θ hz hθ hθ2).2.1
    rw [Work.Construction.L12_Fstar_eq hα hα1 (le_of_lt hz),
        Work.FTS.Nonlinear.FstarPkg.FK_Fstar hα hα1] at h
    have hαne : α ≠ 0 := ne_of_gt hα
    have h1z : (1 : ℝ) + z ≠ 0 := by positivity
    have key : -(3 / (2 * α)) * Real.sin (2 * θ) * (2 * α / (1 + z))
          + (1 / 2) * Real.sin (2 * θ) * (α * (2 * z / (1 + z) ^ 2))
        = 2 * Real.sin (2 * θ) * (-(3 / (2 * (1 + z))) + α * z / (2 * (1 + z) ^ 2)) := by
      field_simp
    rw [key] at h
    have hsin : Real.sin (2 * θ) ≠ 0 := by
      apply ne_of_gt
      apply Real.sin_pos_of_pos_of_lt_pi
      · linarith
      · linarith [Real.pi_pos]
    have hU : Work.Construction.Uop α (Work.Construction.Theta α (Work.Construction.Fstar α)) z θ
        = Real.sin (2 * θ) * (-(3 / (2 * (1 + z))) + α * z / (2 * (1 + z) ^ 2)) := by
      linarith
    rw [hU, Work.Construction.s2]
    rw [div_eq_iff hsin]
    ring

end Work.FTS.EpsEngine
