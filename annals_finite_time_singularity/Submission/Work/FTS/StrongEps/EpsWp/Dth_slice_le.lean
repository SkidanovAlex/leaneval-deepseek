import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Submission.Work.Construction.Defs
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.Gamma_WlInf
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.Galerkin.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Dth_slice_le`

A small glue lemma for the strong-`ε` layer of the Elgindi project.

For a Galerkin family `G` whose `s`-slice is `C^∞` on the open quadrant, and for
`0 < z`, `0 < θ < π/2`, the angular derivative `D_θ = sin(2θ) ∂_θ` of the slice is dominated by
the two `∂_θ`-derivatives appearing in the split `F(τ) = F_* + g(τ)`:

`|D_θ (G · · s) z θ| ≤ |∂_θ (F_* + G · · s) z θ| + |∂_θ F_* z θ|`.

This is the triangle inequality for `∂_θ` (the slice of `F_*` is differentiable at every interior
angle, and the derivative splits, `∂_θ(F_* + g) = ∂_θF_* + ∂_θg`), together with `|sin(2θ)| ≤ 1`.
No smoothness of the family `G` in the angle beyond `SmoothOpen (slice G s)` is used.
-/

noncomputable section

open scoped Real Topology

namespace Work.FTS.StrongEps.EpsWp

/-- The `θ`-slice of the reference profile `F_* = α(Γ/c)·F_{*,rad}` is differentiable at every
interior angle `0 < θ < π/2`: there `sin θ · cos²θ > 0`, so the angular profile
`Γ(θ) = (sin θ cos²θ)^{α/3}` is differentiable by the chain rule for real powers, and the
remaining factor is a constant of the slice. -/
theorem differentiableAt_Fstar_slice_theta (α z θ : ℝ) (hθ : 0 < θ ∧ θ < π / 2) :
    DifferentiableAt ℝ (fun θ' => Work.Construction.Fstar α z θ') θ := by
  have hsin : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ.1 (by linarith [Real.pi_pos])
  have hcos : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hθ.2⟩
  have hbase : Real.sin θ * Real.cos θ ^ 2 ≠ 0 := by positivity
  have hGam : DifferentiableAt ℝ (fun θ' => Work.Spaces.Gam α θ') θ := by
    rw [show Work.Spaces.Gam α = fun y : ℝ => (Real.sin y * Real.cos y ^ 2) ^ (α / 3) from rfl]
    exact (Real.differentiableAt_sin.mul (Real.differentiableAt_cos.pow 2)).rpow_const
      (Or.inl hbase)
  have h := ((hGam.div_const (Work.Spaces.c α)).const_mul α).mul_const (Work.FM.Fstar z)
  simpa [Work.Construction.Fstar] using h

theorem Dth_slice_le {α : ℝ} {G : Work.FTS.Galerkin.Fam} {s z θ : ℝ}
    (hreg : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.Galerkin.slice G s))
    (hz : 0 < z) (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2) :
    |Work.Spaces.Dth (Work.FTS.Galerkin.slice G s) z θ| ≤
      |Work.Spaces.pth (Work.Construction.Ftau α G s) z θ|
        + |Work.Spaces.pth (Work.Construction.Fstar α) z θ| := by
  have hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2) := ⟨hθ0, hθ1⟩
  -- differentiability of the two `θ`-slices at `θ`
  have hGs : DifferentiableAt ℝ (fun θ' => G z θ' s) θ :=
    ((hreg.curry_θ hz).differentiableOn Work.FTS.LocData.smoothOrder_ne_zero).differentiableAt
      (isOpen_Ioo.mem_nhds hθ)
  have hFs : DifferentiableAt ℝ (fun θ' => Work.Construction.Fstar α z θ') θ :=
    differentiableAt_Fstar_slice_theta α z θ ⟨hθ0, hθ1⟩
  -- the `θ`-derivative of the full profile splits
  have hsplit : Work.Spaces.pth (Work.Construction.Ftau α G s) z θ
      = Work.Spaces.pth (Work.Construction.Fstar α) z θ
        + Work.Spaces.pth (Work.FTS.Galerkin.slice G s) z θ := by
    simp only [Work.Spaces.pth, Work.Construction.Ftau, Work.FTS.Galerkin.slice]
    rw [show (fun θ' => Work.Construction.Fstar α z θ' + G z θ' s)
        = (fun θ' => Work.Construction.Fstar α z θ') + (fun θ' => G z θ' s) from rfl,
      deriv_add hFs hGs]
  have hpth_eq : Work.Spaces.pth (Work.FTS.Galerkin.slice G s) z θ
      = Work.Spaces.pth (Work.Construction.Ftau α G s) z θ
        - Work.Spaces.pth (Work.Construction.Fstar α) z θ := by
    rw [hsplit]; ring
  calc |Work.Spaces.Dth (Work.FTS.Galerkin.slice G s) z θ|
      = |Real.sin (2 * θ)| * |Work.Spaces.pth (Work.FTS.Galerkin.slice G s) z θ| := by
        rw [Work.Spaces.Dth, abs_mul]
    _ ≤ 1 * |Work.Spaces.pth (Work.FTS.Galerkin.slice G s) z θ| :=
        mul_le_mul_of_nonneg_right (Real.abs_sin_le_one (2 * θ)) (abs_nonneg _)
    _ = |Work.Spaces.pth (Work.FTS.Galerkin.slice G s) z θ| := one_mul _
    _ = |Work.Spaces.pth (Work.Construction.Ftau α G s) z θ
            - Work.Spaces.pth (Work.Construction.Fstar α) z θ| := by rw [hpth_eq]
    _ ≤ |Work.Spaces.pth (Work.Construction.Ftau α G s) z θ|
          + |Work.Spaces.pth (Work.Construction.Fstar α) z θ| := by
        rw [abs_sub_le_iff]
        constructor <;>
          linarith [le_abs_self (Work.Spaces.pth (Work.Construction.Ftau α G s) z θ),
            le_abs_self (Work.Spaces.pth (Work.Construction.Fstar α) z θ),
            neg_abs_le (Work.Spaces.pth (Work.Construction.Ftau α G s) z θ),
            neg_abs_le (Work.Spaces.pth (Work.Construction.Fstar α) z θ)]

end Work.FTS.StrongEps.EpsWp
