import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Analysis.Real.Sqrt
import Submission.Work.FTS.RegExportIface.RXT.Leaves
import Submission.Work.FTS.FinalV2.Defs
import Submission.Work.FTS.StrongEps.SupPort.classC_mixed_sup_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_RegExport.RXT.MixedUniform` — uniform interior bounds for the slices of `g`

The class-`C` interior `L^∞`–`ℋ⁴` trade-off of Elgindi's Corollary `SecondDerivativesBounded`
(`Work.FTS.StrongEps.SupPort.classC_mixed_sup_le`) applied to the approximating sequence of
`LimApprox` and passed to the limit: every mixed slot of order `≤ 2` of `slice g τ` is bounded
on the open quadrant by `10/√(γ-1) · (C₀ α²)`, uniformly in `τ ∈ [0,T]` and in `(z,θ) ∈ Q0`.

This is the `(b,a)`-uniform form of RX-A2 (`lim_mixed_bounds_proved`) that the domination
arguments for the angular parametric integrals of `coeff_C2` need.
-/

noncomputable section
open scoped Real Topology
open Set Filter MeasureTheory

namespace Work.FTS_RegExport.RXT

open Work.FTS.Galerkin (Fn Fam slice)
open Work.FTS.FinalV2 (LimApprox)

set_option autoImplicit false

/-- **Uniform mixed-slot bounds of the slices of `g`.**  From the `LimApprox` clause of
`DynOK'` (class-`C` approximants with `ℋ⁴`-bounds and jet convergence) and the class-`C`
interior trade-off `classC_mixed_sup_le`. -/
theorem mixed_uniform {α C₀ : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    {Φs : Fn} {E : Fn →ₗ[ℝ] Fn} {g : Fam}
    (hA : LimApprox α C₀ Φs E g) (T : ℝ) (hT : 0 < T) :
    ∀ τ ∈ Icc (0 : ℝ) T, ∀ b a : ℕ, a + b ≤ 2 → ∀ z θ : ℝ,
      (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      |Work.Spaces.mixed b a (slice g τ) z θ|
        ≤ 10 / Real.sqrt (Work.Spaces.gam α - 1) * (C₀ * α ^ 2) := by
  intro τ hτ b a hab z θ hzθ
  obtain ⟨gn, B, L, hC, -, hjet, -⟩ := hA T hT
  have hγ1 : 0 < Work.Spaces.gam α - 1 := by
    rw [Work.Spaces.gam_sub_one]; linarith
  have hK : (0 : ℝ) ≤ 10 / Real.sqrt (Work.Spaces.gam α - 1) :=
    div_nonneg (by norm_num) (Real.sqrt_nonneg _)
  have h1 : ∀ n : ℕ, |Work.Spaces.mixed b a (slice (gn n) τ) z θ|
      ≤ 10 / Real.sqrt (Work.Spaces.gam α - 1) * (C₀ * α ^ 2) := by
    intro n
    refine le_trans (Work.FTS.StrongEps.SupPort.classC_mixed_sup_le hα hα1
      (hC n τ hτ).1 b a hab hzθ) ?_
    exact mul_le_mul_of_nonneg_left (hC n τ hτ).2.1 hK
  have h2 : Tendsto (fun n : ℕ => |Work.Spaces.mixed b a (slice (gn n) τ) z θ|) atTop
      (𝓝 |Work.Spaces.mixed b a (slice g τ) z θ|) :=
    (hjet τ hτ b a (by omega) z θ hzθ).abs
  exact le_of_tendsto h2 (Eventually.of_forall h1)

end Work.FTS_RegExport.RXT
