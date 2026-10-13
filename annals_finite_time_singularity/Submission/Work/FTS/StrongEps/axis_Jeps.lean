/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/StrongEps/axis_Jeps.lean` — `J_ε` preserves the axis condition

The map `f ↦ J_ε f` of `StrongEps/Basic.lean` is, on the open quadrant, the convolution

  `Jeps ρ ε f z θ = ∫ p, Jker ρ ε p * f (z e^{-p₁}) (arctan (tan θ e^{-p₂}))`

in the log coordinates `s = log z`, `ζ = log tan θ`, with the kernel `Jker ρ ε p = ε⁻¹²ρ(p/ε)`
supported in the ball of radius `ε` and of total mass `1` (`Jker_integral_eq_one`).

The **axis condition** of the paper is `f z θ = o(z)` as `z → 0⁺`, uniformly in `θ ∈ (0, π/2)`.
It is one of the clauses of the lead's class `ClassC` (`Submission/Work/FTS/ClassC/`), and it is
preserved by the mollifier: this file proves that `J_ε f z θ / z → 0` as `z → 0⁺` for every fixed
`θ ∈ (0, π/2)`, from the axis condition alone.

The proof is one line of bookkeeping.  Write `M(z, p) := f (z e^{-p₁}) (arctan (tan θ e^{-p₂}))`.
For `z` small and `|p| ≤ ε` the shifted first coordinate `z e^{-p₁}` is `≤ z e^{ε}`, hence still in
the region where the axis condition holds; dividing by `z` rather than by `z e^{-p₁}` therefore
costs only the factor `e^{ε}`:

  `|M(z, p) / z| ≤ e^{ε} · |f (z e^{-p₁}) (…)| / (z e^{-p₁}) ≤ e^{ε} ε'`  for `z e^{ε} < δ(ε')`.

Inserting this into `abs_Jeps_le_sup` (with the constant `ε' z e^{ε}`) and using the unit mass of
the kernel gives `|J_ε f z θ| ≤ ε' z e^{ε}` for all `z < δ(ε') e^{-ε}/2`; the left-hand side is
`|J_ε f z θ / z| ≤ ε' e^{ε}`, and `ε' > 0` is arbitrary, so the quotient tends to `0`.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.StrongEps.Basic
import Submission.Work.FTS.StrongEps.Kernel
import Submission.Work.FTS.StrongEps.Jker_integral_eq_one
import Submission.Work.FTS.StrongEps.JepsBasic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps

theorem axis_Jeps {ρ : ℝ × ℝ → ℝ} (hρ : IsMollKernel ρ) {ε : ℝ} (hε : 0 < ε)
    {f : ℝ → ℝ → ℝ}
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f) Quad)
    (hax : ∀ ε' > 0, ∃ δ > 0, ∀ z : ℝ, 0 < z → z < δ →
      ∀ θ : ℝ, θ ∈ Set.Ioo 0 (π / 2) → |f z θ / z| ≤ ε') :
    ∀ θ ∈ Set.Ioo 0 (π / 2),
      Filter.Tendsto (fun z : ℝ => Jeps ρ ε f z θ / z) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  -- the smoothness hypothesis is not needed: the bound uses only the axis condition
  have _hsm := hsm
  intro θ hθ
  rw [Metric.tendsto_nhds]
  intro η hη
  -- the tolerance of the axis condition: `ε' = η / (2 e^ε)`
  have heps' : (0 : ℝ) < η / (2 * Real.exp ε) := by positivity
  obtain ⟨δ', hδ'pos, hδ'⟩ := hax (η / (2 * Real.exp ε)) heps'
  -- the `z`-window: `z e^ε < δ'`
  set δ : ℝ := δ' / 2 * Real.exp (-ε) with hδdef
  have hδpos : 0 < δ := mul_pos (by linarith) (Real.exp_pos _)
  refine Filter.mem_of_superset (Ioc_mem_nhdsGT hδpos) ?_
  intro z hz
  rw [Set.mem_Ioc] at hz
  obtain ⟨hzpos, hzle⟩ := hz
  -- the mollified profile is `O(z)`
  have hJ : |Jeps ρ ε f z θ| ≤ η / 2 * z := by
    refine abs_Jeps_le_sup ρ hρ hε hzpos hθ (M := η / 2 * z) ?_
      (mul_nonneg (by linarith) hzpos.le)
    intro p hp1 hp2
    -- the shifted point still lies in the region where the axis condition holds
    have hneg : -p.1 ≤ ε := by
      have h := (abs_le.mp hp1).1
      linarith
    have hshift : z * Real.exp (-p.1) ≤ δ' / 2 := by
      have h1 : Real.exp (-p.1) ≤ Real.exp ε := Real.exp_le_exp.mpr hneg
      have h2 : z * Real.exp (-p.1) ≤ δ * Real.exp ε :=
        mul_le_mul hzle h1 (Real.exp_pos _).le hδpos.le
      have h3 : δ * Real.exp ε = δ' / 2 := by
        rw [hδdef]
        rw [mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one]
      linarith
    have hzsp : 0 < zShift z p.1 := zShift_pos hzpos
    have hzsp' : zShift z p.1 < δ' := by
      have h4 : zShift z p.1 = z * Real.exp (-p.1) := rfl
      rw [h4]
      linarith
    have hbd := hδ' (zShift z p.1) hzsp hzsp' (thShift θ p.2) (thShift_mem hθ)
    -- `|f| ≤ ε' · z e^ε` on the shifted point, and `ε' e^ε = η/2`
    calc |f (zShift z p.1) (thShift θ p.2)|
        = |f (zShift z p.1) (thShift θ p.2) / zShift z p.1| * zShift z p.1 := by
          rw [abs_div, abs_of_pos hzsp, div_mul_cancel₀ _ hzsp.ne']
      _ ≤ (η / (2 * Real.exp ε)) * zShift z p.1 :=
          mul_le_mul_of_nonneg_right hbd hzsp.le
      _ ≤ (η / (2 * Real.exp ε)) * (z * Real.exp ε) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          simp only [zShift]
          exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hneg) hzpos.le
      _ = η / 2 * z := by
          field_simp
  -- divide by `z > 0`
  show dist (Jeps ρ ε f z θ / z) 0 < η
  rw [Real.dist_eq, sub_zero]
  have hbound : |Jeps ρ ε f z θ / z| ≤ η / 2 := by
    rw [abs_div, abs_of_pos hzpos, div_le_iff₀ hzpos]
    exact hJ
  linarith

end Work.FTS.StrongEps
