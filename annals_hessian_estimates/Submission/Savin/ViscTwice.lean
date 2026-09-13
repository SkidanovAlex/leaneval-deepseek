import Submission.GOperator
import Submission.Savin.Iteration
import Submission.Commons.Analysis.Calculus.FDeriv.hessianWithin_eq_hessian
import Submission.Commons.Analysis.Calculus.FDeriv.hessianWithin_add_quadratic

open HessianEstimates
open Commons.Analysis.Calculus.FDeriv
open Metric MeasureTheory Filter Set Asymptotics
open scoped BigOperators RealInnerProductSpace Topology ENNReal

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Submission

local notation "ℝ⁴" => EuclideanSpace ℝ (Fin 4)

noncomputable section

/-- `z ↦ c * ‖z - y‖²` is `C²`. -/
theorem contDiff_const_mul_norm_sq_sub (y : ℝ⁴) (c : ℝ) :
    ContDiff ℝ 2 (fun z : ℝ⁴ => c * ‖z - y‖ ^ 2) := by
  have h : ContDiff ℝ 2 (fun z : ℝ⁴ => z - y) := contDiff_id.sub contDiff_const
  have h2 : ContDiff ℝ 2 (fun z : ℝ⁴ => inner ℝ (z - y) (z - y)) := ContDiff.inner ℝ h h
  have h3 : ContDiff ℝ 2 (fun z : ℝ⁴ => ‖z - y‖ ^ 2) := by
    simpa [real_inner_self_eq_norm_sq] using h2
  have h4 : ContDiff ℝ 2 (fun z : ℝ⁴ => c • ‖z - y‖ ^ 2) :=
    ContDiff.const_smul (𝕜 := ℝ) (R := ℝ) c h3
  simpa [smul_eq_mul] using h4

/-- The Hessian of the shifted model quadratic `z ↦ ⟪A (z - y), z - y⟫/2 + L (z - y) + c` is
`A`. -/
theorem hessOp_shifted_quad {A : ℝ⁴ →L[ℝ] ℝ⁴} (hA : A.IsSymmetric) (L : ℝ⁴ →L[ℝ] ℝ) (c : ℝ)
    (y x : ℝ⁴) :
    hessOp (fun z => ⟪A (z - y), z - y⟫ / 2 + L (z - y) + c) x = A := by
  have hcd : ContDiffAt ℝ 2 (fun t : ℝ⁴ => ⟪A t, t⟫ / 2 + L t + c)
      (-y + (1 : ℝ) • x) := (contDiff_modelQuad A L c).contDiffAt
  have h := hessOp_comp_affine (φ := fun t : ℝ⁴ => ⟪A t, t⟫ / 2 + L t + c)
    (x₀ := -y) (r := 1) (x := x) hcd
  have hfun : (fun z : ℝ⁴ => ⟪A (z - y), z - y⟫ / 2 + L (z - y) + c)
      = (fun z => (fun t : ℝ⁴ => ⟪A t, t⟫ / 2 + L t + c) (-y + (1 : ℝ) • z)) := by
    funext z
    have hz : z + -y = -y + z := add_comm _ _
    simp only [one_smul, sub_eq_add_neg]
    rw [hz]
  rw [hfun, h, one_mul, one_smul]
  exact hessOp_modelQuad hA L c (-y + (1 : ℝ) • x)

/-- The model quadratic on the shifted frame is `C²`. -/
theorem contDiffOn_shifted_quad {A : ℝ⁴ →L[ℝ] ℝ⁴} (L : ℝ⁴ →L[ℝ] ℝ) (c : ℝ) (y : ℝ⁴)
    (s : Set ℝ⁴) :
    ContDiffOn ℝ 2 (fun z : ℝ⁴ => ⟪A (z - y), z - y⟫ / 2 + L (z - y) + c) s := by
  have h2 : ContDiff ℝ 2
      (fun z : ℝ⁴ => (fun t : ℝ⁴ => ⟪A t, t⟫ / 2 + L t + c) (z - y)) :=
    (contDiff_modelQuad A L c).comp (contDiff_id.sub contDiff_const)
  refine (h2.contDiffOn).congr fun z _ => ?_
  ring

/-- **The equation holds pointwise at a point of twice differentiability.**  If `g` is a viscosity
solution of `-G(D²g) = 0` on an open set `s` and has a second order Taylor expansion with quadratic
part `A` at `y ∈ s`, then `G(A) = 0`. -/
theorem Gop_eq_zero_of_twiceDiff {g : ℝ⁴ → ℝ} {s : Set ℝ⁴} {y : ℝ⁴}
    {A : ℝ⁴ →L[ℝ] ℝ⁴} {L : ℝ⁴ →L[ℝ] ℝ}
    (hs : IsOpen s) (hy : y ∈ s) (hA : A.IsSymmetric)
    (hvisc : IsViscSolution (fun M => -Gop M) g s)
    (hTay : (fun z => g z - g y - L (z - y) - ⟪A (z - y), (z - y)⟫ / 2)
      =o[𝓝 y] (fun z => ‖z - y‖ ^ 2)) :
    Gop A = 0 := by
  set Q : ℝ⁴ → ℝ := fun z => g y + L (z - y) + ⟪A (z - y), (z - y)⟫ / 2 with hQdef
  have hQcd : ContDiffOn ℝ 2 Q s := by
    rw [hQdef]
    refine (contDiffOn_shifted_quad (A := A) L (g y) y s).congr fun z _ => ?_
    ring
  have hQcdAt : ContDiffWithinAt ℝ 2 Q s y := hQcd.contDiffWithinAt hy
  have hQhess : hessOp Q y = A := by
    rw [hQdef]
    rw [show (fun z : ℝ⁴ => g y + L (z - y) + ⟪A (z - y), z - y⟫ / 2)
        = (fun z => ⟪A (z - y), z - y⟫ / 2 + L (z - y) + g y) from by
      funext z; ring]
    exact hessOp_shifted_quad hA L (g y) y y
  have hQy : Q y = g y := by simp [hQdef]
  have hQH : HessOp Q s y = A := by
    rw [show HessOp Q s y = hessOp Q y from hessianWithin_eq_hessian (hs.mem_nhds hy), hQhess]
  set f : ℝ⁴ → ℝ := fun z => g z - g y - L (z - y) - ⟪A (z - y), (z - y)⟫ / 2 with hfdef
  have hfz : ∀ z, g z - Q z = f z := by
    intro z; simp only [hQdef, hfdef]; ring
  -- the subsolution side
  have hsub : ∀ ε : ℝ, 0 < ε → 0 ≤ Gop (A + ε • (1 : ℝ⁴ →L[ℝ] ℝ⁴)) := by
    intro ε hε
    set φ : ℝ⁴ → ℝ := fun z => Q z + (ε / 2) * ‖z - y‖ ^ 2 with hφdef
    have hφcd : ContDiffOn ℝ 2 φ s := by
      rw [hφdef]
      exact hQcd.add ((contDiff_const_mul_norm_sq_sub y (ε / 2)).contDiffOn)
    have htouch : ∀ᶠ z in 𝓝[s] y, g z - φ z ≤ g y - φ y := by
      have hbound := (show f =o[𝓝 y] (fun z => ‖z - y‖ ^ 2) from hTay).bound
        (show 0 < ε / 4 by positivity)
      have hb : ∀ᶠ z in 𝓝 y, f z ≤ (ε / 4) * ‖z - y‖ ^ 2 := by
        filter_upwards [hbound] with z hz
        have h1 : ‖(fun w : ℝ⁴ => ‖w - y‖ ^ 2) z‖ = ‖z - y‖ ^ 2 :=
          Real.norm_of_nonneg (sq_nonneg _)
        rw [h1] at hz
        have h2 := (abs_le.mp hz).2
        linarith
      filter_upwards [Filter.Eventually.filter_mono nhdsWithin_le_nhds hb] with z hz
      have h5 : g z - φ z = f z - (ε / 2) * ‖z - y‖ ^ 2 := by
        rw [hφdef]
        dsimp only
        rw [show g z - (Q z + ε / 2 * ‖z - y‖ ^ 2)
            = (g z - Q z) - ε / 2 * ‖z - y‖ ^ 2 from by ring, hfz z]
      have h6 : g y - φ y = 0 := by rw [hφdef]; simp [hQy]
      rw [h5, h6]
      nlinarith [hz, sq_nonneg ‖z - y‖]
    have hv := hvisc.1 φ hφcd y hy htouch
    have hhess : HessOp φ s y = A + ε • (1 : ℝ⁴ →L[ℝ] ℝ⁴) := by
      have h1 : HessOp φ s y = HessOp Q s y + (2 * (ε / 2)) • (1 : ℝ⁴ →L[ℝ] ℝ⁴) := by
        rw [hφdef]
        exact hessOp_add_quadratic (x₀ := y) (x := y) hs hy (ε := ε / 2) hQcdAt
      rw [h1, hQH, show 2 * (ε / 2) = ε by ring]
    rw [hhess] at hv
    simpa only [neg_nonpos] using hv
  -- the supersolution side
  have hsup : ∀ ε : ℝ, 0 < ε → Gop (A + (-ε) • (1 : ℝ⁴ →L[ℝ] ℝ⁴)) ≤ 0 := by
    intro ε hε
    set φ : ℝ⁴ → ℝ := fun z => Q z + (-(ε / 2)) * ‖z - y‖ ^ 2 with hφdef
    have hφcd : ContDiffOn ℝ 2 φ s := by
      rw [hφdef]
      exact hQcd.add ((contDiff_const_mul_norm_sq_sub y (-(ε / 2))).contDiffOn)
    have htouch : ∀ᶠ z in 𝓝[s] y, g y - φ y ≤ g z - φ z := by
      have hbound := (show f =o[𝓝 y] (fun z => ‖z - y‖ ^ 2) from hTay).bound
        (show 0 < ε / 4 by positivity)
      have hb : ∀ᶠ z in 𝓝 y, -(ε / 4) * ‖z - y‖ ^ 2 ≤ f z := by
        filter_upwards [hbound] with z hz
        have h1 : ‖(fun w : ℝ⁴ => ‖w - y‖ ^ 2) z‖ = ‖z - y‖ ^ 2 :=
          Real.norm_of_nonneg (sq_nonneg _)
        rw [h1] at hz
        have h2 := (abs_le.mp hz).1
        linarith
      filter_upwards [Filter.Eventually.filter_mono nhdsWithin_le_nhds hb] with z hz
      have h5 : g y - φ y = 0 := by rw [hφdef]; simp [hQy]
      have h6 : g z - φ z = f z + (ε / 2) * ‖z - y‖ ^ 2 := by
        rw [hφdef]
        dsimp only
        rw [show g z - (Q z + -(ε / 2) * ‖z - y‖ ^ 2)
            = (g z - Q z) + ε / 2 * ‖z - y‖ ^ 2 from by ring, hfz z]
      rw [h5, h6]
      nlinarith [hz, sq_nonneg ‖z - y‖]
    have hv := hvisc.2 φ hφcd y hy htouch
    have hhess : HessOp φ s y = A + (-ε) • (1 : ℝ⁴ →L[ℝ] ℝ⁴) := by
      have h1 : HessOp φ s y = HessOp Q s y + (2 * (-(ε / 2))) • (1 : ℝ⁴ →L[ℝ] ℝ⁴) := by
        rw [hφdef]
        exact hessOp_add_quadratic (x₀ := y) (x := y) hs hy (ε := -(ε / 2)) hQcdAt
      rw [h1, hQH, show 2 * (-(ε / 2)) = -ε by ring]
    rw [hhess] at hv
    simpa only [neg_nonneg] using hv
  -- pass to the limit
  have hzero : (0 : ℝ) • (1 : ℝ⁴ →L[ℝ] ℝ⁴) = 0 := by ext v; simp
  have htend1 : Tendsto (fun n : ℕ => A + ((1 : ℝ) / (n + 1)) • (1 : ℝ⁴ →L[ℝ] ℝ⁴)) atTop
      (𝓝 A) := by
    have h1 : Tendsto (fun n : ℕ => ((1 : ℝ) / (n + 1))) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
    have h2 : Tendsto (fun n : ℕ => ((1 : ℝ) / (n + 1)) • (1 : ℝ⁴ →L[ℝ] ℝ⁴)) atTop
        (𝓝 ((0 : ℝ) • (1 : ℝ⁴ →L[ℝ] ℝ⁴))) := h1.smul tendsto_const_nhds
    have h3 : Tendsto (fun n : ℕ => A + ((1 : ℝ) / (n + 1)) • (1 : ℝ⁴ →L[ℝ] ℝ⁴)) atTop
        (𝓝 (A + (0 : ℝ) • (1 : ℝ⁴ →L[ℝ] ℝ⁴))) := tendsto_const_nhds.add h2
    rw [hzero, add_zero] at h3
    exact h3
  have htend2 : Tendsto (fun n : ℕ => A + (-((1 : ℝ) / (n + 1))) • (1 : ℝ⁴ →L[ℝ] ℝ⁴))
      atTop (𝓝 A) := by
    have h1 : Tendsto (fun n : ℕ => ((1 : ℝ) / (n + 1))) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
    have h2 : Tendsto (fun n : ℕ => (-((1 : ℝ) / (n + 1))) • (1 : ℝ⁴ →L[ℝ] ℝ⁴)) atTop
        (𝓝 ((-(0 : ℝ)) • (1 : ℝ⁴ →L[ℝ] ℝ⁴))) := h1.neg.smul tendsto_const_nhds
    have h0b : (-(0 : ℝ)) • (1 : ℝ⁴ →L[ℝ] ℝ⁴) = 0 := by rw [neg_zero, hzero]
    have h3 : Tendsto (fun n : ℕ => A + (-((1 : ℝ) / (n + 1))) • (1 : ℝ⁴ →L[ℝ] ℝ⁴)) atTop
        (𝓝 (A + (-(0 : ℝ)) • (1 : ℝ⁴ →L[ℝ] ℝ⁴))) := tendsto_const_nhds.add h2
    rw [h0b, add_zero] at h3
    exact h3
  have hge : 0 ≤ Gop A :=
    ge_of_tendsto' ((continuous_Gop.tendsto A).comp htend1)
      (fun n => hsub ((1 : ℝ) / (n + 1)) (by
        have h : (0 : ℝ) < (n : ℝ) + 1 := by positivity
        exact one_div_pos.mpr h))
  have hle : Gop A ≤ 0 :=
    le_of_tendsto' ((continuous_Gop.tendsto A).comp htend2)
      (fun n => hsup ((1 : ℝ) / (n + 1)) (by
        have h : (0 : ℝ) < (n : ℝ) + 1 := by positivity
        exact one_div_pos.mpr h))
  exact le_antisymm hle hge

end
end Submission
