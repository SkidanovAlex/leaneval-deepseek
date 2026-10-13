import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS_StreamBdry.Basic
import Submission.Work.FTS_StreamBdry.SB25.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_StreamBdry.SB25.dq1_facts` — the first log-difference quotient

`Dq1Facts g L B` says: if `g` is differentiable on `[L, ∞)` (`L > 0`) and `|z g'(z)| ≤ B`
there, then for every `h > 0` the first difference quotient along the multiplicative ray
`z ↦ z e^h` is bounded by `B`, and it converges to `z g'(z)` as `h → 0⁺`.

The proof is the mean value theorem applied to the one-variable function
`t ↦ g (z e^t)`, whose derivative is `g'(z e^t) · z e^t`; the hypothesis `|z g'(z)| ≤ B`
controls it along the whole ray (since `e^t ≥ 1` for `t ≥ 0`).  The endpoint limit is
exactly the statement that this derivative at `t = 0` is `z g'(z)`.
-/

namespace Work.FTS_StreamBdry.SB25

theorem dq1_facts (g : ℝ → ℝ) (L B : ℝ) :
    Work.FTS_StreamBdry.SB25.Dq1Facts g L B := by
  unfold Work.FTS_StreamBdry.SB25.Dq1Facts
  intro hL hdiff hbnd
  refine ⟨?_, ?_⟩
  · -- first conjunct: the difference quotient is bounded by `B`
    intro h hh z hz
    have hz' : 0 < z := lt_of_lt_of_le hL hz
    -- the ray function `t ↦ g (z e^t)`
    let F : ℝ → ℝ := fun t => g (Real.exp t * z)
    have hFdiff : ∀ t ∈ Set.Icc (0 : ℝ) h, DifferentiableAt ℝ F t := by
      intro t ht
      have hle : L ≤ Real.exp t * z :=
        le_trans hz (le_mul_of_one_le_left hz'.le (Real.one_le_exp ht.1))
      exact (hdiff _ hle).comp t (Real.differentiableAt_exp.mul_const z)
    have hFderiv : ∀ t : ℝ, 0 ≤ t →
        deriv F t = deriv g (Real.exp t * z) * (Real.exp t * z) := by
      intro t ht
      have hle : L ≤ Real.exp t * z :=
        le_trans hz (le_mul_of_one_le_left hz'.le (Real.one_le_exp ht))
      have h1 : HasDerivAt (fun s : ℝ => Real.exp s * z) (Real.exp t * z) t := by
        simpa using (Real.hasDerivAt_exp t).mul_const z
      have h2 : DifferentiableAt ℝ g (Real.exp t * z) := hdiff _ hle
      have h3 : HasDerivAt F (deriv g (Real.exp t * z) * (Real.exp t * z)) t := by
        simpa [F, Function.comp_def] using (h2.hasDerivAt).comp t h1
      exact h3.deriv
    have hbound : ∀ t ∈ Set.Icc (0 : ℝ) h, ‖deriv F t‖ ≤ B := by
      intro t ht
      rw [hFderiv t ht.1, Real.norm_eq_abs]
      have hle : L ≤ Real.exp t * z :=
        le_trans hz (le_mul_of_one_le_left hz'.le (Real.one_le_exp ht.1))
      have hb := hbnd (Real.exp t * z) hle
      rw [mul_comm (Real.exp t * z) (deriv g (Real.exp t * z))] at hb
      exact hb
    have hMVT := Convex.norm_image_sub_le_of_norm_deriv_le (f := F) (s := Set.Icc (0 : ℝ) h)
      (x := 0) (y := h) (C := B) hFdiff hbound (convex_Icc 0 h)
      ⟨le_rfl, hh.le⟩ ⟨hh.le, le_rfl⟩
    have hmain : |F h - F 0| ≤ B * h := by
      simpa [Real.norm_eq_abs, sub_zero, Real.norm_of_nonneg hh.le] using hMVT
    have hFh : F h = g (Real.exp h * z) := rfl
    have hF0 : F 0 = g z := by simp [F]
    rw [hFh, hF0] at hmain
    rw [abs_div, abs_of_pos hh]
    exact (div_le_iff₀ hh).mpr hmain
  · -- second conjunct: the difference quotient tends to `z g'(z)` as `h → 0⁺`
    intro z hz
    have hd : HasDerivAt (fun t : ℝ => g (Real.exp t * z)) (z * deriv g z) 0 := by
      have h1 : HasDerivAt (fun s : ℝ => Real.exp s * z) (Real.exp 0 * z) 0 := by
        simpa using (Real.hasDerivAt_exp 0).mul_const z
      have h2 : DifferentiableAt ℝ g (Real.exp 0 * z) := by
        simpa using hdiff z hz.le
      have hgoal : HasDerivAt (fun t : ℝ => g (Real.exp t * z))
          (deriv g (Real.exp 0 * z) * (Real.exp 0 * z)) 0 := by
        simpa [Function.comp_def] using (h2.hasDerivAt).comp 0 h1
      convert hgoal using 1
      rw [Real.exp_zero, one_mul, mul_comm]
    -- `hd.tendsto_slope_zero_right` is the limit of `h ↦ h⁻¹ • (g (z e^h) - g z)`; rewrite
    -- it into the stated division form.
    have key := hd.tendsto_slope_zero_right
    convert key using 1
    · ext h
      simp [div_eq_mul_inv, mul_comm]

end Work.FTS_StreamBdry.SB25
