import Mathlib
import Submission.Work.Asymptotics.Kaxis_tile_aux
import Submission.Work.Asymptotics.E4Fun_sub_one_explicit
import Submission.Work.FunnelNumerics.E4_funnel_bounds
import Submission.Work.FunnelNumerics.Delta_funnel_bounds

namespace Work.Asymptotics.Tile

open UpperHalfPlane
open scoped MatrixGroups UpperHalfPlane Manifold

noncomputable section

/-! ## The divisor lower bound on the cusp-`0` tile

For `w` in the cusp-`0` neighbourhood `E = KEpsilon` and `0 < t ≤ Im w / 2` the divisor
`Δ(i/t) (j w - j(i/t))` of the CKMRV kernel is bounded below by `1/4`.

The estimate is *not* an orbit-separation statement: with `z = i/t` one has the identity

  `Δ(z) (j w - j z) = Δ(z) j w - E₄(z)³`     (`Δ · j = E₄³`),

and the two terms are estimated separately.

* `E₄(z)³` is within `O(e^{-2π/t})` of `1`: `‖E₄(z) - 1‖ ≤ 20000 ‖q(z)‖`
  (`E4Fun_sub_one_explicit`) and `‖q(z)‖ = e^{-2π/t} ≤ e^{-8π} ≤ 10^{-5}` because
  `t ≤ Im w / 2 ≤ 1/4` forces `2π/t ≥ 8π ≥ 24`.  Hence `‖E₄(z)³‖ ≥ 1/2`.
* `Δ(z) j w` is tiny: `‖Δ(i t')‖ ≤ e^{-2π t'}` for `t' ≥ 1` (`Delta_funnel_bounds`) applied at
  `t' = 1/t ≥ 4`, while `‖j w‖ = ‖j (S • w)‖ ≤ (27/4) e^{2π Im (S · w)}` on the funnel
  (`S`-invariance of `j` together with `‖E₄‖ ≤ 3/2` and `‖Δ‖ ≥ (1/2) e^{-2π Im}`).  Since
  `Im (S • w) ≤ 1/(2t)` (`tile_im_S_le`) the product is at most `(27/4) e^{-2π} ≤ 1/16`.

`1/2 - 1/16 = 7/16 ≥ 1/4` then gives the claim. -/

/-- `2.7 ≤ e`. -/
private lemma two_seven_le_exp_one : (2.7 : ℝ) ≤ Real.exp 1 := by
  have h : (2.7182818283 : ℝ) ≤ Real.exp 1 := le_of_lt Real.exp_one_gt_d9
  linarith

/-- `10^5 ≤ e^{24}`. -/
private lemma exp_24_ge : (10 : ℝ) ^ 5 ≤ Real.exp 24 := by
  have h : (2.7 : ℝ) ^ 24 ≤ Real.exp 24 := by
    rw [show (24 : ℝ) = ((24 : ℕ) : ℝ) * 1 by norm_num, Real.exp_nat_mul]
    exact pow_le_pow_left₀ (by norm_num) two_seven_le_exp_one 24
  have h2 : (10 : ℝ) ^ 5 ≤ (2.7 : ℝ) ^ 24 := by norm_num
  linarith

/-- `108 ≤ e^{2π}`. -/
private lemma exp_two_pi_ge : (108 : ℝ) ≤ Real.exp (2 * Real.pi) := by
  have h6 : (6 : ℝ) ≤ 2 * Real.pi := by nlinarith [Real.pi_gt_three]
  have h1 : Real.exp 6 ≤ Real.exp (2 * Real.pi) := Real.exp_le_exp.mpr h6
  have h2 : Real.exp 6 = (Real.exp 1) ^ 6 := by
    rw [show (6 : ℝ) = ((6 : ℕ) : ℝ) * 1 by norm_num, Real.exp_nat_mul]
  have h3 : (2.7 : ℝ) ^ 6 ≤ (Real.exp 1) ^ 6 :=
    pow_le_pow_left₀ (by norm_num) two_seven_le_exp_one 6
  have h4 : (108 : ℝ) ≤ (2.7 : ℝ) ^ 6 := by norm_num
  rw [h2] at h1
  linarith

theorem tile_divisor_lower (w : UpperHalfPlane) (hw : w ∈ Work.Asymptotics.KEpsilon) (t : ℝ) (ht : 0 < t)
    (htle : t ≤ w.im / 2) :
    (1 / 4 : ℝ) ≤ ‖Work.Kernels.DeltaFun (Work.Kernels.imagAxis t⁻¹ (inv_pos.mpr ht)) *
      (Work.Kernels.jInvariantFun w -
        Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t⁻¹ (inv_pos.mpr ht)))‖ := by
  have hti : 0 < t⁻¹ := inv_pos.mpr ht
  -- `t ≤ 1/4`, hence `1/t ≥ 4 ≥ 1`
  have hquarter : t ≤ 1 / 4 := by
    have h := Work.Asymptotics.tile_im_le_half hw
    linarith
  have h4 : (4 : ℝ) ≤ t⁻¹ := by
    refine (le_inv_comm₀ (show (0 : ℝ) < 4 by norm_num) ht).mpr ?_
    rw [show ((4 : ℝ))⁻¹ = 1 / 4 by norm_num]
    exact hquarter
  have ht1 : (1 : ℝ) ≤ t⁻¹ := by linarith
  -- the imaginary part of `i/t` and the fact that it is at least `1`
  have hzim : (Work.Kernels.imagAxis t⁻¹ hti).im = t⁻¹ := by
    simp [Work.Kernels.imagAxis]
  have hz1 : (1 : ℝ) ≤ (Work.Kernels.imagAxis t⁻¹ hti).im := by rw [hzim]; exact ht1
  -- `S • w` lies on the funnel
  have hfun : Work.Asymptotics.Funnel (ModularGroup.S • w) :=
    ⟨Work.Asymptotics.S_smul_mem_DomainD hw.1, hw.2⟩
  -- the height of `S • w`
  have hSim : (ModularGroup.S • w).im ≤ (1 / 2) / t :=
    Work.Asymptotics.tile_im_S_le hw ht htle
  have hgap : 1 ≤ t⁻¹ - (ModularGroup.S • w).im := by
    have ht2 : t ≤ 1 / 2 := by linarith
    have hstep : (1 / 2 : ℝ) * t⁻¹ ≤ (1 - t) * t⁻¹ :=
      mul_le_mul_of_nonneg_right (by linarith) (le_of_lt hti)
    have hval : (1 - t) * t⁻¹ = t⁻¹ - 1 := by
      rw [sub_mul, one_mul, mul_inv_cancel₀ (ne_of_gt ht)]
    have hhalf : (1 / 2 : ℝ) / t ≤ t⁻¹ - 1 := by
      calc (1 / 2 : ℝ) / t = (1 / 2) * t⁻¹ := by rw [div_eq_mul_inv]
        _ ≤ (1 - t) * t⁻¹ := hstep
        _ = t⁻¹ - 1 := hval
    linarith
  -- ## Step 1: `E₄(i/t)` is exponentially close to `1`
  have hE4close : ‖Work.Kernels.E4Fun (Work.Kernels.imagAxis t⁻¹ hti) - 1‖ ≤ 1 / 5 := by
    have h := Work.Asymptotics.E4Fun_sub_one_explicit (w := Work.Kernels.imagAxis t⁻¹ hti) hz1
    have hq : ‖Work.Kernels.qParamFun (Work.Kernels.imagAxis t⁻¹ hti)‖ ≤ 1 / (10 : ℝ) ^ 5 := by
      rw [Work.Asymptotics.norm_qParamFun, hzim, Real.exp_neg]
      have h24 : (24 : ℝ) ≤ 2 * Real.pi * t⁻¹ := by nlinarith [Real.pi_gt_three, h4]
      have hexp : Real.exp (24 : ℝ) ≤ Real.exp (2 * Real.pi * t⁻¹) := Real.exp_le_exp.mpr h24
      have hge : (10 : ℝ) ^ 5 ≤ Real.exp (2 * Real.pi * t⁻¹) := le_trans exp_24_ge hexp
      simpa [one_div] using (inv_le_inv₀ (Real.exp_pos _) (by norm_num : (0 : ℝ) < (10:ℝ)^5)).mpr hge
    have h2 : 20000 * ‖Work.Kernels.qParamFun (Work.Kernels.imagAxis t⁻¹ hti)‖ ≤ 1 / 5 := by
      have := mul_le_mul_of_nonneg_left hq (by norm_num : (0 : ℝ) ≤ 20000)
      linarith
    linarith
  have hE4low : (4 / 5 : ℝ) ≤ ‖Work.Kernels.E4Fun (Work.Kernels.imagAxis t⁻¹ hti)‖ := by
    have hsub : (1 : ℝ)
        ≤ ‖Work.Kernels.E4Fun (Work.Kernels.imagAxis t⁻¹ hti)‖
          + ‖Work.Kernels.E4Fun (Work.Kernels.imagAxis t⁻¹ hti) - 1‖ := by
      have h := norm_sub_le (Work.Kernels.E4Fun (Work.Kernels.imagAxis t⁻¹ hti))
        (Work.Kernels.E4Fun (Work.Kernels.imagAxis t⁻¹ hti) - 1)
      rw [show Work.Kernels.E4Fun (Work.Kernels.imagAxis t⁻¹ hti)
          - (Work.Kernels.E4Fun (Work.Kernels.imagAxis t⁻¹ hti) - 1) = 1 by ring, norm_one] at h
      exact h
    linarith
  have hE43 : (1 / 2 : ℝ) ≤ ‖Work.Kernels.E4Fun (Work.Kernels.imagAxis t⁻¹ hti) ^ 3‖ := by
    rw [norm_pow]
    calc (1 / 2 : ℝ) ≤ (4 / 5 : ℝ) ^ 3 := by norm_num
      _ ≤ ‖Work.Kernels.E4Fun (Work.Kernels.imagAxis t⁻¹ hti)‖ ^ 3 :=
          pow_le_pow_left₀ (by norm_num) hE4low 3
  -- ## Step 2: `‖Δ(i/t)‖ ≤ e^{-2π/t}`
  have hΔz : ‖Work.Kernels.DeltaFun (Work.Kernels.imagAxis t⁻¹ hti)‖
      ≤ Real.exp (-(2 * Real.pi * t⁻¹)) :=
    (Work.FunnelNumerics.Delta_funnel_bounds).2 t⁻¹ hti ht1
  -- ## Step 3: `‖j w‖ ≤ (27/4) e^{2π Im (S · w)}`
  have hjw : ‖Work.Kernels.jInvariantFun w‖
      ≤ (27 / 4) * Real.exp (2 * Real.pi * (ModularGroup.S • w).im) := by
    rw [← Work.Kernels.KernelFacts.jInvariantFun_S_smul w]
    have hΔlow : (1 / 2 : ℝ) * Real.exp (-(2 * Real.pi * (ModularGroup.S • w).im))
        ≤ ‖Work.Kernels.DeltaFun (ModularGroup.S • w)‖ := by
      rw [← Work.Asymptotics.norm_qParamFun]
      exact (Work.FunnelNumerics.Delta_funnel_bounds).1 (ModularGroup.S • w) hfun.2
    have hE4b : ‖Work.Kernels.E4Fun (ModularGroup.S • w)‖ ≤ (3 / 2 : ℝ) :=
      (Work.FunnelNumerics.E4_funnel_bounds).1 (ModularGroup.S • w) hfun
    have hnum : ‖Work.Kernels.E4Fun (ModularGroup.S • w) ^ 3‖ ≤ (3 / 2 : ℝ) ^ 3 := by
      rw [norm_pow]
      exact pow_le_pow_left₀ (norm_nonneg _) hE4b 3
    have hpos : 0 < (1 / 2 : ℝ) * Real.exp (-(2 * Real.pi * (ModularGroup.S • w).im)) := by
      positivity
    have hcoe : Work.Kernels.jInvariantFun (ModularGroup.S • w)
        = Work.Kernels.E4Fun (ModularGroup.S • w) ^ 3
            / Work.Kernels.DeltaFun (ModularGroup.S • w) := rfl
    rw [hcoe, norm_div]
    have hinv : (‖Work.Kernels.DeltaFun (ModularGroup.S • w)‖)⁻¹
        ≤ ((1 / 2 : ℝ) * Real.exp (-(2 * Real.pi * (ModularGroup.S • w).im)))⁻¹ :=
      inv_anti₀ hpos hΔlow
    have hrec : ((1 / 2 : ℝ) * Real.exp (-(2 * Real.pi * (ModularGroup.S • w).im)))⁻¹
        = 2 * Real.exp (2 * Real.pi * (ModularGroup.S • w).im) := by
      rw [Real.exp_neg]; field_simp
    rw [hrec] at hinv
    calc ‖Work.Kernels.E4Fun (ModularGroup.S • w) ^ 3‖
          / ‖Work.Kernels.DeltaFun (ModularGroup.S • w)‖
        = ‖Work.Kernels.E4Fun (ModularGroup.S • w) ^ 3‖
            * (‖Work.Kernels.DeltaFun (ModularGroup.S • w)‖)⁻¹ := by ring
      _ ≤ (3 / 2) ^ 3 * (2 * Real.exp (2 * Real.pi * (ModularGroup.S • w).im)) :=
          mul_le_mul hnum hinv (by positivity) (by positivity)
      _ = (27 / 4) * Real.exp (2 * Real.pi * (ModularGroup.S • w).im) := by norm_num; ring
  -- ## Step 4: `‖Δ(i/t) j w‖ ≤ 1/16`
  have hprod : ‖Work.Kernels.DeltaFun (Work.Kernels.imagAxis t⁻¹ hti)
      * Work.Kernels.jInvariantFun w‖ ≤ 1 / 16 := by
    rw [norm_mul]
    have h1 : ‖Work.Kernels.DeltaFun (Work.Kernels.imagAxis t⁻¹ hti)‖
          * ‖Work.Kernels.jInvariantFun w‖
        ≤ Real.exp (-(2 * Real.pi * t⁻¹))
          * ((27 / 4) * Real.exp (2 * Real.pi * (ModularGroup.S • w).im)) :=
      mul_le_mul hΔz hjw (norm_nonneg _) (by positivity)
    have h2 : Real.exp (-(2 * Real.pi * t⁻¹))
          * ((27 / 4) * Real.exp (2 * Real.pi * (ModularGroup.S • w).im))
        = (27 / 4) * Real.exp (-(2 * Real.pi * (t⁻¹ - (ModularGroup.S • w).im))) := by
      rw [show Real.exp (-(2 * Real.pi * t⁻¹))
            * ((27 / 4) * Real.exp (2 * Real.pi * (ModularGroup.S • w).im))
          = (27 / 4) * (Real.exp (-(2 * Real.pi * t⁻¹))
              * Real.exp (2 * Real.pi * (ModularGroup.S • w).im)) by ring, ← Real.exp_add]
      congr 1
      ring_nf
    have h3 : Real.exp (-(2 * Real.pi * (t⁻¹ - (ModularGroup.S • w).im)))
        ≤ Real.exp (-(2 * Real.pi)) := by
      apply Real.exp_le_exp.mpr
      nlinarith [Real.pi_pos, hgap]
    have h4 : Real.exp (-(2 * Real.pi)) ≤ 1 / 108 := by
      have h := (inv_le_inv₀ (Real.exp_pos (2 * Real.pi)) (by norm_num : (0 : ℝ) < 108)).mpr
        exp_two_pi_ge
      rw [Real.exp_neg, show (1 : ℝ) / 108 = ((108 : ℝ))⁻¹ by norm_num]
      exact h
    have h5 : (27 / 4) * Real.exp (-(2 * Real.pi)) ≤ 1 / 16 := by
      have h := mul_le_mul_of_nonneg_left h4 (by norm_num : (0 : ℝ) ≤ 27 / 4)
      linarith
    calc ‖Work.Kernels.DeltaFun (Work.Kernels.imagAxis t⁻¹ hti)‖
          * ‖Work.Kernels.jInvariantFun w‖
        ≤ Real.exp (-(2 * Real.pi * t⁻¹))
          * ((27 / 4) * Real.exp (2 * Real.pi * (ModularGroup.S • w).im)) := h1
      _ = (27 / 4) * Real.exp (-(2 * Real.pi * (t⁻¹ - (ModularGroup.S • w).im))) := h2
      _ ≤ (27 / 4) * Real.exp (-(2 * Real.pi)) := mul_le_mul_of_nonneg_left h3 (by norm_num)
      _ ≤ 1 / 16 := h5
  -- ## Step 5: the divisor identity
  have hkey : Work.Kernels.DeltaFun (Work.Kernels.imagAxis t⁻¹ hti)
        * (Work.Kernels.jInvariantFun w
            - Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t⁻¹ hti))
      = Work.Kernels.DeltaFun (Work.Kernels.imagAxis t⁻¹ hti) * Work.Kernels.jInvariantFun w
        - Work.Kernels.E4Fun (Work.Kernels.imagAxis t⁻¹ hti) ^ 3 := by
    rw [mul_sub, Work.Kernels.ClassicalFacts.DeltaFun_mul_jInvariantFun]
  rw [hkey]
  calc (1 / 4 : ℝ) ≤ 1 / 2 - 1 / 16 := by norm_num
    _ ≤ ‖Work.Kernels.E4Fun (Work.Kernels.imagAxis t⁻¹ hti) ^ 3‖
          - ‖Work.Kernels.DeltaFun (Work.Kernels.imagAxis t⁻¹ hti)
              * Work.Kernels.jInvariantFun w‖ := by linarith
    _ ≤ ‖Work.Kernels.E4Fun (Work.Kernels.imagAxis t⁻¹ hti) ^ 3
          - Work.Kernels.DeltaFun (Work.Kernels.imagAxis t⁻¹ hti)
              * Work.Kernels.jInvariantFun w‖ := norm_sub_norm_le _ _
    _ = ‖Work.Kernels.DeltaFun (Work.Kernels.imagAxis t⁻¹ hti)
            * Work.Kernels.jInvariantFun w
          - Work.Kernels.E4Fun (Work.Kernels.imagAxis t⁻¹ hti) ^ 3‖ := norm_sub_rev _ _

end

end Work.Asymptotics.Tile
