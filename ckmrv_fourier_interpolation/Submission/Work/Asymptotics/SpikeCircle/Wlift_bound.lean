import Mathlib
import Submission.Work.Asymptotics.SpikeCircle.SpikeDefs
import Submission.Work.Asymptotics.SpikeCircle.jInvariantFunUpperDisc
import Submission.Work.Asymptotics.SpikeCircle.jInvariantFun_eq_iff_disc
import Submission.Work.Asymptotics.SpikeCircle.Wlift_id
import Submission.Work.Asymptotics.SpikeCircle.Wlift_differentiableOn
import Submission.Work.Asymptotics.SpikeCircle.Wlift_vanishing
import Submission.Work.Asymptotics.SpikeCircle.spikeCircleBound

noncomputable section
open UpperHalfPlane
open scoped Topology Manifold

namespace Work.Asymptotics.SpikeCircle

open Work.Kernels Work.Residues

/-! ## Elementary geometry of the spike sphere

Throughout, `Wlift ℓ d τ ·` is the lifted spike
`Δ(τ)Δ(w)·(AfunFun ℓ d τ w - Tleft τ w)`, which is holomorphic on the upper half plane and
vanishes at the three points `τ`, `τ ± 1`.  The estimate below is the CKMRV Lemma 4.12 input
(the circle bound `‖Kfun‖ ≤ C (scale τ)^N`) turned into a bound for `Wlift` on the circle of
radius `29/20` around `τ`, followed by the Schwarz-type three-zeros argument of
`Work.Analysis.ThreeZeros.three_zeros_bound_ball` which produces the three linear factors
`‖w-τ‖‖w-(τ+1)‖‖w-(τ-1)‖`.
-/

/-- On the sphere `‖w - τ‖ = 29/20` the product of the distances to `τ`, `τ+1`, `τ-1` is at
least `(9/20)^3`. -/
lemma sphere_prod_ge (τ : UpperHalfPlane) {w : ℂ} (hw : ‖w - (τ : ℂ)‖ = 29 / 20) :
    (9 / 20 : ℝ) ^ 3
      ≤ ‖w - (τ : ℂ)‖ * ‖w - ((τ : ℂ) + 1)‖ * ‖w - ((τ : ℂ) - 1)‖ := by
  have h₁ : (9 / 20 : ℝ) ≤ ‖w - ((τ : ℂ) + 1)‖ := by
    have h : w - ((τ : ℂ) + 1) = (w - (τ : ℂ)) - 1 := by ring
    rw [h]
    have h2 : |‖w - (τ : ℂ)‖ - ‖(1 : ℂ)‖| ≤ ‖(w - (τ : ℂ)) - 1‖ :=
      abs_norm_sub_norm_le _ _
    rw [norm_one, hw] at h2
    have : |(29 : ℝ) / 20 - 1| = 9 / 20 := by norm_num
    rw [this] at h2
    exact h2
  have h₂ : (9 / 20 : ℝ) ≤ ‖w - ((τ : ℂ) - 1)‖ := by
    have h : w - ((τ : ℂ) - 1) = (w - (τ : ℂ)) + 1 := by ring
    rw [h]
    have h2 : |‖w - (τ : ℂ)‖ - ‖(-(1 : ℂ))‖| ≤ ‖(w - (τ : ℂ)) - (-(1 : ℂ))‖ :=
      abs_norm_sub_norm_le _ _
    rw [norm_neg, norm_one, hw] at h2
    have h3 : (w - (τ : ℂ)) - (-(1 : ℂ)) = (w - (τ : ℂ)) + 1 := by ring
    rw [h3] at h2
    have : |(29 : ℝ) / 20 - 1| = 9 / 20 := by norm_num
    rw [this] at h2
    exact h2
  have h₀ : (9 / 20 : ℝ) ≤ ‖w - (τ : ℂ)‖ := by rw [hw]; norm_num
  have hpos : (0 : ℝ) ≤ (9 / 20) ^ 3 := by norm_num
  calc (9 / 20 : ℝ) ^ 3 = (9 / 20) * (9 / 20) * (9 / 20) := by ring
    _ ≤ ‖w - (τ : ℂ)‖ * ‖w - ((τ : ℂ) + 1)‖ * ‖w - ((τ : ℂ) - 1)‖ := by
        gcongr

/-- The imaginary part of a point of the spike sphere is at least `11/20`. -/
lemma im_ge_of_sphere (τ ζ : UpperHalfPlane) (hτ : (2 : ℝ) ≤ τ.im)
    (hζ : ‖(ζ : ℂ) - (τ : ℂ)‖ = 29 / 20) :
    11 / 20 ≤ ζ.im := by
  have h1 : |ζ.im - τ.im| ≤ ‖(ζ : ℂ) - (τ : ℂ)‖ := by
    have h : ((ζ : ℂ) - (τ : ℂ)).im = ζ.im - τ.im := by simp
    rw [← h]
    exact Complex.abs_im_le_norm _
  rw [hζ] at h1
  have := (abs_le.mp h1).1
  linarith

/-- The imaginary part of a point of the closed spike disc is at least `11/20`; in particular it
is positive, so the disc lies in the upper half plane. -/
lemma im_pos_of_ball (τ : UpperHalfPlane) (hτ : (2 : ℝ) ≤ τ.im) {w : ℂ}
    (hw : ‖w - (τ : ℂ)‖ ≤ 29 / 20) :
    0 < w.im := by
  have h1 : |w.im - τ.im| ≤ ‖w - (τ : ℂ)‖ := by
    have h : (w - (τ : ℂ)).im = w.im - τ.im := by simp
    rw [← h]
    exact Complex.abs_im_le_norm _
  have := (abs_le.mp (le_trans h1 hw)).1
  linarith

/-- `j τ ≠ j ζ` for `ζ` on the spike sphere. -/
lemma j_ne_of_sphere {τ ζ : UpperHalfPlane} (hτ : Work.Asymptotics.Funnel τ)
    (hζ : ‖(ζ : ℂ) - (τ : ℂ)‖ = 29 / 20) :
    Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun ζ := by
  intro h
  have hle : ‖(ζ : ℂ) - (τ : ℂ)‖ ≤ 29 / 20 := le_of_eq hζ
  rcases (jInvariantFun_eq_iff_disc hτ hle).mp h with h' | h' | h'
  · rw [h'] at hζ
    norm_num at hζ
  · rw [h', coe_one_vadd] at hζ
    norm_num at hζ
  · rw [h', coe_neg_one_vadd] at hζ
    norm_num at hζ

/-- The principal part `PP` is bounded on the spike sphere: `‖PP τ ζ‖ ≤ 20/(9π)`. -/
lemma PP_bound_sphere (τ ζ : UpperHalfPlane) (hζ : ‖(ζ : ℂ) - (τ : ℂ)‖ = 29 / 20) :
    ‖PP τ ζ‖ ≤ 20 / (9 * Real.pi) := by
  have h₁ : (9 / 20 : ℝ) ≤ ‖(ζ : ℂ) - ((τ : ℂ) + 1)‖ := by
    have h : (ζ : ℂ) - ((τ : ℂ) + 1) = ((ζ : ℂ) - (τ : ℂ)) - 1 := by ring
    rw [h]
    have h2 : |‖(ζ : ℂ) - (τ : ℂ)‖ - ‖(1 : ℂ)‖| ≤ ‖((ζ : ℂ) - (τ : ℂ)) - 1‖ :=
      abs_norm_sub_norm_le _ _
    rw [norm_one, hζ] at h2
    have : |(29 : ℝ) / 20 - 1| = 9 / 20 := by norm_num
    rwa [this] at h2
  have h₂ : (9 / 20 : ℝ) ≤ ‖(ζ : ℂ) - ((τ : ℂ) - 1)‖ := by
    have h : (ζ : ℂ) - ((τ : ℂ) - 1) = ((ζ : ℂ) - (τ : ℂ)) - (-(1 : ℂ)) := by ring
    rw [h]
    have h2 : |‖(ζ : ℂ) - (τ : ℂ)‖ - ‖(-(1 : ℂ))‖| ≤ ‖((ζ : ℂ) - (τ : ℂ)) - (-(1 : ℂ))‖ :=
      abs_norm_sub_norm_le _ _
    rw [norm_neg, norm_one, hζ] at h2
    have : |(29 : ℝ) / 20 - 1| = 9 / 20 := by norm_num
    rwa [this] at h2
  rw [PP, norm_mul]
  have hnorm : ‖(1 / (2 * (Real.pi : ℂ)))‖ = 1 / (2 * Real.pi) := by
    rw [norm_div, norm_one, norm_mul, Complex.norm_ofNat, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  rw [hnorm]
  have hmain : ‖(1 : ℂ) / ((ζ : ℂ) - ((τ : ℂ) - 1)) - 1 / ((ζ : ℂ) - ((τ : ℂ) + 1))‖
      ≤ 20 / 9 + 20 / 9 := by
    refine le_trans (norm_sub_le _ _) ?_
    rw [norm_div, norm_div, norm_one]
    have e1 : 1 / ‖(ζ : ℂ) - ((τ : ℂ) - 1)‖ ≤ 1 / ((9 : ℝ) / 20) :=
      one_div_le_one_div_of_le (by norm_num) h₂
    have e2 : 1 / ‖(ζ : ℂ) - ((τ : ℂ) + 1)‖ ≤ 1 / ((9 : ℝ) / 20) :=
      one_div_le_one_div_of_le (by norm_num) h₁
    have h9 : 1 / ((9 : ℝ) / 20) = 20 / 9 := by norm_num
    rw [h9] at e1 e2
    linarith
  calc (1 / (2 * Real.pi)) * ‖(1 : ℂ) / ((ζ : ℂ) - ((τ : ℂ) - 1)) - 1 / ((ζ : ℂ) - ((τ : ℂ) + 1))‖
      ≤ (1 / (2 * Real.pi)) * (20 / 9 + 20 / 9) :=
        mul_le_mul_of_nonneg_left hmain (by positivity)
    _ = 20 / (9 * Real.pi) := by field_simp; norm_num

/-- **The spike bound on the circle.**  Assuming the CKMRV circle bound for `Kfun`, the lifted
spike on the circle `‖ζ - τ‖ = 29/20` is bounded by `C (scale τ)^N exp (-2π Im τ)`. -/
lemma Wlift_sphere_bound (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (hcrux : ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧ ∀ (τ ζ : UpperHalfPlane), Work.Asymptotics.Funnel τ →
      ‖(ζ : ℂ) - (τ : ℂ)‖ = 29 / 20 →
      Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun ζ →
      ‖Work.Kernels.Kfun ℓ d τ ζ‖ ≤ C * (Work.Kernels.scale τ) ^ N) :
    ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧ ∀ (τ ζ : UpperHalfPlane), Work.Asymptotics.Funnel τ →
      ‖(ζ : ℂ) - (τ : ℂ)‖ = 29 / 20 →
      ‖Wlift ℓ d τ (ζ : ℂ)‖ ≤ C * (Work.Kernels.scale τ) ^ N
        * Real.exp (-(2 * Real.pi * τ.im)) := by
  obtain ⟨C₀, N₀, hC₀, hN₀, hK⟩ := hcrux
  obtain ⟨cΔ, CΔ, hcΔ, hCΔ, hΔ⟩ := DeltaFunBoundsHalf
  obtain ⟨CJ, hCJ, hJ⟩ := jInvariantFunUpperDisc
  have hApos : 0 < CΔ * CΔ * CJ * (C₀ + 20 / (9 * Real.pi)) * Real.exp (2 * Real.pi * (29 / 20)) := by
    have hπ : 0 < 20 / (9 * Real.pi) := by positivity
    have h1 : 0 < C₀ + 20 / (9 * Real.pi) := by linarith
    exact mul_pos (mul_pos (mul_pos (mul_pos hCΔ hCΔ) hCJ) h1) (Real.exp_pos _)
  refine ⟨CΔ * CΔ * CJ * (C₀ + 20 / (9 * Real.pi)) * Real.exp (2 * Real.pi * (29 / 20)), N₀,
    hApos, hN₀, fun τ ζ hτ hζ => ?_⟩
  have hτ2 : (2 : ℝ) ≤ τ.im := hτ.2
  have hhalfτ : (1 / 2 : ℝ) ≤ τ.im := by linarith
  have hζim : τ.im - 29 / 20 ≤ ζ.im := by
    have h1 : |ζ.im - τ.im| ≤ (29 : ℝ) / 20 := by
      have h := Complex.abs_im_le_norm ((ζ : ℂ) - (τ : ℂ))
      have h2 : ((ζ : ℂ) - (τ : ℂ)).im = ζ.im - τ.im := by simp
      rw [h2, hζ] at h
      exact h
    have h2 := (abs_le.mp h1).1
    linarith
  have hhalfζ : (1 / 2 : ℝ) ≤ ζ.im := by
    have h := im_ge_of_sphere τ ζ hτ2 hζ
    linarith
  have hjne := j_ne_of_sphere hτ hζ
  set x : ℝ := Real.exp (-(2 * Real.pi * τ.im)) with hx
  set y : ℝ := Real.exp (2 * Real.pi * τ.im) with hy
  set zz : ℝ := Real.exp (-(2 * Real.pi * ζ.im)) with hzz
  set s : ℝ := (Work.Kernels.scale τ) ^ N₀ with hs
  have hxy : x * y = 1 := by
    rw [hx, hy, ← Real.exp_add]
    norm_num
  have hz_le : zz ≤ Real.exp (2 * Real.pi * (29 / 20)) * x := by
    rw [hzz, hx, ← Real.exp_add]
    exact Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos, hζim])
  have hΔτ : ‖DeltaFun τ‖ ≤ CΔ * x := by
    rw [hx]; exact (hΔ τ hhalfτ).2
  have hΔζ : ‖DeltaFun ζ‖ ≤ CΔ * zz := by
    rw [hzz]; exact (hΔ ζ hhalfζ).2
  have hJζ : ‖Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun ζ‖ ≤ CJ * y := by
    rw [hy]; exact hJ τ ζ hτ (le_of_eq hζ)
  have hsc : (1 : ℝ) ≤ s := by
    rw [hs]; exact Real.one_le_rpow (Work.Kernels.one_le_scale τ) hN₀
  have hKb : ‖Work.Kernels.Kfun ℓ d τ ζ - PP τ ζ‖
      ≤ (C₀ + 20 / (9 * Real.pi)) * s := by
    have h1 : ‖Work.Kernels.Kfun ℓ d τ ζ - PP τ ζ‖ ≤ C₀ * s + 20 / (9 * Real.pi) := by
      rw [hs]
      exact le_trans (norm_sub_le _ _)
        (add_le_add (hK τ ζ hτ hζ hjne) (PP_bound_sphere τ ζ hζ))
    have h2 : C₀ * s + 20 / (9 * Real.pi) ≤ (C₀ + 20 / (9 * Real.pi)) * s := by
      have hc : (0 : ℝ) ≤ 20 / (9 * Real.pi) := by positivity
      have h3 := mul_le_mul_of_nonneg_left hsc hc
      have h4 : C₀ * s + 20 / (9 * Real.pi) ≤ C₀ * s + (20 / (9 * Real.pi)) * s := by linarith
      calc C₀ * s + 20 / (9 * Real.pi) ≤ C₀ * s + (20 / (9 * Real.pi)) * s := h4
        _ = (C₀ + 20 / (9 * Real.pi)) * s := by ring
    linarith
  rw [Wlift_id ℓ d hd τ ζ hjne, norm_mul, norm_mul, norm_mul]
  have hstep : ‖DeltaFun τ‖ * ‖DeltaFun ζ‖
        * (‖Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun ζ‖
          * ‖Work.Kernels.Kfun ℓ d τ ζ - PP τ ζ‖)
      ≤ (CΔ * x) * (CΔ * zz) * ((CJ * y) * ((C₀ + 20 / (9 * Real.pi)) * s)) := by
    gcongr
  refine le_trans hstep ?_
  calc (CΔ * x) * (CΔ * zz) * ((CJ * y) * ((C₀ + 20 / (9 * Real.pi)) * s))
      = (CΔ * CΔ * CJ * (C₀ + 20 / (9 * Real.pi)) * s) * (x * y) * zz := by ring
    _ = (CΔ * CΔ * CJ * (C₀ + 20 / (9 * Real.pi)) * s) * zz := by rw [hxy]; ring
    _ ≤ (CΔ * CΔ * CJ * (C₀ + 20 / (9 * Real.pi)) * s)
          * (Real.exp (2 * Real.pi * (29 / 20)) * x) :=
        mul_le_mul_of_nonneg_left hz_le (by positivity)
    _ = (CΔ * CΔ * CJ * (C₀ + 20 / (9 * Real.pi)) * Real.exp (2 * Real.pi * (29 / 20))) * s * x := by
        ring

/-- The imaginary part of a point of the spike sphere is positive (for `τ` in the funnel). -/
lemma im_pos_of_sphere (τ : UpperHalfPlane) (hτ : (2 : ℝ) ≤ τ.im) {w : ℂ}
    (hw : ‖w - (τ : ℂ)‖ = 29 / 20) :
    0 < w.im := by
  have h1 : |w.im - τ.im| ≤ ‖w - (τ : ℂ)‖ := by
    have h : (w - (τ : ℂ)).im = w.im - τ.im := by simp
    rw [← h]
    exact Complex.abs_im_le_norm _
  rw [hw] at h1
  have := (abs_le.mp h1).1
  linarith

/-- `Wlift ℓ d τ ·` is holomorphic on a neighbourhood of the closed spike disc. -/
lemma wlift_DiffContOnCl (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (τ : UpperHalfPlane) (hτ : (2 : ℝ) ≤ τ.im) :
    DiffContOnCl ℂ (Wlift ℓ d τ) (Metric.ball (τ : ℂ) (29 / 20)) := by
  refine ⟨?_, ?_⟩
  · refine (Wlift_differentiableOn ℓ d hd τ).mono ?_
    intro w hw
    exact im_pos_of_ball τ hτ (le_of_lt (by rwa [Metric.mem_ball, dist_eq_norm] at hw))
  · refine ((Wlift_differentiableOn ℓ d hd τ).continuousOn).mono ?_
    intro w hw
    have h1 : w ∈ Metric.closedBall (τ : ℂ) (29 / 20) :=
      closure_minimal Metric.ball_subset_closedBall Metric.isClosed_closedBall hw
    exact im_pos_of_ball τ hτ (by rwa [Metric.mem_closedBall, dist_eq_norm] at h1)

/-- **The spike bound on the closed disc.**  Assuming the CKMRV circle bound for `Kfun`, the
lifted spike is bounded by `C (scale τ)^N exp (-2π Im τ)` on `‖w - τ‖ ≤ 29/20`. -/
lemma Wlift_disc_bound (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (hcrux : ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧ ∀ (τ ζ : UpperHalfPlane), Work.Asymptotics.Funnel τ →
      ‖(ζ : ℂ) - (τ : ℂ)‖ = 29 / 20 →
      Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun ζ →
      ‖Work.Kernels.Kfun ℓ d τ ζ‖ ≤ C * (Work.Kernels.scale τ) ^ N) :
    ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧ ∀ (τ : UpperHalfPlane) (w : ℂ), Work.Asymptotics.Funnel τ →
      ‖w - (τ : ℂ)‖ ≤ 29 / 20 →
      ‖Wlift ℓ d τ w‖ ≤ C * (Work.Kernels.scale τ) ^ N * Real.exp (-(2 * Real.pi * τ.im)) := by
  obtain ⟨A, N, hA, hN, hsph⟩ := Wlift_sphere_bound ℓ d hd hcrux
  refine ⟨max A 1, N, lt_of_lt_of_le zero_lt_one (le_max_right _ _), hN, fun τ w hτ hw => ?_⟩
  have hτ2 : (2 : ℝ) ≤ τ.im := hτ.2
  by_cases hcase : ‖w - (τ : ℂ)‖ = 29 / 20
  · have him : 0 < w.im := im_pos_of_sphere τ hτ2 hcase
    have h1 := hsph τ ⟨w, him⟩ hτ hcase
    have h2 : A * (Work.Kernels.scale τ) ^ N * Real.exp (-(2 * Real.pi * τ.im))
        ≤ max A 1 * (Work.Kernels.scale τ) ^ N * Real.exp (-(2 * Real.pi * τ.im)) := by
      apply mul_le_mul_of_nonneg_right _ (le_of_lt (Real.exp_pos _))
      apply mul_le_mul_of_nonneg_right _
        (Real.rpow_nonneg (le_of_lt (Work.Kernels.scale_pos τ)) N)
      exact le_max_left A 1
    exact le_trans h1 h2
  · have hlt : ‖w - (τ : ℂ)‖ < 29 / 20 := lt_of_le_of_ne hw hcase
    have hball : w ∈ Metric.ball (τ : ℂ) (29 / 20) := by
      rwa [Metric.mem_ball, dist_eq_norm]
    have hfront : ∀ u ∈ frontier (Metric.ball (τ : ℂ) (29 / 20)),
        ‖Wlift ℓ d τ u‖ ≤ max A 1 * (Work.Kernels.scale τ) ^ N
          * Real.exp (-(2 * Real.pi * τ.im)) := by
      intro u hu
      have hsphere : u ∈ Metric.sphere (τ : ℂ) (29 / 20) := Metric.frontier_ball_subset_sphere hu
      have hnorm : ‖u - (τ : ℂ)‖ = 29 / 20 := by
        rwa [Metric.mem_sphere, dist_eq_norm] at hsphere
      have him : 0 < u.im := im_pos_of_sphere τ hτ2 hnorm
      have h1 := hsph τ ⟨u, him⟩ hτ hnorm
      have h2 : A * (Work.Kernels.scale τ) ^ N * Real.exp (-(2 * Real.pi * τ.im))
          ≤ max A 1 * (Work.Kernels.scale τ) ^ N * Real.exp (-(2 * Real.pi * τ.im)) := by
        apply mul_le_mul_of_nonneg_right _ (le_of_lt (Real.exp_pos _))
        apply mul_le_mul_of_nonneg_right _
          (Real.rpow_nonneg (le_of_lt (Work.Kernels.scale_pos τ)) N)
        exact le_max_left A 1
      exact le_trans h1 h2
    exact Complex.norm_le_of_forall_mem_frontier_norm_le Metric.isBounded_ball
      (wlift_DiffContOnCl ℓ d hd τ hτ2) hfront (subset_closure hball)

/-- **The lifted spike bound** (CKMRV, spike circle), assuming the circle bound for `Kfun`.

The lifted spike `Wlift ℓ d τ` is holomorphic on the disc `‖w - τ‖ ≤ 29/20`, vanishes at the
three points `τ`, `τ ± 1`, and is bounded there by `C (scale τ)^N exp (-2π Im τ)` (from the
circle bound and the sharp `Δ`/`j` asymptotics).  The Schwarz-type three-zeros estimate
`Work.Analysis.ThreeZeros.three_zeros_bound_ball` then produces the three linear factors of the
statement. -/
theorem Wlift_bound_of_crux (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (hcrux : ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧ ∀ (τ ζ : UpperHalfPlane), Work.Asymptotics.Funnel τ →
      ‖(ζ : ℂ) - (τ : ℂ)‖ = 29 / 20 →
      Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun ζ →
      ‖Work.Kernels.Kfun ℓ d τ ζ‖ ≤ C * (Work.Kernels.scale τ) ^ N) :
    ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧ ∀ (τ z : UpperHalfPlane), Work.Asymptotics.Funnel τ →
      ‖(z : ℂ) - (τ : ℂ)‖ ≤ 29 / 20 → z ≠ τ → z ≠ (1 : ℝ) +ᵥ τ → z ≠ (-1 : ℝ) +ᵥ τ →
      ‖Wlift ℓ d τ (z : ℂ)‖ ≤ C * (Work.Kernels.scale τ) ^ N
        * Real.exp (-(2 * Real.pi * τ.im)) * ‖(z : ℂ) - (τ : ℂ)‖
        * ‖(z : ℂ) - ((τ : ℂ) + 1)‖ * ‖(z : ℂ) - ((τ : ℂ) - 1)‖ := by
  obtain ⟨A, N, hA, hN, hdisc⟩ := Wlift_disc_bound ℓ d hd hcrux
  have hδpos : (0 : ℝ) < (9 / 20) ^ 3 := by norm_num
  refine ⟨A / (9 / 20) ^ 3 + 1, N, by positivity, hN, fun τ z hτ hzle _ _ _ => ?_⟩
  have hτ2 : (2 : ℝ) ≤ τ.im := hτ.2
  have hsnn : (0 : ℝ) ≤ (Work.Kernels.scale τ) ^ N :=
    Real.rpow_nonneg (le_of_lt (Work.Kernels.scale_pos τ)) N
  have hepos : (0 : ℝ) < Real.exp (-(2 * Real.pi * τ.im)) := Real.exp_pos _
  have hMnn : (0 : ℝ) ≤ A * (Work.Kernels.scale τ) ^ N * Real.exp (-(2 * Real.pi * τ.im)) :=
    mul_nonneg (mul_nonneg hA.le hsnn) hepos.le
  have hdnn : 0 ≤ ‖(z : ℂ) - (τ : ℂ)‖ * ‖(z : ℂ) - ((τ : ℂ) + 1)‖
      * ‖(z : ℂ) - ((τ : ℂ) - 1)‖ := by positivity
  by_cases hcase : ‖(z : ℂ) - (τ : ℂ)‖ = 29 / 20
  · -- boundary case: use the disc bound and the explicit lower bound for the three distances
    have h1 : ‖Wlift ℓ d τ (z : ℂ)‖ ≤ A * (Work.Kernels.scale τ) ^ N
        * Real.exp (-(2 * Real.pi * τ.im)) := hdisc τ (z : ℂ) hτ (le_of_eq hcase)
    have h2 : (9 / 20 : ℝ) ^ 3 ≤ ‖(z : ℂ) - (τ : ℂ)‖ * ‖(z : ℂ) - ((τ : ℂ) + 1)‖
        * ‖(z : ℂ) - ((τ : ℂ) - 1)‖ := sphere_prod_ge τ hcase
    have h3 : A * (Work.Kernels.scale τ) ^ N * Real.exp (-(2 * Real.pi * τ.im))
        ≤ (A / (9 / 20) ^ 3 + 1) * (Work.Kernels.scale τ) ^ N * Real.exp (-(2 * Real.pi * τ.im))
          * (‖(z : ℂ) - (τ : ℂ)‖ * ‖(z : ℂ) - ((τ : ℂ) + 1)‖
            * ‖(z : ℂ) - ((τ : ℂ) - 1)‖) := by
      have h4 : A * (Work.Kernels.scale τ) ^ N * Real.exp (-(2 * Real.pi * τ.im))
          = (A / (9 / 20) ^ 3) * (9 / 20 : ℝ) ^ 3
            * ((Work.Kernels.scale τ) ^ N * Real.exp (-(2 * Real.pi * τ.im))) := by
        field_simp
      rw [h4]
      have h5 : (A / (9 / 20) ^ 3) * (9 / 20 : ℝ) ^ 3
            * ((Work.Kernels.scale τ) ^ N * Real.exp (-(2 * Real.pi * τ.im)))
          ≤ (A / (9 / 20) ^ 3) * (‖(z : ℂ) - (τ : ℂ)‖ * ‖(z : ℂ) - ((τ : ℂ) + 1)‖
              * ‖(z : ℂ) - ((τ : ℂ) - 1)‖)
            * ((Work.Kernels.scale τ) ^ N * Real.exp (-(2 * Real.pi * τ.im))) := by
        apply mul_le_mul_of_nonneg_right _ (mul_nonneg hsnn hepos.le)
        exact mul_le_mul_of_nonneg_left h2 (by positivity)
      refine le_trans h5 ?_
      have h6 : (0 : ℝ) ≤ (‖(z : ℂ) - (τ : ℂ)‖ * ‖(z : ℂ) - ((τ : ℂ) + 1)‖
          * ‖(z : ℂ) - ((τ : ℂ) - 1)‖) * ((Work.Kernels.scale τ) ^ N
            * Real.exp (-(2 * Real.pi * τ.im))) := by positivity
      nlinarith [h6]
    calc ‖Wlift ℓ d τ (z : ℂ)‖ ≤ A * (Work.Kernels.scale τ) ^ N
          * Real.exp (-(2 * Real.pi * τ.im)) := h1
      _ ≤ (A / (9 / 20) ^ 3 + 1) * (Work.Kernels.scale τ) ^ N
            * Real.exp (-(2 * Real.pi * τ.im))
            * (‖(z : ℂ) - (τ : ℂ)‖ * ‖(z : ℂ) - ((τ : ℂ) + 1)‖
              * ‖(z : ℂ) - ((τ : ℂ) - 1)‖) := h3
      _ = (A / (9 / 20) ^ 3 + 1) * (Work.Kernels.scale τ) ^ N
            * Real.exp (-(2 * Real.pi * τ.im)) * ‖(z : ℂ) - (τ : ℂ)‖
            * ‖(z : ℂ) - ((τ : ℂ) + 1)‖ * ‖(z : ℂ) - ((τ : ℂ) - 1)‖ := by ring
  · -- interior case: the three-zeros estimate
    have hlt : ‖(z : ℂ) - (τ : ℂ)‖ < 29 / 20 := lt_of_le_of_ne hzle hcase
    have hmem : (z : ℂ) ∈ Metric.ball (τ : ℂ) (29 / 20) := by
      rwa [Metric.mem_ball, dist_eq_norm]
    have hbd : ∀ w ∈ Metric.ball (τ : ℂ) (29 / 20),
        ‖Wlift ℓ d τ w‖ ≤ A * (Work.Kernels.scale τ) ^ N * Real.exp (-(2 * Real.pi * τ.im)) := by
      intro w hw
      exact hdisc τ w hτ (le_of_lt (by rwa [Metric.mem_ball, dist_eq_norm] at hw))
    have hv := Wlift_vanishing ℓ d hd τ
    have hne₁ : (τ : ℂ) ≠ (τ : ℂ) + 1 := by ring_nf; norm_num
    have hne₂ : (τ : ℂ) ≠ (τ : ℂ) - 1 := by ring_nf; norm_num
    have hne₃ : (τ : ℂ) + 1 ≠ (τ : ℂ) - 1 := by ring_nf; norm_num
    have hbound : ∀ w ∈ Metric.sphere (τ : ℂ) (29 / 20),
        (9 / 20 : ℝ) ^ 3 ≤ ‖w - (τ : ℂ)‖ * ‖w - ((τ : ℂ) + 1)‖ * ‖w - ((τ : ℂ) - 1)‖ := by
      intro w hw
      exact sphere_prod_ge τ (by rwa [Metric.mem_sphere, dist_eq_norm] at hw)
    have hthree := Work.Analysis.ThreeZeros.three_zeros_bound_ball
      (f := Wlift ℓ d τ) (c := (τ : ℂ)) (ρ := 29 / 20)
      (M := A * (Work.Kernels.scale τ) ^ N * Real.exp (-(2 * Real.pi * τ.im))) (δ := (9 / 20) ^ 3)
      (z₁ := (τ : ℂ)) (z₂ := (τ : ℂ) + 1) (z₃ := (τ : ℂ) - 1)
      (by norm_num) hMnn hδpos (wlift_DiffContOnCl ℓ d hd τ hτ2) hbd hne₁ hne₂ hne₃
      hv.1 hv.2.1 hv.2.2 hbound (z : ℂ) hmem
    have hnn2 : (0 : ℝ) ≤ (Work.Kernels.scale τ) ^ N * Real.exp (-(2 * Real.pi * τ.im))
        * ‖(z : ℂ) - (τ : ℂ)‖ * ‖(z : ℂ) - ((τ : ℂ) + 1)‖ * ‖(z : ℂ) - ((τ : ℂ) - 1)‖ := by
      positivity
    have hthree' : ‖Wlift ℓ d τ (z : ℂ)‖ ≤ (A / (9 / 20) ^ 3) * (Work.Kernels.scale τ) ^ N
        * Real.exp (-(2 * Real.pi * τ.im)) * ‖(z : ℂ) - (τ : ℂ)‖
        * ‖(z : ℂ) - ((τ : ℂ) + 1)‖ * ‖(z : ℂ) - ((τ : ℂ) - 1)‖ := by
      have hsix : A * (Work.Kernels.scale τ) ^ N * Real.exp (-(2 * Real.pi * τ.im))
            / (9 / 20 : ℝ) ^ 3
          = (A / (9 / 20) ^ 3) * (Work.Kernels.scale τ) ^ N
            * Real.exp (-(2 * Real.pi * τ.im)) := by field_simp
      rw [hsix] at hthree
      exact hthree
    refine le_trans hthree' ?_
    calc (A / (9 / 20) ^ 3) * (Work.Kernels.scale τ) ^ N * Real.exp (-(2 * Real.pi * τ.im))
          * ‖(z : ℂ) - (τ : ℂ)‖ * ‖(z : ℂ) - ((τ : ℂ) + 1)‖ * ‖(z : ℂ) - ((τ : ℂ) - 1)‖
        = (A / (9 / 20) ^ 3) * ((Work.Kernels.scale τ) ^ N * Real.exp (-(2 * Real.pi * τ.im))
            * ‖(z : ℂ) - (τ : ℂ)‖ * ‖(z : ℂ) - ((τ : ℂ) + 1)‖
            * ‖(z : ℂ) - ((τ : ℂ) - 1)‖) := by ring
      _ ≤ (A / (9 / 20) ^ 3 + 1) * ((Work.Kernels.scale τ) ^ N * Real.exp (-(2 * Real.pi * τ.im))
            * ‖(z : ℂ) - (τ : ℂ)‖ * ‖(z : ℂ) - ((τ : ℂ) + 1)‖
            * ‖(z : ℂ) - ((τ : ℂ) - 1)‖) := by
          apply mul_le_mul_of_nonneg_right _ hnn2
          linarith
      _ = (A / (9 / 20) ^ 3 + 1) * (Work.Kernels.scale τ) ^ N * Real.exp (-(2 * Real.pi * τ.im))
            * ‖(z : ℂ) - (τ : ℂ)‖ * ‖(z : ℂ) - ((τ : ℂ) + 1)‖
            * ‖(z : ℂ) - ((τ : ℂ) - 1)‖ := by ring

/-- **The lift of the spike, bounded by the three distances.**  This is the CKMRV spike-circle
estimate for the lifted spike `Wlift ℓ d τ`: on the disc `‖w - τ‖ ≤ 29/20` (minus the three
points `τ`, `τ ± 1` where `Wlift` vanishes) we have

`‖Wlift ℓ d τ w‖ ≤ C (S τ)^N e^{-2π Im τ} ‖w-τ‖‖w-(τ+1)‖‖w-(τ-1)‖`.

The circle bound `spikeCircleBound` gives `‖Kfun‖ ≤ C (S τ)^N`; converting it through the
identity `Wlift = Δ(τ)Δ(ζ)(j τ - j ζ)(Kfun - PP)` and the sharp `Δ`/`j` asymptotics gives the
bound on the circle, and the three-zeros argument propagates it to the disc. -/
theorem Wlift_bound (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) : ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧ ∀ (τ z : UpperHalfPlane), Work.Asymptotics.Funnel τ → ‖(z : ℂ) - (τ : ℂ)‖ ≤ 29 / 20 → z ≠ τ → z ≠ (1 : ℝ) +ᵥ τ → z ≠ (-1 : ℝ) +ᵥ τ → ‖Work.Asymptotics.SpikeCircle.Wlift ℓ d τ (z : ℂ)‖ ≤ C * (Work.Kernels.scale τ) ^ N * Real.exp (-(2 * Real.pi * τ.im)) * ‖(z : ℂ) - (τ : ℂ)‖ * ‖(z : ℂ) - ((τ : ℂ) + 1)‖ * ‖(z : ℂ) - ((τ : ℂ) - 1)‖ :=
  Wlift_bound_of_crux ℓ d hd (spikeCircleBound ℓ d hd)

end Work.Asymptotics.SpikeCircle
