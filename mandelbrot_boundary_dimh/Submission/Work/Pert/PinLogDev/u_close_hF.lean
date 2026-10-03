import Mathlib
import Submission.Work.Pert.PinLogDev.Setup

/-!
# `Work.Pert.PinLogDev.u_close_hF`

The perturbed model germ `u` (of `f z = z + z (z - σ) u z`) is `O(δ₀ + ‖σ‖)`-close to the
unperturbed model germ `hF` (of `f₀ z = z + z² hF z`) in the `C¹`-sense at the origin, uniformly
in all the data, on a ball of radius `rr` on which `f` and `f₀` are `δ₀`-close (`NearOn`).

The proof is a plain Cauchy estimate on the *defect* function

  `g z = f z - f₀ z`,  `g z = z² (u z - hF z) - σ (z u z)`  for `z` in the ball,

which is holomorphic on the ball `ball 0 rr` and bounded by `δ₀` on `closedBall 0 rr` (whence on
`sphere 0 (rr/2) ⊆ closedBall 0 rr ⊆ L`).  Since `g` vanishes to order `2` at the origin after
removing the `σ z u z` term, the second and third Taylor coefficients of `g` at `0` control
`u 0 - hF 0` and `deriv u 0 - deriv hF 0` up to the `σ`-multiples `σ deriv u 0`,
`σ iteratedDeriv 2 u 0` (which are `O(‖σ‖)` because `‖u‖ ≤ 2` on the ball).  Concretely, writing

  `g z = z² (u z - hF z) - σ (z u z)`,  `V := u - hF`,

one has `g''(0) = 2 V(0) - 2σ u'(0)` and `g'''(0) = 6 V'(0) - 3σ u''(0)`, both Taylor coefficients of
the bounded holomorphic `g`, giving the two bounds

  `‖u 0 - hF 0‖ ≤ C (δ₀ + ‖σ‖)`,  `‖deriv u 0 - deriv hF 0‖ ≤ C (δ₀ + ‖σ‖)`

with a constant `C` depending only on `rr`.
-/

namespace Work.Pert.PinLogDev

open MandelDim Complex Set Metric Filter
open scoped Topology

noncomputable section

set_option linter.unusedSimpArgs false

/-! ## Elementary `iteratedDeriv` computations at `0`

For an analytic germ `V` at `0` the products `z² V` and `z V` have the following Taylor
coefficients at `0`: the `z²`-coefficient of `z² V` is `V 0`, its `z³`-coefficient is `deriv V 0`;
the `z²`-coefficient of `z V` is `deriv V 0` and its `z³`-coefficient is
`iteratedDeriv 2 V 0 / 2` (the `iteratedDeriv` being `n!`-times the Taylor coefficient). -/

private lemma itd2_sq (V : ℂ → ℂ) (hV : ContDiffAt ℂ 2 V 0) :
    iteratedDeriv 2 (fun z => z ^ 2 * V z) 0 = 2 * V 0 := by
  change iteratedDeriv 2 ((fun z : ℂ => z ^ 2) * V) 0 = 2 * V 0
  rw [iteratedDeriv_mul (f := fun z : ℂ => z ^ 2) (g := V) (by fun_prop) hV]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Finset.sum_empty,
    iteratedDeriv_pow, iteratedDeriv_zero]
  norm_num

private lemma itd3_sq (V : ℂ → ℂ) (hV : ContDiffAt ℂ 3 V 0) :
    iteratedDeriv 3 (fun z => z ^ 2 * V z) 0 = 6 * deriv V 0 := by
  change iteratedDeriv 3 ((fun z : ℂ => z ^ 2) * V) 0 = 6 * deriv V 0
  rw [iteratedDeriv_mul (f := fun z : ℂ => z ^ 2) (g := V) (by fun_prop) hV]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Finset.sum_empty,
    iteratedDeriv_pow, iteratedDeriv_zero, iteratedDeriv_one]
  norm_num

private lemma itd2_id (V : ℂ → ℂ) (hV : ContDiffAt ℂ 2 V 0) :
    iteratedDeriv 2 (fun z => z * V z) 0 = 2 * deriv V 0 := by
  change iteratedDeriv 2 ((fun z : ℂ => z) * V) 0 = 2 * deriv V 0
  rw [iteratedDeriv_mul (f := fun z : ℂ => z) (g := V) (by fun_prop) hV]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Finset.sum_empty,
    iteratedDeriv_fun_id_zero, iteratedDeriv_zero, iteratedDeriv_one]
  norm_num

private lemma itd3_id (V : ℂ → ℂ) (hV : ContDiffAt ℂ 3 V 0) :
    iteratedDeriv 3 (fun z => z * V z) 0 = 3 * iteratedDeriv 2 V 0 := by
  change iteratedDeriv 3 ((fun z : ℂ => z) * V) 0 = 3 * iteratedDeriv 2 V 0
  rw [iteratedDeriv_mul (f := fun z : ℂ => z) (g := V) (by fun_prop) hV]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Finset.sum_empty,
    iteratedDeriv_fun_id_zero, iteratedDeriv_zero, iteratedDeriv_one]
  norm_num

/-- `g''(0)` for the defect `g z = z² (u z - hF z) - σ (z u z)`. -/
private lemma itd2_defect (u hF : ℂ → ℂ) (σ : ℂ)
    (hu : ContDiffAt ℂ 2 u 0) (hh : ContDiffAt ℂ 2 hF 0) :
    iteratedDeriv 2 (fun z => z ^ 2 * (u z - hF z) - σ * (z * u z)) 0
      = 2 * (u 0 - hF 0) - 2 * σ * deriv u 0 := by
  have hA : ContDiffAt ℂ 2 (fun z : ℂ => z ^ 2 * (u z - hF z)) 0 := by fun_prop
  have hB : ContDiffAt ℂ 2 (fun z : ℂ => σ * (z * u z)) 0 := by fun_prop
  change iteratedDeriv 2 ((fun z : ℂ => z^2 * (u z - hF z)) - (fun z : ℂ => σ * (z * u z))) 0
      = 2 * (u 0 - hF 0) - 2 * σ * deriv u 0
  rw [iteratedDeriv_sub hA hB, itd2_sq (fun z => u z - hF z) (by fun_prop)]
  simp only [iteratedDeriv_const_mul_field]
  rw [itd2_id u hu]
  ring

/-- `g'''(0)` for the defect `g z = z² (u z - hF z) - σ (z u z)`. -/
private lemma itd3_defect (u hF : ℂ → ℂ) (σ : ℂ)
    (hu : ContDiffAt ℂ 3 u 0) (hh : ContDiffAt ℂ 3 hF 0) :
    iteratedDeriv 3 (fun z => z ^ 2 * (u z - hF z) - σ * (z * u z)) 0
      = 6 * (deriv u 0 - deriv hF 0) - 3 * σ * iteratedDeriv 2 u 0 := by
  have hA : ContDiffAt ℂ 3 (fun z : ℂ => z ^ 2 * (u z - hF z)) 0 := by fun_prop
  have hB : ContDiffAt ℂ 3 (fun z : ℂ => σ * (z * u z)) 0 := by fun_prop
  change iteratedDeriv 3 ((fun z : ℂ => z^2 * (u z - hF z)) - (fun z : ℂ => σ * (z * u z))) 0
      = 6 * (deriv u 0 - deriv hF 0) - 3 * σ * iteratedDeriv 2 u 0
  rw [iteratedDeriv_sub hA hB, itd3_sq (fun z => u z - hF z) (by fun_prop)]
  simp only [iteratedDeriv_const_mul_field]
  rw [itd3_id u hu]
  have hderiv : deriv (fun z => u z - hF z) 0 = deriv u 0 - deriv hF 0 :=
    deriv_sub (hu.differentiableAt (by norm_num)) (hh.differentiableAt (by norm_num))
  rw [hderiv]
  ring

theorem u_close_hF (rr : ℝ) (hrr : 0 < rr) :
    ∃ C : ℝ, 0 < C ∧ ∀ {f₀ f : ℂ → ℂ} {Df L : Set ℂ} {u hF : ℂ → ℂ} {σ : ℂ} {δ₀ : ℝ},
      (0 < δ₀) → (Metric.closedBall (0 : ℂ) rr ⊆ L) → MandelDim.NearOn f₀ f Df L δ₀ →
      (∀ z ∈ Metric.ball (0 : ℂ) rr, f z = z + z * (z - σ) * u z) →
      (∀ z ∈ Metric.ball (0 : ℂ) rr, f₀ z = z + z ^ 2 * hF z) →
      DifferentiableOn ℂ hF (Metric.ball (0 : ℂ) rr) →
      DifferentiableOn ℂ u (Metric.ball (0 : ℂ) rr) →
      (∀ z ∈ Metric.ball (0 : ℂ) rr, 1 / 2 ≤ ‖u z‖ ∧ ‖u z‖ ≤ 2) →
      ‖u 0 - hF 0‖ ≤ C * (δ₀ + ‖σ‖) ∧ ‖deriv u 0 - deriv hF 0‖ ≤ C * (δ₀ + ‖σ‖) := by
  set M : ℝ := max (max (4 / rr^2) (4 / rr)) (max (8 / rr^3) (8 / rr^2)) with hM
  refine ⟨M + 1, ?_, ?_⟩
  · have hM1 : 4 / rr ^ 2 ≤ M := by
      rw [hM]; exact le_trans (le_max_left _ _) (le_max_left _ _)
    have hpos : 0 < 4 / rr ^ 2 := by positivity
    linarith
  · intro f₀ f Df L u hF σ δ₀ hδ₀ hL hnear hf hf0 hhFd hud hu2
    have hr2 : (0:ℝ) < rr / 2 := by linarith
    have hlt : rr / 2 < rr := by linarith
    -- `f₀` is holomorphic on the ball (it is `z + z² hF` there)
    have hf0d : DifferentiableOn ℂ f₀ (Metric.ball 0 rr) := by
      have h : DifferentiableOn ℂ (fun z : ℂ => z + z ^ 2 * hF z) (Metric.ball 0 rr) := by
        fun_prop
      exact h.congr (fun z hz => hf0 z hz)
    -- `f` is holomorphic on the ball (`ball 0 rr ⊆ closedBall 0 rr ⊆ L ⊆ Df`)
    have hfd : DifferentiableOn ℂ f (Metric.ball 0 rr) :=
      hnear.2.2.1.mono (fun z hz => hnear.2.1 (hL (Metric.ball_subset_closedBall hz)))
    have hg : DifferentiableOn ℂ (fun z : ℂ => f z - f₀ z) (Metric.ball 0 rr) := hfd.sub hf0d
    have hgball : DifferentiableOn ℂ (fun z : ℂ => f z - f₀ z) (Metric.ball 0 (rr/2)) :=
      hg.mono (Metric.ball_subset_ball (le_of_lt hlt))
    have hgcl : DifferentiableOn ℂ (fun z : ℂ => f z - f₀ z) (Metric.closedBall 0 (rr/2)) :=
      hg.mono (Metric.closedBall_subset_ball hlt)
    have hgdcc : DiffContOnCl ℂ (fun z : ℂ => f z - f₀ z) (Metric.ball 0 (rr/2)) :=
      DiffContOnCl.mk_ball hgball hgcl.continuousOn
    -- the defect is bounded by `δ₀` on the sphere of radius `rr/2`
    have hgbound : ∀ z ∈ Metric.sphere 0 (rr/2), ‖f z - f₀ z‖ ≤ δ₀ := by
      intro z hz
      have hzL : z ∈ L :=
        hL (Metric.closedBall_subset_closedBall (le_of_lt hlt) (Metric.sphere_subset_closedBall hz))
      exact le_of_lt (hnear.2.2.2 z hzL)
    -- Cauchy's estimate on the defect
    have hc2 : ‖iteratedDeriv 2 (fun z : ℂ => f z - f₀ z) 0‖ ≤ 2 * δ₀ / (rr/2)^2 := by
      have h := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le
          (f := fun z : ℂ => f z - f₀ z) 2 hr2 hgdcc hgbound
      norm_num [Nat.factorial] at h
      exact h
    have hc3 : ‖iteratedDeriv 3 (fun z : ℂ => f z - f₀ z) 0‖ ≤ 6 * δ₀ / (rr/2)^3 := by
      have h := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le
          (f := fun z : ℂ => f z - f₀ z) 3 hr2 hgdcc hgbound
      norm_num [Nat.factorial] at h
      exact h
    -- Cauchy's estimate on `u`, using `‖u‖ ≤ 2`
    have huball : DifferentiableOn ℂ u (Metric.ball 0 (rr/2)) :=
      hud.mono (Metric.ball_subset_ball (le_of_lt hlt))
    have hucl : DifferentiableOn ℂ u (Metric.closedBall 0 (rr/2)) :=
      hud.mono (Metric.closedBall_subset_ball hlt)
    have hudcc : DiffContOnCl ℂ u (Metric.ball 0 (rr/2)) :=
      DiffContOnCl.mk_ball huball hucl.continuousOn
    have hubound : ∀ z ∈ Metric.sphere 0 (rr/2), ‖u z‖ ≤ 2 := by
      intro z hz
      exact (hu2 z (Metric.closedBall_subset_ball hlt (Metric.sphere_subset_closedBall hz))).2
    have hcu1 : ‖deriv u 0‖ ≤ 2 / (rr/2) := by
      have h := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le
          (f := u) 1 hr2 hudcc hubound
      norm_num [Nat.factorial] at h
      simpa using h
    have hcu2 : ‖iteratedDeriv 2 u 0‖ ≤ 4 / (rr/2)^2 := by
      have h := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le
          (f := u) 2 hr2 hudcc hubound
      norm_num [Nat.factorial] at h
      exact h
    -- analyticity at the origin
    have huCa2 : ContDiffAt ℂ 2 u 0 := (hud.analyticAt (Metric.ball_mem_nhds 0 hrr)).contDiffAt
    have hhCa2 : ContDiffAt ℂ 2 hF 0 := (hhFd.analyticAt (Metric.ball_mem_nhds 0 hrr)).contDiffAt
    have huCa3 : ContDiffAt ℂ 3 u 0 := (hud.analyticAt (Metric.ball_mem_nhds 0 hrr)).contDiffAt
    have hhCa3 : ContDiffAt ℂ 3 hF 0 := (hhFd.analyticAt (Metric.ball_mem_nhds 0 hrr)).contDiffAt
    -- the defect is the explicit expression on the ball
    have hpt : ∀ z ∈ Metric.ball 0 rr,
        f z - f₀ z = z^2 * (u z - hF z) - σ * (z * u z) := by
      intro z hz
      rw [hf z hz, hf0 z hz]; ring
    have hGE : (fun z : ℂ => f z - f₀ z) =ᶠ[𝓝 0]
        (fun z : ℂ => z^2 * (u z - hF z) - σ * (z * u z)) :=
      Filter.eventually_of_mem (Metric.ball_mem_nhds 0 hrr) hpt
    have hg2 : iteratedDeriv 2 (fun z : ℂ => f z - f₀ z) 0
        = 2 * (u 0 - hF 0) - 2 * σ * deriv u 0 :=
      (hGE.iteratedDeriv_eq 2).trans (itd2_defect u hF σ huCa2 hhCa2)
    have hg3 : iteratedDeriv 3 (fun z : ℂ => f z - f₀ z) 0
        = 6 * (deriv u 0 - deriv hF 0) - 3 * σ * iteratedDeriv 2 u 0 :=
      (hGE.iteratedDeriv_eq 3).trans (itd3_defect u hF σ huCa3 hhCa3)
    -- solve for the quantities of interest
    have hV0 : u 0 - hF 0
        = iteratedDeriv 2 (fun z : ℂ => f z - f₀ z) 0 / 2 + σ * deriv u 0 := by
      rw [hg2]; ring
    have hV1 : deriv u 0 - deriv hF 0 =
        (iteratedDeriv 3 (fun z : ℂ => f z - f₀ z) 0 + 3 * σ * iteratedDeriv 2 u 0) / 6 := by
      rw [hg3]; ring
    -- the two bounds
    have hb0 : ‖u 0 - hF 0‖ ≤ 4 * δ₀ / rr^2 + 4 * ‖σ‖ / rr := by
      rw [hV0]
      calc ‖iteratedDeriv 2 (fun z : ℂ => f z - f₀ z) 0 / 2 + σ * deriv u 0‖
          ≤ ‖iteratedDeriv 2 (fun z : ℂ => f z - f₀ z) 0 / 2‖ + ‖σ * deriv u 0‖ := norm_add_le _ _
        _ = ‖iteratedDeriv 2 (fun z : ℂ => f z - f₀ z) 0‖ / 2 + ‖σ‖ * ‖deriv u 0‖ := by
              rw [norm_div, norm_mul, Complex.norm_ofNat]
        _ ≤ 2 * δ₀ / (rr/2)^2 / 2 + ‖σ‖ * (2 / (rr/2)) := by
              apply add_le_add
              · apply div_le_div_of_nonneg_right hc2 (by norm_num)
              · exact mul_le_mul_of_nonneg_left hcu1 (norm_nonneg σ)
        _ = 4 * δ₀ / rr^2 + 4 * ‖σ‖ / rr := by ring
    have hb1 : ‖deriv u 0 - deriv hF 0‖ ≤ 8 * δ₀ / rr^3 + 8 * ‖σ‖ / rr^2 := by
      rw [hV1]
      calc ‖(iteratedDeriv 3 (fun z : ℂ => f z - f₀ z) 0 + 3 * σ * iteratedDeriv 2 u 0) / 6‖
          ≤ ‖iteratedDeriv 3 (fun z : ℂ => f z - f₀ z) 0 + 3 * σ * iteratedDeriv 2 u 0‖ / 6 := by
              rw [norm_div, Complex.norm_ofNat]
        _ ≤ (‖iteratedDeriv 3 (fun z : ℂ => f z - f₀ z) 0‖ + ‖3 * σ * iteratedDeriv 2 u 0‖) / 6 := by
              apply div_le_div_of_nonneg_right (norm_add_le _ _) (by norm_num)
        _ = (‖iteratedDeriv 3 (fun z : ℂ => f z - f₀ z) 0‖ + 3 * ‖σ‖ * ‖iteratedDeriv 2 u 0‖) / 6 := by
              simp only [norm_mul, Complex.norm_ofNat]
        _ ≤ (6 * δ₀ / (rr/2)^3 + 3 * ‖σ‖ * (4 / (rr/2)^2)) / 6 := by
              apply div_le_div_of_nonneg_right _ (by norm_num)
              apply add_le_add hc3
              apply mul_le_mul_of_nonneg_left hcu2 (by positivity)
        _ = 8 * δ₀ / rr^3 + 8 * ‖σ‖ / rr^2 := by ring
    -- collect the constant
    have hC1 : 4 / rr^2 ≤ M + 1 := by
      have : 4 / rr^2 ≤ M := by rw [hM]; exact le_trans (le_max_left _ _) (le_max_left _ _)
      linarith
    have hC2 : 4 / rr ≤ M + 1 := by
      have : 4 / rr ≤ M := by rw [hM]; exact le_trans (le_max_right _ _) (le_max_left _ _)
      linarith
    have hC3 : 8 / rr^3 ≤ M + 1 := by
      have : 8 / rr^3 ≤ M := by rw [hM]; exact le_trans (le_max_left _ _) (le_max_right _ _)
      linarith
    have hC4 : 8 / rr^2 ≤ M + 1 := by
      have : 8 / rr^2 ≤ M := by rw [hM]; exact le_trans (le_max_right _ _) (le_max_right _ _)
      linarith
    refine ⟨?_, ?_⟩
    · calc ‖u 0 - hF 0‖ ≤ 4 * δ₀ / rr^2 + 4 * ‖σ‖ / rr := hb0
        _ ≤ (M + 1) * δ₀ + (M + 1) * ‖σ‖ := by
              apply add_le_add
              · have h := mul_le_mul_of_nonneg_right hC1 hδ₀.le
                calc 4 * δ₀ / rr^2 = (4 / rr^2) * δ₀ := by ring
                  _ ≤ (M + 1) * δ₀ := h
              · have h := mul_le_mul_of_nonneg_right hC2 (norm_nonneg σ)
                calc 4 * ‖σ‖ / rr = (4 / rr) * ‖σ‖ := by ring
                  _ ≤ (M + 1) * ‖σ‖ := h
        _ = (M + 1) * (δ₀ + ‖σ‖) := by ring
    · calc ‖deriv u 0 - deriv hF 0‖ ≤ 8 * δ₀ / rr^3 + 8 * ‖σ‖ / rr^2 := hb1
        _ ≤ (M + 1) * δ₀ + (M + 1) * ‖σ‖ := by
              apply add_le_add
              · have h := mul_le_mul_of_nonneg_right hC3 hδ₀.le
                calc 8 * δ₀ / rr^3 = (8 / rr^3) * δ₀ := by ring
                  _ ≤ (M + 1) * δ₀ := h
              · have h := mul_le_mul_of_nonneg_right hC4 (norm_nonneg σ)
                calc 8 * ‖σ‖ / rr^2 = (8 / rr^2) * ‖σ‖ := by ring
                  _ ≤ (M + 1) * ‖σ‖ := h
        _ = (M + 1) * (δ₀ + ‖σ‖) := by ring

end

end Work.Pert.PinLogDev
