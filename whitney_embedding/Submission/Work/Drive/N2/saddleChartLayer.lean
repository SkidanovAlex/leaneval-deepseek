import Mathlib
import Submission.Work.Drive.N2.windowDatum
import Submission.Work.Drive.N2.modelFlowDefs
import Submission.Work.Drive.N2.windowChartCoord


/-!
# The scaled saddle chart coordinate of a `WindowDatum`

The saddle case of the `n = 2` critical-window drawing uses a *scaled* chart coordinate
`Z = σc · W / λ` (`W` the chart coordinate of the marked Morse chart, `λ = ρ / 8`, `σc = 1` or
`σc = I` according to the sign of the Morse normal form) in which

* the level law has the model form `f = c + lam · Re (Z ·)²` with `lam = λ²`,
* the chart trajectory of the datum's flow solves the model ODE
  `(Z ∘ Φ)' = chartMult (ρ/8) (lam ‖Z‖²) · (Re Z, - Im Z)`.

This file isolates that bookkeeping so that the geometric part of the saddle window can be stated
for a single canonical chart.
-/

namespace Work.Drive.N2

open scoped Manifold ContDiff Topology
open Set

set_option backward.isDefEq.respectTransparency false

variable {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]

variable {f : M → ℝ} {p : M}

/-- The model-space complex coordinate `u ↦ u 0 + i · u 1`, as a continuous linear map. -/
noncomputable def cl_chartZLM : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℂ :=
  (coordProj 0).smulRight (1 : ℂ) + (coordProj 1).smulRight Complex.I

lemma cl_chartZLM_apply (u : EuclideanSpace ℝ (Fin 2)) :
    cl_chartZLM u = ((u 0 : ℝ) : ℂ) + ((u 1 : ℝ) : ℂ) * Complex.I := by
  simp [cl_chartZLM, ContinuousLinearMap.smulRight_apply, coordProj_apply, Complex.real_smul]

lemma cl_chartZ_eq_chartZLM (φ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 2))) (y : M) :
    chartZ φ y = cl_chartZLM (φ y) := by
  rw [chartZ_apply, cl_chartZLM_apply]

/-- The model complex coordinate preserves the norm. -/
lemma cl_norm_chartZLM (u : EuclideanSpace ℝ (Fin 2)) : ‖cl_chartZLM u‖ = ‖u‖ := by
  have hsq : ‖cl_chartZLM u‖ ^ 2 = ‖u‖ ^ 2 := by
    rw [cl_chartZLM_apply, Complex.sq_norm, Complex.normSq_apply, ← norm_uVec u]
    simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_one, mul_zero, sub_zero, zero_add,
      add_zero]
    ring
  have ha : (0 : ℝ) ≤ ‖cl_chartZLM u‖ := norm_nonneg _
  have hb : (0 : ℝ) ≤ ‖u‖ := norm_nonneg _
  have h := (sq_eq_sq_iff_abs_eq_abs _ _).mp hsq
  rwa [abs_of_nonneg ha, abs_of_nonneg hb] at h

lemma cl_chartZLM_injective : Function.Injective cl_chartZLM := by
  intro u v huv
  have h1 : (u 0 : ℝ) = (v 0 : ℝ) := by
    have := congrArg Complex.re huv
    simpa [cl_chartZLM_apply] using this
  have h2 : (u 1 : ℝ) = (v 1 : ℝ) := by
    have := congrArg Complex.im huv
    simpa [cl_chartZLM_apply] using this
  ext j
  fin_cases j
  · exact h1
  · exact h2

/-- The multiplication by a complex constant, as a continuous linear map. -/
noncomputable def cl_scaleCLM (c : ℂ) : ℂ →L[ℝ] ℂ := c • ContinuousLinearMap.id ℝ ℂ

lemma cl_scaleCLM_apply (c z : ℂ) : cl_scaleCLM c z = c * z := by
  simp [cl_scaleCLM]

lemma cl_scaleCLM_injective {c : ℂ} (hc : c ≠ 0) : Function.Injective (cl_scaleCLM c) := by
  intro u v huv
  have h := congrArg (fun z => c⁻¹ * z) huv
  simpa [cl_scaleCLM_apply, ← mul_assoc, hc] using h

/-- **The differential of a chart (smooth in both directions) is injective on its source.** -/
lemma cl_injective_mfderiv_chart {φ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 2))}
    (hφ : ContMDiffOn (𝓡 2) (𝓡 2) ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y => φ y) φ.source)
    (hφ' : ContMDiffOn (𝓡 2) (𝓡 2) ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z => φ.symm z) φ.target)
    {x : M} (hx : x ∈ φ.source) :
    Function.Injective (mfderiv (𝓡 2) (𝓡 2) (fun y => φ y) x) := by
  have hφx : MDifferentiableAt (𝓡 2) (𝓡 2) (fun y => φ y) x :=
    ((hφ x hx).mdifferentiableWithinAt (by norm_num)).mdifferentiableAt
      (φ.open_source.mem_nhds hx)
  have hφ'x : MDifferentiableAt (𝓡 2) (𝓡 2) (fun z => φ.symm z) (φ x) :=
    ((hφ' (φ x) (φ.map_source hx)).mdifferentiableWithinAt (by norm_num)).mdifferentiableAt
      (φ.open_target.mem_nhds (φ.map_source hx))
  have heq : ((fun z => φ.symm z) ∘ (fun y => φ y)) =ᶠ[𝓝 x] id := by
    filter_upwards [φ.open_source.mem_nhds hx] with y hy
    exact φ.left_inv hy
  have h1 : mfderiv (𝓡 2) (𝓡 2) ((fun z => φ.symm z) ∘ (fun y => φ y)) x
      = ContinuousLinearMap.id ℝ (TangentSpace (𝓡 2) x) := by
    rw [Filter.EventuallyEq.mfderiv_eq heq]
    exact mfderiv_id
  have hcomp := mfderiv_comp (f := fun y => φ y) (g := fun z => φ.symm z) x hφ'x hφx
  have key : ∀ w, (mfderiv (𝓡 2) (𝓡 2) (fun z => φ.symm z) (φ x))
      ((mfderiv (𝓡 2) (𝓡 2) (fun y => φ y) x) w) = w := by
    intro w
    change ((mfderiv (𝓡 2) (𝓡 2) (fun z => φ.symm z) (φ x)).comp
      (mfderiv (𝓡 2) (𝓡 2) (fun y => φ y) x)) w = w
    rw [← hcomp, h1]
    rfl
  intro u v huv
  rw [← key u, huv, key v]

/-- **The scaled saddle chart coordinate** of a `WindowDatum`: `Z = σc · W / (ρ/8)`. -/
noncomputable def cl_saddleZ {f : M → ℝ} {p : M} (D : WindowDatum f p) (σc : ℂ) : M → ℂ :=
  fun y => cl_scaleCLM (σc / ((D.ρ D.j / 8 : ℝ) : ℂ)) (cl_chartZLM (D.φ D.j y))

lemma cl_saddleZ_eq (D : WindowDatum f p) (σc : ℂ) (y : M) :
    cl_saddleZ D σc y = σc / ((D.ρ D.j / 8 : ℝ) : ℂ) * chartZ (D.φ D.j) y := by
  rw [cl_saddleZ, cl_scaleCLM_apply, cl_chartZ_eq_chartZLM]

/-- The written form of `cl_saddleZ`. -/
lemma cl_saddleZ_apply (D : WindowDatum f p) (σc : ℂ) (y : M) :
    cl_saddleZ D σc y = σc * (((D.φ D.j y 0 : ℝ) : ℂ) + ((D.φ D.j y 1 : ℝ) : ℂ) * Complex.I)
      / ((D.ρ D.j / 8 : ℝ) : ℂ) := by
  rw [cl_saddleZ_eq, chartZ_apply]
  ring

/-- The norm of `cl_saddleZ` in terms of the chart norm (for `‖σc‖ = 1`). -/
lemma cl_norm_saddleZ (D : WindowDatum f p) {σc : ℂ} (hσc : ‖σc‖ = 1) (y : M) :
    ‖cl_saddleZ D σc y‖ = ‖D.φ D.j y‖ / (D.ρ D.j / 8) := by
  have hρ : (0 : ℝ) < D.ρ D.j := D.hρ D.j
  have hnorm : ‖(((D.ρ D.j / 8 : ℝ)) : ℂ)‖ = D.ρ D.j / 8 := by
    rw [Complex.norm_def, Complex.normSq_ofReal, Real.sqrt_mul_self (by positivity)]
  rw [cl_saddleZ, cl_scaleCLM_apply, norm_mul, norm_div, hnorm, hσc, cl_norm_chartZLM,
    div_eq_mul_inv, div_eq_mul_inv]
  ring

/-- **The argument of `chartMult` in the `Z`-coordinate is `lam ‖Z‖² = ‖W‖²`.** -/
lemma cl_lam_mul_norm_saddleZ_sq (D : WindowDatum f p) {σc : ℂ} (hσc : ‖σc‖ = 1) (y : M) :
    (D.ρ D.j / 8) ^ 2 * ‖cl_saddleZ D σc y‖ ^ 2 = ‖D.φ D.j y‖ ^ 2 := by
  have hb : (D.ρ D.j / 8) ≠ 0 := by
    have := D.hρ D.j; positivity
  have hρ : D.ρ D.j ≠ 0 := ne_of_gt (D.hρ D.j)
  rw [cl_norm_saddleZ D hσc y]
  field_simp

/-- The real part of `c` times the model coordinate `u₀ + i u₁`. -/
lemma cl_re_mul_chart (c : ℂ) (u₀ u₁ : ℝ) :
    (c * (((u₀ : ℝ) : ℂ) + ((u₁ : ℝ) : ℂ) * Complex.I)).re = c.re * u₀ - c.im * u₁ := by
  rw [Complex.mul_re]
  simp

/-- The imaginary part of `c` times the model coordinate `u₀ + i u₁`. -/
lemma cl_im_mul_chart (c : ℂ) (u₀ u₁ : ℝ) :
    (c * (((u₀ : ℝ) : ℂ) + ((u₁ : ℝ) : ℂ) * Complex.I)).im = c.im * u₀ + c.re * u₁ := by
  rw [Complex.mul_im]
  simp
  ring

lemma cl_re_div_ofReal (c : ℂ) (r : ℝ) : (c / ((r : ℝ) : ℂ)).re = c.re / r := by
  rw [Complex.div_ofReal]

lemma cl_im_div_ofReal (c : ℂ) (r : ℝ) : (c / ((r : ℝ) : ℂ)).im = c.im / r := by
  rw [Complex.div_ofReal]

/-- The real part of `cl_saddleZ` in terms of the chart coordinates. -/
lemma cl_saddleZ_re (D : WindowDatum f p) (σc : ℂ) (y : M) :
    (cl_saddleZ D σc y).re
      = (σc.re * D.φ D.j y 0 - σc.im * D.φ D.j y 1) / (D.ρ D.j / 8) := by
  rw [cl_saddleZ_eq, chartZ_apply, cl_re_mul_chart, cl_re_div_ofReal, cl_im_div_ofReal]
  ring

/-- The imaginary part of `cl_saddleZ` in terms of the chart coordinates. -/
lemma cl_saddleZ_im (D : WindowDatum f p) (σc : ℂ) (y : M) :
    (cl_saddleZ D σc y).im
      = (σc.im * D.φ D.j y 0 + σc.re * D.φ D.j y 1) / (D.ρ D.j / 8) := by
  rw [cl_saddleZ_eq, chartZ_apply, cl_im_mul_chart, cl_re_div_ofReal, cl_im_div_ofReal]
  ring

/-- **Smoothness of the scaled saddle chart coordinate on the chart ball.** -/
lemma cl_contMDiffOn_saddleZ (D : WindowDatum f p) (σc : ℂ) :
    ContMDiffOn (𝓡 2) 𝓘(ℝ, ℂ) ((⊤ : ℕ∞) : WithTop ℕ∞) (cl_saddleZ D σc)
      (modelBall (D.φ D.j) (D.ρ D.j)) := by
  have h1 : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℂ) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun y => cl_chartZLM (D.φ D.j y)) (D.φ D.j).source :=
    cl_chartZLM.contMDiff.comp_contMDiffOn (D.hφ D.j)
  have h2 : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℂ) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun y => cl_scaleCLM (σc / ((D.ρ D.j / 8 : ℝ) : ℂ)) (cl_chartZLM (D.φ D.j y)))
      (D.φ D.j).source :=
    (cl_scaleCLM _).contMDiff.comp_contMDiffOn h1
  exact h2.mono (fun _ hy => hy.1)

/-- Multiplication by a real constant, on the real part. -/
lemma cl_re_ofReal_mul (r : ℝ) (z : ℂ) : (((r : ℝ) : ℂ) * z).re = r * z.re := by
  rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]; ring

/-- Multiplication by a real constant, on the imaginary part. -/
lemma cl_im_ofReal_mul (r : ℝ) (z : ℂ) : (((r : ℝ) : ℂ) * z).im = r * z.im := by
  rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]; ring

/-- **The quadratic identity**: in the scaled coordinate the Morse normal form `s₁ u₀² + s₂ u₁²`
with `s₂ = -s₁ = ±1` is `λ² · Re (Z ·)²`. -/
lemma cl_saddleZ_quadratic (D : WindowDatum f p) {σc : ℂ} {s₁ s₂ : ℝ}
    (hsgn : s₁ = -s₂) (hσcsq : σc * σc = ((s₁ : ℝ) : ℂ)) (y : M) :
    (D.ρ D.j / 8) ^ 2 * ((cl_saddleZ D σc y) ^ 2).re
      = s₁ * (D.φ D.j y 0) ^ 2 + s₂ * (D.φ D.j y 1) ^ 2 := by
  have hlam0 : (D.ρ D.j / 8) ≠ 0 := by
    have := D.hρ D.j; positivity
  have hlam : ((((D.ρ D.j / 8) ^ 2 : ℝ)) : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero]; exact pow_ne_zero 2 hlam0
  have hσcsq2 : σc ^ 2 = ((s₁ : ℝ) : ℂ) := by rw [pow_two, hσcsq]
  have hsq : (cl_saddleZ D σc y) ^ 2
      = ((s₁ : ℝ) : ℂ) * (chartZ (D.φ D.j) y) ^ 2 / (((D.ρ D.j / 8) ^ 2 : ℝ) : ℂ) := by
    rw [cl_saddleZ_eq, mul_pow, div_pow, hσcsq2]
    rw [← Complex.ofReal_pow]
    ring
  have hmul : ((((D.ρ D.j / 8) ^ 2 : ℝ)) : ℂ) * (cl_saddleZ D σc y) ^ 2
      = ((s₁ : ℝ) : ℂ) * (chartZ (D.φ D.j) y) ^ 2 := by
    rw [hsq, mul_div_cancel₀ _ hlam]
  have hre := congrArg Complex.re hmul
  rw [cl_re_ofReal_mul, cl_re_ofReal_mul, chartZ_sq_re] at hre
  rw [hre, hsgn]
  ring

/-- **The level law in the scaled coordinate.** -/
lemma cl_saddleZ_level (D : WindowDatum f p) {σc : ℂ} {s₁ s₂ : ℝ}
    (hs1 : D.s₁ D.j = s₁) (hs2 : D.s₂ D.j = s₂) (hsgn : s₁ = -s₂)
    (hσcsq : σc * σc = ((s₁ : ℝ) : ℂ)) {y : M} (hy : y ∈ (D.φ D.j).source) :
    f y = f p + (D.ρ D.j / 8) ^ 2 * ((cl_saddleZ D σc y) ^ 2).re := by
  have hval := D.hval D.j y hy
  rw [D.hxj] at hval
  have hq := cl_saddleZ_quadratic D hsgn hσcsq y
  rw [hval, hs1, hs2]
  simp only [chartQ]
  rw [← hq]

/-- **`cl_saddleZ` is injective on the chart ball.** -/
lemma cl_injOn_saddleZ (D : WindowDatum f p) {σc : ℂ} (hσc : σc ≠ 0) :
    Set.InjOn (cl_saddleZ D σc) (modelBall (D.φ D.j) (D.ρ D.j)) := by
  have hlam0 : (D.ρ D.j / 8) ≠ 0 := by
    have := D.hρ D.j; positivity
  have hb : ((D.ρ D.j / 8 : ℝ) : ℂ) ≠ 0 := by
    rwa [Complex.ofReal_ne_zero]
  have hc : σc / ((D.ρ D.j / 8 : ℝ) : ℂ) ≠ 0 := div_ne_zero hσc hb
  intro x hx y hy hxy
  have h1 : chartZ (D.φ D.j) x = chartZ (D.φ D.j) y := by
    refine mul_left_cancel₀ hc ?_
    rw [← cl_saddleZ_eq, ← cl_saddleZ_eq]
    exact hxy
  have h3 : D.φ D.j x = D.φ D.j y :=
    cl_chartZLM_injective (by simpa [cl_chartZ_eq_chartZLM] using h1)
  exact (D.φ D.j).injOn hx.1 hy.1 h3

/-- **The differential of `cl_saddleZ` as a composition of linear maps.** -/
lemma cl_mfderiv_saddleZ (D : WindowDatum f p) (σc : ℂ) {x : M}
    (hx : x ∈ (D.φ D.j).source) :
    mfderiv (𝓡 2) 𝓘(ℝ, ℂ) (cl_saddleZ D σc) x
      = (cl_scaleCLM (σc / ((D.ρ D.j / 8 : ℝ) : ℂ))).comp
          ((cl_chartZLM).comp (mfderiv (𝓡 2) (𝓡 2) (fun y => D.φ D.j y) x)) := by
  have hφx : MDifferentiableAt (𝓡 2) (𝓡 2) (fun y => D.φ D.j y) x :=
    ((D.hφ D.j x hx).mdifferentiableWithinAt (by norm_num)).mdifferentiableAt
      ((D.φ D.j).open_source.mem_nhds hx)
  have hinner : MDifferentiableAt (𝓡 2) 𝓘(ℝ, ℂ) (fun y => cl_chartZLM (D.φ D.j y)) x := by
    have h := ((cl_chartZLM.contMDiff.comp_contMDiffOn (D.hφ D.j)).contMDiffAt
      ((D.φ D.j).open_source.mem_nhds hx)).mdifferentiableAt (by norm_num)
    simpa only [Function.comp_def] using h
  have houter : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ)
      (cl_scaleCLM (σc / ((D.ρ D.j / 8 : ℝ) : ℂ))) (cl_chartZLM (D.φ D.j x)) :=
    (cl_scaleCLM _).mdifferentiableAt
  have h2 : mfderiv (𝓡 2) 𝓘(ℝ, ℂ) (fun y => cl_chartZLM (D.φ D.j y)) x
      = (cl_chartZLM).comp (mfderiv (𝓡 2) (𝓡 2) (fun y => D.φ D.j y) x) := by
    rw [show (fun y => cl_chartZLM (D.φ D.j y)) = cl_chartZLM ∘ (fun y => D.φ D.j y) from rfl,
      mfderiv_comp x cl_chartZLM.mdifferentiableAt hφx, ContinuousLinearMap.mfderiv_eq]
  rw [show cl_saddleZ D σc
        = (cl_scaleCLM (σc / ((D.ρ D.j / 8 : ℝ) : ℂ))) ∘
            (fun y => cl_chartZLM (D.φ D.j y)) from rfl,
    mfderiv_comp x houter hinner, ContinuousLinearMap.mfderiv_eq, h2]

/-- The applied form of the chain rule for `cl_saddleZ`. -/
lemma cl_mfderiv_saddleZ_apply (D : WindowDatum f p) (σc : ℂ) {x : M}
    (hx : x ∈ (D.φ D.j).source) (v : TangentSpace (𝓡 2) x) :
    (mfderiv (𝓡 2) 𝓘(ℝ, ℂ) (cl_saddleZ D σc) x) v
      = cl_scaleCLM (σc / ((D.ρ D.j / 8 : ℝ) : ℂ))
          (cl_chartZLM ((mfderiv (𝓡 2) (𝓡 2) (fun y => D.φ D.j y) x) v)) := by
  rw [cl_mfderiv_saddleZ D σc hx]
  rfl

/-- **The differential of `cl_saddleZ` is injective on the chart ball.** -/
lemma cl_injective_mfderiv_saddleZ (D : WindowDatum f p) {σc : ℂ} (hσc : σc ≠ 0)
    {x : M} (hx : x ∈ modelBall (D.φ D.j) (D.ρ D.j)) :
    Function.Injective (mfderiv (𝓡 2) 𝓘(ℝ, ℂ) (cl_saddleZ D σc) x) := by
  have hb : ((D.ρ D.j / 8 : ℝ) : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero]
    have := D.hρ D.j; positivity
  have hc : σc / ((D.ρ D.j / 8 : ℝ) : ℂ) ≠ 0 := div_ne_zero hσc hb
  intro u v huv
  have huv' : cl_scaleCLM (σc / ((D.ρ D.j / 8 : ℝ) : ℂ))
      (cl_chartZLM ((mfderiv (𝓡 2) (𝓡 2) (fun y => D.φ D.j y) x) u))
      = cl_scaleCLM (σc / ((D.ρ D.j / 8 : ℝ) : ℂ))
        (cl_chartZLM ((mfderiv (𝓡 2) (𝓡 2) (fun y => D.φ D.j y) x) v)) := by
    rw [← cl_mfderiv_saddleZ_apply D σc hx.1 u, ← cl_mfderiv_saddleZ_apply D σc hx.1 v]
    exact huv
  have h1 : cl_chartZLM ((mfderiv (𝓡 2) (𝓡 2) (fun y => D.φ D.j y) x) u)
      = cl_chartZLM ((mfderiv (𝓡 2) (𝓡 2) (fun y => D.φ D.j y) x) v) :=
    cl_scaleCLM_injective hc huv'
  have h2 : (mfderiv (𝓡 2) (𝓡 2) (fun y => D.φ D.j y) x) u
      = (mfderiv (𝓡 2) (𝓡 2) (fun y => D.φ D.j y) x) v := cl_chartZLM_injective h1
  exact cl_injective_mfderiv_chart (D.hφ D.j) (D.hφ' D.j) hx.1 h2

/-- If `a * b = a` then `a * (C * (b * u)) = C * (a * u)`. -/
lemma cl_scalar_mul_of_mul_eq (a b u C : ℝ) (h : a * b = a) :
    a * (C * (b * u)) = C * (a * u) := by
  calc a * (C * (b * u)) = C * (a * (b * u)) := by ring
    _ = C * ((a * b) * u) := by rw [mul_assoc]
    _ = C * (a * u) := by rw [h]

/-- If `a * b = -a` then `a * (C * (b * u)) = C * (-(a * u))`. -/
lemma cl_scalar_mul_of_mul_eq_neg (a b u C : ℝ) (h : a * b = -a) :
    a * (C * (b * u)) = C * (-(a * u)) := by
  calc a * (C * (b * u)) = C * (a * (b * u)) := by ring
    _ = C * ((a * b) * u) := by rw [mul_assoc]
    _ = C * ((-a) * u) := by rw [h]
    _ = C * (-(a * u)) := by ring

/-- **The flow identity in the scaled saddle coordinate.** -/
lemma cl_hasDerivAt_saddleZ (D : WindowDatum f p) {σc : ℂ} {s₁ s₂ : ℝ}
    (hs1 : D.s₁ D.j = s₁) (hs2 : D.s₂ D.j = s₂) (hσcn : ‖σc‖ = 1)
    (hre1 : σc.re * s₁ = σc.re) (him2 : σc.im * s₂ = σc.im)
    (him1 : σc.im * s₁ = -σc.im) (hre2 : σc.re * s₂ = -σc.re)
    {y : M} {τ : ℝ}
    (hy : ∀ u ∈ Set.Icc (min 0 τ) (max 0 τ), D.Φ (u, y) ∈ D.C D.j) :
    HasDerivAt (fun σ : ℝ => (cl_saddleZ D σc (D.Φ (σ, y))).re)
        (chartMult (D.ρ D.j / 8) ((D.ρ D.j / 8) ^ 2 * ‖cl_saddleZ D σc (D.Φ (τ, y))‖ ^ 2)
          * (cl_saddleZ D σc (D.Φ (τ, y))).re) τ ∧
      HasDerivAt (fun σ : ℝ => (cl_saddleZ D σc (D.Φ (σ, y))).im)
        (chartMult (D.ρ D.j / 8) ((D.ρ D.j / 8) ^ 2 * ‖cl_saddleZ D σc (D.Φ (τ, y))‖ ^ 2)
          * (-(cl_saddleZ D σc (D.Φ (τ, y))).im)) τ := by
  obtain ⟨hd0, hd1⟩ := D.hODE D.j y τ hy
  rw [hs1] at hd0
  rw [hs2] at hd1
  have harg : (D.ρ D.j / 8) ^ 2 * ‖cl_saddleZ D σc (D.Φ (τ, y))‖ ^ 2
      = ‖D.φ D.j (D.Φ (τ, y))‖ ^ 2 := cl_lam_mul_norm_saddleZ_sq D hσcn _
  constructor
  · -- the real part
    have hbase : HasDerivAt (fun σ : ℝ => (σc.re * D.φ D.j (D.Φ (σ, y)) 0
        - σc.im * D.φ D.j (D.Φ (σ, y)) 1) / (D.ρ D.j / 8)) _ τ :=
      (((hd0.const_mul σc.re).sub (hd1.const_mul σc.im))).div_const (D.ρ D.j / 8)
    have hfix : (fun σ : ℝ => (cl_saddleZ D σc (D.Φ (σ, y))).re) =ᶠ[𝓝 τ]
        (fun σ : ℝ => (σc.re * D.φ D.j (D.Φ (σ, y)) 0
            - σc.im * D.φ D.j (D.Φ (σ, y)) 1) / (D.ρ D.j / 8)) := by
      filter_upwards with σ
      rw [cl_saddleZ_re]
    refine (hbase.congr_of_eventuallyEq hfix).congr_deriv ?_
    rw [harg, cl_saddleZ_re,
      cl_scalar_mul_of_mul_eq σc.re s₁ (D.φ D.j (D.Φ (τ, y)) 0)
        (chartMult (D.ρ D.j / 8) (‖D.φ D.j (D.Φ (τ, y))‖ ^ 2)) hre1,
      cl_scalar_mul_of_mul_eq σc.im s₂ (D.φ D.j (D.Φ (τ, y)) 1)
        (chartMult (D.ρ D.j / 8) (‖D.φ D.j (D.Φ (τ, y))‖ ^ 2)) him2,
      ← mul_div_assoc]
    congr 1
    ring
  · -- the imaginary part
    have hbase : HasDerivAt (fun σ : ℝ => (σc.im * D.φ D.j (D.Φ (σ, y)) 0
        + σc.re * D.φ D.j (D.Φ (σ, y)) 1) / (D.ρ D.j / 8)) _ τ :=
      (((hd0.const_mul σc.im).add (hd1.const_mul σc.re))).div_const (D.ρ D.j / 8)
    have hfix : (fun σ : ℝ => (cl_saddleZ D σc (D.Φ (σ, y))).im) =ᶠ[𝓝 τ]
        (fun σ : ℝ => (σc.im * D.φ D.j (D.Φ (σ, y)) 0
            + σc.re * D.φ D.j (D.Φ (σ, y)) 1) / (D.ρ D.j / 8)) := by
      filter_upwards with σ
      rw [cl_saddleZ_im]
    refine (hbase.congr_of_eventuallyEq hfix).congr_deriv ?_
    rw [harg, cl_saddleZ_im,
      cl_scalar_mul_of_mul_eq_neg σc.im s₁ (D.φ D.j (D.Φ (τ, y)) 0)
        (chartMult (D.ρ D.j / 8) (‖D.φ D.j (D.Φ (τ, y))‖ ^ 2)) him1,
      cl_scalar_mul_of_mul_eq_neg σc.re s₂ (D.φ D.j (D.Φ (τ, y)) 1)
        (chartMult (D.ρ D.j / 8) (‖D.φ D.j (D.Φ (τ, y))‖ ^ 2)) hre2,
      ← neg_div, ← mul_div_assoc]
    congr 1
    ring

theorem saddleChartLayer {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    {f : M → ℝ} {p : M} (D : Work.Drive.N2.WindowDatum f p)
    (hsgn : D.s₁ D.j = - D.s₂ D.j) :
    ∃ (φ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 2))) (σc : ℂ) (Z : M → ℂ)
      (lam0 lam : ℝ),
      (σc = 1 ∨ σc = Complex.I) ∧ lam0 = D.ρ D.j / 8 ∧ lam = lam0 ^ 2 ∧
      φ.source = (D.φ D.j).source ∧
      (∀ r : ℝ, Work.Drive.N2.modelBall φ r = Work.Drive.N2.modelBall (D.φ D.j) r) ∧
      (∀ y : M, Z y = σc * (((φ y 0 : ℝ) : ℂ) + ((φ y 1 : ℝ) : ℂ) * Complex.I) / (lam0 : ℂ)) ∧
      (∀ y ∈ Work.Drive.N2.modelBall (D.φ D.j) (D.ρ D.j),
        f y = f p + lam * ((Z y) ^ 2).re) ∧
      ContMDiffOn (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
        (modelWithCornersSelf ℝ ℂ) ((⊤ : ℕ∞) : WithTop ℕ∞) Z
        (Work.Drive.N2.modelBall (D.φ D.j) (D.ρ D.j)) ∧
      Set.InjOn Z (Work.Drive.N2.modelBall (D.φ D.j) (D.ρ D.j)) ∧
      (∀ x ∈ Work.Drive.N2.modelBall (D.φ D.j) (D.ρ D.j),
        Function.Injective (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
          (modelWithCornersSelf ℝ ℂ) Z x)) ∧
      (∀ (y : M) (τ : ℝ),
        (∀ u ∈ Set.Icc (min 0 τ) (max 0 τ), D.Φ (u, y) ∈ D.C D.j) →
        HasDerivAt (fun σ : ℝ => (Z (D.Φ (σ, y))).re)
          (Work.Drive.N2.chartMult (D.ρ D.j / 8) (lam * ‖Z (D.Φ (τ, y))‖ ^ 2)
            * (Z (D.Φ (τ, y))).re) τ ∧
        HasDerivAt (fun σ : ℝ => (Z (D.Φ (σ, y))).im)
          (Work.Drive.N2.chartMult (D.ρ D.j / 8) (lam * ‖Z (D.Φ (τ, y))‖ ^ 2)
            * (-(Z (D.Φ (τ, y))).im)) τ) := by
  rcases D.hsgn D.j with ⟨h1, h2⟩
  rcases h1 with h1 | h1
  · -- `s₁ = 1`, hence `s₂ = -1`: the scaled coordinate with `σc = 1`
    have hs2 : D.s₂ D.j = -1 := by linarith [hsgn, h1]
    refine ⟨D.φ D.j, 1, cl_saddleZ D 1, D.ρ D.j / 8, (D.ρ D.j / 8) ^ 2, Or.inl rfl, rfl,
      rfl, rfl, fun r => rfl, fun y => cl_saddleZ_apply D 1 y, ?_, ?_, ?_, ?_, ?_⟩
    · intro y hy
      exact cl_saddleZ_level D h1 hs2 (by norm_num) (by norm_num) hy.1
    · exact cl_contMDiffOn_saddleZ D 1
    · exact cl_injOn_saddleZ D one_ne_zero
    · intro x hx
      exact cl_injective_mfderiv_saddleZ D one_ne_zero hx
    · intro y τ hy
      exact cl_hasDerivAt_saddleZ D h1 hs2 (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) hy
  · -- `s₁ = -1`, hence `s₂ = 1`: the scaled coordinate with `σc = I`
    have hs2 : D.s₂ D.j = 1 := by linarith [hsgn, h1]
    have hI : Complex.I * Complex.I = ((-1 : ℝ) : ℂ) := by
      rw [Complex.I_mul_I]; norm_num
    have hIn : ‖Complex.I‖ = 1 := by simp
    refine ⟨D.φ D.j, Complex.I, cl_saddleZ D Complex.I, D.ρ D.j / 8, (D.ρ D.j / 8) ^ 2,
      Or.inr rfl, rfl, rfl, rfl, fun r => rfl, fun y => cl_saddleZ_apply D Complex.I y,
      ?_, ?_, ?_, ?_, ?_⟩
    · intro y hy
      exact cl_saddleZ_level D h1 hs2 (by norm_num) hI hy.1
    · exact cl_contMDiffOn_saddleZ D Complex.I
    · exact cl_injOn_saddleZ D Complex.I_ne_zero
    · intro x hx
      exact cl_injective_mfderiv_saddleZ D Complex.I_ne_zero hx
    · intro y τ hy
      exact cl_hasDerivAt_saddleZ D h1 hs2 hIn (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) hy

end Work.Drive.N2
