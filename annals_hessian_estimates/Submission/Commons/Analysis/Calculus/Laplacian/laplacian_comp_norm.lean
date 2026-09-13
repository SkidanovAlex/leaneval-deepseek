import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Topology.GDelta.MetrizableSpace
import Submission.Commons.Analysis.InnerProductSpace.fderiv_norm_single
import Submission.Commons.Analysis.InnerProductSpace.orthonormalBasis_normSq_sum
import Submission.Commons.Analysis.Calculus.FDeriv.fderiv_fderiv_nonneg_of_localMin

namespace Commons.Analysis.Calculus.Laplacian

open scoped RealInnerProductSpace
open scoped BigOperators
open scoped Topology

set_option autoImplicit false

/-- The derivative at `0` of `t ↦ ‖y + t • W‖` for `y ≠ 0` is `⟪y, W⟫ / ‖y‖`. -/
lemma deriv_norm_line {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (y W : E) (hy : y ≠ 0) :
    deriv (fun t : ℝ => ‖y + t • W‖) 0 = inner ℝ y W / ‖y‖ := by
  have hψ0 : HasDerivAt (fun t : ℝ => y + t • W) W 0 := by
    have h1 : HasDerivAt (fun t : ℝ => t • W) ((1:ℝ) • W) 0 :=
      (hasDerivAt_id (0:ℝ)).smul_const W
    have h2 : HasDerivAt (fun t : ℝ => y + t • W) ((1:ℝ) • W) 0 := h1.const_add y
    simpa using h2
  have hN : HasFDerivAt (fun z : E => ‖z‖) ((‖y‖)⁻¹ • innerSL ℝ y) y :=
    Commons.Analysis.InnerProductSpace.hasFDerivAt_norm_ne_zero hy
  have hN' : HasFDerivAt (fun z : E => ‖z‖) ((‖y‖)⁻¹ • innerSL ℝ y) (y + (0:ℝ) • W) := by
    simpa using hN
  have hcomp := hN'.comp_hasDerivAt 0 hψ0
  have hval : (((‖y‖)⁻¹ • innerSL ℝ y) W) = inner ℝ y W / ‖y‖ := by
    simp only [smul_apply, smul_eq_mul, innerSL_apply_apply]
    rw [div_eq_inv_mul]
  simpa only [Function.comp_def, hval] using hcomp.deriv

/-- The second derivative at `0` of `t ↦ ‖y + t • W‖` for `y ≠ 0`. -/
lemma radial_norm_second_deriv_line {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (y W : E) (hy : y ≠ 0) :
    deriv (deriv (fun t : ℝ => ‖y + t • W‖)) 0
      = ‖W‖ ^ 2 / ‖y‖ - (inner ℝ y W) ^ 2 / ‖y‖ ^ 3 := by
  have hψ0 : HasDerivAt (fun t : ℝ => y + t • W) W 0 := by
    have h1 : HasDerivAt (fun t : ℝ => t • W) ((1:ℝ) • W) 0 :=
      (hasDerivAt_id (0:ℝ)).smul_const W
    have h2 : HasDerivAt (fun t : ℝ => y + t • W) ((1:ℝ) • W) 0 := h1.const_add y
    simpa using h2
  have hev : ∀ᶠ t in 𝓝 (0:ℝ), y + t • W ≠ 0 := by
    have hc : ContinuousAt (fun t : ℝ => y + t • W) 0 := by fun_prop
    exact hc.eventually (isOpen_compl_singleton.mem_nhds (by simpa using hy))
  have hyne : ‖y‖ ≠ 0 := norm_ne_zero_iff.mpr hy
  have hFG : deriv (fun t : ℝ => ‖y + t • W‖)
      =ᶠ[𝓝 (0:ℝ)] ((fun t : ℝ => inner ℝ (y + t • W) W) / fun t : ℝ => ‖y + t • W‖) := by
    filter_upwards [hev] with t ht
    have hψt : HasDerivAt (fun s : ℝ => y + s • W) W t := by
      have h1 : HasDerivAt (fun s : ℝ => s • W) ((1:ℝ) • W) t :=
        (hasDerivAt_id t).smul_const W
      have h2 : HasDerivAt (fun s : ℝ => y + s • W) ((1:ℝ) • W) t := h1.const_add y
      simpa using h2
    have hN : HasFDerivAt (fun z : E => ‖z‖)
        ((‖y + t • W‖)⁻¹ • innerSL ℝ (y + t • W)) (y + t • W) :=
      Commons.Analysis.InnerProductSpace.hasFDerivAt_norm_ne_zero ht
    have hcomp := hN.comp_hasDerivAt t hψt
    have hderiv : deriv (fun t : ℝ => ‖y + t • W‖) t
        = ((‖y + t • W‖)⁻¹ • innerSL ℝ (y + t • W)) W := hcomp.deriv
    rw [hderiv]
    simp only [smul_apply, smul_eq_mul, innerSL_apply_apply, Pi.div_apply]
    rw [div_eq_inv_mul]
  have hu : HasDerivAt (fun t : ℝ => inner ℝ (y + t • W) W) (inner ℝ W W) 0 := by
    have hfun : (fun t : ℝ => inner ℝ (y + t • W) W)
        = fun t : ℝ => inner ℝ y W + t * inner ℝ W W := by
      funext t
      rw [inner_add_left, real_inner_smul_left]
    rw [hfun]
    have h1 : HasDerivAt (fun t : ℝ => t * inner ℝ W W) (inner ℝ W W) 0 := by
      simpa using (hasDerivAt_id (0:ℝ)).mul_const (inner ℝ W W)
    simpa using h1.const_add (inner ℝ y W)
  have hv : HasDerivAt (fun t : ℝ => ‖y + t • W‖) (inner ℝ y W / ‖y‖) 0 := by
    have hN : HasFDerivAt (fun z : E => ‖z‖) ((‖y‖)⁻¹ • innerSL ℝ y) y :=
      Commons.Analysis.InnerProductSpace.hasFDerivAt_norm_ne_zero hy
    have hN' : HasFDerivAt (fun z : E => ‖z‖) ((‖y‖)⁻¹ • innerSL ℝ y) (y + (0:ℝ) • W) := by
      simpa using hN
    have hcomp := hN'.comp_hasDerivAt 0 hψ0
    have hval : (((‖y‖)⁻¹ • innerSL ℝ y) W) = inner ℝ y W / ‖y‖ := by
      simp only [smul_apply, smul_eq_mul, innerSL_apply_apply]
      rw [div_eq_inv_mul]
    simpa only [Function.comp_def, hval] using hcomp
  have hF : deriv ((fun t : ℝ => inner ℝ (y + t • W) W) / fun t : ℝ => ‖y + t • W‖) 0
      = ‖W‖ ^ 2 / ‖y‖ - (inner ℝ y W) ^ 2 / ‖y‖ ^ 3 := by
    have hdiv := HasDerivAt.div hu hv (by simpa using hyne)
    rw [hdiv.deriv]
    rw [real_inner_self_eq_norm_sq]
    simp only [zero_smul, add_zero]
    field_simp
  rw [hFG.deriv_eq, hF]

/-- **One-dimensional second-order chain rule.**
If `φ` is `C²` at `ρ 0` and `ρ` is `C²` at `0`, then
`(φ ∘ ρ)''(0) = φ''(ρ 0) · (ρ'(0))² + φ'(ρ 0) · ρ''(0)`. -/
lemma radial_deriv_deriv_comp {φ ρ : ℝ → ℝ} (hφ : ContDiffAt ℝ 2 φ (ρ 0))
    (hρ : ContDiffAt ℝ 2 ρ 0) :
    deriv (deriv (φ ∘ ρ)) 0
      = deriv (deriv φ) (ρ 0) * (deriv ρ 0) ^ 2 + deriv φ (ρ 0) * deriv (deriv ρ) 0 := by
  have hφ' : ContDiffAt ℝ 1 (deriv φ) (ρ 0) := hφ.derivWithin (m := 1) (by norm_num)
  have hρ' : ContDiffAt ℝ 1 (deriv ρ) 0 := hρ.derivWithin (m := 1) (by norm_num)
  have hdφ' : DifferentiableAt ℝ (deriv φ) (ρ 0) := hφ'.differentiableAt (by norm_num)
  have hdρ : DifferentiableAt ℝ ρ 0 := hρ.differentiableAt (by norm_num)
  have hdρ' : DifferentiableAt ℝ (deriv ρ) 0 := hρ'.differentiableAt (by norm_num)
  have hdφev : ∀ᶠ z in 𝓝 (ρ 0), DifferentiableAt ℝ φ z :=
    (hφ.eventually (by norm_num)).mono (fun z hz => hz.differentiableAt (by norm_num))
  have hev : deriv (φ ∘ ρ) =ᶠ[𝓝 (0:ℝ)] fun t => deriv φ (ρ t) * deriv ρ t := by
    filter_upwards [hρ.continuousAt.tendsto.eventually hdφev,
      (hρ.eventually (by norm_num)).mono (fun t ht => ht.differentiableAt (by norm_num))]
      with t h1 h2
    exact deriv_comp (hh₂ := h1) (hh := h2)
  rw [hev.deriv_eq]
  have hc : DifferentiableAt ℝ (fun t => deriv φ (ρ t)) 0 :=
    DifferentiableAt.fun_comp' 0 (g := deriv φ) (f := ρ) hdφ' hdρ
  have hdc : deriv (fun t => deriv φ (ρ t)) 0 = deriv (deriv φ) (ρ 0) * deriv ρ 0 := by
    have h := deriv_comp (hh₂ := hdφ') (hh := hdρ)
    simpa only [Function.comp_def] using h
  rw [deriv_fun_mul hc hdρ', hdc]
  ring

/-- **Second directional derivative of a radial function.**
For `y ≠ 0`, `φ` twice differentiable at `‖y‖` and `W : E`,
the second derivative of `z ↦ φ ‖z‖` at `y` in the direction `W` is
`φ''(‖y‖) · (⟪y,W⟫/‖y‖)² + φ'(‖y‖) · (‖W‖²/‖y‖ - ⟪y,W⟫²/‖y‖³)`. -/
lemma iteratedFDeriv_two_comp_norm_apply {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {φ : ℝ → ℝ} {y : E} (hy : y ≠ 0)
    (hφ : ContDiffAt ℝ 2 φ ‖y‖) (W : E) :
    (iteratedFDeriv ℝ 2 (fun z : E => φ ‖z‖) y) ![W, W]
      = deriv (deriv φ) ‖y‖ * (inner ℝ y W / ‖y‖) ^ 2
        + deriv φ ‖y‖ * (‖W‖ ^ 2 / ‖y‖ - (inner ℝ y W) ^ 2 / ‖y‖ ^ 3) := by
  have hf : ContDiffAt ℝ 2 (fun z : E => φ ‖z‖) y :=
    hφ.comp y ((contDiffAt_id (x := y)).norm ℝ hy)
  have hline : ContDiffAt ℝ 2 (fun t : ℝ => y + t • W) 0 := by fun_prop
  have hρ : ContDiffAt ℝ 2 (fun t : ℝ => ‖y + t • W‖) 0 :=
    hline.norm ℝ (by simpa using hy)
  have hmain : deriv (deriv (fun t : ℝ => φ ‖y + t • W‖)) 0
      = deriv (deriv φ) ‖y‖ * (inner ℝ y W / ‖y‖) ^ 2
        + deriv φ ‖y‖ * (‖W‖ ^ 2 / ‖y‖ - (inner ℝ y W) ^ 2 / ‖y‖ ^ 3) := by
    have h := radial_deriv_deriv_comp (φ := φ) (ρ := fun t : ℝ => ‖y + t • W‖)
      (by simpa using hφ) hρ
    rw [deriv_norm_line y W hy, radial_norm_second_deriv_line y W hy] at h
    simpa only [Function.comp_def, zero_smul, add_zero] using h
  rw [iteratedFDeriv_two_apply]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [← Commons.Analysis.Calculus.FDeriv.deriv_deriv_comp_line hf W]
  simpa only [Function.comp_def] using hmain

/-- **The Laplacian of a radial function.**
For `E` a finite-dimensional real inner product space, `φ : ℝ → ℝ` twice differentiable at
`‖y‖` and `y ≠ 0`,
`Δ (z ↦ φ ‖z‖) y = φ''(‖y‖) + ((finrank ℝ E) - 1) / ‖y‖ * φ'(‖y‖)`.
Suggested proof: compute the second derivative in each direction `b i` of an orthonormal basis
via `Commons.Analysis.Calculus.FDeriv.deriv_deriv_comp_line`, the one-dimensional chain rule
`(φ ∘ ρ)'' = φ''(ρ) ρ'^2 + φ' ρ''` and `ρ(t) = ‖y + t • b i‖` with `ρ'(0) = ⟪y, b i⟫/‖y‖`,
`ρ''(0) = (1 - (⟪y, b i⟫/‖y‖)^2)/‖y‖`; then sum over `i` using `∑ i, ⟪y, b i⟫^2 = ‖y‖^2`. -/
theorem laplacian_comp_norm {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {φ : ℝ → ℝ} {y : E} (hy : y ≠ 0) (hφ : ContDiffAt ℝ 2 φ ‖y‖) :
    Laplacian.laplacian (fun z : E => φ ‖z‖) y =
      deriv (deriv φ) ‖y‖ + ((Module.finrank ℝ E : ℝ) - 1) / ‖y‖ * deriv φ ‖y‖ := by
  classical
  let v : OrthonormalBasis (Fin (Module.finrank ℝ E)) ℝ E := stdOrthonormalBasis ℝ E
  have hlap : Laplacian.laplacian (fun z : E => φ ‖z‖) y
      = ∑ i, iteratedFDeriv ℝ 2 (fun z : E => φ ‖z‖) y ![(v i), (v i)] := by
    have h := congrFun (_root_.InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis
      (fun z : E => φ ‖z‖) v) y
    simpa using h
  have hsum_sq : ∑ i : Fin (Module.finrank ℝ E), (inner ℝ y (v i)) ^ 2 = ‖y‖ ^ 2 := by
    rw [Commons.Analysis.InnerProductSpace.orthonormalBasis_normSq_sum v y]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [OrthonormalBasis.repr_apply_apply, real_inner_comm]
  have hsum_norm : ∑ i : Fin (Module.finrank ℝ E), ‖v i‖ ^ 2 = (Module.finrank ℝ E : ℝ) := by
    have h1 : ∀ i : Fin (Module.finrank ℝ E), ‖v i‖ ^ 2 = (1:ℝ) := by
      intro i
      rw [v.orthonormal.norm_eq_one i]
      norm_num
    rw [Finset.sum_congr rfl (fun i _ => h1 i)]
    simp
  have hterm : ∀ i : Fin (Module.finrank ℝ E),
      deriv (deriv φ) ‖y‖ * (inner ℝ y (v i) / ‖y‖) ^ 2
        + deriv φ ‖y‖ * (‖v i‖ ^ 2 / ‖y‖ - (inner ℝ y (v i)) ^ 2 / ‖y‖ ^ 3)
      = (deriv (deriv φ) ‖y‖ / ‖y‖ ^ 2 - deriv φ ‖y‖ / ‖y‖ ^ 3) * (inner ℝ y (v i)) ^ 2
        + deriv φ ‖y‖ * (‖v i‖ ^ 2 / ‖y‖) := by
    intro i
    ring
  have hr : ‖y‖ ≠ 0 := norm_ne_zero_iff.mpr hy
  rw [hlap,
    Finset.sum_congr rfl (fun i _ => iteratedFDeriv_two_comp_norm_apply hy hφ (v i)),
    Finset.sum_congr rfl (fun i _ => hterm i),
    Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hsum_sq,
    ← Finset.sum_div, hsum_norm]
  field_simp
  ring

end Commons.Analysis.Calculus.Laplacian