/-
Copyright: work module for the Elgindi finite-time singularity project.

# `sin θ cos²θ` is in the kernel of the adjoint of `L₀`

Elgindi, Annals 194 (3) 2021, §'Elliptic Regularity Estimates'.  The `α = 0` part of the
elliptic operator (PolarBSL) is

  `L₀(Ψ)(z,θ) = -∂_θθΨ + ∂_θ(tan θ · Ψ) - 6Ψ`   (`Work.Elliptic.Lzero`),

and the angular weight of the solvability condition of Proposition `prop:L2` is
`φ(θ) = sin θ cos²θ` (`Work.Elliptic.sinCos2`).  The point of this file is that the two are
formally adjoint on `[0,π/2]` with Dirichlet conditions `Ψ(z,0) = Ψ(z,π/2) = 0`:

  `∫_0^{π/2} L₀(Ψ)(z,θ) · sin θ cos²θ dθ = 0`.

Concretely, for `f = Ψ z` the integrand is an exact `θ`-derivative,

  `L₀(Ψ) · φ = d/dθ [ -f'(θ) · sin θ cos²θ + f(θ) · cos θ cos 2θ ]`,

(the bracket has the alternative, manifestly smooth form `-f'(θ) sinθcos²θ + f(θ) cosθ cos2θ`
once `tan θ · φ(θ) = sin²θ cosθ` and `φ'(θ) = cosθ cos2θ - sin²θ cosθ` are used), and the
bracket vanishes at both endpoints *because* `φ` vanishes there together with `f`.  This is
the analytic content of `LzeroAdj_sinCos2 = 0` (see the header of `Work.Elliptic.Defs`).

The theorem is stated with the second order hypothesis `ContDiffOn ℝ 2 (Ψ z) (Icc 0 π/2)`
only: the endpoint values of `deriv (Ψ z)` are irrelevant since they are multiplied by the
vanishing weight `φ`.  For the same reason the proof integrates the *smooth* antiderivative
`H` built from `derivWithin f (Icc 0 (π/2))` (which is `C¹` on the closed interval by
`ContDiffOn.derivWithin`) rather than the `deriv f`-version, which is what makes
`intervalIntegral.integral_deriv_of_contDiffOn_Icc` applicable.
-/
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff
import Mathlib.Order.CompletePartialOrder
import Submission.Work.Elliptic.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Elliptic

set_option autoImplicit false

/-! ## Two elementary rewritings of `L₀` -/

/-- `L₀` written with the one-variable derivatives of `f = Ψ z`:
`L₀(Ψ)(z,θ) = -(deriv (deriv f)) θ + deriv (tan · f) θ - 6 f θ`. -/
lemma Lzero_eq_deriv (Ψ : ℝ → ℝ → ℝ) (z x : ℝ) :
    Lzero Ψ z x = -(deriv (deriv (fun θ : ℝ => Ψ z θ)) x)
      + deriv (fun θ : ℝ => Real.tan θ * Ψ z θ) x - 6 * Ψ z x := by
  unfold Lzero
  simp only [Work.Spaces.pthIter_succ, Work.Spaces.pthIter_zero, Work.Spaces.pth]

/-- `deriv sinCos2 θ = cos θ ^ 3 - 2 sin θ ^ 2 cos θ`. -/
lemma deriv_sinCos2 (x : ℝ) :
    deriv sinCos2 x = Real.cos x ^ 3 - 2 * Real.sin x ^ 2 * Real.cos x := by
  unfold sinCos2
  have h : HasDerivAt (fun θ : ℝ => Real.sin θ * Real.cos θ ^ 2)
      (Real.cos x * Real.cos x ^ 2
        + Real.sin x * (2 * Real.cos x ^ (2-1) * (-Real.sin x))) x :=
    (Real.hasDerivAt_sin x).mul ((Real.hasDerivAt_cos x).pow 2)
  have h' : Real.cos x * Real.cos x ^ 2
      + Real.sin x * (2 * Real.cos x ^ (2-1) * (-Real.sin x))
      = Real.cos x ^ 3 - 2 * Real.sin x ^ 2 * Real.cos x := by ring
  exact (h.congr_deriv h').deriv

/-- `deriv (fun θ ↦ cos θ · cos 2θ) x = sin x - 6 sin x cos²x`. -/
lemma deriv_cos_mul_cos_two (x : ℝ) :
    deriv (fun θ : ℝ => Real.cos θ * Real.cos (2 * θ)) x
      = Real.sin x - 6 * Real.sin x * Real.cos x ^ 2 := by
  have h : HasDerivAt (fun θ : ℝ => Real.cos θ * Real.cos (2 * θ))
      ((-Real.sin x) * Real.cos (2*x) + Real.cos x * (-Real.sin (2*x) * 2)) x := by
    have h₂ : HasDerivAt (fun θ : ℝ => Real.cos (2*θ)) (-Real.sin (2*x) * 2) x := by
      have := (Real.hasDerivAt_cos (2*x)).comp x (hasDerivAt_const_mul (x := x) 2)
      simpa [Function.comp_def, mul_comm] using this
    exact (Real.hasDerivAt_cos x).mul h₂
  have h' : (-Real.sin x) * Real.cos (2*x) + Real.cos x * (-Real.sin (2*x) * 2)
      = Real.sin x - 6 * Real.sin x * Real.cos x ^ 2 := by
    rw [Real.cos_two_mul, Real.sin_two_mul]; ring
  exact (h.congr_deriv h').deriv

/-! ## The antiderivative of the integrand -/

/-- `sinCos2` is differentiable. -/
lemma differentiableAt_sinCos2 (x : ℝ) : DifferentiableAt ℝ sinCos2 x := by
  unfold sinCos2; fun_prop

/-- `θ ↦ cos θ · cos 2θ` is differentiable. -/
lemma differentiableAt_cosCosTwo (x : ℝ) :
    DifferentiableAt ℝ (fun θ : ℝ => Real.cos θ * Real.cos (2 * θ)) x := by
  fun_prop

/-- **The pointwise identity behind the orthogonality.**  For `x` in the *open* interval, where
`tan` is differentiable and all the `deriv`'s in `Lzero` are honest derivatives, the function

  `F(θ) = -(deriv f) θ · sinCos2 θ + f θ · cos θ cos 2θ`  (with `f = Ψ z`)

has derivative `L₀(Ψ)(z,x) · sinCos2 x`: the two identities
`φ'' + tan θ φ' + 6φ = 0` and `(tan θ · φ)' = φ'` conspire so that the `(cos θ cos 2θ)`
correction absorbs the `tan`-singularity. -/
lemma hasDerivAt_Lzero_antideriv (Ψ : ℝ → ℝ → ℝ) (z x : ℝ) (hx : x ∈ Set.Ioo 0 (π / 2))
    (h2 : ContDiffAt ℝ 2 (fun θ : ℝ => Ψ z θ) x) :
    HasDerivAt (fun θ : ℝ => -(deriv (fun θ : ℝ => Ψ z θ) θ) * sinCos2 θ
        + Ψ z θ * (Real.cos θ * Real.cos (2 * θ)))
      (Lzero Ψ z x * sinCos2 x) x := by
  have hcos : Real.cos x ≠ 0 := by
    have : x ∈ Set.Ioo (-(Real.pi/2)) (Real.pi/2) :=
      ⟨by linarith [hx.1, Real.pi_pos], by linarith [hx.2, Real.pi_pos]⟩
    exact ne_of_gt (Real.cos_pos_of_mem_Ioo this)
  have hfd : HasDerivAt (fun θ : ℝ => Ψ z θ) (deriv (fun θ : ℝ => Ψ z θ) x) x :=
    (h2.differentiableAt (by norm_num)).hasDerivAt
  have hd : ContDiffAt ℝ 1 (deriv (fun θ : ℝ => Ψ z θ)) x :=
    h2.derivWithin (by norm_num)
  have hfd2 : HasDerivAt (deriv (fun θ : ℝ => Ψ z θ))
      (deriv (deriv (fun θ : ℝ => Ψ z θ)) x) x :=
    (hd.differentiableAt (by norm_num)).hasDerivAt
  have htan : HasDerivAt (fun θ : ℝ => Real.tan θ * Ψ z θ)
      ((1/Real.cos x^2) * Ψ z x + Real.tan x * deriv (fun θ : ℝ => Ψ z θ) x) x :=
    (Real.hasDerivAt_tan hcos).mul hfd
  have hφ : HasDerivAt sinCos2 (Real.cos x ^ 3 - 2 * Real.sin x ^ 2 * Real.cos x) x :=
    (differentiableAt_sinCos2 x).hasDerivAt.congr_deriv (deriv_sinCos2 x)
  have hψ : HasDerivAt (fun θ : ℝ => Real.cos θ * Real.cos (2 * θ))
      (Real.sin x - 6 * Real.sin x * Real.cos x ^ 2) x :=
    (differentiableAt_cosCosTwo x).hasDerivAt.congr_deriv (deriv_cos_mul_cos_two x)
  have hF := ((hfd2.neg).mul hφ).add (hfd.mul hψ)
  refine hF.congr_deriv ?_
  rw [Lzero_eq_deriv, htan.deriv]
  unfold sinCos2
  simp only [Pi.neg_apply]
  rw [Real.tan_eq_sin_div_cos, Real.cos_two_mul]
  field_simp
  linear_combination (Real.cos x * deriv (fun θ : ℝ => Ψ z θ) x) * Real.sin_sq_add_cos_sq x

/-! ## The orthogonality -/

theorem Lzero_orthogonal (Ψ : ℝ → ℝ → ℝ) (z : ℝ)
    (hsm : ContDiffOn ℝ 2 (fun θ : ℝ => Ψ z θ) (Set.Icc 0 (π / 2)))
    (h0 : Ψ z 0 = 0) (h1 : Ψ z (π / 2) = 0) :
    ∫ θ in Work.Spaces.Iθ, Work.Elliptic.Lzero Ψ z θ * Work.Elliptic.sinCos2 θ = 0 := by
  have hle : (0:ℝ) ≤ π/2 := by positivity
  have hlt : (0:ℝ) < π/2 := by positivity
  -- the antiderivative `H`, built from `derivWithin` so that it is `C¹` on the closed interval
  set f : ℝ → ℝ := fun θ => Ψ z θ with hf
  set H : ℝ → ℝ := fun θ => -(derivWithin f (Set.Icc 0 (π/2)) θ) * sinCos2 θ
      + f θ * (Real.cos θ * Real.cos (2 * θ)) with hHdef
  have hsm_f : ContDiffOn ℝ 2 f (Set.Icc 0 (π/2)) := by rw [hf]; exact hsm
  have hHcd : ContDiffOn ℝ 1 H (Set.Icc 0 (π/2)) := by
    rw [hHdef]
    have hu : UniqueDiffOn ℝ (Set.Icc (0:ℝ) (π/2)) := uniqueDiffOn_Icc hlt
    have hdw : ContDiffOn ℝ 1 (derivWithin f (Set.Icc 0 (π/2))) (Set.Icc 0 (π/2)) :=
      hsm_f.derivWithin hu (by norm_num)
    have hsm1 : ContDiffOn ℝ 1 f (Set.Icc 0 (π/2)) := hsm_f.of_le (by norm_num)
    have hsincos : ContDiffOn ℝ 1 sinCos2 (Set.Icc 0 (π/2)) := by
      unfold sinCos2; fun_prop
    have hcc : ContDiffOn ℝ 1 (fun θ : ℝ => Real.cos θ * Real.cos (2 * θ))
        (Set.Icc 0 (π/2)) := by fun_prop
    exact (hdw.neg.mul hsincos).add (hsm1.mul hcc)
  have hFTC := intervalIntegral.integral_deriv_of_contDiffOn_Icc hHcd hle
  -- on the open interval `H` is the `deriv`-version of the antiderivative, hence computes `Lzero·φ`
  have hpoint : ∀ θ ∈ Set.Ioo (0:ℝ) (π/2),
      Lzero Ψ z θ * sinCos2 θ = deriv H θ := by
    intro θ hθ
    have h2 : ContDiffAt ℝ 2 (fun θ : ℝ => Ψ z θ) θ :=
      hsm.contDiffAt (Icc_mem_nhds hθ.1 hθ.2)
    have hHF : H =ᶠ[𝓝 θ] (fun θ : ℝ => -(deriv (fun θ : ℝ => Ψ z θ) θ) * sinCos2 θ
        + Ψ z θ * (Real.cos θ * Real.cos (2 * θ))) := by
      filter_upwards [Ioo_mem_nhds hθ.1 hθ.2] with y hy
      simp only [hHdef, hf, derivWithin_of_mem_nhds (Icc_mem_nhds hy.1 hy.2)]
    exact ((hasDerivAt_Lzero_antideriv Ψ z θ hθ h2).congr_of_eventuallyEq hHF).deriv.symm
  -- they agree almost everywhere on `(0, π/2]`
  have hae : ∀ᵐ θ ∂(volume : Measure ℝ), θ ∈ Set.uIoc (0:ℝ) (π/2) →
      Lzero Ψ z θ * sinCos2 θ = deriv H θ := by
    rw [MeasureTheory.ae_iff]
    refine MeasureTheory.measure_mono_null ?_ (MeasureTheory.measure_singleton (π/2))
    intro θ hθ
    simp only [Set.mem_ofPred_eq, not_imp] at hθ
    obtain ⟨hθu, hθne⟩ := hθ
    rw [Set.mem_singleton_iff]
    by_contra hne
    rw [Set.uIoc_of_le hle] at hθu
    exact hθne (hpoint θ ⟨hθu.1, lt_of_le_of_ne hθu.2 hne⟩)
  have hH0 : H 0 = 0 := by simp [hHdef, hf, h0, sinCos2]
  have hHpi : H (π/2) = 0 := by simp [hHdef, hf, h1, sinCos2]
  change ∫ θ in Set.Icc (0:ℝ) (π/2), Lzero Ψ z θ * sinCos2 θ = 0
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hle]
  rw [intervalIntegral.integral_congr_ae hae, hFTC, hHpi, hH0]
  ring

end Work.Elliptic
