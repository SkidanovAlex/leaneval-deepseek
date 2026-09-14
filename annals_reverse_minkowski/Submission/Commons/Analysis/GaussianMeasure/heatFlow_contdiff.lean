import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Normed.Operator.Prod
import Mathlib.RingTheory.Finiteness.Prod
import Submission.Commons.Analysis.Gaussian.gaussian_kernel_partial_bounds

open Real MeasureTheory Metric

namespace Commons.Analysis.GaussianMeasure

namespace HeatFlow

noncomputable section

noncomputable def K (u x y : ℝ) : ℝ := u * Real.exp (-Real.pi * u^2 * (y - x)^2)
noncomputable def K_u (u x y : ℝ) : ℝ := Real.exp (-Real.pi * u^2 * (y - x)^2) * (1 - 2 * Real.pi * u^2 * (y - x)^2)
noncomputable def K_x (u x y : ℝ) : ℝ := 2 * Real.pi * u^3 * (y - x) * Real.exp (-Real.pi * u^2 * (y - x)^2)
noncomputable def K_uu (u x y : ℝ) : ℝ := Real.exp (-Real.pi * u^2 * (y - x)^2) * (4 * Real.pi^2 * u^3 * (y - x)^4 - 6 * Real.pi * u * (y - x)^2)
noncomputable def K_ux (u x y : ℝ) : ℝ := Real.exp (-Real.pi * u^2 * (y - x)^2) * (6 * Real.pi * u^2 * (y - x) - 4 * Real.pi^2 * u^4 * (y - x)^3)
noncomputable def K_xx (u x y : ℝ) : ℝ := Real.exp (-Real.pi * u^2 * (y - x)^2) * (4 * Real.pi^2 * u^5 * (y - x)^2 - 2 * Real.pi * u^3)

noncomputable def D1 (u x y : ℝ) : (ℝ × ℝ) →L[ℝ] ℝ :=
  (K_u u x y) • (ContinuousLinearMap.fst ℝ ℝ ℝ) + (K_x u x y) • (ContinuousLinearMap.snd ℝ ℝ ℝ)
noncomputable def M1 (u x y : ℝ) : (ℝ × ℝ) →L[ℝ] ℝ :=
  (K_uu u x y) • (ContinuousLinearMap.fst ℝ ℝ ℝ) + (K_ux u x y) • (ContinuousLinearMap.snd ℝ ℝ ℝ)
noncomputable def M2 (u x y : ℝ) : (ℝ × ℝ) →L[ℝ] ℝ :=
  (K_ux u x y) • (ContinuousLinearMap.fst ℝ ℝ ℝ) + (K_xx u x y) • (ContinuousLinearMap.snd ℝ ℝ ℝ)
noncomputable def D2 (u x y : ℝ) : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) →L[ℝ] ℝ :=
  ((1 : ℝ →L[ℝ] ℝ).smulRight (M1 u x y)).coprod ((1 : ℝ →L[ℝ] ℝ).smulRight (M2 u x y))

lemma deriv_E_u (u x y : ℝ) :
    deriv (fun u' => Real.exp (-Real.pi * u'^2 * (y - x)^2)) u
      = -2 * Real.pi * u * (y-x)^2 * Real.exp (-Real.pi * u^2 * (y - x)^2) := by
  rw [deriv_exp (f := fun u' : ℝ => -Real.pi * u'^2 * (y - x)^2) (by fun_prop)]
  rw [show (fun u' : ℝ => -Real.pi * u'^2 * (y - x)^2)
        = ((fun u' : ℝ => -Real.pi * u'^2) * fun _ : ℝ => (y - x)^2) by
        funext z; simp [Pi.mul_apply]]
  rw [deriv_mul (by fun_prop : DifferentiableAt ℝ (fun u' : ℝ => -Real.pi * u'^2) u) (differentiableAt_const ((y-x)^2))]
  rw [deriv_const_mul _ (by fun_prop : DifferentiableAt ℝ (fun u' : ℝ => u'^2) u)]
  rw [deriv_pow_field, deriv_const]; ring

lemma deriv_E_x (u x y : ℝ) :
    deriv (fun x' => Real.exp (-Real.pi * u^2 * (y - x')^2)) x
      = 2 * Real.pi * u^2 * (y-x) * Real.exp (-Real.pi * u^2 * (y - x)^2) := by
  rw [deriv_exp (f := fun x' : ℝ => -Real.pi * u^2 * (y - x')^2) (by fun_prop)]
  rw [show (fun x' : ℝ => -Real.pi * u^2 * (y - x')^2)
        = ((fun _ : ℝ => -Real.pi * u^2) * fun x' : ℝ => (y - x')^2) by
        funext z; simp [Pi.mul_apply]]
  rw [deriv_mul (differentiableAt_const _) (by fun_prop : DifferentiableAt ℝ (fun x' : ℝ => (y - x')^2) x)]
  rw [deriv_const]
  rw [show (fun x' : ℝ => (y - x')^2) = (fun x' : ℝ => y - x')^2 by funext z; simp [Pi.pow_apply]]
  rw [deriv_pow (by fun_prop : DifferentiableAt ℝ (fun x' : ℝ => y - x') x) 2]
  rw [deriv_const_sub (f := fun x' : ℝ => x'), deriv_id'']; ring

lemma deriv_K_u (u x y : ℝ) : deriv (fun u' => K u' x y) u = K_u u x y := by
  simp only [K, K_u]
  rw [show (fun u' : ℝ => u' * Real.exp (-Real.pi * u'^2 * (y - x)^2))
        = (id * fun u' : ℝ => Real.exp (-Real.pi * u'^2 * (y - x)^2)) by
        funext z; simp [Pi.mul_apply]]
  rw [deriv_mul differentiableAt_id (by fun_prop : DifferentiableAt ℝ (fun u' : ℝ => Real.exp (-Real.pi * u'^2 * (y - x)^2)) u)]
  rw [deriv_id, deriv_E_u]; simp only [id_eq]; ring

lemma deriv_K_x (u x y : ℝ) : deriv (fun x' => K u x' y) x = K_x u x y := by
  simp only [K, K_x]
  rw [show (fun x' : ℝ => u * Real.exp (-Real.pi * u^2 * (y - x')^2))
        = ((fun _ : ℝ => u) * fun x' : ℝ => Real.exp (-Real.pi * u^2 * (y - x')^2)) by
        funext z; simp [Pi.mul_apply]]
  rw [deriv_mul (differentiableAt_const _) (by fun_prop : DifferentiableAt ℝ (fun x' : ℝ => Real.exp (-Real.pi * u^2 * (y - x')^2)) x)]
  rw [deriv_const, deriv_E_x]; ring

lemma deriv_K_uu (u x y : ℝ) : deriv (fun u' => K_u u' x y) u = K_uu u x y := by
  simp only [K_u, K_uu]
  rw [show (fun u' : ℝ => Real.exp (-Real.pi * u'^2 * (y - x)^2) * (1 - 2 * Real.pi * u'^2 * (y - x)^2))
        = ((fun u' : ℝ => Real.exp (-Real.pi * u'^2 * (y - x)^2)) *
           (fun u' : ℝ => (1 - 2 * Real.pi * u'^2 * (y - x)^2))) by funext z; simp [Pi.mul_apply]]
  rw [deriv_mul (by fun_prop : DifferentiableAt ℝ (fun u' : ℝ => Real.exp (-Real.pi * u'^2 * (y - x)^2)) u)
        (by fun_prop : DifferentiableAt ℝ (fun u' : ℝ => (1 - 2 * Real.pi * u'^2 * (y - x)^2)) u)]
  rw [deriv_E_u]
  rw [show (fun u' : ℝ => (1 - 2 * Real.pi * u'^2 * (y - x)^2))
        = ((fun _ : ℝ => (1:ℝ)) - fun u' : ℝ => 2 * Real.pi * u'^2 * (y - x)^2) by
        funext z; simp [Pi.sub_apply]]
  rw [deriv_sub (differentiableAt_const _) (by fun_prop : DifferentiableAt ℝ (fun u' : ℝ => 2 * Real.pi * u'^2 * (y - x)^2) u)]
  rw [deriv_const]
  rw [show (fun u' : ℝ => 2 * Real.pi * u'^2 * (y - x)^2)
        = ((fun u' : ℝ => 2 * Real.pi * u'^2) * fun _ : ℝ => (y - x)^2) by funext z; simp [Pi.mul_apply]]
  rw [deriv_mul (by fun_prop : DifferentiableAt ℝ (fun u' : ℝ => 2 * Real.pi * u'^2) u) (differentiableAt_const _), deriv_const]
  rw [show (fun u' : ℝ => 2 * Real.pi * u'^2) = ((fun _ : ℝ => 2*Real.pi) * fun u' : ℝ => u'^2) by funext z; simp [Pi.mul_apply]]
  rw [deriv_mul (differentiableAt_const _) (by fun_prop : DifferentiableAt ℝ (fun u' : ℝ => u'^2) u), deriv_const, deriv_pow_field]
  ring

lemma deriv_K_ux_x (u x y : ℝ) : deriv (fun x' => K_u u x' y) x = K_ux u x y := by
  simp only [K_u, K_ux]
  rw [show (fun x' : ℝ => Real.exp (-Real.pi * u^2 * (y - x')^2) * (1 - 2 * Real.pi * u^2 * (y - x')^2))
        = ((fun x' : ℝ => Real.exp (-Real.pi * u^2 * (y - x')^2)) *
           (fun x' : ℝ => (1 - 2 * Real.pi * u^2 * (y - x')^2))) by funext z; simp [Pi.mul_apply]]
  rw [deriv_mul (by fun_prop : DifferentiableAt ℝ (fun x' : ℝ => Real.exp (-Real.pi * u^2 * (y - x')^2)) x)
        (by fun_prop : DifferentiableAt ℝ (fun x' : ℝ => (1 - 2 * Real.pi * u^2 * (y - x')^2)) x)]
  rw [deriv_E_x]
  rw [show (fun x' : ℝ => (1 - 2 * Real.pi * u^2 * (y - x')^2))
        = ((fun _ : ℝ => (1:ℝ)) - fun x' : ℝ => 2 * Real.pi * u^2 * (y - x')^2) by
        funext z; simp [Pi.sub_apply]]
  rw [deriv_sub (differentiableAt_const _) (by fun_prop : DifferentiableAt ℝ (fun x' : ℝ => 2 * Real.pi * u^2 * (y - x')^2) x)]
  rw [deriv_const]
  rw [show (fun x' : ℝ => 2 * Real.pi * u^2 * (y - x')^2)
        = ((fun _ : ℝ => 2 * Real.pi * u^2) * fun x' : ℝ => (y - x')^2) by funext z; simp [Pi.mul_apply]]
  rw [deriv_mul (differentiableAt_const _) (by fun_prop : DifferentiableAt ℝ (fun x' : ℝ => (y - x')^2) x), deriv_const]
  rw [show (fun x' : ℝ => (y - x')^2) = (fun x' : ℝ => y - x')^2 by funext z; simp [Pi.pow_apply]]
  rw [deriv_pow (by fun_prop : DifferentiableAt ℝ (fun x' : ℝ => y - x') x) 2]
  rw [deriv_const_sub (f := fun x' : ℝ => x'), deriv_id'']; ring

lemma deriv_K_xu_u (u x y : ℝ) : deriv (fun u' => K_x u' x y) u = K_ux u x y := by
  simp only [K_x, K_ux]
  rw [show (fun u' : ℝ => 2 * Real.pi * u'^3 * (y - x) * Real.exp (-Real.pi * u'^2 * (y - x)^2))
        = ((fun u' : ℝ => 2 * Real.pi * u'^3 * (y - x)) *
           (fun u' : ℝ => Real.exp (-Real.pi * u'^2 * (y - x)^2))) by funext z; simp [Pi.mul_apply]]
  rw [deriv_mul (by fun_prop : DifferentiableAt ℝ (fun u' : ℝ => 2 * Real.pi * u'^3 * (y - x)) u)
        (by fun_prop : DifferentiableAt ℝ (fun u' : ℝ => Real.exp (-Real.pi * u'^2 * (y - x)^2)) u)]
  rw [deriv_E_u]
  rw [show (fun u' : ℝ => 2 * Real.pi * u'^3 * (y - x))
        = ((fun u' : ℝ => 2 * Real.pi * u'^3) * fun _ : ℝ => (y - x)) by funext z; simp [Pi.mul_apply]]
  rw [deriv_mul (by fun_prop : DifferentiableAt ℝ (fun u' : ℝ => 2 * Real.pi * u'^3) u) (differentiableAt_const _), deriv_const]
  rw [show (fun u' : ℝ => 2 * Real.pi * u'^3) = ((fun _ : ℝ => 2*Real.pi) * fun u' : ℝ => u'^3) by funext z; simp [Pi.mul_apply]]
  rw [deriv_mul (differentiableAt_const _) (by fun_prop : DifferentiableAt ℝ (fun u' : ℝ => u'^3) u), deriv_const, deriv_pow_field]
  ring

lemma deriv_K_xx (u x y : ℝ) : deriv (fun x' => K_x u x' y) x = K_xx u x y := by
  simp only [K_x, K_xx]
  rw [show (fun x' : ℝ => 2 * Real.pi * u^3 * (y - x') * Real.exp (-Real.pi * u^2 * (y - x')^2))
        = ((fun x' : ℝ => 2 * Real.pi * u^3 * (y - x')) *
           (fun x' : ℝ => Real.exp (-Real.pi * u^2 * (y - x')^2))) by funext z; simp [Pi.mul_apply]]
  rw [deriv_mul (by fun_prop : DifferentiableAt ℝ (fun x' : ℝ => 2 * Real.pi * u^3 * (y - x')) x)
        (by fun_prop : DifferentiableAt ℝ (fun x' : ℝ => Real.exp (-Real.pi * u^2 * (y - x')^2)) x)]
  rw [deriv_E_x]
  rw [show (fun x' : ℝ => 2 * Real.pi * u^3 * (y - x'))
        = ((fun _ : ℝ => 2 * Real.pi * u^3) * fun x' : ℝ => (y - x')) by funext z; simp [Pi.mul_apply]]
  rw [deriv_mul (differentiableAt_const _) (by fun_prop : DifferentiableAt ℝ (fun x' : ℝ => (y - x')) x), deriv_const]
  rw [deriv_const_sub (f := fun x' : ℝ => x'), deriv_id'']; ring

lemma hasDerivAt_K_u (u x y : ℝ) : HasDerivAt (fun u' => K u' x y) (K_u u x y) u := by
  have hd : DifferentiableAt ℝ (fun u' => K u' x y) u := by unfold K; fun_prop
  rw [← deriv_K_u u x y]; exact hd.hasDerivAt

lemma hasDerivAt_K_x (u x y : ℝ) : HasDerivAt (fun x' => K u x' y) (K_x u x y) x := by
  have hd : DifferentiableAt ℝ (fun x' => K u x' y) x := by unfold K; fun_prop
  rw [← deriv_K_x u x y]; exact hd.hasDerivAt

lemma hasDerivAt_K_uu (u x y : ℝ) : HasDerivAt (fun u' => K_u u' x y) (K_uu u x y) u := by
  have hd : DifferentiableAt ℝ (fun u' => K_u u' x y) u := by unfold K_u; fun_prop
  rw [← deriv_K_uu u x y]; exact hd.hasDerivAt

lemma hasDerivAt_K_ux_x (u x y : ℝ) : HasDerivAt (fun x' => K_u u x' y) (K_ux u x y) x := by
  have hd : DifferentiableAt ℝ (fun x' => K_u u x' y) x := by unfold K_u; fun_prop
  rw [← deriv_K_ux_x u x y]; exact hd.hasDerivAt

lemma hasDerivAt_K_xu_u (u x y : ℝ) : HasDerivAt (fun u' => K_x u' x y) (K_ux u x y) u := by
  have hd : DifferentiableAt ℝ (fun u' => K_x u' x y) u := by unfold K_x; fun_prop
  rw [← deriv_K_xu_u u x y]; exact hd.hasDerivAt

lemma hasDerivAt_K_xx (u x y : ℝ) : HasDerivAt (fun x' => K_x u x' y) (K_xx u x y) x := by
  have hd : DifferentiableAt ℝ (fun x' => K_x u x' y) x := by unfold K_x; fun_prop
  rw [← deriv_K_xx u x y]; exact hd.hasDerivAt

lemma continuous_K_u (y : ℝ) : Continuous (fun p : ℝ × ℝ => K_u p.1 p.2 y) := by unfold K_u; fun_prop
lemma continuous_K_x (y : ℝ) : Continuous (fun p : ℝ × ℝ => K_x p.1 p.2 y) := by unfold K_x; fun_prop
lemma continuous_K_uu (y : ℝ) : Continuous (fun p : ℝ × ℝ => K_uu p.1 p.2 y) := by unfold K_uu; fun_prop
lemma continuous_K_ux (y : ℝ) : Continuous (fun p : ℝ × ℝ => K_ux p.1 p.2 y) := by unfold K_ux; fun_prop
lemma continuous_K_xx (y : ℝ) : Continuous (fun p : ℝ × ℝ => K_xx p.1 p.2 y) := by unfold K_xx; fun_prop

lemma continuous_M1 (y : ℝ) : Continuous (fun p : ℝ × ℝ => M1 p.1 p.2 y) := by
  simp only [M1]
  exact ((continuous_K_uu y).smul continuous_const).add ((continuous_K_ux y).smul continuous_const)

lemma continuous_M2 (y : ℝ) : Continuous (fun p : ℝ × ℝ => M2 p.1 p.2 y) := by
  simp only [M2]
  exact ((continuous_K_ux y).smul continuous_const).add ((continuous_K_xx y).smul continuous_const)

lemma hasFDerivAt_K (u x y : ℝ) :
    HasFDerivAt (fun p : ℝ × ℝ => K p.1 p.2 y) (D1 u x y) (u,x) := by
  have h := hasStrictFDerivAt_uncurry_coprod
    (u := (u,x))
    (f := fun (u' : ℝ) (x' : ℝ) => K u' x' y)
    (f₁ := fun (u' : ℝ) (x' : ℝ) => (1 : ℝ →L[ℝ] ℝ).smulRight (K_u u' x' y))
    (f₂ := fun (u' : ℝ) (x' : ℝ) => (1 : ℝ →L[ℝ] ℝ).smulRight (K_x u' x' y))
    (by filter_upwards with v; exact (hasDerivAt_K_u v.1 v.2 y).hasFDerivAt)
    (by filter_upwards with v; exact (hasDerivAt_K_x v.1 v.2 y).hasFDerivAt)
    (((ContinuousLinearMap.smulRightL ℝ ℝ ℝ (1 : ℝ →L[ℝ] ℝ)).continuous.comp (continuous_K_u y)).continuousAt)
    (((ContinuousLinearMap.smulRightL ℝ ℝ ℝ (1 : ℝ →L[ℝ] ℝ)).continuous.comp (continuous_K_x y)).continuousAt)
  have key : ((1 : ℝ →L[ℝ] ℝ).smulRight (K_u u x y)).coprod ((1 : ℝ →L[ℝ] ℝ).smulRight (K_x u x y)) = D1 u x y := by
    apply ContinuousLinearMap.ext
    intro v
    simp only [D1, ContinuousLinearMap.coprod_apply, ContinuousLinearMap.smulRight_apply,
      add_apply, smul_apply, one_apply_eq_self, ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd']
    ring
  have hh : HasFDerivAt (fun p : ℝ × ℝ => K p.1 p.2 y)
      (((1 : ℝ →L[ℝ] ℝ).smulRight (K_u u x y)).coprod ((1 : ℝ →L[ℝ] ℝ).smulRight (K_x u x y))) (u,x) :=
    h.hasFDerivAt
  rw [key] at hh
  exact hh

lemma hasDerivAt_D1_u (u x y : ℝ) : HasDerivAt (fun u' => D1 u' x y) (M1 u x y) u := by
  have h1 : HasDerivAt (fun u' : ℝ => (K_u u' x y) • (ContinuousLinearMap.fst ℝ ℝ ℝ))
      ((K_uu u x y) • (ContinuousLinearMap.fst ℝ ℝ ℝ)) u :=
    (hasDerivAt_K_uu u x y).smul_const (ContinuousLinearMap.fst ℝ ℝ ℝ)
  have h2 : HasDerivAt (fun u' : ℝ => (K_x u' x y) • (ContinuousLinearMap.snd ℝ ℝ ℝ))
      ((K_ux u x y) • (ContinuousLinearMap.snd ℝ ℝ ℝ)) u :=
    (hasDerivAt_K_xu_u u x y).smul_const (ContinuousLinearMap.snd ℝ ℝ ℝ)
  have h := h1.add h2
  simp only [D1, M1]
  exact h

lemma hasDerivAt_D1_x (u x y : ℝ) : HasDerivAt (fun x' => D1 u x' y) (M2 u x y) x := by
  have h1 : HasDerivAt (fun x' : ℝ => (K_u u x' y) • (ContinuousLinearMap.fst ℝ ℝ ℝ))
      ((K_ux u x y) • (ContinuousLinearMap.fst ℝ ℝ ℝ)) x :=
    (hasDerivAt_K_ux_x u x y).smul_const (ContinuousLinearMap.fst ℝ ℝ ℝ)
  have h2 : HasDerivAt (fun x' : ℝ => (K_x u x' y) • (ContinuousLinearMap.snd ℝ ℝ ℝ))
      ((K_xx u x y) • (ContinuousLinearMap.snd ℝ ℝ ℝ)) x :=
    (hasDerivAt_K_xx u x y).smul_const (ContinuousLinearMap.snd ℝ ℝ ℝ)
  have h := h1.add h2
  simp only [D1, M2]
  exact h

lemma hasFDerivAt_D1 (u x y : ℝ) :
    HasFDerivAt (fun p : ℝ × ℝ => D1 p.1 p.2 y) (D2 u x y) (u,x) := by
  have h := hasStrictFDerivAt_uncurry_coprod
    (u := (u,x))
    (f := fun (u' : ℝ) (x' : ℝ) => D1 u' x' y)
    (f₁ := fun (u' : ℝ) (x' : ℝ) => (1 : ℝ →L[ℝ] ℝ).smulRight (M1 u' x' y))
    (f₂ := fun (u' : ℝ) (x' : ℝ) => (1 : ℝ →L[ℝ] ℝ).smulRight (M2 u' x' y))
    (by filter_upwards with v; exact (hasDerivAt_D1_u v.1 v.2 y).hasFDerivAt)
    (by filter_upwards with v; exact (hasDerivAt_D1_x v.1 v.2 y).hasFDerivAt)
    (((ContinuousLinearMap.smulRightL ℝ ℝ (ℝ × ℝ →L[ℝ] ℝ) (1 : ℝ →L[ℝ] ℝ)).continuous.comp (continuous_M1 y)).continuousAt)
    (((ContinuousLinearMap.smulRightL ℝ ℝ (ℝ × ℝ →L[ℝ] ℝ) (1 : ℝ →L[ℝ] ℝ)).continuous.comp (continuous_M2 y)).continuousAt)
  exact h.hasFDerivAt

/-! ### integrability and continuity in `y` -/

lemma integrable_K (u x : ℝ) : Integrable (fun y => K u x y) := by
  rcases eq_or_ne u 0 with rfl | hu
  · simp [K]
  have hb : 0 < Real.pi * u^2 := mul_pos Real.pi_pos (sq_pos_of_ne_zero hu)
  have h1 : Integrable (fun t : ℝ => Real.exp (-(Real.pi * u^2) * (t - x)^2)) :=
    (integrable_exp_neg_mul_sq hb).comp_sub_right x
  have h2 : (fun y => K u x y) = fun t : ℝ => u * Real.exp (-(Real.pi * u^2) * (t - x)^2) := by
    funext t; simp only [K]; ring_nf
  rw [h2]
  exact h1.const_mul u

lemma continuous_K_y (u x : ℝ) : Continuous (fun y => K u x y) := by unfold K; fun_prop
lemma continuous_K_u_y (u x : ℝ) : Continuous (fun y => K_u u x y) := by unfold K_u; fun_prop
lemma continuous_K_x_y (u x : ℝ) : Continuous (fun y => K_x u x y) := by unfold K_x; fun_prop
lemma continuous_K_uu_y (u x : ℝ) : Continuous (fun y => K_uu u x y) := by unfold K_uu; fun_prop
lemma continuous_K_ux_y (u x : ℝ) : Continuous (fun y => K_ux u x y) := by unfold K_ux; fun_prop
lemma continuous_K_xx_y (u x : ℝ) : Continuous (fun y => K_xx u x y) := by unfold K_xx; fun_prop

lemma continuous_M1_y (u x : ℝ) : Continuous (fun y => M1 u x y) := by
  simp only [M1]
  exact ((continuous_K_uu_y u x).smul continuous_const).add ((continuous_K_ux_y u x).smul continuous_const)

lemma continuous_M2_y (u x : ℝ) : Continuous (fun y => M2 u x y) := by
  simp only [M2]
  exact ((continuous_K_ux_y u x).smul continuous_const).add ((continuous_K_xx_y u x).smul continuous_const)

lemma continuous_D1_y (u x : ℝ) : Continuous (fun y => D1 u x y) := by
  simp only [D1]
  exact ((continuous_K_u_y u x).smul continuous_const).add ((continuous_K_x_y u x).smul continuous_const)

lemma continuous_D2_y (u x : ℝ) : Continuous (fun y => D2 u x y) := by
  simp only [D2]
  refine Continuous.continuousLinearMapCoprod ?_ ?_
  · exact (ContinuousLinearMap.smulRightL ℝ ℝ (ℝ × ℝ →L[ℝ] ℝ) (1 : ℝ →L[ℝ] ℝ)).continuous.comp (continuous_M1_y u x)
  · exact (ContinuousLinearMap.smulRightL ℝ ℝ (ℝ × ℝ →L[ℝ] ℝ) (1 : ℝ →L[ℝ] ℝ)).continuous.comp (continuous_M2_y u x)

/-! ### norm bounds on the derivative maps -/

lemma norm_coprod_le {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
    (f : E →L[ℝ] G) (g : F →L[ℝ] G) : ‖f.coprod g‖ ≤ ‖f‖ + ‖g‖ := by
  refine ContinuousLinearMap.opNorm_le_bound (f.coprod g) ?_ ?_
  · exact add_nonneg (norm_nonneg f) (norm_nonneg g)
  intro v
  calc ‖(f.coprod g) v‖ = ‖f v.1 + g v.2‖ := by rw [ContinuousLinearMap.coprod_apply]
    _ ≤ ‖f v.1‖ + ‖g v.2‖ := norm_add_le _ _
    _ ≤ ‖f‖ * ‖v.1‖ + ‖g‖ * ‖v.2‖ := add_le_add (f.le_opNorm _) (g.le_opNorm _)
    _ ≤ ‖f‖ * ‖v‖ + ‖g‖ * ‖v‖ := by
        gcongr
        · exact norm_fst_le v
        · exact norm_snd_le v
    _ = (‖f‖ + ‖g‖) * ‖v‖ := by ring

lemma norm_M1_le (u x y : ℝ) : ‖M1 u x y‖ ≤ |K_uu u x y| + |K_ux u x y| := by
  simp only [M1]
  calc ‖(K_uu u x y) • (ContinuousLinearMap.fst ℝ ℝ ℝ) + (K_ux u x y) • (ContinuousLinearMap.snd ℝ ℝ ℝ)‖
      ≤ ‖(K_uu u x y) • (ContinuousLinearMap.fst ℝ ℝ ℝ)‖ + ‖(K_ux u x y) • (ContinuousLinearMap.snd ℝ ℝ ℝ)‖ :=
        norm_add_le _ _
    _ ≤ |K_uu u x y| + |K_ux u x y| := by
        apply add_le_add
        · rw [norm_smul, Real.norm_eq_abs]
          calc |K_uu u x y| * ‖ContinuousLinearMap.fst ℝ ℝ ℝ‖ ≤ |K_uu u x y| * 1 := by
                gcongr; exact ContinuousLinearMap.norm_fst_le ℝ ℝ ℝ
            _ = |K_uu u x y| := by ring
        · rw [norm_smul, Real.norm_eq_abs]
          calc |K_ux u x y| * ‖ContinuousLinearMap.snd ℝ ℝ ℝ‖ ≤ |K_ux u x y| * 1 := by
                gcongr; exact ContinuousLinearMap.norm_snd_le ℝ ℝ ℝ
            _ = |K_ux u x y| := by ring

lemma norm_M2_le (u x y : ℝ) : ‖M2 u x y‖ ≤ |K_ux u x y| + |K_xx u x y| := by
  simp only [M2]
  calc ‖(K_ux u x y) • (ContinuousLinearMap.fst ℝ ℝ ℝ) + (K_xx u x y) • (ContinuousLinearMap.snd ℝ ℝ ℝ)‖
      ≤ ‖(K_ux u x y) • (ContinuousLinearMap.fst ℝ ℝ ℝ)‖ + ‖(K_xx u x y) • (ContinuousLinearMap.snd ℝ ℝ ℝ)‖ :=
        norm_add_le _ _
    _ ≤ |K_ux u x y| + |K_xx u x y| := by
        apply add_le_add
        · rw [norm_smul, Real.norm_eq_abs]
          calc |K_ux u x y| * ‖ContinuousLinearMap.fst ℝ ℝ ℝ‖ ≤ |K_ux u x y| * 1 := by
                gcongr; exact ContinuousLinearMap.norm_fst_le ℝ ℝ ℝ
            _ = |K_ux u x y| := by ring
        · rw [norm_smul, Real.norm_eq_abs]
          calc |K_xx u x y| * ‖ContinuousLinearMap.snd ℝ ℝ ℝ‖ ≤ |K_xx u x y| * 1 := by
                gcongr; exact ContinuousLinearMap.norm_snd_le ℝ ℝ ℝ
            _ = |K_xx u x y| := by ring

lemma norm_D1_le (u x y : ℝ) : ‖D1 u x y‖ ≤ |K_u u x y| + |K_x u x y| := by
  simp only [D1]
  calc ‖(K_u u x y) • (ContinuousLinearMap.fst ℝ ℝ ℝ) + (K_x u x y) • (ContinuousLinearMap.snd ℝ ℝ ℝ)‖
      ≤ ‖(K_u u x y) • (ContinuousLinearMap.fst ℝ ℝ ℝ)‖ + ‖(K_x u x y) • (ContinuousLinearMap.snd ℝ ℝ ℝ)‖ :=
        norm_add_le _ _
    _ ≤ |K_u u x y| + |K_x u x y| := by
        apply add_le_add
        · rw [norm_smul, Real.norm_eq_abs]
          calc |K_u u x y| * ‖ContinuousLinearMap.fst ℝ ℝ ℝ‖ ≤ |K_u u x y| * 1 := by
                gcongr; exact ContinuousLinearMap.norm_fst_le ℝ ℝ ℝ
            _ = |K_u u x y| := by ring
        · rw [norm_smul, Real.norm_eq_abs]
          calc |K_x u x y| * ‖ContinuousLinearMap.snd ℝ ℝ ℝ‖ ≤ |K_x u x y| * 1 := by
                gcongr; exact ContinuousLinearMap.norm_snd_le ℝ ℝ ℝ
            _ = |K_x u x y| := by ring

lemma norm_one_clm : ‖(1 : ℝ →L[ℝ] ℝ)‖ = 1 := by
  rw [show (1 : ℝ →L[ℝ] ℝ) = ContinuousLinearMap.id ℝ ℝ from by ext x; simp,
    ContinuousLinearMap.norm_id]

lemma norm_smulRight_one_le (M : (ℝ × ℝ) →L[ℝ] ℝ) :
    ‖(1 : ℝ →L[ℝ] ℝ).smulRight M‖ ≤ ‖M‖ := by
  rw [ContinuousLinearMap.norm_smulRight_apply, norm_one_clm, one_mul]

lemma norm_D2_le (u x y : ℝ) :
    ‖D2 u x y‖ ≤ |K_uu u x y| + |K_ux u x y| + |K_ux u x y| + |K_xx u x y| := by
  simp only [D2]
  have hc : ‖((1 : ℝ →L[ℝ] ℝ).smulRight (M1 u x y)).coprod ((1 : ℝ →L[ℝ] ℝ).smulRight (M2 u x y))‖
      ≤ ‖(1 : ℝ →L[ℝ] ℝ).smulRight (M1 u x y)‖ + ‖(1 : ℝ →L[ℝ] ℝ).smulRight (M2 u x y)‖ :=
    norm_coprod_le _ _
  calc ‖((1 : ℝ →L[ℝ] ℝ).smulRight (M1 u x y)).coprod ((1 : ℝ →L[ℝ] ℝ).smulRight (M2 u x y))‖
      ≤ ‖(1 : ℝ →L[ℝ] ℝ).smulRight (M1 u x y)‖ + ‖(1 : ℝ →L[ℝ] ℝ).smulRight (M2 u x y)‖ := hc
    _ ≤ ‖M1 u x y‖ + ‖M2 u x y‖ := add_le_add (norm_smulRight_one_le _) (norm_smulRight_one_le _)
    _ ≤ (|K_uu u x y| + |K_ux u x y|) + (|K_ux u x y| + |K_xx u x y|) :=
        add_le_add (norm_M1_le _ _ _) (norm_M2_le _ _ _)
    _ = |K_uu u x y| + |K_ux u x y| + |K_ux u x y| + |K_xx u x y| := by ring

/-! ### continuity in the parameter `p = (u,x)` -/

lemma continuous_D1 (y : ℝ) : Continuous (fun p : ℝ × ℝ => D1 p.1 p.2 y) := by
  simp only [D1]
  exact ((continuous_K_u y).smul continuous_const).add ((continuous_K_x y).smul continuous_const)

lemma continuous_D2 (y : ℝ) : Continuous (fun p : ℝ × ℝ => D2 p.1 p.2 y) := by
  simp only [D2]
  exact Continuous.continuousLinearMapCoprod
    ((ContinuousLinearMap.smulRightL ℝ ℝ (ℝ × ℝ →L[ℝ] ℝ) (1 : ℝ →L[ℝ] ℝ)).continuous.comp (continuous_M1 y))
    ((ContinuousLinearMap.smulRightL ℝ ℝ (ℝ × ℝ →L[ℝ] ℝ) (1 : ℝ →L[ℝ] ℝ)).continuous.comp (continuous_M2 y))

/-! ### differentiation under the integral sign -/

lemma abs_K_xx_le_add (u x y : ℝ) (hu : 0 ≤ u) :
    |K_xx u x y| ≤ |Real.exp (-Real.pi * u^2 * (y - x)^2) *
      (2 * Real.pi * u^3 + 4 * Real.pi^2 * u^5 * (y - x)^2)| := by
  have hA : (0:ℝ) ≤ 4 * Real.pi^2 * u^5 * (y - x)^2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) (pow_nonneg hu 5)) (sq_nonneg _)
  have hB : (0:ℝ) ≤ 2 * Real.pi * u^3 :=
    mul_nonneg (mul_nonneg (by norm_num) Real.pi_pos.le) (pow_nonneg hu 3)
  have key : |4 * Real.pi^2 * u^5 * (y - x)^2 - 2 * Real.pi * u^3| ≤
      2 * Real.pi * u^3 + 4 * Real.pi^2 * u^5 * (y - x)^2 := by
    rw [abs_sub_le_iff]; constructor <;> linarith
  simp only [K_xx]
  rw [abs_mul, abs_of_pos (Real.exp_pos _), abs_mul, abs_of_pos (Real.exp_pos _),
    abs_of_nonneg (by linarith : (0:ℝ) ≤ 2 * Real.pi * u^3 + 4 * Real.pi^2 * u^5 * (y - x)^2)]
  exact mul_le_mul_of_nonneg_left key (Real.exp_pos _).le

lemma hasFDerivAt_Φ (q : ℝ → ℝ) (hq : AEStronglyMeasurable q volume) (hq1 : ∀ x, |q x| ≤ 1)
    (p₀ : ℝ × ℝ) (hp₀ : 0 < p₀.1) :
    HasFDerivAt (fun p : ℝ × ℝ => ∫ y, q y * K p.1 p.2 y)
      (∫ y, q y • D1 p₀.1 p₀.2 y) p₀ := by
  obtain ⟨δ, hδpos, hδu, B, hBint, hb1, hb2, hb3, hb4, hb5⟩ :=
    Commons.Analysis.Gaussian.gaussian_kernel_partial_bounds p₀.1 p₀.2 hp₀
  have hlt₁ : ∀ p : ℝ × ℝ, dist p p₀ < δ → |p.1 - p₀.1| < δ := by
    intro p hp
    rw [Prod.dist_eq] at hp
    exact lt_of_le_of_lt (le_max_left _ _) hp
  have hlt₂ : ∀ p : ℝ × ℝ, dist p p₀ < δ → |p.2 - p₀.2| < δ := by
    intro p hp
    rw [Prod.dist_eq] at hp
    exact lt_of_le_of_lt (le_max_right _ _) hp
  have hD1bd : ∀ (p : ℝ × ℝ) (y : ℝ), dist p p₀ < δ → ‖D1 p.1 p.2 y‖ ≤ 2 * B y := by
    intro p y hp
    calc ‖D1 p.1 p.2 y‖ ≤ |K_u p.1 p.2 y| + |K_x p.1 p.2 y| := norm_D1_le _ _ _
      _ ≤ B y + B y := add_le_add (hb1 _ _ _ (hlt₁ p hp) (hlt₂ p hp)) (hb2 _ _ _ (hlt₁ p hp) (hlt₂ p hp))
      _ = 2 * B y := by ring
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F := fun p y => q y * K p.1 p.2 y) (F' := fun p y => q y • D1 p.1 p.2 y)
    (s := ball p₀ δ) (bound := fun y => 2 * B y) (ball_mem_nhds p₀ hδpos) ?_ ?_ ?_ ?_ ?_ ?_
  · filter_upwards with x
    exact hq.mul (continuous_K_y x.1 x.2).aestronglyMeasurable
  · refine Integrable.mono' (integrable_K p₀.1 p₀.2) ?_ ?_
    · exact hq.mul (continuous_K_y p₀.1 p₀.2).aestronglyMeasurable
    · filter_upwards with y
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      have hK : 0 ≤ K p₀.1 p₀.2 y := by unfold K; positivity
      calc |q y| * |K p₀.1 p₀.2 y| ≤ 1 * |K p₀.1 p₀.2 y| := by gcongr; exact hq1 y
        _ = K p₀.1 p₀.2 y := by rw [one_mul, abs_of_nonneg hK]
  · exact hq.smul (continuous_D1_y p₀.1 p₀.2).aestronglyMeasurable
  · filter_upwards with y p hp
    rw [norm_smul, Real.norm_eq_abs]
    calc |q y| * ‖D1 p.1 p.2 y‖ ≤ 1 * ‖D1 p.1 p.2 y‖ := by gcongr; exact hq1 y
      _ = ‖D1 p.1 p.2 y‖ := one_mul _
      _ ≤ 2 * B y := hD1bd p y hp
  · exact hBint.const_mul 2
  · filter_upwards with y p hp
    exact (hasFDerivAt_K p.1 p.2 y).const_mul (q y)

lemma hasFDerivAt_Φ1 (q : ℝ → ℝ) (hq : AEStronglyMeasurable q volume) (hq1 : ∀ x, |q x| ≤ 1)
    (p₀ : ℝ × ℝ) (hp₀ : 0 < p₀.1) :
    HasFDerivAt (fun p : ℝ × ℝ => ∫ y, q y • D1 p.1 p.2 y)
      (∫ y, q y • D2 p₀.1 p₀.2 y) p₀ := by
  obtain ⟨δ, hδpos, hδu, B, hBint, hb1, hb2, hb3, hb4, hb5⟩ :=
    Commons.Analysis.Gaussian.gaussian_kernel_partial_bounds p₀.1 p₀.2 hp₀
  have hlt₁ : ∀ p : ℝ × ℝ, dist p p₀ < δ → |p.1 - p₀.1| < δ := by
    intro p hp; rw [Prod.dist_eq] at hp
    exact lt_of_le_of_lt (le_max_left _ _) hp
  have hlt₂ : ∀ p : ℝ × ℝ, dist p p₀ < δ → |p.2 - p₀.2| < δ := by
    intro p hp; rw [Prod.dist_eq] at hp
    exact lt_of_le_of_lt (le_max_right _ _) hp
  have hD2bd : ∀ (p : ℝ × ℝ) (y : ℝ), dist p p₀ < δ → ‖D2 p.1 p.2 y‖ ≤ 4 * B y := by
    intro p y hp
    have h1 := hlt₁ p hp
    have h2 := hlt₂ p hp
    have hu : 0 ≤ p.1 := by rw [abs_lt] at h1; linarith [h1.1, hδu]
    have hxx : |K_xx p.1 p.2 y| ≤ B y :=
      le_trans (abs_K_xx_le_add p.1 p.2 y hu) (hb5 p.1 p.2 y h1 h2)
    have huu : |K_uu p.1 p.2 y| ≤ B y := hb3 p.1 p.2 y h1 h2
    have hux : |K_ux p.1 p.2 y| ≤ B y := hb4 p.1 p.2 y h1 h2
    calc ‖D2 p.1 p.2 y‖ ≤ |K_uu p.1 p.2 y| + |K_ux p.1 p.2 y| + |K_ux p.1 p.2 y| + |K_xx p.1 p.2 y| :=
          norm_D2_le _ _ _
      _ ≤ B y + B y + B y + B y := by linarith
      _ = 4 * B y := by ring
  have hD1bd0 : ∀ y, ‖D1 p₀.1 p₀.2 y‖ ≤ 2 * B y := by
    intro y
    have hp : dist p₀ p₀ < δ := by rw [dist_self]; exact hδpos
    calc ‖D1 p₀.1 p₀.2 y‖ ≤ |K_u p₀.1 p₀.2 y| + |K_x p₀.1 p₀.2 y| := norm_D1_le _ _ _
      _ ≤ B y + B y := add_le_add (hb1 _ _ _ (hlt₁ p₀ hp) (hlt₂ p₀ hp)) (hb2 _ _ _ (hlt₁ p₀ hp) (hlt₂ p₀ hp))
      _ = 2 * B y := by ring
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F := fun p y => q y • D1 p.1 p.2 y) (F' := fun p y => q y • D2 p.1 p.2 y)
    (s := ball p₀ δ) (bound := fun y => 4 * B y) (ball_mem_nhds p₀ hδpos) ?_ ?_ ?_ ?_ ?_ ?_
  · filter_upwards with x
    exact hq.smul (continuous_D1_y x.1 x.2).aestronglyMeasurable
  · refine Integrable.mono' (hBint.const_mul 2) ?_ ?_
    · exact hq.smul (continuous_D1_y p₀.1 p₀.2).aestronglyMeasurable
    · filter_upwards with y
      rw [norm_smul, Real.norm_eq_abs]
      calc |q y| * ‖D1 p₀.1 p₀.2 y‖ ≤ 1 * ‖D1 p₀.1 p₀.2 y‖ := by gcongr; exact hq1 y
        _ = ‖D1 p₀.1 p₀.2 y‖ := one_mul _
        _ ≤ 2 * B y := hD1bd0 y
  · exact hq.smul (continuous_D2_y p₀.1 p₀.2).aestronglyMeasurable
  · filter_upwards with y p hp
    rw [norm_smul, Real.norm_eq_abs]
    calc |q y| * ‖D2 p.1 p.2 y‖ ≤ 1 * ‖D2 p.1 p.2 y‖ := by gcongr; exact hq1 y
      _ = ‖D2 p.1 p.2 y‖ := one_mul _
      _ ≤ 4 * B y := hD2bd p y hp
  · exact hBint.const_mul 4
  · filter_upwards with y p hp
    exact (hasFDerivAt_D1 p.1 p.2 y).const_smul (q y)

lemma continuousAt_Φ2 (q : ℝ → ℝ) (hq : AEStronglyMeasurable q volume) (hq1 : ∀ x, |q x| ≤ 1)
    (p₀ : ℝ × ℝ) (hp₀ : 0 < p₀.1) :
    ContinuousAt (fun p : ℝ × ℝ => ∫ y, q y • D2 p.1 p.2 y) p₀ := by
  obtain ⟨δ, hδpos, hδu, B, hBint, hb1, hb2, hb3, hb4, hb5⟩ :=
    Commons.Analysis.Gaussian.gaussian_kernel_partial_bounds p₀.1 p₀.2 hp₀
  have hlt₁ : ∀ p : ℝ × ℝ, dist p p₀ < δ → |p.1 - p₀.1| < δ := by
    intro p hp; rw [Prod.dist_eq] at hp
    exact lt_of_le_of_lt (le_max_left _ _) hp
  have hlt₂ : ∀ p : ℝ × ℝ, dist p p₀ < δ → |p.2 - p₀.2| < δ := by
    intro p hp; rw [Prod.dist_eq] at hp
    exact lt_of_le_of_lt (le_max_right _ _) hp
  have hD2bd : ∀ (p : ℝ × ℝ) (y : ℝ), dist p p₀ < δ → ‖D2 p.1 p.2 y‖ ≤ 4 * B y := by
    intro p y hp
    have h1 := hlt₁ p hp
    have h2 := hlt₂ p hp
    have hu : 0 ≤ p.1 := by rw [abs_lt] at h1; linarith [h1.1, hδu]
    have hxx : |K_xx p.1 p.2 y| ≤ B y :=
      le_trans (abs_K_xx_le_add p.1 p.2 y hu) (hb5 p.1 p.2 y (hlt₁ p hp) (hlt₂ p hp))
    have huu : |K_uu p.1 p.2 y| ≤ B y := hb3 p.1 p.2 y (hlt₁ p hp) (hlt₂ p hp)
    have hux : |K_ux p.1 p.2 y| ≤ B y := hb4 p.1 p.2 y (hlt₁ p hp) (hlt₂ p hp)
    calc ‖D2 p.1 p.2 y‖ ≤ |K_uu p.1 p.2 y| + |K_ux p.1 p.2 y| + |K_ux p.1 p.2 y| + |K_xx p.1 p.2 y| :=
          norm_D2_le _ _ _
      _ ≤ B y + B y + B y + B y := by linarith
      _ = 4 * B y := by ring
  have hcont : ContinuousOn (fun p : ℝ × ℝ => ∫ y, q y • D2 p.1 p.2 y) (ball p₀ δ) := by
    refine continuousOn_of_dominated (F := fun (p : ℝ × ℝ) (y : ℝ) => q y • D2 p.1 p.2 y)
      (bound := fun y => 4 * B y) ?_ ?_ ?_ ?_
    · intro p hp
      exact hq.smul (continuous_D2_y p.1 p.2).aestronglyMeasurable
    · intro p hp
      filter_upwards with y
      have hnorm : ‖q y • D2 p.1 p.2 y‖ ≤ |q y| * ‖D2 p.1 p.2 y‖ := by
        refine ContinuousLinearMap.opNorm_le_bound _
          (mul_nonneg (abs_nonneg (q y)) (norm_nonneg (D2 p.1 p.2 y))) ?_
        intro v
        rw [smul_apply]
        calc ‖q y • (D2 p.1 p.2 y) v‖ = |q y| * ‖(D2 p.1 p.2 y) v‖ := by
              rw [norm_smul, Real.norm_eq_abs]
          _ ≤ |q y| * (‖D2 p.1 p.2 y‖ * ‖v‖) := by gcongr; exact (D2 p.1 p.2 y).le_opNorm v
          _ = (|q y| * ‖D2 p.1 p.2 y‖) * ‖v‖ := by ring
      calc ‖q y • D2 p.1 p.2 y‖ ≤ |q y| * ‖D2 p.1 p.2 y‖ := hnorm
        _ ≤ 1 * ‖D2 p.1 p.2 y‖ := by gcongr; exact hq1 y
        _ = ‖D2 p.1 p.2 y‖ := one_mul _
        _ ≤ 4 * B y := hD2bd p y hp
    · exact hBint.const_mul 4
    · filter_upwards with y
      exact ((continuous_D2 y).const_smul (q y)).continuousOn
  exact hcont.continuousAt (ball_mem_nhds p₀ hδpos)

lemma contDiffOn_Φ (q : ℝ → ℝ) (hq : AEStronglyMeasurable q volume) (hq1 : ∀ x, |q x| ≤ 1) :
    ContDiffOn ℝ 2 (fun p : ℝ × ℝ => ∫ y, q y * K p.1 p.2 y) {p : ℝ × ℝ | 0 < p.1} := by
  have hU : IsOpen {p : ℝ × ℝ | 0 < p.1} := isOpen_lt continuous_const continuous_fst
  have hA : ∀ p ∈ {p : ℝ × ℝ | 0 < p.1},
      HasFDerivAt (fun p : ℝ × ℝ => ∫ y, q y * K p.1 p.2 y)
        (∫ y, q y • D1 p.1 p.2 y) p := fun p hp => hasFDerivAt_Φ q hq hq1 p hp
  have hB : ∀ p ∈ {p : ℝ × ℝ | 0 < p.1},
      HasFDerivAt (fun p : ℝ × ℝ => ∫ y, q y • D1 p.1 p.2 y)
        (∫ y, q y • D2 p.1 p.2 y) p := fun p hp => hasFDerivAt_Φ1 q hq hq1 p hp
  have hC : ContinuousOn (fun p : ℝ × ℝ => ∫ y, q y • D2 p.1 p.2 y) {p : ℝ × ℝ | 0 < p.1} :=
    fun p hp => (continuousAt_Φ2 q hq hq1 p hp).continuousWithinAt
  have hG1_diff : DifferentiableOn ℝ (fun p : ℝ × ℝ => ∫ y, q y • D1 p.1 p.2 y)
      {p : ℝ × ℝ | 0 < p.1} := fun p hp => (hB p hp).differentiableAt.differentiableWithinAt
  have hG2_cd : ContDiffOn ℝ 0 (fderiv ℝ (fun p : ℝ × ℝ => ∫ y, q y • D1 p.1 p.2 y))
      {p : ℝ × ℝ | 0 < p.1} := by
    rw [contDiffOn_zero]
    apply ContinuousOn.congr hC
    intro p hp
    exact (hB p hp).fderiv
  have hG1_cd : ContDiffOn ℝ 1 (fun p : ℝ × ℝ => ∫ y, q y • D1 p.1 p.2 y)
      {p : ℝ × ℝ | 0 < p.1} := by
    rw [show (1 : WithTop ℕ∞) = 0 + 1 from rfl, contDiffOn_succ_iff_fderiv_of_isOpen hU]
    exact ⟨hG1_diff, by simp, hG2_cd⟩
  rw [show (2 : WithTop ℕ∞) = 1 + 1 from rfl, contDiffOn_succ_iff_fderiv_of_isOpen hU]
  refine ⟨?_, by simp, ?_⟩
  · intro p hp; exact (hA p hp).differentiableAt.differentiableWithinAt
  · apply ContDiffOn.congr hG1_cd
    intro p hp
    exact (hA p hp).fderiv

/-! ### the substitution identity -/

lemma exp_arg_sq (t : ℝ) (ht : 0 < t) : ((Real.sqrt t)⁻¹) ^ 2 = t⁻¹ := by
  rw [inv_pow, Real.sq_sqrt ht.le]

lemma subst_K (q : ℝ → ℝ) {t x : ℝ} (ht : 0 < t) :
    (∫ z, q (x + Real.sqrt t * z) * Real.exp (-Real.pi * z^2))
      = ∫ y, q y * K ((Real.sqrt t)⁻¹) x y := by
  have hs : 0 < Real.sqrt t := Real.sqrt_pos.2 ht
  set g : ℝ → ℝ := fun w => q (x + w) * Real.exp (-Real.pi * w^2 / t) with hg
  have h1 : (fun z : ℝ => q (x + Real.sqrt t * z) * Real.exp (-Real.pi * z^2))
      = fun z : ℝ => g (Real.sqrt t * z) := by
    funext z
    simp only [hg, g]
    rw [mul_pow, Real.sq_sqrt ht.le]
    congr 2
    field_simp
  rw [h1, Measure.integral_comp_mul_left]
  rw [abs_of_nonneg (inv_nonneg.2 hs.le), smul_eq_mul, ← integral_const_mul]
  rw [← integral_add_left_eq_self (fun y => q y * K ((Real.sqrt t)⁻¹) x y) x]
  apply integral_congr_ae
  filter_upwards with w
  simp only [hg, g, Pi.mul_apply, K]
  rw [exp_arg_sq t ht, show (x + w) - x = w by ring]
  ring_nf

/-! ### non-measurable case -/

lemma not_aesm_mul_K {q : ℝ → ℝ} {u x : ℝ} (hu : 0 < u)
    (hq : ¬ AEStronglyMeasurable q volume) :
    ¬ AEStronglyMeasurable (fun y => q y * K u x y) volume := by
  intro h
  apply hq
  have hK : AEStronglyMeasurable (fun y => (K u x y)⁻¹) volume := by
    apply Continuous.aestronglyMeasurable
    exact (continuous_K_y u x).inv₀ (fun y => ne_of_gt (by unfold K; positivity))
  have h2 : AEStronglyMeasurable (fun y => (q y * K u x y) * (K u x y)⁻¹) volume := h.mul hK
  refine h2.congr ?_
  filter_upwards with y
  have hpos : K u x y ≠ 0 := ne_of_gt (by unfold K; positivity)
  field_simp

/-! ### the smoothness of the composed function -/

theorem contDiffOn_K_comp (q : ℝ → ℝ) (hq : AEStronglyMeasurable q volume) (hq1 : ∀ x, |q x| ≤ 1) :
    ContDiffOn ℝ 2 (fun p : ℝ × ℝ => ∫ y, q y * K ((Real.sqrt p.1)⁻¹) p.2 y)
      {p : ℝ × ℝ | 0 < p.1} := by
  have hΦ : ContDiffOn ℝ 2 (fun p : ℝ × ℝ => ∫ y, q y * K p.1 p.2 y) {p : ℝ × ℝ | 0 < p.1} :=
    contDiffOn_Φ q hq hq1
  have hψ : ContDiffOn ℝ 2 (fun p : ℝ × ℝ => ((Real.sqrt p.1)⁻¹, p.2)) {p : ℝ × ℝ | 0 < p.1} := by
    apply ContDiffOn.prodMk
    · apply ContDiffOn.inv
      · apply ContDiffOn.sqrt
        · fun_prop
        · intro x hx; exact ne_of_gt hx
      · intro x hx; exact ne_of_gt (Real.sqrt_pos.2 hx)
    · fun_prop
  have hmaps : Set.MapsTo (fun p : ℝ × ℝ => ((Real.sqrt p.1)⁻¹, p.2))
      {p : ℝ × ℝ | 0 < p.1} {p : ℝ × ℝ | 0 < p.1} := by
    intro p hp
    exact inv_pos.mpr (Real.sqrt_pos.2 hp)
  refine (hΦ.comp hψ hmaps).congr ?_
  intro p hp
  rfl


end

end HeatFlow

open HeatFlow

theorem heatFlow_contdiff (q : ℝ → ℝ) (hq : ∀ x, |q x| ≤ 1) :
    ContDiffOn ℝ 2 (fun p : ℝ × ℝ => ∫ z, q (p.2 + Real.sqrt p.1 * z) * Real.exp (-Real.pi * z ^ 2))
      {p : ℝ × ℝ | 0 < p.1} := by
  by_cases hmeas : AEStronglyMeasurable q volume
  · refine (contDiffOn_K_comp q hmeas hq).congr ?_
    intro p hp
    exact subst_K q hp
  · refine ContDiffOn.congr (contDiffOn_const (c := (0 : ℝ)) (𝕜 := ℝ) (s := {p : ℝ × ℝ | 0 < p.1})) ?_
    intro p hp
    rw [subst_K q hp]
    exact integral_non_aestronglyMeasurable
      (not_aesm_mul_K (u := (Real.sqrt p.1)⁻¹) (inv_pos.mpr (Real.sqrt_pos.2 hp)) hmeas)

end Commons.Analysis.GaussianMeasure