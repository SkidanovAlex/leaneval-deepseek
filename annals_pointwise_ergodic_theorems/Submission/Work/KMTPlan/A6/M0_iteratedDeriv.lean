import Mathlib
import Submission.Work.KMTAreas.A7.ModelApproxM0Deriv

/-!
# The iterated `ξ`-derivatives of the symbol difference `M₀` of the §6 model approximation

For the symbol difference `M0 P N q α₁ α₂ ξ₁ ξ₂` of Proposition `mod-approx`
(`Submission/Work/KMTAreas/A7/ModelApproxDefs.lean`) and its `(ξ₁,ξ₂)`-derivatives
`M0deriv P N q α₁ α₂ ξ₁ ξ₂ j₁ j₂` (`…/ModelApproxM0Deriv.lean`) we prove that the
iterated derivatives of `M₀` *are* `M0deriv`:

`iteratedDeriv j₁ (fun a => iteratedDeriv j₂ (fun b => M0 P N q α₁ α₂ a b) y) x
   = M0deriv P N q α₁ α₂ x y j₁ j₂` (`j₁, j₂ ≤ 2`).

The proof is a computation organised as follows.

* `M0Aux.norm_ee`, `M0Aux.continuous_ee`, `M0Aux.hasDerivAt_ee_*` : the elementary facts about
  the character `e(x) = exp(2πix)` and the affine phases `A ξ + B`, `B + ξ A`, `ξ A + B`.
* `M0Aux.hasDerivAt_integral_ee` (`…ee'`) : differentiation under the integral sign for the family
  `ξ ↦ ∫ e(θ t + ξ g t) h t dt`, obtained from the dominated convergence theorem for interval
  integrals; this handles the continuous part `mTilde`.
* `M0Aux.hasDerivAt_momPhaseDeriv_snd/_fst` : the `ξ₁`- and `ξ₂`-derivatives of the discrete
  summand, with the derivative bookkeeping `(j₁,j₂) ↦ (j₁+1,j₂)` / `(j₁,j₂+1)`.
* `M0Aux.iterate_deriv_weylAvg`, `M0Aux.iterate_deriv_weylAvgSum_fst`, `M0Aux.iterate_deriv_mTilde`,
  `M0Aux.iterate_deriv_mTildeDeriv_fst` : the `n`-fold `deriv` of the discrete average, of its
  `ξ₁`-family, and of the continuous part, again as functions of the remaining variable.
* `M0Aux.iterate_deriv_sub`, `M0Aux.iterate_deriv_const_mul` : `deriv^[n]` is additive and
  homogeneous on the classes of functions for which the intermediate derivatives are
  differentiable (which is what `M0Aux.differentiable_*` supply here).
* the assembly at the bottom: the two-variable statement, obtained by running the one-variable
  computations in the two slots.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

namespace Work.KMTPlan.A6

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators Interval
open Work.KMTAreas.A7

namespace M0Aux

/-! ## 1. The exponential `e(x) = exp(2πi x)` -/

theorem norm_ee (x : ℝ) : ‖ee x‖ = 1 := by
  unfold ee
  have h : (2 * (Real.pi : ℂ) * Complex.I * (x : ℂ)) = (((2 * Real.pi * x : ℝ)) : ℂ) * Complex.I := by
    push_cast; ring
  rw [h, Complex.norm_exp_ofReal_mul_I]

theorem continuous_ee : Continuous ee := by
  unfold ee
  exact Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)

theorem continuous_PevalR_mul (P : Polynomial ℤ) (N : ℝ) :
    Continuous fun t : ℝ => PevalR P (N * t) := by
  unfold PevalR
  exact (P.map (Int.castRingHom ℝ)).continuous.comp (continuous_const.mul continuous_id)

theorem hasDerivAt_ee_left (A B : ℝ) (b : ℝ) :
    HasDerivAt (fun ξ : ℝ => ee (A * ξ + B))
      (ee (A * b + B) * (2 * Real.pi * Complex.I * (A : ℂ))) b := by
  have h1 : HasDerivAt (fun ξ : ℝ => A * ξ + B) A b := by
    simpa using (hasDerivAt_const_mul (𝕜 := ℝ) A).add_const B
  have h2 : HasDerivAt (fun ξ : ℝ => ((A * ξ + B : ℝ) : ℂ)) ((A : ℂ)) b := h1.ofReal_comp
  have h3 : HasDerivAt (fun ξ : ℝ => (2 * (Real.pi : ℂ) * Complex.I) * ((A * ξ + B : ℝ) : ℂ))
      ((2 * (Real.pi : ℂ) * Complex.I) * (A : ℂ)) b := h2.const_mul _
  have h4 := h3.cexp
  have hfun : (fun ξ : ℝ => Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * ((A * ξ + B : ℝ) : ℂ)))
      = fun ξ : ℝ => ee (A * ξ + B) := rfl
  rw [hfun] at h4
  have hexp : Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((A * b + B : ℝ) : ℂ)) = ee (A * b + B) := rfl
  rw [hexp] at h4
  exact h4

theorem hasDerivAt_ee_right (A B : ℝ) (b : ℝ) :
    HasDerivAt (fun ξ : ℝ => ee (B + ξ * A))
      (ee (B + b * A) * (2 * Real.pi * Complex.I * (A : ℂ))) b := by
  have h1 : HasDerivAt (fun ξ : ℝ => B + ξ * A) A b := by
    have h : HasDerivAt (fun ξ : ℝ => ξ * A) A b := by
      simpa using (hasDerivAt_id b).mul_const A
    exact h.const_add B
  have h2 : HasDerivAt (fun ξ : ℝ => ((B + ξ * A : ℝ) : ℂ)) ((A : ℂ)) b := h1.ofReal_comp
  have h3 : HasDerivAt (fun ξ : ℝ => (2 * (Real.pi : ℂ) * Complex.I) * ((B + ξ * A : ℝ) : ℂ))
      ((2 * (Real.pi : ℂ) * Complex.I) * (A : ℂ)) b := h2.const_mul _
  have h4 := h3.cexp
  have hfun : (fun ξ : ℝ => Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * ((B + ξ * A : ℝ) : ℂ)))
      = fun ξ : ℝ => ee (B + ξ * A) := rfl
  rw [hfun] at h4
  have hexp : Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((B + b * A : ℝ) : ℂ)) = ee (B + b * A) := rfl
  rw [hexp] at h4
  exact h4

theorem hasDerivAt_const_mul_ee_left (C : ℂ) (A B : ℝ) (b : ℝ) :
    HasDerivAt (fun ξ : ℝ => C * ee (A * ξ + B))
      (C * ee (A * b + B) * (2 * Real.pi * Complex.I * (A : ℂ))) b := by
  simpa only [mul_assoc] using (hasDerivAt_ee_left A B b).const_mul C

theorem hasDerivAt_const_mul_ee_right (C : ℂ) (A B : ℝ) (b : ℝ) :
    HasDerivAt (fun ξ : ℝ => C * ee (B + ξ * A))
      (C * ee (B + b * A) * (2 * Real.pi * Complex.I * (A : ℂ))) b := by
  simpa only [mul_assoc] using (hasDerivAt_ee_right A B b).const_mul C

theorem hasDerivAt_ee_mul_const_right (C : ℂ) (A B : ℝ) (b : ℝ) :
    HasDerivAt (fun ξ : ℝ => ee (B + ξ * A) * C)
      (ee (B + b * A) * C * (2 * Real.pi * Complex.I * (A : ℂ))) b := by
  simpa only [mul_assoc, mul_comm, mul_left_comm] using (hasDerivAt_ee_right A B b).mul_const C

theorem hasDerivAt_ee_vf (A B : ℝ) (b : ℝ) :
    HasDerivAt (fun ξ : ℝ => ee (ξ * A + B))
      (ee (b * A + B) * (2 * Real.pi * Complex.I * (A : ℂ))) b := by
  have h1 : HasDerivAt (fun ξ : ℝ => ξ * A + B) A b := by
    have h : HasDerivAt (fun ξ : ℝ => ξ * A) A b := by
      simpa using (hasDerivAt_id b).mul_const A
    exact h.add_const B
  have h2 : HasDerivAt (fun ξ : ℝ => ((ξ * A + B : ℝ) : ℂ)) ((A : ℂ)) b := h1.ofReal_comp
  have h3 : HasDerivAt (fun ξ : ℝ => (2 * (Real.pi : ℂ) * Complex.I) * ((ξ * A + B : ℝ) : ℂ))
      ((2 * (Real.pi : ℂ) * Complex.I) * (A : ℂ)) b := h2.const_mul _
  have h4 := h3.cexp
  have hfun : (fun ξ : ℝ => Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * ((ξ * A + B : ℝ) : ℂ)))
      = fun ξ : ℝ => ee (ξ * A + B) := rfl
  rw [hfun] at h4
  have hexp : Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((b * A + B : ℝ) : ℂ)) = ee (b * A + B) := rfl
  rw [hexp] at h4
  exact h4

theorem hasDerivAt_const_mul_ee_vf (C : ℂ) (A B : ℝ) (b : ℝ) :
    HasDerivAt (fun ξ : ℝ => C * ee (ξ * A + B))
      (C * ee (b * A + B) * (2 * Real.pi * Complex.I * (A : ℂ))) b := by
  simpa only [mul_assoc] using (hasDerivAt_ee_vf A B b).const_mul C

/-- Differentiating under the integral sign along the family `ξ ↦ ∫ e(θ t + ξ g t) h t`. -/
theorem hasDerivAt_integral_ee (c d : ℝ) (θ g : ℝ → ℝ) (h : ℝ → ℂ)
    (hθ : Continuous θ) (hg : Continuous g) (hh : Continuous h) (ξ : ℝ) :
    HasDerivAt (fun ξ' : ℝ => ∫ t in c..d, ee (θ t + ξ' * g t) * h t)
      (∫ t in c..d, ee (θ t + ξ * g t) * h t * (2 * Real.pi * Complex.I * ((g t : ℝ) : ℂ))) ξ := by
  have hFcont : ∀ ξ' : ℝ, Continuous fun t : ℝ => ee (θ t + ξ' * g t) * h t := fun ξ' =>
    (continuous_ee.comp (hθ.add (continuous_const.mul hg))).mul hh
  have hF'cont : Continuous fun t : ℝ =>
      ee (θ t + ξ * g t) * h t * (2 * Real.pi * Complex.I * ((g t : ℝ) : ℂ)) :=
    (hFcont ξ).mul (continuous_const.mul (Complex.continuous_ofReal.comp hg))
  have hboundcont : Continuous fun t : ℝ =>
      ‖h t‖ * ‖2 * Real.pi * Complex.I * ((g t : ℝ) : ℂ)‖ :=
    hh.norm.mul ((continuous_const.mul (Complex.continuous_ofReal.comp hg)).norm)
  have h := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume) (a := c) (b := d) (E := ℂ) (x₀ := ξ) (s := Set.univ)
    (F := fun ξ' t => ee (θ t + ξ' * g t) * h t)
    (F' := fun ξ' t => ee (θ t + ξ' * g t) * h t * (2 * Real.pi * Complex.I * ((g t : ℝ) : ℂ)))
    (bound := fun t => ‖h t‖ * ‖2 * Real.pi * Complex.I * ((g t : ℝ) : ℂ)‖)
    Filter.univ_mem
    (Filter.Eventually.of_forall fun ξ' =>
      ((hFcont ξ').aestronglyMeasurable).mono_measure Measure.restrict_le_self)
    ((hFcont ξ).intervalIntegrable c d)
    (hF'cont.aestronglyMeasurable.mono_measure Measure.restrict_le_self)
    (Filter.Eventually.of_forall fun t _ _ _ => by
      rw [norm_mul, norm_mul, norm_ee, one_mul])
    (hboundcont.intervalIntegrable c d)
    (Filter.Eventually.of_forall fun t _ x _ => hasDerivAt_ee_mul_const_right (h t) (g t) (θ t) x)
  exact h.2

/-- Variant of `hasDerivAt_integral_ee` with the variable in the first summand of the phase. -/
theorem hasDerivAt_integral_ee' (c d : ℝ) (θ g : ℝ → ℝ) (h : ℝ → ℂ)
    (hθ : Continuous θ) (hg : Continuous g) (hh : Continuous h) (ξ : ℝ) :
    HasDerivAt (fun ξ' : ℝ => ∫ t in c..d, ee (ξ' * g t + θ t) * h t)
      (∫ t in c..d, ee (ξ * g t + θ t) * h t * (2 * Real.pi * Complex.I * ((g t : ℝ) : ℂ))) ξ := by
  have hmain := hasDerivAt_integral_ee c d θ g h hθ hg hh ξ
  have hfun : (fun ξ' : ℝ => ∫ t in c..d, ee (ξ' * g t + θ t) * h t)
      = (fun ξ' : ℝ => ∫ t in c..d, ee (θ t + ξ' * g t) * h t) := by
    funext ξ'
    refine intervalIntegral.integral_congr (fun t _ => ?_)
    have hph : ξ' * g t + θ t = θ t + ξ' * g t := by ring
    rw [hph]
  have hval : (∫ t in c..d, ee (θ t + ξ * g t) * h t * (2 * Real.pi * Complex.I * ((g t : ℝ) : ℂ)))
      = (∫ t in c..d, ee (ξ * g t + θ t) * h t
          * (2 * Real.pi * Complex.I * ((g t : ℝ) : ℂ))) := by
    refine intervalIntegral.integral_congr (fun t _ => ?_)
    have hph : ξ * g t + θ t = θ t + ξ * g t := by ring
    rw [hph]
  rw [← hfun, hval] at hmain
  exact hmain

/-! ## 3. The derivatives of the discrete summand `momPhase` -/

theorem momPhaseDeriv_eq (P : Polynomial ℤ) (N : ℕ)
    (α₁ α₂ : Work.Analysis.IonescuWainger.Circle) (a y : ℝ) (n : ℤ) (i j : ℕ) :
    momPhaseDeriv P N α₁ α₂ a y n i j
      = (fourier (T := 1) n α₁ * fourier (T := 1) (P.eval n) α₂)
        * (2 * Real.pi * Complex.I * (n : ℂ)) ^ i
        * (2 * Real.pi * Complex.I * ((PevalR P (n : ℝ) : ℝ) : ℂ)) ^ j
        * ee (a * (n : ℝ) + y * PevalR P (n : ℝ)) := by
  simp only [momPhaseDeriv, momPhase]
  ring

/-- The coefficient of `ee` in `momPhaseDeriv`. -/
noncomputable def momCoeff (P : Polynomial ℤ) (α₁ α₂ : Work.Analysis.IonescuWainger.Circle)
    (n : ℤ) (i j : ℕ) : ℂ :=
  (fourier (T := 1) n α₁ * fourier (T := 1) (P.eval n) α₂)
    * (2 * Real.pi * Complex.I * (n : ℂ)) ^ i
    * (2 * Real.pi * Complex.I * ((PevalR P (n : ℝ) : ℝ) : ℂ)) ^ j

theorem momPhaseDeriv_eq_coeff (P : Polynomial ℤ) (N : ℕ)
    (α₁ α₂ : Work.Analysis.IonescuWainger.Circle) (a y : ℝ) (n : ℤ) (i j : ℕ) :
    momPhaseDeriv P N α₁ α₂ a y n i j
      = momCoeff P α₁ α₂ n i j * ee (a * (n : ℝ) + y * PevalR P (n : ℝ)) := by
  rw [momPhaseDeriv_eq]
  rfl

theorem hasDerivAt_momPhaseDeriv_snd (P : Polynomial ℤ) (N : ℕ)
    (α₁ α₂ : Work.Analysis.IonescuWainger.Circle) (a : ℝ) (n : ℤ) (i j : ℕ) (y : ℝ) :
    HasDerivAt (fun y' : ℝ => momPhaseDeriv P N α₁ α₂ a y' n i j)
      (momPhaseDeriv P N α₁ α₂ a y n i (j + 1)) y := by
  have hfun : (fun y' : ℝ => momPhaseDeriv P N α₁ α₂ a y' n i j)
      = fun y' : ℝ => momCoeff P α₁ α₂ n i j * ee (a * (n : ℝ) + y' * PevalR P (n : ℝ)) := by
    funext y'
    rw [momPhaseDeriv_eq_coeff]
  rw [hfun]
  have hval : momCoeff P α₁ α₂ n i j * ee (a * (n : ℝ) + y * PevalR P (n : ℝ))
        * (2 * Real.pi * Complex.I * ((PevalR P (n : ℝ) : ℝ) : ℂ))
      = momPhaseDeriv P N α₁ α₂ a y n i (j + 1) := by
    rw [momPhaseDeriv_eq_coeff]
    simp only [momCoeff, pow_succ]
    ring
  have h := hasDerivAt_const_mul_ee_right (momCoeff P α₁ α₂ n i j)
    (PevalR P (n : ℝ)) (a * (n : ℝ)) y
  rw [hval] at h
  exact h

theorem hasDerivAt_momPhaseDeriv_fst (P : Polynomial ℤ) (N : ℕ)
    (α₁ α₂ : Work.Analysis.IonescuWainger.Circle) (y : ℝ) (n : ℤ) (i j : ℕ) (x : ℝ) :
    HasDerivAt (fun x' : ℝ => momPhaseDeriv P N α₁ α₂ x' y n i j)
      (momPhaseDeriv P N α₁ α₂ x y n (i + 1) j) x := by
  have hfun : (fun x' : ℝ => momPhaseDeriv P N α₁ α₂ x' y n i j)
      = fun x' : ℝ => momCoeff P α₁ α₂ n i j * ee (x' * (n : ℝ) + y * PevalR P (n : ℝ)) := by
    funext x'
    rw [momPhaseDeriv_eq_coeff]
  rw [hfun]
  have hval : momCoeff P α₁ α₂ n i j * ee (x * (n : ℝ) + y * PevalR P (n : ℝ))
        * (2 * Real.pi * Complex.I * (((n : ℝ) : ℝ) : ℂ))
      = momPhaseDeriv P N α₁ α₂ x y n (i + 1) j := by
    rw [momPhaseDeriv_eq_coeff]
    simp only [momCoeff, pow_succ, Complex.ofReal_intCast]
    ring
  have h := hasDerivAt_const_mul_ee_vf (momCoeff P α₁ α₂ n i j)
    ((n : ℝ)) (y * PevalR P (n : ℝ)) x
  rw [hval] at h
  exact h

theorem differentiable_momPhaseDeriv_snd (P : Polynomial ℤ) (N : ℕ)
    (α₁ α₂ : Work.Analysis.IonescuWainger.Circle) (a : ℝ) (n : ℤ) (i j : ℕ) :
    Differentiable ℝ (fun y : ℝ => momPhaseDeriv P N α₁ α₂ a y n i j) :=
  fun y => (hasDerivAt_momPhaseDeriv_snd P N α₁ α₂ a n i j y).differentiableAt

theorem differentiable_momPhaseDeriv_fst (P : Polynomial ℤ) (N : ℕ)
    (α₁ α₂ : Work.Analysis.IonescuWainger.Circle) (y : ℝ) (n : ℤ) (i j : ℕ) :
    Differentiable ℝ (fun x : ℝ => momPhaseDeriv P N α₁ α₂ x y n i j) :=
  fun x => (hasDerivAt_momPhaseDeriv_fst P N α₁ α₂ y n i j x).differentiableAt

theorem differentiable_weylAvgSum_snd (P : Polynomial ℤ) (N : ℕ)
    (α₁ α₂ : Work.Analysis.IonescuWainger.Circle) (a : ℝ) (j : ℕ) :
    Differentiable ℝ (fun y : ℝ =>
      (N : ℂ)⁻¹ * ∑ n ∈ Finset.Ioc (N / 2) N, momPhaseDeriv P N α₁ α₂ a y (n : ℤ) 0 j) := by
  exact (Differentiable.fun_sum (u := Finset.Ioc (N / 2) N)
    (fun n _ => differentiable_momPhaseDeriv_snd P N α₁ α₂ a (n : ℤ) 0 j)).const_mul ((N : ℂ)⁻¹)

theorem differentiable_weylAvgSum_fst (P : Polynomial ℤ) (N : ℕ)
    (α₁ α₂ : Work.Analysis.IonescuWainger.Circle) (y : ℝ) (i j : ℕ) :
    Differentiable ℝ (fun x : ℝ =>
      (N : ℂ)⁻¹ * ∑ n ∈ Finset.Ioc (N / 2) N, momPhaseDeriv P N α₁ α₂ x y (n : ℤ) i j) := by
  exact (Differentiable.fun_sum (u := Finset.Ioc (N / 2) N)
    (fun n _ => differentiable_momPhaseDeriv_fst P N α₁ α₂ y (n : ℤ) i j)).const_mul ((N : ℂ)⁻¹)

theorem deriv_weylAvgSum_snd (P : Polynomial ℤ) (N : ℕ)
    (α₁ α₂ : Work.Analysis.IonescuWainger.Circle) (a : ℝ) (j : ℕ) :
    deriv (fun y : ℝ =>
        (N : ℂ)⁻¹ * ∑ n ∈ Finset.Ioc (N / 2) N, momPhaseDeriv P N α₁ α₂ a y (n : ℤ) 0 j)
      = fun y : ℝ =>
        (N : ℂ)⁻¹ * ∑ n ∈ Finset.Ioc (N / 2) N, momPhaseDeriv P N α₁ α₂ a y (n : ℤ) 0 (j + 1) := by
  funext y
  have h := HasDerivAt.const_mul ((N : ℂ)⁻¹)
    (HasDerivAt.fun_sum (u := Finset.Ioc (N / 2) N)
      (fun n _ => hasDerivAt_momPhaseDeriv_snd P N α₁ α₂ a (n : ℤ) 0 j y))
  exact h.deriv

theorem iterate_deriv_weylAvg (P : Polynomial ℤ) (N : ℕ)
    (α₁ α₂ : Work.Analysis.IonescuWainger.Circle) (a : ℝ) (j : ℕ) :
    deriv^[j] (fun b : ℝ => weylAvg P N α₁ α₂ a b)
      = fun y : ℝ =>
        (N : ℂ)⁻¹ * ∑ n ∈ Finset.Ioc (N / 2) N, momPhaseDeriv P N α₁ α₂ a y (n : ℤ) 0 j := by
  induction j with
  | zero =>
      funext y
      simp only [Function.iterate_zero, id_eq, weylAvg, momPhaseDeriv, pow_zero, mul_one]
  | succ j ih =>
      rw [Function.iterate_succ', Function.comp_apply, ih, deriv_weylAvgSum_snd]

theorem differentiable_weylAvg_iterated (P : Polynomial ℤ) (N : ℕ)
    (α₁ α₂ : Work.Analysis.IonescuWainger.Circle) (a : ℝ) (k : ℕ) :
    Differentiable ℝ (deriv^[k] (fun b : ℝ => weylAvg P N α₁ α₂ a b)) := by
  rw [iterate_deriv_weylAvg]
  exact differentiable_weylAvgSum_snd P N α₁ α₂ a k

theorem deriv_weylAvgSum_fst (P : Polynomial ℤ) (N : ℕ)
    (α₁ α₂ : Work.Analysis.IonescuWainger.Circle) (y : ℝ) (i j : ℕ) :
    deriv (fun x : ℝ =>
        (N : ℂ)⁻¹ * ∑ n ∈ Finset.Ioc (N / 2) N, momPhaseDeriv P N α₁ α₂ x y (n : ℤ) i j)
      = fun x : ℝ =>
        (N : ℂ)⁻¹ * ∑ n ∈ Finset.Ioc (N / 2) N, momPhaseDeriv P N α₁ α₂ x y (n : ℤ) (i + 1) j := by
  funext x
  have h := HasDerivAt.const_mul ((N : ℂ)⁻¹)
    (HasDerivAt.fun_sum (u := Finset.Ioc (N / 2) N)
      (fun n _ => hasDerivAt_momPhaseDeriv_fst P N α₁ α₂ y (n : ℤ) i j x))
  exact h.deriv

theorem iterate_deriv_weylAvgSum_fst (P : Polynomial ℤ) (N : ℕ)
    (α₁ α₂ : Work.Analysis.IonescuWainger.Circle) (y : ℝ) (j₂ i : ℕ) :
    deriv^[i] (fun x : ℝ =>
        (N : ℂ)⁻¹ * ∑ n ∈ Finset.Ioc (N / 2) N, momPhaseDeriv P N α₁ α₂ x y (n : ℤ) 0 j₂)
      = fun x : ℝ =>
        (N : ℂ)⁻¹ * ∑ n ∈ Finset.Ioc (N / 2) N, momPhaseDeriv P N α₁ α₂ x y (n : ℤ) i j₂ := by
  induction i with
  | zero => funext x; simp only [Function.iterate_zero, id_eq]
  | succ i ih =>
      rw [Function.iterate_succ', Function.comp_apply, ih, deriv_weylAvgSum_fst]

/-! ## 4. The derivatives of the continuous part `mTilde` -/

theorem mTilde_eq (P : Polynomial ℤ) (N : ℕ) (a b : ℝ) :
    mTilde P N a b
      = ∫ t in (1/2 : ℝ)..1, ee (a * (N : ℝ) * t + b * PevalR P ((N : ℝ) * t)) := rfl

theorem hasDerivAt_mTilde_snd (P : Polynomial ℤ) (N : ℕ) (a b : ℝ) :
    HasDerivAt (fun y : ℝ => mTilde P N a y)
      (∫ t in (1/2 : ℝ)..1, ee (a * (N : ℝ) * t + b * PevalR P ((N : ℝ) * t))
        * (2 * Real.pi * Complex.I * ((PevalR P ((N : ℝ) * t) : ℝ) : ℂ))) b := by
  have h := hasDerivAt_integral_ee (1/2) 1 (fun t : ℝ => a * (N : ℝ) * t)
    (fun t : ℝ => PevalR P ((N : ℝ) * t)) (fun _ : ℝ => 1)
    (continuous_const.mul continuous_id) (continuous_PevalR_mul P (N : ℝ)) continuous_const b
  simpa only [mTilde, mul_one] using h

theorem hasDerivAt_mTildeDeriv_snd (P : Polynomial ℤ) (N : ℕ) (a : ℝ) (j : ℕ) (y : ℝ) :
    HasDerivAt (fun y' : ℝ => mTildeDeriv P N a y' 0 j)
      (mTildeDeriv P N a y 0 (j + 1)) y := by
  have hcont : Continuous fun t : ℝ =>
      (2 * Real.pi * Complex.I * ((PevalR P ((N : ℝ) * t) : ℝ) : ℂ)) ^ j :=
    (continuous_const.mul (Complex.continuous_ofReal.comp (continuous_PevalR_mul P (N : ℝ)))).pow j
  have h := hasDerivAt_integral_ee (1/2) 1 (fun t : ℝ => a * (N : ℝ) * t)
    (fun t : ℝ => PevalR P ((N : ℝ) * t))
    (fun t : ℝ => (2 * Real.pi * Complex.I * ((PevalR P ((N : ℝ) * t) : ℝ) : ℂ)) ^ j)
    (continuous_const.mul continuous_id) (continuous_PevalR_mul P (N : ℝ)) hcont y
  simpa only [mTildeDeriv, pow_zero, mul_one, one_mul, pow_succ, mul_assoc, mul_comm, mul_left_comm] using h

theorem deriv_mTildeDeriv_snd (P : Polynomial ℤ) (N : ℕ) (a : ℝ) (j : ℕ) :
    deriv (fun y : ℝ => mTildeDeriv P N a y 0 j)
      = fun y : ℝ => mTildeDeriv P N a y 0 (j + 1) := by
  funext y
  exact (hasDerivAt_mTildeDeriv_snd P N a j y).deriv

theorem iterate_deriv_mTilde (P : Polynomial ℤ) (N : ℕ) (a : ℝ) (j : ℕ) :
    deriv^[j] (fun b : ℝ => mTilde P N a b) = fun y : ℝ => mTildeDeriv P N a y 0 j := by
  induction j with
  | zero =>
      funext y
      simp only [Function.iterate_zero, id_eq, mTilde, mTildeDeriv, pow_zero, mul_one]
  | succ j ih => rw [Function.iterate_succ', Function.comp_apply, ih, deriv_mTildeDeriv_snd]

theorem differentiable_mTildeDeriv_snd (P : Polynomial ℤ) (N : ℕ) (a : ℝ) (j : ℕ) :
    Differentiable ℝ (fun y : ℝ => mTildeDeriv P N a y 0 j) :=
  fun y => (hasDerivAt_mTildeDeriv_snd P N a j y).differentiableAt

theorem differentiable_mTilde_iterated (P : Polynomial ℤ) (N : ℕ) (a : ℝ) (k : ℕ) :
    Differentiable ℝ (deriv^[k] (fun b : ℝ => mTilde P N a b)) := by
  rw [iterate_deriv_mTilde]
  exact differentiable_mTildeDeriv_snd P N a k

theorem hasDerivAt_mTildeDeriv_fst (P : Polynomial ℤ) (N : ℕ) (y : ℝ) (i j : ℕ) (x : ℝ) :
    HasDerivAt (fun x' : ℝ => mTildeDeriv P N x' y i j)
      (mTildeDeriv P N x y (i + 1) j) x := by
  have hcont : Continuous fun t : ℝ =>
      (2 * Real.pi * Complex.I * (((N : ℝ) * t : ℝ) : ℂ)) ^ i
        * (2 * Real.pi * Complex.I * ((PevalR P ((N : ℝ) * t) : ℝ) : ℂ)) ^ j :=
    ((continuous_const.mul (Complex.continuous_ofReal.comp (continuous_const.mul continuous_id))).pow i).mul
      ((continuous_const.mul (Complex.continuous_ofReal.comp (continuous_PevalR_mul P (N : ℝ)))).pow j)
  have h := hasDerivAt_integral_ee' (1/2) 1
    (fun t : ℝ => y * PevalR P ((N : ℝ) * t)) (fun t : ℝ => (N : ℝ) * t)
    (fun t : ℝ => (2 * Real.pi * Complex.I * (((N : ℝ) * t : ℝ) : ℂ)) ^ i
      * (2 * Real.pi * Complex.I * ((PevalR P ((N : ℝ) * t) : ℝ) : ℂ)) ^ j)
    (continuous_const.mul (continuous_PevalR_mul P (N : ℝ))) (continuous_const.mul continuous_id) hcont x
  simpa only [mTildeDeriv, pow_zero, mul_one, one_mul, pow_succ, mul_assoc, mul_comm, mul_left_comm] using h

theorem deriv_mTildeDeriv_fst (P : Polynomial ℤ) (N : ℕ) (y : ℝ) (i j : ℕ) :
    deriv (fun x : ℝ => mTildeDeriv P N x y i j)
      = fun x : ℝ => mTildeDeriv P N x y (i + 1) j := by
  funext x
  exact (hasDerivAt_mTildeDeriv_fst P N y i j x).deriv

theorem iterate_deriv_mTildeDeriv_fst (P : Polynomial ℤ) (N : ℕ) (y : ℝ) (j₂ i : ℕ) :
    deriv^[i] (fun x : ℝ => mTildeDeriv P N x y 0 j₂)
      = fun x : ℝ => mTildeDeriv P N x y i j₂ := by
  induction i with
  | zero => funext x; simp only [Function.iterate_zero, id_eq]
  | succ i ih => rw [Function.iterate_succ', Function.comp_apply, ih, deriv_mTildeDeriv_fst]

theorem differentiable_mTildeDeriv_fst (P : Polynomial ℤ) (N : ℕ) (y : ℝ) (i j : ℕ) :
    Differentiable ℝ (fun x : ℝ => mTildeDeriv P N x y i j) :=
  fun x => (hasDerivAt_mTildeDeriv_fst P N y i j x).differentiableAt

theorem differentiable_mTildeDeriv_fst_iterated (P : Polynomial ℤ) (N : ℕ) (y : ℝ)
    (j₂ k : ℕ) :
    Differentiable ℝ (deriv^[k] (fun x : ℝ => mTildeDeriv P N x y 0 j₂)) := by
  rw [iterate_deriv_mTildeDeriv_fst]
  exact differentiable_mTildeDeriv_fst P N y k j₂

/-! ## 5. Iterated derivatives of differences and constant multiples -/

theorem iterate_deriv_sub (n : ℕ) (f g : ℝ → ℂ)
    (hf : ∀ k ≤ n, Differentiable ℝ (deriv^[k] f))
    (hg : ∀ k ≤ n, Differentiable ℝ (deriv^[k] g)) :
    deriv^[n] (f - g) = deriv^[n] f - deriv^[n] g := by
  induction n with
  | zero =>
      funext x
      simp only [Function.iterate_zero, id_eq]
  | succ n ih =>
      rw [Function.iterate_succ', Function.comp_apply,
        ih (fun k hk => hf k (le_trans hk (Nat.le_succ n)))
           (fun k hk => hg k (le_trans hk (Nat.le_succ n)))]
      rw [show deriv (deriv^[n] f - deriv^[n] g) = deriv (deriv^[n] f) - deriv (deriv^[n] g) from by
        funext x
        exact deriv_sub (hf n (Nat.le_succ n) x) (hg n (Nat.le_succ n) x)]
      rfl

theorem iterate_deriv_const_mul (n : ℕ) (c : ℂ) (f : ℝ → ℂ) :
    deriv^[n] (fun x : ℝ => c * f x) = fun x : ℝ => c * deriv^[n] f x := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ', Function.comp_apply, ih, deriv_const_mul_field']
      rfl

theorem differentiable_const_mul_mTilde_iterated (P : Polynomial ℤ) (N q : ℕ)
    (α₁ α₂ : Work.Analysis.IonescuWainger.Circle) (a : ℝ) (k : ℕ) :
    Differentiable ℝ (deriv^[k] (fun b : ℝ => mZ P q α₁ α₂ * mTilde P N a b)) := by
  rw [iterate_deriv_const_mul]
  exact (differentiable_mTilde_iterated P N a k).const_mul (mZ P q α₁ α₂)

theorem iterate_deriv_M0_snd (P : Polynomial ℤ) (N q : ℕ)
    (α₁ α₂ : Work.Analysis.IonescuWainger.Circle) (a : ℝ) (j : ℕ) :
    deriv^[j] (fun b : ℝ => M0 P N q α₁ α₂ a b)
      = fun y : ℝ => (N : ℂ)⁻¹ * ∑ n ∈ Finset.Ioc (N / 2) N,
            momPhaseDeriv P N α₁ α₂ a y (n : ℤ) 0 j
          - mZ P q α₁ α₂ * mTildeDeriv P N a y 0 j := by
  have hfun : (fun b : ℝ => M0 P N q α₁ α₂ a b)
      = (fun b : ℝ => weylAvg P N α₁ α₂ a b)
        - (fun b : ℝ => mZ P q α₁ α₂ * mTilde P N a b) := by
    funext b
    rfl
  rw [hfun, iterate_deriv_sub j _ _
    (fun k _ => differentiable_weylAvg_iterated P N α₁ α₂ a k)
    (fun k _ => differentiable_const_mul_mTilde_iterated P N q α₁ α₂ a k)]
  rw [iterate_deriv_const_mul, iterate_deriv_weylAvg, iterate_deriv_mTilde]
  rfl

theorem differentiable_weylAvgSum_fst_iterated (P : Polynomial ℤ) (N : ℕ)
    (α₁ α₂ : Work.Analysis.IonescuWainger.Circle) (y : ℝ) (j₂ k : ℕ) :
    Differentiable ℝ (deriv^[k] (fun x : ℝ =>
      (N : ℂ)⁻¹ * ∑ n ∈ Finset.Ioc (N / 2) N, momPhaseDeriv P N α₁ α₂ x y (n : ℤ) 0 j₂)) := by
  rw [iterate_deriv_weylAvgSum_fst]
  exact differentiable_weylAvgSum_fst P N α₁ α₂ y k j₂

theorem differentiable_const_mul_mTildeDeriv_fst (P : Polynomial ℤ) (N q : ℕ)
    (α₁ α₂ : Work.Analysis.IonescuWainger.Circle) (y : ℝ) (j₂ k : ℕ) :
    Differentiable ℝ (deriv^[k] (fun a : ℝ => mZ P q α₁ α₂ * mTildeDeriv P N a y 0 j₂)) := by
  rw [iterate_deriv_const_mul]
  exact (differentiable_mTildeDeriv_fst_iterated P N y j₂ k).const_mul (mZ P q α₁ α₂)

end M0Aux

/-! ## 6. The iterated `ξ`-derivatives of `M₀` -/

theorem M0_iteratedDeriv (P : Polynomial ℤ) (N q : ℕ) (α₁ α₂ : Work.Analysis.IonescuWainger.Circle) {j₁ j₂ : ℕ} (hj₁ : j₁ ≤ 2) (hj₂ : j₂ ≤ 2) (x y : ℝ) : iteratedDeriv j₁ (fun a => iteratedDeriv j₂ (fun b => Work.KMTAreas.A7.M0 P N q α₁ α₂ a b) y) x = Work.KMTAreas.A7.M0deriv P N q α₁ α₂ x y j₁ j₂ := by
  have hinner : (fun a : ℝ => iteratedDeriv j₂ (fun b : ℝ => M0 P N q α₁ α₂ a b) y)
      = (fun a : ℝ => (N : ℂ)⁻¹ * ∑ n ∈ Finset.Ioc (N / 2) N,
            momPhaseDeriv P N α₁ α₂ a y (n : ℤ) 0 j₂)
        - (fun a : ℝ => mZ P q α₁ α₂ * mTildeDeriv P N a y 0 j₂) := by
    funext a
    rw [iteratedDeriv_eq_iterate, M0Aux.iterate_deriv_M0_snd]
    rfl
  rw [hinner, iteratedDeriv_eq_iterate]
  have hsub := M0Aux.iterate_deriv_sub j₁
    (fun a : ℝ => (N : ℂ)⁻¹ * ∑ n ∈ Finset.Ioc (N / 2) N,
      momPhaseDeriv P N α₁ α₂ a y (n : ℤ) 0 j₂)
    (fun a : ℝ => mZ P q α₁ α₂ * mTildeDeriv P N a y 0 j₂)
    (fun k _ => M0Aux.differentiable_weylAvgSum_fst_iterated P N α₁ α₂ y j₂ k)
    (fun k _ => M0Aux.differentiable_const_mul_mTildeDeriv_fst P N q α₁ α₂ y j₂ k)
  rw [hsub]
  have hsum := M0Aux.iterate_deriv_weylAvgSum_fst P N α₁ α₂ y j₂ j₁
  have hmT : deriv^[j₁] (fun a : ℝ => mZ P q α₁ α₂ * mTildeDeriv P N a y 0 j₂)
      = fun x : ℝ => mZ P q α₁ α₂ * mTildeDeriv P N x y j₁ j₂ := by
    rw [M0Aux.iterate_deriv_const_mul, M0Aux.iterate_deriv_mTildeDeriv_fst]
  rw [hsum, hmT, M0deriv]
  rfl


end
end Work.KMTPlan.A6
