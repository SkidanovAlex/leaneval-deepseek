import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.InnerProductSpace.Dual
import Submission.Commons.Measure.Integral.integrable_pow_mul_exp_neg_norm_sq

open MeasureTheory Set Real Filter
open scoped Real Topology BigOperators

namespace Commons.Analysis.MeasureTheory

variable {n : ℕ}

/-- The coordinate projection `w ↦ w i` as a continuous linear form, turned into a continuous
bilinear form `B c w = c * w i`. -/
private noncomputable def coordB (i : Fin n) :
    ℝ →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ :=
  ContinuousLinearMap.toSpanSingleton ℝ
    (PiLp.proj (p := 2) (𝕜 := ℝ) (β := fun _ : Fin n => ℝ) i)

private lemma coordB_apply (i : Fin n) (c : ℝ) (w : EuclideanSpace ℝ (Fin n)) :
    coordB i c w = c * w i := by
  simp [coordB, ContinuousLinearMap.toSpanSingleton_apply, PiLp.proj_apply]

/-- A vector of `EuclideanSpace ℝ (Fin n)` is the sum of its coordinates against the standard
basis vectors. -/
private lemma sum_single_eq_self (x : EuclideanSpace ℝ (Fin n)) :
    (∑ i : Fin n, (x i) • EuclideanSpace.single i 1) = x := by
  apply WithLp.ofLp_injective
  funext j
  simp only [WithLp.ofLp_sum, WithLp.ofLp_smul, PiLp.ofLp_single]
  rw [Finset.sum_apply, Finset.sum_eq_single j]
  · simp
  · intro i _ hij
    simp [Pi.single_eq_of_ne (Ne.symm hij)]
  · intro hj; exact absurd (Finset.mem_univ j) hj

/-- A continuous linear form evaluated at `x` is the sum over the coordinates of `x` of the
coordinate times the value of the form on the corresponding standard basis vector. -/
private lemma clm_apply_eq_sum {n : ℕ} (L : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
    (x : EuclideanSpace ℝ (Fin n)) :
    L x = ∑ i : Fin n, (x i) * L (EuclideanSpace.single i 1) := by
  conv_lhs => rw [← sum_single_eq_self x]
  rw [map_sum]
  exact Finset.sum_congr rfl (fun i _ => by rw [map_smul, smul_eq_mul])

/-- A function dominated by `K * (1 + ‖x‖)^N * exp (-π ‖x‖²)` is integrable. -/
private lemma integrable_of_gaussian_bound {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] [MeasurableSpace F] [BorelSpace F] [FiniteDimensional ℝ F]
    (u : F → ℝ) (hu : Continuous u) (K : ℝ) (N : ℕ)
    (h : ∀ x, ‖u x‖ ≤ K * ((1 + ‖x‖)^N * Real.exp (-Real.pi * ‖x‖^2))) :
    Integrable u volume := by
  have hg : Integrable (fun x : F => K * ((1 + ‖x‖)^N * Real.exp (-Real.pi * ‖x‖^2))) volume :=
    (Commons.Measure.Integral.integrable_pow_mul_exp_neg_norm_sq Real.pi Real.pi_pos N).const_mul K
  exact Integrable.mono' hg hu.aestronglyMeasurable (Filter.Eventually.of_forall h)

theorem weighted_divergence_growth {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (W : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (hf : ContDiff ℝ 1 f) (hW : ContDiff ℝ 1 W) (hgW : ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ x : EuclideanSpace ℝ (Fin n), ‖W x‖ ≤ C * (1 + ‖x‖) ^ N ∧ ‖fderiv ℝ W x‖ ≤ C * (1 + ‖x‖) ^ N) (hdec : ∃ c : ℝ, ∀ x : EuclideanSpace ℝ (Fin n), c + Real.pi * ‖x‖ ^ 2 ≤ f x) (hgf : ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ x v : EuclideanSpace ℝ (Fin n), |fderiv ℝ f x v| ≤ C * (1 + ‖x‖) ^ N * ‖v‖) : (∫ x, (∑ i : Fin n, (fderiv ℝ W x (EuclideanSpace.single i 1)) i) * Real.exp (-(f x))) = ∫ x, inner ℝ ((InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm (fderiv ℝ f x)) (W x) * Real.exp (-(f x)) := by
  classical
  obtain ⟨Cw, hCw, Nw, hWb⟩ := hgW
  obtain ⟨Cf, hCf, Nf, hfb⟩ := hgf
  obtain ⟨c, hc⟩ := hdec
  let ρ : (EuclideanSpace ℝ (Fin n)) → ℝ := fun x => Real.exp (-(f x))
  change (∫ x, (∑ i : Fin n, (fderiv ℝ W x (EuclideanSpace.single i 1)) i) * ρ x)
      = ∫ x, inner ℝ ((InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm (fderiv ℝ f x)) (W x) * ρ x
  have hρ_cd : ContDiff ℝ 1 ρ := ContDiff.exp hf.neg
  have hρ_cont : Continuous ρ := hρ_cd.continuous
  have hρ_nonneg : ∀ x, 0 ≤ ρ x := fun x => (Real.exp_pos _).le
  have hρ_le : ∀ x, ρ x ≤ Real.exp (-c) * Real.exp (-Real.pi * ‖x‖^2) := by
    intro x
    have h1 : -(f x) ≤ -c + (-(Real.pi * ‖x‖^2)) := by linarith [hc x]
    calc ρ x = Real.exp (-(f x)) := rfl
      _ ≤ Real.exp (-c + -(Real.pi * ‖x‖^2)) := Real.exp_le_exp.mpr h1
      _ = Real.exp (-c) * Real.exp (-(Real.pi * ‖x‖^2)) := Real.exp_add _ _
      _ = Real.exp (-c) * Real.exp (-Real.pi * ‖x‖^2) := by
          congr 1; congr 1; ring
  have hρ_deriv : ∀ x v, fderiv ℝ ρ x v = -(ρ x * fderiv ℝ f x v) := by
    intro x v
    have h1 : HasFDerivAt (fun y : (EuclideanSpace ℝ (Fin n)) => -(f y)) (-(fderiv ℝ f x)) x :=
      (hf.differentiable one_ne_zero).differentiableAt.hasFDerivAt.neg
    have hd : HasFDerivAt ρ (Real.exp (-(f x)) • (-(fderiv ℝ f x))) x := by
      simpa only [ρ] using h1.exp
    rw [hd.fderiv]
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.neg_apply]
    rw [smul_eq_mul]
    show Real.exp (-(f x)) * -(fderiv ℝ f x v) = -(Real.exp (-(f x)) * fderiv ℝ f x v)
    ring
  have hW_norm : ∀ x, ‖W x‖ ≤ Cw * (1 + ‖x‖)^Nw := fun x => (hWb x).1
  have hdW_norm : ∀ x, ‖fderiv ℝ W x‖ ≤ Cw * (1 + ‖x‖)^Nw := fun x => (hWb x).2
  have hdf_norm : ∀ x, ‖fderiv ℝ f x‖ ≤ Cf * (1 + ‖x‖)^Nf := by
    intro x
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) ?_
    intro v
    simpa [Real.norm_eq_abs] using hfb x v
  have hsingle : ∀ i : Fin n, ‖EuclideanSpace.single i (1:ℝ)‖ = 1 := by
    intro i; rw [PiLp.norm_single]; norm_num
  have hcoord : ∀ (v : (EuclideanSpace ℝ (Fin n))) (i : Fin n), ‖v i‖ ≤ ‖v‖ := fun v i => PiLp.norm_apply_le v i
  have hInt1 : ∀ i : Fin n,
      Integrable (fun x : (EuclideanSpace ℝ (Fin n)) => ρ x * (fderiv ℝ W x (EuclideanSpace.single i 1)) i) := by
    intro i
    refine integrable_of_gaussian_bound _ ?_ (Real.exp (-c) * Cw) Nw ?_
    · fun_prop
    · intro x
      have hc1 : ‖(fderiv ℝ W x (EuclideanSpace.single i 1)) i‖ ≤ Cw * (1 + ‖x‖)^Nw := by
        calc ‖(fderiv ℝ W x (EuclideanSpace.single i 1)) i‖
            ≤ ‖fderiv ℝ W x (EuclideanSpace.single i 1)‖ := hcoord _ _
          _ ≤ ‖fderiv ℝ W x‖ * ‖EuclideanSpace.single i (1:ℝ)‖ :=
              ContinuousLinearMap.le_opNorm _ _
          _ = ‖fderiv ℝ W x‖ := by rw [hsingle i]; ring
          _ ≤ Cw * (1 + ‖x‖)^Nw := hdW_norm x
      calc ‖ρ x * (fderiv ℝ W x (EuclideanSpace.single i 1)) i‖
          = ρ x * ‖(fderiv ℝ W x (EuclideanSpace.single i 1)) i‖ := by
            rw [norm_mul, Real.norm_of_nonneg (hρ_nonneg x)]
        _ ≤ ρ x * (Cw * (1 + ‖x‖)^Nw) :=
            mul_le_mul_of_nonneg_left hc1 (hρ_nonneg x)
        _ ≤ (Real.exp (-c) * Real.exp (-Real.pi * ‖x‖^2)) * (Cw * (1 + ‖x‖)^Nw) :=
            mul_le_mul_of_nonneg_right (hρ_le x)
              (mul_nonneg hCw (pow_nonneg (by positivity) _))
        _ = (Real.exp (-c) * Cw) * ((1 + ‖x‖)^Nw * Real.exp (-Real.pi * ‖x‖^2)) := by ring
  have hInt3 : ∀ i : Fin n, Integrable (fun x : (EuclideanSpace ℝ (Fin n)) => ρ x * (W x) i) := by
    intro i
    refine integrable_of_gaussian_bound _ ?_ (Real.exp (-c) * Cw) Nw ?_
    · fun_prop
    · intro x
      have hc2 : ‖(W x) i‖ ≤ Cw * (1 + ‖x‖)^Nw := by
        calc ‖(W x) i‖ ≤ ‖W x‖ := hcoord _ _
          _ ≤ Cw * (1 + ‖x‖)^Nw := hW_norm x
      calc ‖ρ x * (W x) i‖ = ρ x * ‖(W x) i‖ := by
            rw [norm_mul, Real.norm_of_nonneg (hρ_nonneg x)]
        _ ≤ ρ x * (Cw * (1 + ‖x‖)^Nw) :=
            mul_le_mul_of_nonneg_left hc2 (hρ_nonneg x)
        _ ≤ (Real.exp (-c) * Real.exp (-Real.pi * ‖x‖^2)) * (Cw * (1 + ‖x‖)^Nw) :=
            mul_le_mul_of_nonneg_right (hρ_le x)
              (mul_nonneg hCw (pow_nonneg (by positivity) _))
        _ = (Real.exp (-c) * Cw) * ((1 + ‖x‖)^Nw * Real.exp (-Real.pi * ‖x‖^2)) := by ring
  have hInt2 : ∀ i : Fin n,
      Integrable (fun x : (EuclideanSpace ℝ (Fin n)) => (fderiv ℝ ρ x (EuclideanSpace.single i 1)) * (W x) i) := by
    intro i
    refine integrable_of_gaussian_bound _ ?_ (Real.exp (-c) * (Cf * Cw)) (Nf + Nw) ?_
    · fun_prop
    · intro x
      have hc1 : ‖(fderiv ℝ f x (EuclideanSpace.single i 1))‖ ≤ Cf * (1 + ‖x‖)^Nf := by
        calc ‖(fderiv ℝ f x (EuclideanSpace.single i 1))‖
            = |fderiv ℝ f x (EuclideanSpace.single i 1)| := Real.norm_eq_abs _
          _ ≤ Cf * (1 + ‖x‖)^Nf * ‖EuclideanSpace.single i (1:ℝ)‖ := hfb x _
          _ = Cf * (1 + ‖x‖)^Nf := by rw [hsingle i]; ring
      have hc2 : ‖(W x) i‖ ≤ Cw * (1 + ‖x‖)^Nw := by
        calc ‖(W x) i‖ ≤ ‖W x‖ := hcoord _ _
          _ ≤ Cw * (1 + ‖x‖)^Nw := hW_norm x
      have hc1nn : 0 ≤ Cf * (1 + ‖x‖)^Nf := mul_nonneg hCf (pow_nonneg (by positivity) _)
      have hc2nn : 0 ≤ Cw * (1 + ‖x‖)^Nw := mul_nonneg hCw (pow_nonneg (by positivity) _)
      calc ‖(fderiv ℝ ρ x (EuclideanSpace.single i 1)) * (W x) i‖
          = (ρ x * |fderiv ℝ f x (EuclideanSpace.single i 1)|) * ‖(W x) i‖ := by
            rw [norm_mul, Real.norm_eq_abs, hρ_deriv, abs_neg, abs_mul,
              abs_of_nonneg (hρ_nonneg x)]
        _ ≤ (ρ x * (Cf * (1 + ‖x‖)^Nf)) * (Cw * (1 + ‖x‖)^Nw) :=
            mul_le_mul (mul_le_mul_of_nonneg_left hc1 (hρ_nonneg x)) hc2
              (norm_nonneg _) (mul_nonneg (hρ_nonneg x) hc1nn)
        _ ≤ (Real.exp (-c) * Real.exp (-Real.pi * ‖x‖^2) * (Cf * (1 + ‖x‖)^Nf))
              * (Cw * (1 + ‖x‖)^Nw) :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right (hρ_le x) hc1nn) hc2nn
        _ = (Real.exp (-c) * (Cf * Cw)) * ((1 + ‖x‖)^(Nf + Nw) * Real.exp (-Real.pi * ‖x‖^2)) := by
            rw [pow_add]; ring
  have hInt4 : ∀ i : Fin n,
      Integrable (fun x : (EuclideanSpace ℝ (Fin n)) => ρ x * (fderiv ℝ f x (EuclideanSpace.single i 1)) * (W x) i) := by
    intro i
    have hneg : Integrable
        (fun x : (EuclideanSpace ℝ (Fin n)) => -((fderiv ℝ ρ x (EuclideanSpace.single i 1)) * (W x) i)) := (hInt2 i).neg
    refine hneg.congr ?_
    filter_upwards with x
    rw [hρ_deriv]; ring
  have hkey : ∀ i : Fin n,
      (∫ x, ρ x * (fderiv ℝ W x (EuclideanSpace.single i 1)) i)
        = ∫ x, ρ x * (fderiv ℝ f x (EuclideanSpace.single i 1)) * (W x) i := by
    intro i
    have hf'g : Integrable
        (fun x : (EuclideanSpace ℝ (Fin n)) => coordB i (fderiv ℝ ρ x (EuclideanSpace.single i 1)) (W x)) := by
      simpa only [coordB_apply] using hInt2 i
    have hfg' : Integrable
        (fun x : (EuclideanSpace ℝ (Fin n)) => coordB i (ρ x) (fderiv ℝ W x (EuclideanSpace.single i 1))) := by
      simpa only [coordB_apply] using hInt1 i
    have hfg : Integrable (fun x : (EuclideanSpace ℝ (Fin n)) => coordB i (ρ x) (W x)) := by
      simpa only [coordB_apply] using hInt3 i
    have hf : ∀ x ∈ tsupport W, DifferentiableAt ℝ ρ x :=
      fun x _ => (hρ_cd.differentiable one_ne_zero).differentiableAt
    have hg : ∀ x ∈ tsupport ρ, DifferentiableAt ℝ W x :=
      fun x _ => (hW.differentiable one_ne_zero).differentiableAt
    have hIBP := integral_bilinear_fderiv_right_eq_neg_left_of_integrable
      (μ := volume) (f := ρ) (g := W) (v := EuclideanSpace.single i 1) (B := coordB i)
      hf'g hfg' hfg hf hg
    have hL : (∫ x, coordB i (ρ x) (fderiv ℝ W x (EuclideanSpace.single i 1)))
        = ∫ x, ρ x * (fderiv ℝ W x (EuclideanSpace.single i 1)) i := by
      apply integral_congr_ae; filter_upwards with x; rw [coordB_apply]
    have hR : (∫ x, coordB i (fderiv ℝ ρ x (EuclideanSpace.single i 1)) (W x))
        = - ∫ x, ρ x * (fderiv ℝ f x (EuclideanSpace.single i 1)) * (W x) i := by
      rw [← integral_neg]
      apply integral_congr_ae; filter_upwards with x
      rw [coordB_apply, hρ_deriv]; ring
    rw [hL, hR] at hIBP
    simpa using hIBP
  have hLHS : (∫ x, (∑ i : Fin n, (fderiv ℝ W x (EuclideanSpace.single i 1)) i) * ρ x)
      = ∑ i : Fin n, ∫ x, ρ x * (fderiv ℝ W x (EuclideanSpace.single i 1)) i := by
    calc (∫ x, (∑ i : Fin n, (fderiv ℝ W x (EuclideanSpace.single i 1)) i) * ρ x)
        = ∫ x, ∑ i : Fin n, ρ x * (fderiv ℝ W x (EuclideanSpace.single i 1)) i := by
          apply integral_congr_ae
          filter_upwards with x
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl (fun i _ => by ring)
      _ = ∑ i : Fin n, ∫ x, ρ x * (fderiv ℝ W x (EuclideanSpace.single i 1)) i :=
          integral_finsetSum Finset.univ (fun i _ => hInt1 i)
  have hRHS : (∫ x, inner ℝ ((InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm (fderiv ℝ f x)) (W x) * ρ x)
      = ∑ i : Fin n, ∫ x, ρ x * (fderiv ℝ f x (EuclideanSpace.single i 1)) * (W x) i := by
    calc (∫ x, inner ℝ ((InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm (fderiv ℝ f x)) (W x) * ρ x)
        = ∫ x, ∑ i : Fin n, ρ x * (fderiv ℝ f x (EuclideanSpace.single i 1)) * (W x) i := by
          apply integral_congr_ae
          filter_upwards with x
          rw [InnerProductSpace.toDual_symm_apply]
          rw [show (fderiv ℝ f x) (W x)
                = ∑ i : Fin n, (W x i) * (fderiv ℝ f x) (EuclideanSpace.single i 1) from
              clm_apply_eq_sum _ _]
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl (fun i _ => by ring)
      _ = ∑ i : Fin n, ∫ x, ρ x * (fderiv ℝ f x (EuclideanSpace.single i 1)) * (W x) i :=
          integral_finsetSum Finset.univ (fun i _ => hInt4 i)
  rw [hLHS, hRHS]
  exact Finset.sum_congr rfl (fun i _ => hkey i)

end Commons.Analysis.MeasureTheory