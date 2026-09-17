import Mathlib.Algebra.Order.Chebyshev
import Submission.Commons.Probability.Gaussian.integral_norm_sq_starProjection_stdGaussian
import Submission.Commons.Analysis.Real.rpow_half_mul_three_sq_le

open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace ENNReal

namespace Commons.Probability.Gaussian

/-- The fourth moment of the standard Gaussian distribution on `ℝ` is `3`. -/
private lemma fourth_moment_gaussianReal_aux :
    ∫ x : ℝ, x ^ 4 ∂(ProbabilityTheory.gaussianReal 0 1) = 3 := by
  have key := iteratedDeriv_mgf_zero (X := fun x : ℝ => x)
    (μ := ProbabilityTheory.gaussianReal (0:ℝ) 1) (by simp) 4
  simp only [Pi.pow_apply] at key
  rw [← key]
  set F : ℝ → ℝ := fun t => Real.exp (t^2/2) with hF
  have hmgf : mgf (fun x : ℝ => x) (ProbabilityTheory.gaussianReal (0:ℝ) 1) = F := by
    rw [mgf_fun_id_gaussianReal]; funext t; simp [F]
  rw [hmgf]
  have hd1 : ∀ t : ℝ, HasDerivAt F (t * Real.exp (t^2/2)) t := by
    intro t
    have h1 : HasDerivAt (fun s : ℝ => s^2/2) t t := by
      have h := (hasDerivAt_pow 2 t).div_const 2
      simpa using h
    have h2 := (Real.hasDerivAt_exp (t^2/2)).comp t h1
    simpa [F, Function.comp_def, mul_comm] using h2
  have hd2 : ∀ t : ℝ, HasDerivAt (fun t : ℝ => t * Real.exp (t^2/2))
      ((1 + t^2) * Real.exp (t^2/2)) t := by
    intro t
    have hexp : HasDerivAt (fun t : ℝ => Real.exp (t^2/2)) (t * Real.exp (t^2/2)) t := hd1 t
    have h := (hasDerivAt_id t).mul hexp
    refine h.congr_deriv ?_
    simp only [id_eq]
    ring
  have hd3 : ∀ t : ℝ, HasDerivAt (fun t : ℝ => (1 + t^2) * Real.exp (t^2/2))
      ((3*t + t^3) * Real.exp (t^2/2)) t := by
    intro t
    have hexp : HasDerivAt (fun t : ℝ => Real.exp (t^2/2)) (t * Real.exp (t^2/2)) t := hd1 t
    have hpoly : HasDerivAt (fun t : ℝ => (1 + t^2)) (2*t) t := by
      have h := (hasDerivAt_pow 2 t).const_add 1
      simpa using h
    have h := hpoly.mul hexp
    refine h.congr_deriv ?_
    ring
  have hd4 : ∀ t : ℝ, HasDerivAt (fun t : ℝ => (3*t + t^3) * Real.exp (t^2/2))
      ((3 + 6*t^2 + t^4) * Real.exp (t^2/2)) t := by
    intro t
    have hexp : HasDerivAt (fun t : ℝ => Real.exp (t^2/2)) (t * Real.exp (t^2/2)) t := hd1 t
    have h1 : HasDerivAt (fun t : ℝ => 3*t) 3 t := by
      have := (hasDerivAt_id t).const_mul (3:ℝ)
      simpa using this
    have h2 : HasDerivAt (fun t : ℝ => t^3) (3*t^2) t := by
      have h := hasDerivAt_pow 3 t
      simpa using h
    have hpoly := h1.add h2
    have h := hpoly.mul hexp
    refine h.congr_deriv ?_
    simp only [Pi.add_apply]
    ring
  have e1 : iteratedDeriv 1 F = fun t => t * Real.exp (t^2/2) := by
    rw [iteratedDeriv_one]; funext t; exact (hd1 t).deriv
  have e2 : iteratedDeriv 2 F = fun t => (1 + t^2) * Real.exp (t^2/2) := by
    rw [iteratedDeriv_succ, e1]
    funext t; exact (hd2 t).deriv
  have e3 : iteratedDeriv 3 F = fun t => (3*t + t^3) * Real.exp (t^2/2) := by
    rw [iteratedDeriv_succ, e2]
    funext t; exact (hd3 t).deriv
  have e4 : iteratedDeriv 4 F = fun t => (3 + 6*t^2 + t^4) * Real.exp (t^2/2) := by
    rw [iteratedDeriv_succ, e3]
    funext t; exact (hd4 t).deriv
  rw [e4]
  norm_num

theorem integral_norm_cube_stdGaussian_le {N : ℕ} :
    ∫ x, ‖x‖ ^ 3 ∂(ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin N)))
      ≤ 3 * (N : ℝ) ^ (3 / 2 : ℝ) := by
  have h2 : ∫ x : EuclideanSpace ℝ (Fin N), ‖x‖ ^ 2
        ∂(ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin N))) = (N:ℝ) := by
    have h := Commons.Probability.Gaussian.integral_norm_sq_starProjection_stdGaussian (d := N)
      (⊤ : Submodule ℝ (EuclideanSpace ℝ (Fin N)))
    rw [Submodule.starProjection_top] at h
    simp only [ContinuousLinearMap.id_apply] at h
    rw [h]
    simp [finrank_euclideanSpace]
  have h4int : Integrable (fun x : EuclideanSpace ℝ (Fin N) => ‖x‖^4)
      (ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin N))) := by
    have h := (IsGaussian.memLp_id (ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin N)))
      (4:ℝ≥0∞) (by norm_num)).integrable_norm_rpow (by norm_num) (by norm_num)
    simpa using h
  have hcoord : ∀ i : Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin N))),
      ∫ x : EuclideanSpace ℝ (Fin N),
        (⟪(stdOrthonormalBasis ℝ (EuclideanSpace ℝ (Fin N))) i, x⟫_ℝ)^4
        ∂(ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin N))) = 3 := by
    intro i
    have hlaw : (ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin N))).map
        (innerSL ℝ ((stdOrthonormalBasis ℝ (EuclideanSpace ℝ (Fin N))) i))
        = ProbabilityTheory.gaussianReal 0 1 := by
      rw [IsGaussian.map_eq_gaussianReal
        (L := innerSL ℝ ((stdOrthonormalBasis ℝ (EuclideanSpace ℝ (Fin N))) i))]
      rw [integral_strongDual_stdGaussian, variance_dual_stdGaussian]
      have hn : ‖innerSL ℝ ((stdOrthonormalBasis ℝ (EuclideanSpace ℝ (Fin N))) i)‖ = 1 := by
        rw [innerSL_apply_norm, OrthonormalBasis.norm_eq_one]
      rw [hn]
      simp
    have hkey : ∫ t, t^4 ∂((ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin N))).map
          (innerSL ℝ ((stdOrthonormalBasis ℝ (EuclideanSpace ℝ (Fin N))) i)))
        = ∫ x, (⟪(stdOrthonormalBasis ℝ (EuclideanSpace ℝ (Fin N))) i, x⟫_ℝ)^4
            ∂(ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin N))) := by
      rw [integral_map (by fun_prop) (by fun_prop)]
      simp only [innerSL_apply_apply]
    rw [← hkey, hlaw]
    exact fourth_moment_gaussianReal_aux
  have h4 : ∫ x : EuclideanSpace ℝ (Fin N), ‖x‖ ^ 4
        ∂(ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin N))) ≤ 3 * (N:ℝ)^2 := by
    have hpt : ∀ x : EuclideanSpace ℝ (Fin N),
        ‖x‖^4 ≤ (Module.finrank ℝ (EuclideanSpace ℝ (Fin N)) : ℝ) *
          ∑ i, (⟪(stdOrthonormalBasis ℝ (EuclideanSpace ℝ (Fin N))) i, x⟫_ℝ)^4 := by
      intro x
      have hcs : (∑ i, (⟪(stdOrthonormalBasis ℝ (EuclideanSpace ℝ (Fin N))) i, x⟫_ℝ)^2)^2
          ≤ (Module.finrank ℝ (EuclideanSpace ℝ (Fin N)) : ℝ) *
            ∑ i, ((⟪(stdOrthonormalBasis ℝ (EuclideanSpace ℝ (Fin N))) i, x⟫_ℝ)^2)^2 := by
        simpa using sq_sum_le_card_mul_sum_sq (s := Finset.univ)
          (f := fun i : Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin N))) =>
            (⟪(stdOrthonormalBasis ℝ (EuclideanSpace ℝ (Fin N))) i, x⟫_ℝ)^2)
      have hsum : (∑ i, ((⟪(stdOrthonormalBasis ℝ (EuclideanSpace ℝ (Fin N))) i, x⟫_ℝ)^2)^2)
          = ∑ i, (⟪(stdOrthonormalBasis ℝ (EuclideanSpace ℝ (Fin N))) i, x⟫_ℝ)^4 := by
        refine Finset.sum_congr rfl ?_
        intro i _
        rw [← pow_mul]
      calc ‖x‖^4
            = (∑ i, (⟪(stdOrthonormalBasis ℝ (EuclideanSpace ℝ (Fin N))) i, x⟫_ℝ)^2)^2 := by
              rw [(stdOrthonormalBasis ℝ (EuclideanSpace ℝ (Fin N))).sum_sq_inner_right]; ring
        _ ≤ _ := hcs
        _ = (Module.finrank ℝ (EuclideanSpace ℝ (Fin N)) : ℝ) *
            ∑ i, (⟪(stdOrthonormalBasis ℝ (EuclideanSpace ℝ (Fin N))) i, x⟫_ℝ)^4 := by
              rw [hsum]
    have hint_i : ∀ i : Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin N))),
        Integrable (fun x : EuclideanSpace ℝ (Fin N) =>
          (⟪(stdOrthonormalBasis ℝ (EuclideanSpace ℝ (Fin N))) i, x⟫_ℝ)^4)
          (ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin N))) := by
      intro i
      have h : MemLp (innerSL ℝ ((stdOrthonormalBasis ℝ (EuclideanSpace ℝ (Fin N))) i))
          (4:ℝ≥0∞) (ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin N))) :=
        IsGaussian.memLp_dual _ _ 4 (by norm_num)
      have h2' := h.integrable_norm_rpow (by norm_num) (by norm_num)
      simp only [ENNReal.toReal_ofNat] at h2'
      have habs : ∀ a : ℝ, |a|^4 = a^4 := by
        intro a; rw [show (4:ℕ) = 2 * 2 from rfl, pow_mul, sq_abs, ← pow_mul]
      simpa [innerSL_apply_apply, Real.norm_eq_abs, habs] using h2'
    have hint_sum : Integrable (fun x : EuclideanSpace ℝ (Fin N) =>
        (Module.finrank ℝ (EuclideanSpace ℝ (Fin N)) : ℝ) *
        ∑ i, (⟪(stdOrthonormalBasis ℝ (EuclideanSpace ℝ (Fin N))) i, x⟫_ℝ)^4)
        (ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin N))) := by
      have hs : Integrable (fun x : EuclideanSpace ℝ (Fin N) =>
          ∑ i, (⟪(stdOrthonormalBasis ℝ (EuclideanSpace ℝ (Fin N))) i, x⟫_ℝ)^4)
          (ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin N))) := by
        refine integrable_finsetSum Finset.univ ?_
        intro i _
        exact hint_i i
      exact hs.const_mul _
    calc ∫ x, ‖x‖ ^ 4 ∂(ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin N)))
        ≤ ∫ x, (Module.finrank ℝ (EuclideanSpace ℝ (Fin N)) : ℝ) *
            ∑ i, (⟪(stdOrthonormalBasis ℝ (EuclideanSpace ℝ (Fin N))) i, x⟫_ℝ)^4
            ∂(ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin N))) :=
            integral_mono h4int hint_sum hpt
      _ = (Module.finrank ℝ (EuclideanSpace ℝ (Fin N)) : ℝ) *
            ∫ x, ∑ i, (⟪(stdOrthonormalBasis ℝ (EuclideanSpace ℝ (Fin N))) i, x⟫_ℝ)^4
              ∂(ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin N))) := by
            rw [integral_const_mul]
      _ = (Module.finrank ℝ (EuclideanSpace ℝ (Fin N)) : ℝ) *
            ∑ i, ∫ x, (⟪(stdOrthonormalBasis ℝ (EuclideanSpace ℝ (Fin N))) i, x⟫_ℝ)^4
              ∂(ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin N))) := by
            rw [integral_finsetSum]; intro i _; exact hint_i i
      _ = (Module.finrank ℝ (EuclideanSpace ℝ (Fin N)) : ℝ) * ∑ i, (3:ℝ) := by
            rw [Finset.sum_congr rfl (fun i _ => hcoord i)]
      _ = 3 * (N:ℝ)^2 := by
            have hc : (Module.finrank ℝ (EuclideanSpace ℝ (Fin N)) : ℝ) = (N:ℝ) := by
              rw [finrank_euclideanSpace, Fintype.card_fin]
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hc]
            ring
  have hf : MemLp (fun x : EuclideanSpace ℝ (Fin N) => ‖x‖) (ENNReal.ofReal 2)
      (ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin N))) := by
    simpa using (IsGaussian.memLp_two_id
      (μ := ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin N)))).norm
  have h2eq : (ENNReal.ofReal 2 : ℝ≥0∞) = 2 := by norm_num
  have hg : MemLp (fun x : EuclideanSpace ℝ (Fin N) => ‖x‖^2) (ENNReal.ofReal 2)
      (ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin N))) := by
    rw [h2eq, memLp_two_iff_integrable_sq (by fun_prop)]
    have : (fun x : EuclideanSpace ℝ (Fin N) => (‖x‖^2)^2)
        = fun x : EuclideanSpace ℝ (Fin N) => ‖x‖^4 := by
      funext x; rw [← pow_mul]
    rw [this]; exact h4int
  have hconj : (2:ℝ).HolderConjugate 2 :=
    Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩
  have hCS : ∫ x : EuclideanSpace ℝ (Fin N), ‖x‖ * ‖x‖^2
        ∂(ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin N)))
      ≤ (∫ x : EuclideanSpace ℝ (Fin N), ‖x‖^2
            ∂(ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin N))))^(1/2:ℝ)
        * (∫ x : EuclideanSpace ℝ (Fin N), ‖x‖^4
            ∂(ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin N))))^(1/2:ℝ) := by
    have h := integral_mul_le_Lp_mul_Lq_of_nonneg
      (μ := ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin N))) (p := 2) (q := 2) hconj
      (by filter_upwards with x; positivity) (by filter_upwards with x; positivity) hf hg
    have heq : (∫ a : EuclideanSpace ℝ (Fin N), ‖a‖ ^ (2:ℝ)
            ∂(ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin N))))^(1/2:ℝ)
        * (∫ a : EuclideanSpace ℝ (Fin N), (‖a‖^2)^(2:ℝ)
            ∂(ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin N))))^(1/2:ℝ)
        = (∫ a : EuclideanSpace ℝ (Fin N), ‖a‖^2
            ∂(ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin N))))^(1/2:ℝ)
        * (∫ a : EuclideanSpace ℝ (Fin N), ‖a‖^4
            ∂(ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin N))))^(1/2:ℝ) := by
      congr 1
      · congr 1
        refine integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
        simp only [Real.rpow_two]
      · congr 1
        refine integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
        simp only [Real.rpow_two, ← pow_mul]
    exact h.trans_eq heq
  calc ∫ x, ‖x‖ ^ 3 ∂(ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin N)))
      = ∫ x : EuclideanSpace ℝ (Fin N), ‖x‖ * ‖x‖^2
          ∂(ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin N))) := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
          ring
    _ ≤ (∫ x : EuclideanSpace ℝ (Fin N), ‖x‖^2
            ∂(ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin N))))^(1/2:ℝ)
        * (∫ x : EuclideanSpace ℝ (Fin N), ‖x‖^4
            ∂(ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin N))))^(1/2:ℝ) := hCS
    _ ≤ (N:ℝ)^(1/2:ℝ) * (3*(N:ℝ)^2)^(1/2:ℝ) := by
          rw [h2]
          refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg (Nat.cast_nonneg N) _)
          exact Real.rpow_le_rpow (integral_nonneg (fun x => by positivity)) h4 (by norm_num)
    _ ≤ 3 * (N:ℝ)^(3/2:ℝ) :=
        Commons.Analysis.Real.rpow_half_mul_three_sq_le N (Nat.cast_nonneg N)

end Commons.Probability.Gaussian