import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Mathlib.Topology.UniformSpace.Uniformizable
import Submission.Commons.Analysis.Calculus.iteratedDeriv_two_comp_curve
import Submission.Commons.Analysis.Calculus.iteratedDeriv_two_intervalIntegral_parametric
import Submission.Commons.Analysis.Calculus.integral_Ioi_mul_inv_sq_eq_integral_Ioi_deriv_mul_inv
import Submission.Commons.Analysis.Calculus.exists_contDiff_eq_inv_sq_on_Icc
import Submission.Commons.Analysis.Calculus.setIntegral_Ioi_eq_intervalIntegral

namespace Commons.Analysis.Calculus

open MeasureTheory
open scoped Topology ContDiff

theorem sphProj_second_deriv_identity {d : ℕ} (f : EuclideanSpace ℝ (Fin d) → ℝ)
    (hf : ContDiff ℝ 2 f) (hsupp : HasCompactSupport f)
    (havoid : ∀ x : EuclideanSpace ℝ (Fin d), ‖x‖ ≤ 1 → f x = 0)
    (y v : EuclideanSpace ℝ (Fin d)) (hy : ‖y‖ = 1) (hv : ‖v‖ = 1)
    (hperp : inner ℝ y v = 0) :
    (∫ t in Set.Ioi (0 : ℝ), (iteratedFDeriv ℝ 2 f (t • y)) (fun _ : Fin 2 => v))
      = (∫ t in Set.Ioi (0 : ℝ), f (t • y) * (t ^ 2)⁻¹)
        + iteratedDeriv 2 (fun θ : ℝ => ∫ t in Set.Ioi (0 : ℝ),
            f (t • (Real.cos θ • y + Real.sin θ • v)) * (t ^ 2)⁻¹) 0 := by
  classical
  -- ## 0. the unit vector `u θ = cos θ • y + sin θ • v`
  have hu_norm : ∀ θ : ℝ, ‖Real.cos θ • y + Real.sin θ • v‖ = 1 := by
    intro θ
    have h1 : ‖Real.cos θ • y + Real.sin θ • v‖ ^ 2 = 1 := by
      rw [norm_add_sq_real]
      have hy2 : ‖Real.cos θ • y‖ ^ 2 = Real.cos θ ^ 2 := by
        rw [norm_smul, hy, mul_one, Real.norm_eq_abs, sq_abs]
      have hv2 : ‖Real.sin θ • v‖ ^ 2 = Real.sin θ ^ 2 := by
        rw [norm_smul, hv, mul_one, Real.norm_eq_abs, sq_abs]
      have hi : inner ℝ (Real.cos θ • y) (Real.sin θ • v) = 0 := by
        simp [inner_smul_left, inner_smul_right, hperp]
      rw [hy2, hv2, hi]
      nlinarith [Real.cos_sq_add_sin_sq θ]
    have h2 : ‖Real.cos θ • y + Real.sin θ • v‖ ^ 2 = (1 : ℝ) ^ 2 := by rw [h1]; norm_num
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp h2 with h | h
    · exact h
    · have := norm_nonneg (Real.cos θ • y + Real.sin θ • v); rw [h] at this; linarith
  -- ## 1. the support radius `R` and the vanishing of `f` near the origin
  obtain ⟨R₀, hR₀⟩ :=
    (Metric.isBounded_iff_subset_closedBall (0 : EuclideanSpace ℝ (Fin d))).1 hsupp.isBounded
  set R : ℝ := max R₀ 1 with hRdef
  have hR1 : 1 ≤ R := le_max_right _ _
  have hRtsup : tsupport f ⊆ Metric.closedBall 0 R := fun x hx => by
    have h := hR₀ hx
    rw [Metric.mem_closedBall] at h ⊢
    linarith [hRdef ▸ le_max_left R₀ (1 : ℝ)]
  have htsup_mem : tsupport f ⊆ {x : EuclideanSpace ℝ (Fin d) | 1 ≤ ‖x‖} := by
    rw [tsupport]
    apply closure_minimal
    · intro x hx
      rw [Function.mem_support] at hx
      exact le_of_not_gt (fun h => hx (havoid x (le_of_lt h)))
    · exact isClosed_le continuous_const continuous_norm
  -- ## 2. the smooth kernel `K` equal to `t⁻²` on `[1, R]`
  obtain ⟨K, hKcd, hK⟩ := exists_contDiff_eq_inv_sq_on_Icc (a := 1) (b := R) one_pos hR1
  -- ## 3. smoothness of the parametrised integrand
  have hF_cd : ContDiff ℝ 2 (Function.uncurry (fun θ t : ℝ =>
      f (t • (Real.cos θ • y + Real.sin θ • v)) * K t)) := by
    have hu_cd : ContDiff ℝ 2 (fun θ : ℝ => Real.cos θ • y + Real.sin θ • v) := by
      apply ContDiff.add
      · exact (Real.contDiff_cos).smul contDiff_const
      · exact (Real.contDiff_sin).smul contDiff_const
    have h1 : ContDiff ℝ 2
        (fun p : ℝ × ℝ => f (p.2 • (Real.cos p.1 • y + Real.sin p.1 • v))) := by
      apply hf.comp
      exact ContDiff.smul contDiff_snd (hu_cd.comp contDiff_fst)
    have h2 : ContDiff ℝ 2 (fun p : ℝ × ℝ => K p.2) := hKcd.comp contDiff_snd
    have h := h1.mul h2
    change ContDiff ℝ 2 (fun p : ℝ × ℝ =>
      f (p.2 • (Real.cos p.1 • y + Real.sin p.1 • v)) * K p.2) at h
    exact h
  -- ## 4. the derivative of `t ↦ f (t • y)`
  have hderiv_phi : ∀ t : ℝ, deriv (fun s : ℝ => f (s • y)) t = (fderiv ℝ f (t • y)) y := by
    intro t
    have hcurve : HasDerivAt (fun s : ℝ => s • y) y t := by
      simpa using (hasDerivAt_id t).smul_const y
    exact ((hf.differentiable (by norm_num)).differentiableAt.hasFDerivAt.comp_hasDerivAt t hcurve).deriv
  -- ## 5. truncation of the left-hand side
  have hA0 : ∀ t : ℝ, 0 < t → t < 1 →
      (iteratedFDeriv ℝ 2 f (t • y)) (fun _ : Fin 2 => v) = 0 := by
    intro t ht0 ht1
    have hnot : t • y ∉ tsupport f := by
      intro hmem
      have hle := htsup_mem hmem
      change 1 ≤ ‖t • y‖ at hle
      rw [norm_smul, hy, mul_one, Real.norm_eq_abs, abs_of_pos ht0] at hle
      linarith
    have hzero : iteratedFDeriv ℝ 2 f (t • y) = 0 :=
      Function.notMem_support.mp (fun h => hnot (support_iteratedFDeriv_subset 2 h))
    rw [hzero]; simp
  have hAR : ∀ t : ℝ, R < t →
      (iteratedFDeriv ℝ 2 f (t • y)) (fun _ : Fin 2 => v) = 0 := by
    intro t ht
    have hnot : t • y ∉ tsupport f := by
      intro hmem
      have hle := hRtsup hmem
      rw [Metric.mem_closedBall, dist_zero_right, norm_smul, hy, mul_one,
        Real.norm_eq_abs, abs_of_pos (by linarith [hR1] : (0 : ℝ) < t)] at hle
      linarith
    have hzero : iteratedFDeriv ℝ 2 f (t • y) = 0 :=
      Function.notMem_support.mp (fun h => hnot (support_iteratedFDeriv_subset 2 h))
    rw [hzero]; simp
  have hA_trunc : (∫ t in Set.Ioi (0 : ℝ), (iteratedFDeriv ℝ 2 f (t • y)) (fun _ : Fin 2 => v))
      = ∫ t in (1 : ℝ)..R, (iteratedFDeriv ℝ 2 f (t • y)) (fun _ : Fin 2 => v) :=
    setIntegral_Ioi_eq_intervalIntegral hR1 hA0 hAR
  -- ## 6. truncation of `deriv φ / t`
  have hD0 : ∀ t : ℝ, 0 < t → t < 1 →
      deriv (fun s : ℝ => f (s • y)) t * t⁻¹ = 0 := by
    intro t ht0 ht1
    have hnot : t • y ∉ tsupport f := by
      intro hmem
      have hle := htsup_mem hmem
      change 1 ≤ ‖t • y‖ at hle
      rw [norm_smul, hy, mul_one, Real.norm_eq_abs, abs_of_pos ht0] at hle
      linarith
    have hfd : fderiv ℝ f (t • y) = 0 :=
      ((hf.differentiable (by norm_num)).differentiableAt.hasFDerivAt).unique
        (HasFDerivAt.of_notMem_tsupport ℝ hnot)
    rw [hderiv_phi t, hfd]; simp
  have hDR : ∀ t : ℝ, R < t → deriv (fun s : ℝ => f (s • y)) t * t⁻¹ = 0 := by
    intro t ht
    have hnot : t • y ∉ tsupport f := by
      intro hmem
      have hle := hRtsup hmem
      rw [Metric.mem_closedBall, dist_zero_right, norm_smul, hy, mul_one,
        Real.norm_eq_abs, abs_of_pos (by linarith [hR1] : (0 : ℝ) < t)] at hle
      linarith
    have hfd : fderiv ℝ f (t • y) = 0 :=
      ((hf.differentiable (by norm_num)).differentiableAt.hasFDerivAt).unique
        (HasFDerivAt.of_notMem_tsupport ℝ hnot)
    rw [hderiv_phi t, hfd]; simp
  have hderiv_trunc : (∫ t in Set.Ioi (0 : ℝ), deriv (fun s : ℝ => f (s • y)) t * t⁻¹)
      = ∫ t in (1 : ℝ)..R, deriv (fun s : ℝ => f (s • y)) t * t⁻¹ :=
    setIntegral_Ioi_eq_intervalIntegral hR1 hD0 hDR
  -- ## 7. integration by parts
  have hφ_cd : ContDiff ℝ 1 (fun s : ℝ => f (s • y)) := by
    have hcurve : ContDiff ℝ 1 (fun s : ℝ => s • y) := contDiff_id.smul contDiff_const
    exact (hf.of_le (by norm_num : ((1 : WithTop ℕ∞) ≤ (2 : WithTop ℕ∞)))).comp hcurve
  have hφ_supp : HasCompactSupport (fun s : ℝ => f (s • y)) := by
    apply HasCompactSupport.intro (isCompact_Icc (a := -R) (b := R))
    intro t ht
    have hnot : t • y ∉ tsupport f := by
      intro hmem
      have hle := hRtsup hmem
      rw [Metric.mem_closedBall, dist_zero_right, norm_smul, hy, mul_one, Real.norm_eq_abs] at hle
      rw [Set.mem_Icc, not_and_or, not_le, not_le] at ht
      rcases ht with hlt | hgt
      · rw [abs_of_neg (by linarith)] at hle; linarith
      · rw [abs_of_pos (by linarith)] at hle; linarith
    exact image_eq_zero_of_notMem_tsupport hnot
  have h0φ : ∀ t : ℝ, 0 < t → t ≤ 1 → f (t • y) = 0 := by
    intro t ht0 ht1
    apply havoid
    rw [norm_smul, hy, mul_one, Real.norm_eq_abs, abs_of_pos ht0]
    exact ht1
  have hIBP : (∫ t in Set.Ioi (0 : ℝ), f (t • y) * (t ^ 2)⁻¹)
      = ∫ t in Set.Ioi (0 : ℝ), deriv (fun s : ℝ => f (s • y)) t * t⁻¹ :=
    integral_Ioi_mul_inv_sq_eq_integral_Ioi_deriv_mul_inv (φ := fun s : ℝ => f (s • y))
      hφ_cd hφ_supp h0φ
  -- ## 8. the theta-integral equals the truncated `K`-integral
  have hfun : (fun θ : ℝ => ∫ t in Set.Ioi (0 : ℝ),
        f (t • (Real.cos θ • y + Real.sin θ • v)) * (t ^ 2)⁻¹)
      = fun θ : ℝ => ∫ t in (1 : ℝ)..R,
          f (t • (Real.cos θ • y + Real.sin θ • v)) * K t := by
    funext θ
    rw [setIntegral_Ioi_eq_intervalIntegral hR1 (fun t ht0 ht1 => by
        have hnorm : ‖t • (Real.cos θ • y + Real.sin θ • v)‖ = t := by
          rw [norm_smul, hu_norm θ, mul_one, Real.norm_eq_abs, abs_of_pos ht0]
        rw [havoid _ (by rw [hnorm]; exact le_of_lt ht1), zero_mul])
      (fun t ht => by
        have hnot : t • (Real.cos θ • y + Real.sin θ • v) ∉ tsupport f := by
          intro hmem
          have hle := hRtsup hmem
          rw [Metric.mem_closedBall, dist_zero_right, norm_smul, hu_norm θ, mul_one,
            Real.norm_eq_abs, abs_of_pos (by linarith [hR1] : (0 : ℝ) < t)] at hle
          linarith
        rw [image_eq_zero_of_notMem_tsupport hnot, zero_mul])]
    exact intervalIntegral.integral_congr (fun t ht =>
      by rw [hK t (by rwa [Set.uIcc_of_le hR1] at ht)])
  -- ## 9. second derivative of the theta-integral
  have hPhi2 : iteratedDeriv 2 (fun θ : ℝ => ∫ t in (1 : ℝ)..R,
        f (t • (Real.cos θ • y + Real.sin θ • v)) * K t) 0
      = (∫ t in (1 : ℝ)..R, (iteratedFDeriv ℝ 2 f (t • y)) (fun _ : Fin 2 => v))
        - ∫ t in (1 : ℝ)..R, deriv (fun s : ℝ => f (s • y)) t * t⁻¹ := by
    have hpar := iteratedDeriv_two_intervalIntegral_parametric (F := fun θ t : ℝ =>
        f (t • (Real.cos θ • y + Real.sin θ • v)) * K t) (a := 1) (b := R) (s₀ := 0) hF_cd
    rw [hpar]
    have hpt : Set.EqOn
        (fun t : ℝ => iteratedDeriv 2
          (fun s : ℝ => f (t • (Real.cos s • y + Real.sin s • v)) * K t) 0)
        (fun t : ℝ => (iteratedFDeriv ℝ 2 f (t • y)) (fun _ : Fin 2 => v)
          - deriv (fun s : ℝ => f (s • y)) t * t⁻¹) (Set.uIcc (1 : ℝ) R) := by
      intro t ht
      show iteratedDeriv 2 (fun s : ℝ => f (t • (Real.cos s • y + Real.sin s • v)) * K t) 0
        = (iteratedFDeriv ℝ 2 f (t • y)) (fun _ : Fin 2 => v)
          - deriv (fun s : ℝ => f (s • y)) t * t⁻¹
      have htIcc : t ∈ Set.Icc (1 : ℝ) R := by rwa [Set.uIcc_of_le hR1] at ht
      have htpos : (0 : ℝ) < t := by linarith [htIcc.1]
      have hcd : ContDiff ℝ 2 (fun s : ℝ => f (t • (Real.cos s • y + Real.sin s • v))) := by
        apply hf.comp
        apply ContDiff.const_smul
        apply ContDiff.add
        · exact (Real.contDiff_cos).smul contDiff_const
        · exact (Real.contDiff_sin).smul contDiff_const
      have hcomm : (fun s : ℝ => f (t • (Real.cos s • y + Real.sin s • v)) * K t)
          = fun s : ℝ => K t * f (t • (Real.cos s • y + Real.sin s • v)) := by
        funext s; rw [mul_comm]
      rw [hcomm, iteratedDeriv_const_mul (c := K t) (n := 2) (x := 0) hcd.contDiffAt,
        hK t htIcc, iteratedDeriv_two_comp_curve f hf t y v, hderiv_phi t]
      field_simp [ne_of_gt htpos]
    rw [intervalIntegral.integral_congr hpt]
    have hintA : IntervalIntegrable (fun t : ℝ =>
        (iteratedFDeriv ℝ 2 f (t • y)) (fun _ : Fin 2 => v)) volume 1 R :=
      (by fun_prop : Continuous (fun t : ℝ =>
        (iteratedFDeriv ℝ 2 f (t • y)) (fun _ : Fin 2 => v))).intervalIntegrable 1 R
    have hintB : IntervalIntegrable (fun t : ℝ =>
        deriv (fun s : ℝ => f (s • y)) t * t⁻¹) volume 1 R := by
      apply ContinuousOn.intervalIntegrable
      rw [Set.uIcc_of_le hR1]
      have heq : (deriv (fun s : ℝ => f (s • y))) = fun t : ℝ => (fderiv ℝ f (t • y)) y :=
        funext hderiv_phi
      rw [heq]
      apply ContinuousOn.mul
      · have h1 : Continuous (fun t : ℝ => fderiv ℝ f (t • y)) :=
          (hf.continuous_fderiv (by norm_num)).comp (continuous_id.smul continuous_const)
        exact (h1.clm_apply continuous_const).continuousOn
      · apply ContinuousOn.inv₀ continuousOn_id
        intro t ht
        exact ne_of_gt (by linarith [ht.1] : (0 : ℝ) < t)
    rw [intervalIntegral.integral_sub hintA hintB]
  -- ## 10. assembly
  rw [hA_trunc, hfun, hPhi2, hIBP, hderiv_trunc]
  ring

end Commons.Analysis.Calculus