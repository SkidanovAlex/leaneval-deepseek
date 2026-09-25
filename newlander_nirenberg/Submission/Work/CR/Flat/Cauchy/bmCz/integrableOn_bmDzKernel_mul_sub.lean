/-
Copyright: none.  Part of the `Newlander-Nirenberg` formalisation project.

# Integrability of `‖∂_{z_k}(bmKernel j)‖ · ‖g - g 0‖` over a Euclidean ball

The kernel `∂_{z_k}(bmKernel j) x = -n \bar x_j \bar x_k ‖x‖^{-2n-2}` is homogeneous of degree
`-2n`, so its norm is dominated by `‖x‖^{-2n}`; against the factor `‖g x - g 0‖`, which is
`O(‖x‖)` for a `C¹` function `g`, the product is dominated by `‖x‖^{1-2n} = ‖x‖^{-(2n-1)}`.
Since `2n - 1 < 2n` is strictly below the dimension `2n` of `ℂⁿ`, the product is integrable on
every ball.  This is the integrability input that lets the Calderón–Zygmund singular integral
`∫_{eucBall (4R)} ∂_{z_k}(bmKernel j) (g - g z)` be written as an honest Lebesgue integral.
-/
import Mathlib
import Submission.Work.CR.Flat.Cauchy.bmCZDefs

noncomputable section

open scoped NNReal ENNReal
open MeasureTheory Set

namespace Work.CR.Flat.Cauchy.bmCz

open Work.CR.Flat.Cauchy

/-! ### Elementary bounds -/

/-- Each coordinate of `x` is bounded by its Euclidean norm. -/
private lemma norm_apply_le_eucNorm_sub {n : ℕ} (x : Fin n → ℂ) (i : Fin n) :
    ‖x i‖ ≤ eucNorm x := by
  have h : ‖x i‖ ^ 2 ≤ eucNorm x ^ 2 := by
    rw [eucNorm_sq]
    exact Finset.single_le_sum (f := fun l : Fin n => ‖x l‖ ^ 2) (fun l _ => sq_nonneg (‖x l‖))
      (Finset.mem_univ i)
  have h3 : |‖x i‖| ≤ |eucNorm x| := sq_le_sq.mp h
  rwa [abs_of_nonneg (norm_nonneg (x i)), abs_of_nonneg (eucNorm_nonneg x)] at h3

/-- The Calderón–Zygmund decay rate of `∂_{z_k}(bmKernel j)` away from the origin. -/
private lemma norm_bmDzKernel_le_rpow {n : ℕ} (k j : Fin n) {x : Fin n → ℂ} (hx : x ≠ 0) :
    ‖bmDzKernel k j x‖ ≤ (n : ℝ) * eucNorm x ^ (-(2 * (n : ℝ))) := by
  have hXpos : 0 < eucNorm x := eucNorm_pos hx
  have h1 : ‖-((n : ℂ)) * starRingEnd ℂ (x j) * starRingEnd ℂ (x k)‖
      = (n : ℝ) * ‖x j‖ * ‖x k‖ := by
    rw [norm_mul, norm_mul, norm_neg, Complex.norm_natCast, Complex.norm_conj, Complex.norm_conj]
  have hnorm : ‖bmDzKernel k j x‖ = (n : ℝ) * ‖x j‖ * ‖x k‖ / (eucNorm x) ^ (2 * n + 2) := by
    rw [bmDzKernel, norm_div, h1, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (eucNorm_nonneg x)]
  rw [hnorm]
  have hle : (n : ℝ) * ‖x j‖ * ‖x k‖ ≤ (n : ℝ) * (eucNorm x) ^ 2 := by
    have hj : ‖x j‖ ≤ eucNorm x := norm_apply_le_eucNorm_sub x j
    have hk : ‖x k‖ ≤ eucNorm x := norm_apply_le_eucNorm_sub x k
    calc (n : ℝ) * ‖x j‖ * ‖x k‖ ≤ (n : ℝ) * eucNorm x * eucNorm x := by gcongr
      _ = (n : ℝ) * (eucNorm x) ^ 2 := by ring
  calc (n : ℝ) * ‖x j‖ * ‖x k‖ / (eucNorm x) ^ (2 * n + 2)
      ≤ (n : ℝ) * (eucNorm x) ^ 2 / (eucNorm x) ^ (2 * n + 2) :=
        div_le_div_of_nonneg_right hle (by positivity)
    _ = (n : ℝ) / (eucNorm x) ^ (2 * n) := by
        rw [pow_add]; rw [mul_div_mul_right _ _ (pow_ne_zero _ hXpos.ne')]
    _ = (n : ℝ) * (eucNorm x) ^ (-(2 * (n : ℝ))) := by
        have hpow : (eucNorm x) ^ (2 * n) = (eucNorm x) ^ (2 * (n : ℝ)) := by
          rw [show (2 * (n : ℝ)) = ((2 * n : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
        rw [hpow, Real.rpow_neg hXpos.le, div_eq_mul_inv]

/-- Measurability of `∂_{z_k}(bmKernel j)`. -/
private lemma measurable_bmDzKernel_sub {n : ℕ} (k j : Fin n) : Measurable (bmDzKernel k j) := by
  unfold bmDzKernel
  refine Measurable.div ?_ ?_
  · exact (measurable_const.mul
        (Complex.continuous_conj.measurable.comp (continuous_apply j).measurable)).mul
      (Complex.continuous_conj.measurable.comp (continuous_apply k).measurable)
  · exact Measurable.pow_const
      (Complex.continuous_ofReal.measurable.comp continuous_eucNorm.measurable) _

/-! ### The integrability statement -/

theorem integrableOn_bmDzKernel_mul_sub {n : ℕ} (hn : 0 < n) (j k : Fin n)
    (g : (Fin n → ℂ) → ℂ) (R : ℝ) (hR : 0 < R)
    (hg : ContDiff ℝ 1 g)
    (hsupp : ∀ x : Fin n → ℂ, R ≤ Work.CR.Flat.Cauchy.eucNorm x → g x = 0) :
    MeasureTheory.IntegrableOn
      (fun x => ‖Work.CR.Flat.Cauchy.bmDzKernel j k x‖ * ‖g x - g 0‖)
      (Work.CR.Flat.Cauchy.eucBall (n := n) (4 * R)) := by
  -- A Lipschitz constant for `g` on the compact ball of radius `4R`.
  obtain ⟨K, hK⟩ := hg.contDiffOn.exists_lipschitzOnWith (n := 1) (by norm_num)
      (convex_closedBall 0 (4 * R)) (isCompact_closedBall 0 (4 * R))
  set α : ℝ := 2 * (n : ℝ) - 1 with hαdef
  set Cc : ℝ := (n : ℝ) * (K : ℝ) with hCdef
  have h4R : (0 : ℝ) < 4 * R := by linarith
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  -- The dimension of `ℂⁿ` over `ℝ` is `2n`.
  have hfin : (Module.finrank ℝ (Fin n → ℂ) : ℝ) = 2 * (n : ℝ) := by
    rw [Module.finrank_pi_fintype]
    simp only [Complex.finrank_real_complex, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    push_cast
    ring
  have hd : 1 ≤ Module.finrank ℝ (Fin n → ℂ) := by
    have h2 : ((1 : ℕ) : ℝ) ≤ (Module.finrank ℝ (Fin n → ℂ) : ℝ) := by
      rw [hfin]; push_cast; linarith
    exact_mod_cast h2
  have hα : α < (Module.finrank ℝ (Fin n → ℂ) : ℝ) := by rw [hαdef, hfin]; linarith
  -- Measurability of the integrand.
  have hmeas : AEStronglyMeasurable
      (fun x : Fin n → ℂ => ‖bmDzKernel j k x‖ * ‖g x - g 0‖) volume := by
    have hm : Measurable (fun x : Fin n → ℂ => ‖bmDzKernel j k x‖ * ‖g x - g 0‖) :=
      (measurable_bmDzKernel_sub j k).norm.mul
        ((hg.continuous.sub continuous_const).norm.measurable)
    exact hm.aestronglyMeasurable
  -- The a.e. decay bound `‖f‖ ≤ C ‖x‖^{-α}` on the ball of radius `4R`.
  have hdecay : ∀ᵐ x ∂volume.restrict (Metric.ball 0 (4 * R)),
      ‖(fun x : Fin n → ℂ => ‖bmDzKernel j k x‖ * ‖g x - g 0‖) x‖ ≤ Cc * ‖x‖ ^ (-α) := by
    rw [MeasureTheory.ae_restrict_iff' Metric.isOpen_ball.measurableSet]
    filter_upwards with x hxmem
    rw [Metric.mem_ball, dist_zero_right] at hxmem
    have hxc : x ∈ Metric.closedBall (0 : Fin n → ℂ) (4 * R) := by
      rw [Metric.mem_closedBall, dist_zero_right]; exact le_of_lt hxmem
    have h0c : (0 : Fin n → ℂ) ∈ Metric.closedBall (0 : Fin n → ℂ) (4 * R) :=
      Metric.mem_closedBall_self h4R.le
    rcases eq_or_ne x 0 with rfl | hx0
    · -- the origin: both sides vanish
      have hf0 : (‖bmDzKernel j k 0‖ * ‖g 0 - g 0‖ : ℝ) = 0 := by simp
      rw [hf0, norm_zero]
      have hαne : -α ≠ 0 := by rw [hαdef]; intro h; linarith
      rw [norm_zero, Real.zero_rpow hαne, mul_zero]
    · -- away from the origin: kernel decay times the Lipschitz bound for `g`
      have hXpos : 0 < eucNorm x := eucNorm_pos hx0
      have hker : ‖bmDzKernel j k x‖ ≤ (n : ℝ) * eucNorm x ^ (-(2 * (n : ℝ))) :=
        norm_bmDzKernel_le_rpow j k hx0
      have hgle : ‖g x - g 0‖ ≤ (K : ℝ) * eucNorm x := by
        have h := hK.dist_le_mul x hxc 0 h0c
        rw [dist_eq_norm, dist_eq_norm, sub_zero] at h
        calc ‖g x - g 0‖ ≤ (K : ℝ) * ‖x‖ := h
          _ ≤ (K : ℝ) * eucNorm x := by
              gcongr; exact pi_norm_le_eucNorm x
      have hfnn : 0 ≤ ‖bmDzKernel j k x‖ * ‖g x - g 0‖ := by positivity
      rw [Real.norm_of_nonneg hfnn]
      have hradd : eucNorm x ^ (-(2 * (n : ℝ))) * eucNorm x
          = eucNorm x ^ (-(2 * (n : ℝ)) + 1) := by
        have h := Real.rpow_add hXpos (-(2 * (n : ℝ))) 1
        rw [Real.rpow_one] at h
        exact h.symm
      calc ‖bmDzKernel j k x‖ * ‖g x - g 0‖
          ≤ ((n : ℝ) * eucNorm x ^ (-(2 * (n : ℝ)))) * ((K : ℝ) * eucNorm x) :=
            mul_le_mul hker hgle (norm_nonneg _)
              (mul_nonneg (Nat.cast_nonneg n) (Real.rpow_nonneg (eucNorm_nonneg x) _))
        _ = Cc * (eucNorm x ^ (-(2 * (n : ℝ))) * eucNorm x) := by rw [hCdef]; ring
        _ = Cc * eucNorm x ^ (-(2 * (n : ℝ)) + 1) := by rw [hradd]
        _ ≤ Cc * ‖x‖ ^ (-(2 * (n : ℝ)) + 1) := by
            refine mul_le_mul_of_nonneg_left ?_ ?_
            · exact Real.rpow_le_rpow_of_nonpos (norm_pos_iff.mpr hx0) (pi_norm_le_eucNorm x)
                (by linarith)
            · rw [hCdef]; positivity
        _ = Cc * ‖x‖ ^ (-α) := by
            rw [show -(2 * (n : ℝ)) + 1 = -α by rw [hαdef]; ring]
  -- Integrability on the ambient ball, then restrict to the Euclidean ball.
  have hIball : IntegrableOn (fun x : Fin n → ℂ => ‖bmDzKernel j k x‖ * ‖g x - g 0‖)
      (Metric.ball 0 (4 * R)) volume :=
    MeasureTheory.integrableOn_ball_of_norm_le_rpow hd hα hdecay hmeas
  exact hIball.mono_set eucBall_subset_ball

end Work.CR.Flat.Cauchy.bmCz
