import Mathlib
import Submission.Commons.NumberTheory.Linnik.completedL_ballZeroCount

open Complex DirichletCharacter Metric Filter
open scoped Real BigOperators
set_option autoImplicit false
noncomputable section

namespace Commons.NumberTheory.Linnik

theorem nearSum_bound {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (hχprim : χ.IsPrimitive) :
    ∃ K : ℝ, ∀ R : ℝ, 2 ≤ R → ∀ w : ℂ, ‖w‖ = R →
      DirichletCharacter.completedLFunction χ w ≠ 0 →
      ‖∑ᶠ u : ℂ, (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
            (Metric.closedBall w 1)) u : ℤ) : ℂ) * (1 / (w - u) + 1 / u)‖ ≤
        K * ((Real.log (R + 2) + Real.log (N : ℝ) + 2) ^ 2 + 1) +
          (∑ᶠ u : ℂ, (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
              (Metric.closedBall w 1)) u : ℤ) : ℝ) * ((‖w - u‖ : ℝ)⁻¹)) := by
  classical
  rcases completedL_ballZeroCount χ hχ hχprim with ⟨c0, hc0⟩
  let c1 : ℝ := max c0 0
  let K : ℝ := 4 * c1
  refine ⟨K, ?_⟩
  intro R hR w hw hΛw
  let m : ℂ → ℤ := fun u => (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
            (Metric.closedBall w 1)) u
  let M : ℂ → ℝ := fun u => (((m u : ℤ) : ℝ))
  have hfinm : Function.HasFiniteSupport m := by
    simpa [m] using (divisor_finiteSupport χ hχ w (1 : ℝ))
  let S : Finset ℂ := hfinm.toFinset
  let x : ℝ := Real.log (R + 2) + Real.log (N : ℝ) + 2
  have hlogR2 : 0 ≤ Real.log (R + 2) := by
    refine Real.log_nonneg ?_
    linarith
  have hlogN : 0 ≤ Real.log (N : ℝ) := by
    exact Real.log_nonneg (by exact_mod_cast (Nat.succ_le_of_lt (Nat.pos_of_ne_zero (NeZero.ne N))))
  have hx0 : 0 ≤ x := by dsimp [x]; linarith
  have hx_le_x2 : x ≤ x ^ 2 + 1 := by nlinarith [sq_nonneg (x - 1 / 2)]
  have hc1pos : 0 ≤ c1 := by dsimp [c1]; exact le_max_right c0 0
  have hKpos : 0 ≤ K := by dsimp [K]; positivity
  -- support facts
  have hmsub_ball : ∀ u : ℂ, m u ≠ 0 → u ∈ Metric.closedBall w 1 := by
    intro u hu
    by_contra huB
    have hcond : ¬ (MeromorphicOn (DirichletCharacter.completedLFunction χ)
          (Metric.closedBall w 1) ∧ u ∈ Metric.closedBall w 1) := by
      intro h
      exact huB h.2
    have hu' : (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
          (Metric.closedBall w 1)) u = 0 := by
      rw [MeromorphicOn.divisor_def (f := DirichletCharacter.completedLFunction χ)
        (U := Metric.closedBall w 1) (z := u), if_neg hcond]
    exact hu (by simpa [m] using hu')
  have hsubM : Function.support M ⊆ (S : Set ℂ) := by
    intro u hu
    have hmne : m u ≠ 0 := by
      intro hm0
      exact hu (by simp [M, hm0])
    have huS : u ∈ S := by
      exact (hfinm.mem_toFinset).2 hmne
    simpa using huS
  have hsubC : Function.support
      (fun u : ℂ => ((m u : ℤ) : ℂ) * (1 / (w - u) + 1 / u)) ⊆ (S : Set ℂ) := by
    intro u hu
    have hmne : m u ≠ 0 := by
      intro hm0
      apply hu
      simp [hm0]
    have huS : u ∈ S := by
      simpa [S] using (hfinm.mem_toFinset).2 hmne
    simpa using huS
  have hsubR : Function.support (fun u : ℂ => M u * ((‖w - u‖ : ℝ)⁻¹)) ⊆ (S : Set ℂ) := by
    intro u hu
    have hmne : M u ≠ 0 := by
      intro hm0
      apply hu
      simp [hm0]
    exact hsubM (Function.mem_support.mpr hmne)
  have hconvC : (∑ᶠ u : ℂ, (((m u : ℤ) : ℂ) * (1 / (w - u) + 1 / u))) =
      ∑ u ∈ S, ((m u : ℤ) : ℂ) * (1 / (w - u) + 1 / u) := by
    exact finsum_eq_sum_of_support_subset (fun u : ℂ => ((m u : ℤ) : ℂ) * (1 / (w - u) + 1 / u)) hsubC
  have hconvR : (∑ᶠ u : ℂ, (M u * ((‖w - u‖ : ℝ)⁻¹))) =
      ∑ u ∈ S, M u * ((‖w - u‖ : ℝ)⁻¹) := by
    exact finsum_eq_sum_of_support_subset (fun u : ℂ => M u * ((‖w - u‖ : ℝ)⁻¹)) hsubR
  -- zero count over the ball (finite support version)
  have hball0 : (∑ᶠ u : ℂ, M u) ≤ 2 * c0 * (Real.log (R + 3) + Real.log (N : ℝ) + 2) := by
    have h := hc0 w 1 (by norm_num : (1 : ℝ) ≤ (1 : ℝ))
    have hw3 : ‖w‖ + 1 + 2 = R + 3 := by rw [hw]; ring
    rw [hw3] at h
    have hnorm : c0 * (1 + 1) * (Real.log (R + 3) + Real.log (N : ℝ) + 2) =
        2 * c0 * (Real.log (R + 3) + Real.log (N : ℝ) + 2) := by ring
    rw [hnorm] at h
    simpa [M, m] using h
  -- nonnegativity and norm facts about the divisor
  have hΛan : AnalyticOnNhd ℂ (DirichletCharacter.completedLFunction χ)
      (Metric.closedBall w 1) := by
    intro z hz
    exact (DirichletCharacter.differentiable_completedLFunction hχ).analyticAt z
  have hm_nonneg : ∀ u : ℂ, (0 : ℤ) ≤ m u := by
    intro u
    by_cases hu : u ∈ Metric.closedBall w 1
    · have hmpos : (0 : ℤ) ≤ MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
          (Metric.closedBall w 1) u := divisor_nonneg_of_analyticOnNhd hΛan hu
      simpa [m] using hmpos
    · have hz : MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
          (Metric.closedBall w 1) u = 0 := by
        rw [MeromorphicOn.divisor_def (f := DirichletCharacter.completedLFunction χ)
          (U := Metric.closedBall w 1) (z := u), if_neg (by intro h; exact hu h.2)]
      change (0 : ℤ) ≤ MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
        (Metric.closedBall w 1) u
      rw [hz]
  have hM_nonneg : ∀ u : ℂ, 0 ≤ M u := by
    intro u
    exact Int.cast_nonneg (hm_nonneg u)
  have hncm : ∀ u : ℂ, ‖((m u : ℤ) : ℂ)‖ = M u := by
    intro u
    calc
      ‖((m u : ℤ) : ℂ)‖ = ‖((m u : ℤ) : ℝ)‖ := by
        rw [← Complex.ofReal_intCast (m u)]
        exact Complex.norm_real ((m u : ℤ) : ℝ)
      _ = |((m u : ℤ) : ℝ)| := Real.norm_eq_abs _
      _ = ((m u : ℤ) : ℝ) := abs_of_nonneg (Int.cast_nonneg (hm_nonneg u))
      _ = M u := by rfl
  -- norm lower bound for points in the support
  have hu_ge1 : ∀ u : ℂ, u ∈ S → 1 ≤ ‖u‖ := by
    intro u huS
    have hmne : m u ≠ 0 := (hfinm.mem_toFinset).1 huS
    have hub : u ∈ Metric.closedBall w 1 := hmsub_ball u hmne
    have hdist : ‖w - u‖ ≤ 1 := by
      have hd := Metric.mem_closedBall.mp hub
      rw [dist_eq_norm, norm_sub_rev] at hd
      exact hd
    have htri : ‖w‖ ≤ ‖w - u‖ + ‖u‖ := by
      have := norm_add_le (w - u) u
      simpa using this
    have hR : R ≤ ‖w - u‖ + ‖u‖ := by simpa [hw] using htri
    linarith
  -- per-term norm bound
  have hterm (u : ℂ) :
      ‖((m u : ℤ) : ℂ) * (1 / (w - u) + 1 / u)‖ ≤
        M u * ((‖w - u‖ : ℝ)⁻¹ + (‖u‖ : ℝ)⁻¹) := by
    calc
      ‖((m u : ℤ) : ℂ) * (1 / (w - u) + 1 / u)‖
          = ‖((m u : ℤ) : ℂ)‖ * ‖(1 / (w - u) + 1 / u)‖ := by rw [norm_mul]
      _ ≤ M u * (‖1 / (w - u)‖ + ‖1 / u‖) := by
        rw [hncm u]
        exact mul_le_mul_of_nonneg_left (norm_add_le (1 / (w - u)) (1 / u)) (hM_nonneg u)
      _ = M u * (((‖w - u‖ : ℝ)⁻¹) + (‖u‖ : ℝ)⁻¹) := by
        congr 1
        simp
  -- log absorption for R+3
  have hlogR3 : 0 ≤ Real.log (R + 3) := by
    refine Real.log_nonneg ?_
    linarith
  have hB2x : Real.log (R + 3) + Real.log (N : ℝ) + 2 ≤ 2 * x := by
    have hRpos : 0 < R + 3 := by linarith
    have hR2pos : 0 < R + 2 := by linarith
    have hsq : R + 3 ≤ (R + 2) ^ 2 := by nlinarith [hR]
    have hlogsq : Real.log (R + 3) ≤ Real.log ((R + 2) ^ 2) := Real.log_le_log hRpos hsq
    have hpow : Real.log ((R + 2) ^ 2) = 2 * Real.log (R + 2) := by
      rw [Real.log_pow]
      norm_num
    have hlog3 : Real.log (R + 3) ≤ 2 * Real.log (R + 2) := by
      simpa [hpow] using hlogsq
    dsimp [x]
    calc
      Real.log (R + 3) + Real.log (N : ℝ) + 2
          ≤ 2 * Real.log (R + 2) + Real.log (N : ℝ) + 2 := by linarith
      _ ≤ 2 * Real.log (R + 2) + 2 * Real.log (N : ℝ) + 4 := by nlinarith [hlogN]
      _ = 2 * (Real.log (R + 2) + Real.log (N : ℝ) + 2) := by ring
  -- zero-count bound in the finite-support form
  have hCount_le : (∑ u ∈ S, M u) ≤ 4 * c1 * (x ^ 2 + 1) := by
    let B : ℝ := Real.log (R + 3) + Real.log (N : ℝ) + 2
    have hsum : (∑ u ∈ S, M u) = ∑ᶠ u : ℂ, M u := by
      rw [finsum_eq_sum_of_support_subset M hsubM]
    have hle0 : (∑ u ∈ S, M u) ≤ 2 * c0 * B := by
      rw [hsum]
      simpa [B] using hball0
    have hBpos : 0 ≤ B := by
      dsimp [B]
      linarith [hlogR3, hlogN]
    have hc0le : c0 ≤ c1 := by dsimp [c1]; exact le_max_left c0 0
    have hle1 : (∑ u ∈ S, M u) ≤ 2 * c1 * B := by
      have h2B : 0 ≤ (2 : ℝ) * B := by exact mul_nonneg (by norm_num) hBpos
      calc
        (∑ u ∈ S, M u) ≤ 2 * c0 * B := hle0
        _ = c0 * (2 * B) := by ring
        _ ≤ c1 * (2 * B) := mul_le_mul_of_nonneg_right hc0le h2B
        _ = 2 * c1 * B := by ring
    have h2c1pos : 0 ≤ 2 * c1 := by
      exact mul_nonneg (by norm_num) hc1pos
    calc
      (∑ u ∈ S, M u) ≤ 2 * c1 * B := hle1
      _ ≤ 2 * c1 * (2 * x) := mul_le_mul_of_nonneg_left hB2x h2c1pos
      _ = 4 * c1 * x := by ring
      _ ≤ 4 * c1 * (x ^ 2 + 1) := by
        exact mul_le_mul_of_nonneg_left hx_le_x2 (mul_nonneg (by norm_num) hc1pos)
  -- split: second sum has terms ≤ M u
  have hsplit2 : (∑ u ∈ S, M u * ((‖u‖ : ℝ)⁻¹)) ≤ ∑ u ∈ S, M u := by
    refine Finset.sum_le_sum ?_
    intro u huS
    have hge : 1 ≤ ‖u‖ := hu_ge1 u huS
    have hposu : 0 < ‖u‖ := by linarith
    have hinv : ((‖u‖ : ℝ)⁻¹) ≤ 1 := (inv_le_one₀ hposu).2 hge
    calc
      M u * ((‖u‖ : ℝ)⁻¹) ≤ M u * 1 := mul_le_mul_of_nonneg_left hinv (hM_nonneg u)
      _ = M u := by ring
  -- main finite inequality
  have hmain : ‖∑ u ∈ S, ((m u : ℤ) : ℂ) * (1 / (w - u) + 1 / u)‖ ≤
      (∑ u ∈ S, M u * ((‖w - u‖ : ℝ)⁻¹)) + 4 * c1 * (x ^ 2 + 1) := by
    calc
      ‖∑ u ∈ S, ((m u : ℤ) : ℂ) * (1 / (w - u) + 1 / u)‖
          ≤ ∑ u ∈ S, ‖((m u : ℤ) : ℂ) * (1 / (w - u) + 1 / u)‖ := norm_sum_le S _
      _ ≤ ∑ u ∈ S, (M u * ((‖w - u‖ : ℝ)⁻¹) + M u * ((‖u‖ : ℝ)⁻¹)) := by
        refine Finset.sum_le_sum ?_
        intro u hu
        calc
          ‖((m u : ℤ) : ℂ) * (1 / (w - u) + 1 / u)‖
              ≤ M u * ((‖w - u‖ : ℝ)⁻¹ + (‖u‖ : ℝ)⁻¹) := hterm u
          _ = M u * ((‖w - u‖ : ℝ)⁻¹) + M u * ((‖u‖ : ℝ)⁻¹) := by ring
      _ = (∑ u ∈ S, M u * ((‖w - u‖ : ℝ)⁻¹)) + (∑ u ∈ S, M u * ((‖u‖ : ℝ)⁻¹)) := by
        rw [Finset.sum_add_distrib]
      _ ≤ (∑ u ∈ S, M u * ((‖w - u‖ : ℝ)⁻¹)) + (∑ u ∈ S, M u) := by
        exact add_le_add_right hsplit2 _
      _ ≤ (∑ u ∈ S, M u * ((‖w - u‖ : ℝ)⁻¹)) + 4 * c1 * (x ^ 2 + 1) := by
        exact add_le_add_right hCount_le _
  -- assemble with the finsums
  have hxK : 4 * c1 * (x ^ 2 + 1) = K * (x ^ 2 + 1) := rfl
  rw [hconvC, hconvR]
  calc
    ‖∑ u ∈ S, ((m u : ℤ) : ℂ) * (1 / (w - u) + 1 / u)‖
        ≤ (∑ u ∈ S, M u * ((‖w - u‖ : ℝ)⁻¹)) + 4 * c1 * (x ^ 2 + 1) := hmain
    _ = (∑ u ∈ S, M u * ((‖w - u‖ : ℝ)⁻¹)) + K * (x ^ 2 + 1) := by rw [hxK]
    _ = K * (x ^ 2 + 1) + (∑ u ∈ S, M u * ((‖w - u‖ : ℝ)⁻¹)) := by rw [add_comm]

end Commons.NumberTheory.Linnik
