import Mathlib
import Submission.Work.ZeroFreeTables.P9.Defs
import Submission.Work.LinnikAreas.A5.LFunction_disc_zeroCount
import Submission.Work.LinnikAreas.ownRepelNW.orderSum_invSq_bound_of_count
import Submission.Work.LinnikAreas.FarRepel.zeroMult_eq_analyticOrderNatAt_of_isPrimitive

namespace Work.ZeroFreeTables.Table4

open DirichletCharacter Complex
open scoped BigOperators

/-- Moving the base point of the inverse-square weight to the line `Re = 1` can only increase
the weight, provided `Re s ≥ 1` and `Re u ≤ 1`: the two expressions differ only in the real
part of `· - u`, where `1 - u.re ≤ s.re - u.re` are both nonnegative. -/
lemma invSq_weight_le {s u : ℂ} (hs : 1 ≤ s.re) (hu : u.re ≤ 1) :
    1 / (1 + ‖s - u‖ ^ 2)
      ≤ 1 / (1 + ‖(1 : ℂ) + (s.im : ℂ) * Complex.I - u‖ ^ 2) := by
  have hre : (1 : ℝ) - u.re ≤ s.re - u.re := by linarith
  have hnn : 0 ≤ (1 : ℝ) - u.re := by linarith
  have hn1 : Complex.normSq ((1 : ℂ) + (s.im : ℂ) * Complex.I - u)
      = (1 - u.re) ^ 2 + (s.im - u.im) ^ 2 := by
    rw [Complex.normSq_apply]
    simp
    ring
  have hn2 : Complex.normSq (s - u) = (s.re - u.re) ^ 2 + (s.im - u.im) ^ 2 := by
    rw [Complex.normSq_apply]
    simp
    ring
  have hsq : ‖(1 : ℂ) + (s.im : ℂ) * Complex.I - u‖ ^ 2 ≤ ‖s - u‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.sq_norm, hn1, hn2]
    have hp1 : (1 - u.re) * (1 - u.re) ≤ (1 - u.re) * (s.re - u.re) :=
      mul_le_mul_of_nonneg_left hre hnn
    have hp2 : (1 - u.re) * (s.re - u.re) ≤ (s.re - u.re) * (s.re - u.re) :=
      mul_le_mul_of_nonneg_right hre (by linarith)
    nlinarith
  have hnorm : ‖(1 : ℂ) + (s.im : ℂ) * Complex.I - u‖ ≤ ‖s - u‖ := by
    rw [← Real.sqrt_sq (norm_nonneg ((1 : ℂ) + (s.im : ℂ) * Complex.I - u)),
      ← Real.sqrt_sq (norm_nonneg (s - u))]
    exact Real.sqrt_le_sqrt hsq
  have hsq2 : ‖(1 : ℂ) + (s.im : ℂ) * Complex.I - u‖ ^ 2 ≤ ‖s - u‖ ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hnorm 2
  exact one_div_le_one_div_of_le (by positivity) (by linarith)

/-- Coarse bound: for `|Im s| ≤ 20` the shifted point `1 + i·Im s` has norm at most `21`, so
`2 + ‖1 + i·Im s‖ ≤ 32 = 2^5` and its logarithm is at most `5`. -/
lemma log_two_add_norm_s0_le {s : ℂ} (him : |s.im| ≤ 20) :
    Real.log (2 + ‖(1 : ℂ) + (s.im : ℂ) * Complex.I‖) ≤ 5 := by
  have hnorm : ‖(1 : ℂ) + (s.im : ℂ) * Complex.I‖ ≤ 21 := by
    have h1 : ‖(1 : ℂ) + (s.im : ℂ) * Complex.I‖ ^ 2 = 1 + s.im ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      simp
      ring
    have h2 : ‖(1 : ℂ) + (s.im : ℂ) * Complex.I‖ ^ 2 ≤ (21 : ℝ) ^ 2 := by
      rw [h1]
      have habs : |s.im| ^ 2 ≤ 400 := by nlinarith [abs_nonneg s.im, him]
      have hsqim : s.im ^ 2 ≤ 400 := by rw [← sq_abs]; exact habs
      nlinarith
    have h3 := (sq_le_sq).mp h2
    rwa [abs_of_nonneg (norm_nonneg _), abs_of_nonneg (by norm_num : (0:ℝ) ≤ 21)] at h3
  have hpos : 0 < 2 + ‖(1 : ℂ) + (s.im : ℂ) * Complex.I‖ := by positivity
  have hlt : 2 + ‖(1 : ℂ) + (s.im : ℂ) * Complex.I‖ ≤ 32 := by linarith
  have hlog := Real.log_le_log hpos hlt
  have h32 : Real.log (32 : ℝ) = 5 * Real.log 2 := by
    rw [show (32 : ℝ) = 2 ^ 5 by norm_num, Real.log_pow]
    norm_num
  rw [h32] at hlog
  have hlog2 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2)
    linarith
  linarith

theorem invSqSum_le : ∃ C : ℝ, 0 < C ∧ ∀ {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (hprim : χ.IsPrimitive) {s : ℂ} (hs : 1 ≤ s.re) (him : |s.im| ≤ 20),
    Work.ZeroFreeTables.P9.invSqSum N χ s ≤ C * (Real.log (N : ℝ) + 2) := by
  -- uniform (in `χ`, `N`) disk zero count of `Λ(·,χ) = completedLFunction χ`
  obtain ⟨c, hcpos, hc⟩ := Work.LinnikAreas.A5.ball_zeroCount_uniformL_A5
  -- the dyadic inverse-square estimate turns a ball count into a bound for the kernel sum
  obtain ⟨C0, hC0pos, hC0⟩ :=
    Work.LinnikAreas.ownRepelNW.orderSum_invSq_bound_of_count hcpos.le
  refine ⟨4 * C0, by positivity, ?_⟩
  intro N _inst χ hχ hprim s hs him
  have hlogN : (0 : ℝ) ≤ Real.log (N : ℝ) := by
    have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast NeZero.one_le
    exact Real.log_nonneg hN1
  -- the shifted base point lies on `Re = 1` and has bounded norm
  set s₀ : ℂ := (1 : ℂ) + (s.im : ℂ) * Complex.I with hs₀
  -- pointwise domination of the weight at `s` by the weight at `s₀`
  have hweight : ∀ u : ℂ, (Work.LinnikContract.zeroMult χ u : ℝ) * (1 / (1 + ‖s - u‖ ^ 2))
      ≤ (analyticOrderNatAt (DirichletCharacter.completedLFunction χ) u : ℝ)
          * (1 / (1 + ‖s₀ - u‖ ^ 2)) := by
    intro u
    by_cases hu : Work.LinnikContract.zeroMult χ u = 0
    · rw [hu, Nat.cast_zero, zero_mul]
      refine mul_nonneg (Nat.cast_nonneg _) ?_
      positivity
    · have hz : analyticOrderNatAt (DirichletCharacter.completedLFunction χ) u
          = Work.LinnikContract.zeroMult χ u :=
        (Work.LinnikAreas.FarRepel.zeroMult_eq_analyticOrderNatAt_of_isPrimitive
          χ hprim u).symm
      have hord : analyticOrderNatAt (DirichletCharacter.completedLFunction χ) u ≠ 0 := by
        rw [hz]; exact hu
      have hzero : DirichletCharacter.completedLFunction χ u = 0 :=
        apply_eq_zero_of_analyticOrderNatAt_ne_zero hord
      have hult : u.re ≤ 1 :=
        le_of_lt (Commons.NumberTheory.DirichletCharacter.zerosInStrip χ hχ hprim u hzero).2
      rw [hz]
      refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
      simpa [hs₀] using invSq_weight_le hs hult
  have hΛan : AnalyticOnNhd ℂ (DirichletCharacter.completedLFunction χ) Set.univ :=
    fun z _ => (DirichletCharacter.differentiable_completedLFunction hχ).analyticAt z
  -- the finite-set bound of the general estimate, at the shifted point `s₀`
  have hfin : ∀ T : Finset ℂ,
      ∑ u ∈ T, (analyticOrderNatAt (DirichletCharacter.completedLFunction χ) u : ℝ)
          * (1 / (1 + ‖s₀ - u‖ ^ 2))
        ≤ C0 * (Real.log (2 + ‖s₀‖) + Real.log (N : ℝ) + 2) := by
    intro T
    exact hC0 (DirichletCharacter.completedLFunction χ) hΛan (Real.log (N : ℝ)) hlogN
      (fun a ρ hρ => hc χ hχ hprim a ρ hρ) s₀ T
  have hfin' : ∀ T : Finset ℂ,
      ∑ u ∈ T, (Work.LinnikContract.zeroMult χ u : ℝ) * (1 / (1 + ‖s - u‖ ^ 2))
        ≤ 4 * C0 * (Real.log (N : ℝ) + 2) := by
    intro T
    have hlog : Real.log (2 + ‖s₀‖) ≤ 5 := by
      simpa [hs₀] using log_two_add_norm_s0_le (s := s) him
    have h1 : C0 * (Real.log (2 + ‖s₀‖) + Real.log (N : ℝ) + 2)
        ≤ 4 * C0 * (Real.log (N : ℝ) + 2) := by
      have h2 : Real.log (2 + ‖s₀‖) + Real.log (N : ℝ) + 2
          ≤ 4 * (Real.log (N : ℝ) + 2) := by linarith
      calc C0 * (Real.log (2 + ‖s₀‖) + Real.log (N : ℝ) + 2)
          ≤ C0 * (4 * (Real.log (N : ℝ) + 2)) :=
            mul_le_mul_of_nonneg_left h2 (le_of_lt hC0pos)
        _ = 4 * C0 * (Real.log (N : ℝ) + 2) := by ring
    calc ∑ u ∈ T, (Work.LinnikContract.zeroMult χ u : ℝ) * (1 / (1 + ‖s - u‖ ^ 2))
        ≤ ∑ u ∈ T, (analyticOrderNatAt (DirichletCharacter.completedLFunction χ) u : ℝ)
            * (1 / (1 + ‖s₀ - u‖ ^ 2)) := Finset.sum_le_sum (fun u _ => hweight u)
      _ ≤ C0 * (Real.log (2 + ‖s₀‖) + Real.log (N : ℝ) + 2) := hfin T
      _ ≤ 4 * C0 * (Real.log (N : ℝ) + 2) := h1
  have hnn : ∀ u : ℂ,
      0 ≤ (Work.LinnikContract.zeroMult χ u : ℝ) * (1 / (1 + ‖s - u‖ ^ 2)) := by
    intro u
    refine mul_nonneg (Nat.cast_nonneg _) ?_
    positivity
  have hmain := Real.tsum_le_of_sum_le hnn hfin'
  simpa [Work.ZeroFreeTables.P9.invSqSum] using hmain

end Work.ZeroFreeTables.Table4
