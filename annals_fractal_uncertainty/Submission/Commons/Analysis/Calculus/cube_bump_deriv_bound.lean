import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.UniformSpace.Uniformizable

namespace Commons.Analysis.Calculus

open scoped ContDiff

noncomputable section

/-!
# Cube bump functions with scaled derivative bounds

We construct a smooth bump function on an axis-parallel cube and show that all its
iterated Fréchet derivatives up to a given order are bounded by constants scaled like
`W^{-a}`.  The construction proceeds in two steps:

* `masterCubeBump d` is a fixed smooth bump on `ℝᵈ` (the product of one-dimensional
  smooth bumps) which equals `1` on the cube `[-1/4,1/4]^d` and vanishes outside the
  cube `[-1/2,1/2]^d`.
* Rescaling and translating it yields the required bump on the cube of side `W`
  centred at `c`, and the chain rule for the scaling produces the `W^{-a}` factor.
-/

/-- The standard one-dimensional smooth bump: it equals `1` on `[-1/4,1/4]` and vanishes
outside the open interval `(-1/2,1/2)`. -/
def cubeBump1 : ContDiffBump (0 : ℝ) := ⟨(1 : ℝ) / 4, (1 : ℝ) / 2, by norm_num, by norm_num⟩

/-- The function underlying `cubeBump1`. -/
def cubeBump1Fun : ℝ → ℝ := cubeBump1

lemma cubeBump1Fun_contDiff (n : ℕ) : ContDiff ℝ n cubeBump1Fun := cubeBump1.contDiff

lemma cubeBump1Fun_nonneg (t : ℝ) : 0 ≤ cubeBump1Fun t := cubeBump1.nonneg

lemma cubeBump1Fun_le_one (t : ℝ) : cubeBump1Fun t ≤ 1 := cubeBump1.le_one

lemma cubeBump1Fun_eq_one (t : ℝ) (h : |t| ≤ 1 / 4) : cubeBump1Fun t = 1 := by
  apply ContDiffBump.one_of_mem_closedBall (f := cubeBump1)
  rw [Metric.mem_closedBall, dist_eq_norm, sub_zero, Real.norm_eq_abs]
  exact h

lemma cubeBump1Fun_eq_zero (t : ℝ) (h : 1 / 2 ≤ |t|) : cubeBump1Fun t = 0 := by
  apply ContDiffBump.zero_of_le_dist (f := cubeBump1)
  rw [dist_eq_norm, sub_zero, Real.norm_eq_abs]
  exact h

/-- The "master" bump on `ℝᵈ`, the product of one-dimensional bumps.  It equals `1` on the
cube `[-1/4,1/4]^d` and vanishes outside the cube `[-1/2,1/2]^d`. -/
def masterCubeBump (d : ℕ) : EuclideanSpace ℝ (Fin d) → ℝ := fun y => ∏ i, cubeBump1Fun (y i)

lemma masterCubeBump_contDiff (d n : ℕ) : ContDiff ℝ n (masterCubeBump d) := by
  unfold masterCubeBump
  apply contDiff_prod
  intro i _
  exact (cubeBump1Fun_contDiff n).comp (by fun_prop)

lemma masterCubeBump_nonneg (d : ℕ) (y : EuclideanSpace ℝ (Fin d)) : 0 ≤ masterCubeBump d y := by
  unfold masterCubeBump
  exact Finset.prod_nonneg fun i _ => cubeBump1Fun_nonneg _

lemma masterCubeBump_le_one (d : ℕ) (y : EuclideanSpace ℝ (Fin d)) : masterCubeBump d y ≤ 1 := by
  unfold masterCubeBump
  refine Finset.prod_le_one (fun i _ => cubeBump1Fun_nonneg _) fun i _ => cubeBump1Fun_le_one _

lemma masterCubeBump_eq_one (d : ℕ) (y : EuclideanSpace ℝ (Fin d))
    (h : ∀ i, |y i| ≤ 1 / 4) : masterCubeBump d y = 1 := by
  unfold masterCubeBump
  apply Finset.prod_eq_one
  intro i _
  exact cubeBump1Fun_eq_one _ (h i)

lemma masterCubeBump_eq_zero (d : ℕ) (y : EuclideanSpace ℝ (Fin d))
    (h : ∃ i, 1 / 2 ≤ |y i|) : masterCubeBump d y = 0 := by
  unfold masterCubeBump
  obtain ⟨i, hi⟩ := h
  exact Finset.prod_eq_zero (Finset.mem_univ i) (cubeBump1Fun_eq_zero _ hi)

lemma masterCubeBump_hasCompactSupport (d : ℕ) : HasCompactSupport (masterCubeBump d) := by
  refine HasCompactSupport.intro
    (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin d)) (Real.sqrt d / 2)) ?_
  intro x hx
  rw [Metric.mem_closedBall, dist_zero_right, not_le] at hx
  refine masterCubeBump_eq_zero d x ?_
  by_contra hcon
  simp only [not_exists, not_le] at hcon
  have hnorm : ‖x‖ ≤ Real.sqrt d / 2 := by
    have hs : ‖x‖ ^ 2 ≤ (d : ℝ) / 4 := by
      rw [EuclideanSpace.norm_sq_eq]
      calc ∑ i, ‖x i‖ ^ 2 ≤ ∑ i : Fin d, (1 / 2 : ℝ) ^ 2 := by
            apply Finset.sum_le_sum
            intro i _
            rw [Real.norm_eq_abs]
            exact pow_le_pow_left₀ (abs_nonneg (x i)) (le_of_lt (hcon i)) 2
        _ = (d : ℝ) * (1 / 2) ^ 2 := by simp
        _ = (d : ℝ) / 4 := by ring
    have h4 : Real.sqrt ((d : ℝ) / 4) = Real.sqrt d / 2 := by
      rw [show (d : ℝ) / 4 = (d : ℝ) * (1 / 2) ^ 2 by ring]
      rw [Real.sqrt_mul (Nat.cast_nonneg d), Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 1 / 2)]
      ring
    have hnn : (0 : ℝ) ≤ ‖x‖ := norm_nonneg x
    have := Real.sqrt_le_sqrt hs
    rwa [Real.sqrt_sq hnn, h4] at this
  linarith

/-- All iterated derivatives of the master bump up to any order are globally bounded. -/
lemma masterCubeBump_iteratedFDeriv_bounded (d a a_max : ℕ) (ha : a ≤ a_max) :
    ∃ C : ℝ, ∀ y : EuclideanSpace ℝ (Fin d),
      ‖iteratedFDeriv ℝ a (masterCubeBump d) y‖ ≤ C := by
  have hc : Continuous fun y => ‖iteratedFDeriv ℝ a (masterCubeBump d) y‖ :=
    ((masterCubeBump_contDiff d a_max).continuous_iteratedFDeriv (by exact_mod_cast ha)).norm
  have hs : HasCompactSupport fun y => ‖iteratedFDeriv ℝ a (masterCubeBump d) y‖ :=
    (masterCubeBump_hasCompactSupport d).iteratedFDeriv a |>.comp_left norm_zero
  obtain ⟨C, hC⟩ := hc.bounded_above_of_compact_support hs
  exact ⟨C, fun y => by simpa using hC y⟩

/-- A smooth bump function on an axis-parallel cube of side `W`, together with bounds on all
its iterated Fréchet derivatives up to order `a_max`, scaled like `W^{-a}`.  This is the
elementary building block of the weight construction of §6.1 of Cohen's *Fractal uncertainty
in higher dimensions* (the paper's `η_𝓠` and `eq:deriv_estimate_etaQ`). -/
theorem cube_bump_deriv_bound (d : ℕ) (a_max : ℕ) (W : ℝ) (hW : 0 < W)
    (c : EuclideanSpace ℝ (Fin d)) :
    ∃ (η : EuclideanSpace ℝ (Fin d) → ℝ) (K : ℕ → ℝ),
      ContDiff ℝ a_max η ∧ (∀ x, 0 ≤ η x) ∧ (∀ x, η x ≤ 1) ∧
      (∀ x, (∀ i : Fin d, |x i - c i| ≤ W / 4) → η x = 1) ∧
      (∀ x, (∃ i : Fin d, W / 2 ≤ |x i - c i|) → η x = 0) ∧
      (∀ a ≤ a_max, 0 ≤ K a) ∧
      (∀ a ≤ a_max, ∀ x, ‖iteratedFDeriv ℝ a η x‖ ≤ K a * W ^ (-(a : ℝ))) := by
  have hbd : ∀ a, ∃ B : ℝ, a ≤ a_max → ∀ y : EuclideanSpace ℝ (Fin d),
      ‖iteratedFDeriv ℝ a (masterCubeBump d) y‖ ≤ B := by
    intro a
    by_cases ha : a ≤ a_max
    · obtain ⟨C, hC⟩ := masterCubeBump_iteratedFDeriv_bounded d a a_max ha
      exact ⟨max C 0, fun _ y => (hC y).trans (le_max_left _ _)⟩
    · exact ⟨0, fun h => absurd h ha⟩
  choose B hB using hbd
  let η : EuclideanSpace ℝ (Fin d) → ℝ := fun x => masterCubeBump d (W⁻¹ • (x - c))
  have hBnn : ∀ a, a ≤ a_max → 0 ≤ B a := by
    intro a ha
    have := hB a ha 0
    have h0 : (0 : ℝ) ≤ ‖iteratedFDeriv ℝ a (masterCubeBump d) 0‖ := norm_nonneg _
    linarith
  have hηdiff : ContDiff ℝ a_max η := by
    have h1 : ContDiff ℝ a_max fun z : EuclideanSpace ℝ (Fin d) => masterCubeBump d (W⁻¹ • z) :=
      (masterCubeBump_contDiff d a_max).comp (by fun_prop)
    exact h1.comp (by fun_prop)
  refine ⟨η, B, hηdiff, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    exact masterCubeBump_nonneg d _
  · intro x
    exact masterCubeBump_le_one d _
  · intro x hx
    apply masterCubeBump_eq_one
    intro i
    have hcoord : (W⁻¹ • (x - c)) i = W⁻¹ * (x i - c i) := by simp
    rw [hcoord, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ W⁻¹)]
    calc W⁻¹ * |x i - c i| ≤ W⁻¹ * (W / 4) :=
          mul_le_mul_of_nonneg_left (hx i) (by positivity)
      _ = 1 / 4 := by field_simp
  · intro x hx
    obtain ⟨i, hi⟩ := hx
    refine masterCubeBump_eq_zero d _ ⟨i, ?_⟩
    have hcoord : (W⁻¹ • (x - c)) i = W⁻¹ * (x i - c i) := by simp
    rw [hcoord, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ W⁻¹)]
    calc (1 : ℝ) / 2 = W⁻¹ * (W / 2) := by field_simp
      _ ≤ W⁻¹ * |x i - c i| := mul_le_mul_of_nonneg_left hi (by positivity)
  · intro a ha
    exact hBnn a ha
  · intro a ha x
    have h1 : iteratedFDeriv ℝ a η x
        = (W⁻¹) ^ a • iteratedFDeriv ℝ a (masterCubeBump d) (W⁻¹ • (x - c)) := by
      have heq : η = fun x : EuclideanSpace ℝ (Fin d) =>
          (fun z => masterCubeBump d (W⁻¹ • z)) (x - c) := rfl
      rw [heq]
      rw [iteratedFDeriv_comp_sub (𝕜 := ℝ)
        (f := fun z : EuclideanSpace ℝ (Fin d) => masterCubeBump d (W⁻¹ • z)) a c x]
      rw [iteratedFDeriv_comp_const_smul (W⁻¹) (masterCubeBump_contDiff d a)]
    rw [h1, norm_smul, Real.norm_of_nonneg (pow_nonneg (by positivity : (0 : ℝ) ≤ W⁻¹) a)]
    calc (W⁻¹) ^ a * ‖iteratedFDeriv ℝ a (masterCubeBump d) (W⁻¹ • (x - c))‖
        ≤ (W⁻¹) ^ a * B a := by gcongr; exact hB a ha _
      _ = B a * W ^ (-(a : ℝ)) := by
          rw [Real.rpow_neg (le_of_lt hW), Real.rpow_natCast, inv_pow]
          ring

end

end Commons.Analysis.Calculus