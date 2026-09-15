import Submission.Commons.Analysis.Calculus.cube_bump_deriv_bound

set_option linter.unusedVariables false

namespace Commons.Analysis.Calculus

open scoped BigOperators Topology
open EuclideanSpace

noncomputable section

/-- Uniform-in-width version of the cube bump estimate: the derivative constants `K a` can be
chosen ONCE AND FOR ALL, independently of the side length `W` (and of the centre `c`).  This is
the form needed to sum bump functions over grids of different widths while keeping a single
derivative constant. -/
theorem cube_bump_deriv_bound_uniformW (d a_max : ℕ) :
    ∃ K : ℕ → ℝ, (∀ a ≤ a_max, 0 ≤ K a) ∧
      ∀ (W : ℝ) (hW : 0 < W) (c : EuclideanSpace ℝ (Fin d)),
        ∃ η : EuclideanSpace ℝ (Fin d) → ℝ,
          ContDiff ℝ a_max η ∧ (∀ x, 0 ≤ η x) ∧ (∀ x, η x ≤ 1) ∧
          (∀ x, (∀ i : Fin d, |x i - c i| ≤ W / 4) → η x = 1) ∧
          (∀ x, (∃ i : Fin d, W / 2 ≤ |x i - c i|) → η x = 0) ∧
          (∀ a ≤ a_max, ∀ x, ‖iteratedFDeriv ℝ a η x‖ ≤ K a * W ^ (-(a : ℝ))) := by
  -- Uniform derivative bounds for the master bump, one for each order `a`.
  have hbd : ∀ a, ∃ B : ℝ, a ≤ a_max → ∀ y : EuclideanSpace ℝ (Fin d),
      ‖iteratedFDeriv ℝ a (masterCubeBump d) y‖ ≤ B := by
    intro a
    by_cases ha : a ≤ a_max
    · obtain ⟨C, hC⟩ := masterCubeBump_iteratedFDeriv_bounded d a a_max ha
      exact ⟨max C 0, fun _ y => (hC y).trans (le_max_left _ _)⟩
    · exact ⟨0, fun h => absurd h ha⟩
  choose B hB using hbd
  have hBnn : ∀ a, a ≤ a_max → 0 ≤ B a := by
    intro a ha
    have := hB a ha 0
    have h0 : (0 : ℝ) ≤ ‖iteratedFDeriv ℝ a (masterCubeBump d) 0‖ := norm_nonneg _
    linarith
  -- The constant, made total by declaring `0` above the truncation order.
  let K : ℕ → ℝ := fun a => if a ≤ a_max then B a else 0
  have hKnn : ∀ a ≤ a_max, 0 ≤ K a := by
    intro a ha
    simp only [K, ha, ↓reduceIte]
    exact hBnn a ha
  refine ⟨K, hKnn, ?_⟩
  intro W hW c
  refine ⟨fun x => masterCubeBump d (W⁻¹ • (x - c)), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hsm : ContDiff ℝ a_max (fun x : EuclideanSpace ℝ (Fin d) => W⁻¹ • (x - c)) := by
      fun_prop
    exact (masterCubeBump_contDiff d a_max).comp hsm
  · intro x; exact masterCubeBump_nonneg d _
  · intro x; exact masterCubeBump_le_one d _
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
  · intro a ha x
    have h1 : iteratedFDeriv ℝ a (fun x : EuclideanSpace ℝ (Fin d) =>
          masterCubeBump d (W⁻¹ • (x - c))) x
        = (W⁻¹) ^ a • iteratedFDeriv ℝ a (masterCubeBump d) (W⁻¹ • (x - c)) := by
      have heq : (fun x : EuclideanSpace ℝ (Fin d) => masterCubeBump d (W⁻¹ • (x - c)))
          = fun x => (fun z : EuclideanSpace ℝ (Fin d) => masterCubeBump d (W⁻¹ • z)) (x - c) :=
        rfl
      rw [heq]
      rw [iteratedFDeriv_comp_sub (𝕜 := ℝ)
        (f := fun z : EuclideanSpace ℝ (Fin d) => masterCubeBump d (W⁻¹ • z)) a c x]
      rw [iteratedFDeriv_comp_const_smul (W⁻¹) (masterCubeBump_contDiff d a)]
    have hBK : B a ≤ K a := by
      have hKa : K a = B a := by simp [K, ha]
      exact hKa.ge
    rw [h1, norm_smul, Real.norm_of_nonneg (pow_nonneg (by positivity : (0 : ℝ) ≤ W⁻¹) a)]
    calc (W⁻¹) ^ a * ‖iteratedFDeriv ℝ a (masterCubeBump d) (W⁻¹ • (x - c))‖
        ≤ (W⁻¹) ^ a * B a := by
          gcongr
          exact hB a ha _
      _ ≤ (W⁻¹) ^ a * K a :=
          mul_le_mul_of_nonneg_left hBK (pow_nonneg (by positivity : (0 : ℝ) ≤ W⁻¹) a)
      _ = K a * W ^ (-(a : ℝ)) := by
          rw [Real.rpow_neg (le_of_lt hW), Real.rpow_natCast, inv_pow]
          ring

end

end Commons.Analysis.Calculus
