import Mathlib
import Submission.Work.HP.Q44Main.min_compare_good2
import Submission.Work.HP.Q44Main.min_compare_good3

/-!
# `Work.HP.Q44Main.min_compare`

The arithmetic comparison `min_compare`: the minimum of the two bounds
`CL·Z⁶·Δ³·(log 2Δ)²` and `CL₁·(Σ terms)·(log 2Δ)²` is `O(Z^{9/2} Δ² (Z^{3/2}+Δ^{3/2}) (log 2Δ)² min(Δ, M⁵³))`,
uniformly over `Z, Δ, M ≥ 1`.

The logarithm factor is common to both sides and non-negative, so it is factored out.
For the remaining monomial inequality `min (CL Z⁶Δ³) (CL₁ S) ≤ K·Z^{9/2}Δ²(Z^{3/2}+Δ^{3/2})·min(Δ,M⁵³)`
one splits into three regimes, using that `min` is below both of its arguments:

* `Δ ≤ M⁵³` (so `min(Δ,M⁵³) = Δ`): the first argument fits because
  `Z^{9/2}Δ²·Z^{3/2}·Δ = Z⁶Δ³`;
* `M⁵³ ≤ Δ` and `Z³ ≤ M¹⁰⁶ Δ`: the first argument fits (`min(Δ,M⁵³) = M⁵³`), using
  `Z^{3/2} ≤ M⁵³Δ^{1/2}` (this is `min_compare_good2`);
* `M⁵³ ≤ Δ` and `M¹⁰⁶ Δ ≤ Z³`: the second argument fits (`min_compare_good3`).
-/

set_option autoImplicit false

noncomputable section

namespace Work.HP.Q44Main

/-- In the regime `Δ ≤ M⁵³` the `CL`-term already fits: `Z^{9/2}·Z^{3/2} = Z⁶` supplies the
`Z⁶Δ²` piece and the remaining factor `Δ` is the `min(Δ,M⁵³)`. -/
private lemma min_compare_good1 (CL Z Δ : ℝ) (hCL : 0 < CL) (hZ : 0 < Z) (hΔ : 0 < Δ) :
    CL * Z ^ (6:ℝ) * Δ ^ (3:ℝ) ≤
      CL * (Z ^ ((9:ℝ)/2) * Δ ^ (2:ℝ) * (Z ^ ((3:ℝ)/2) + Δ ^ ((3:ℝ)/2)) * Δ) := by
  have hZr : Z ^ ((9:ℝ)/2) * Z ^ ((3:ℝ)/2) = Z ^ (6:ℝ) := by
    rw [← Real.rpow_add hZ]; norm_num
  have hD : Δ ^ (2:ℝ) * Δ = Δ ^ (3:ℝ) := by
    have h := Real.rpow_add hΔ (2:ℝ) (1:ℝ)
    rw [Real.rpow_one] at h
    rw [show (2:ℝ) + 1 = (3:ℝ) by norm_num] at h
    exact h.symm
  have hkey : Z ^ (6:ℝ) * Δ ^ (3:ℝ)
      ≤ Z ^ ((9:ℝ)/2) * Δ ^ (2:ℝ) * (Z ^ ((3:ℝ)/2) + Δ ^ ((3:ℝ)/2)) * Δ := by
    have hexp : Z ^ ((9:ℝ)/2) * Δ ^ (2:ℝ) * (Z ^ ((3:ℝ)/2) + Δ ^ ((3:ℝ)/2)) * Δ
        = Z ^ ((9:ℝ)/2) * Δ ^ (2:ℝ) * Z ^ ((3:ℝ)/2) * Δ
          + Z ^ ((9:ℝ)/2) * Δ ^ (2:ℝ) * Δ ^ ((3:ℝ)/2) * Δ := by ring
    have hA : Z ^ ((9:ℝ)/2) * Δ ^ (2:ℝ) * Z ^ ((3:ℝ)/2) * Δ = Z ^ (6:ℝ) * Δ ^ (3:ℝ) := by
      rw [show Z ^ ((9:ℝ)/2) * Δ ^ (2:ℝ) * Z ^ ((3:ℝ)/2) * Δ
            = (Z ^ ((9:ℝ)/2) * Z ^ ((3:ℝ)/2)) * (Δ ^ (2:ℝ) * Δ) by ring, hZr, hD]
    have hB : 0 ≤ Z ^ ((9:ℝ)/2) * Δ ^ (2:ℝ) * Δ ^ ((3:ℝ)/2) * Δ := by positivity
    rw [hexp, hA]; linarith
  calc CL * Z ^ (6:ℝ) * Δ ^ (3:ℝ)
      = CL * (Z ^ (6:ℝ) * Δ ^ (3:ℝ)) := by ring
    _ ≤ CL * (Z ^ ((9:ℝ)/2) * Δ ^ (2:ℝ) * (Z ^ ((3:ℝ)/2) + Δ ^ ((3:ℝ)/2)) * Δ) :=
        mul_le_mul_of_nonneg_left hkey hCL.le

theorem min_compare (CL CL1 : ℝ) (hCL : 0 < CL) (hCL1 : 0 < CL1) :
    ∃ K : ℝ, 0 < K ∧ ∀ Z Δ M : ℝ, 1 ≤ Z → 1 ≤ Δ → 1 ≤ M →
      min (CL * Z ^ (6:ℝ) * Δ ^ (3:ℝ) * Real.log (2 * Δ) ^ 2)
          (CL1 * (M ^ (70:ℝ) * Z ^ (4:ℝ) * Δ ^ ((7:ℝ)/2) + M ^ (70:ℝ) * Z ^ (6:ℝ) * Δ ^ ((3:ℝ)/2)
            + M ^ (70:ℝ) * Z ^ (4:ℝ) * Δ ^ ((11:ℝ)/3) + M ^ (40:ℝ) * Z ^ (4:ℝ) * Δ ^ (3:ℝ)
            + M ^ (40:ℝ) * Z ^ (6:ℝ) * Δ ^ (2:ℝ)) * Real.log (2 * Δ) ^ 2)
        ≤ K * Z ^ ((9:ℝ)/2) * Δ ^ (2:ℝ) * (Z ^ ((3:ℝ)/2) + Δ ^ ((3:ℝ)/2))
            * Real.log (2 * Δ) ^ 2 * min Δ (M ^ (53:ℝ)) := by
  refine ⟨max CL (5 * CL1), lt_of_lt_of_le hCL (le_max_left _ _), ?_⟩
  intro Z Δ M hZ hΔ hM
  have hZpos : 0 < Z := by linarith
  have hΔpos : 0 < Δ := by linarith
  have hMpos : 0 < M := by linarith
  set L2 : ℝ := Real.log (2 * Δ) ^ 2 with hL2
  have hL2nn : 0 ≤ L2 := by rw [hL2]; exact sq_nonneg _
  set S : ℝ := M ^ (70:ℝ) * Z ^ (4:ℝ) * Δ ^ ((7:ℝ)/2) + M ^ (70:ℝ) * Z ^ (6:ℝ) * Δ ^ ((3:ℝ)/2)
            + M ^ (70:ℝ) * Z ^ (4:ℝ) * Δ ^ ((11:ℝ)/3) + M ^ (40:ℝ) * Z ^ (4:ℝ) * Δ ^ (3:ℝ)
            + M ^ (40:ℝ) * Z ^ (6:ℝ) * Δ ^ (2:ℝ) with hS
  have hRnn : 0 ≤ Z ^ ((9:ℝ)/2) * Δ ^ (2:ℝ) * (Z ^ ((3:ℝ)/2) + Δ ^ ((3:ℝ)/2)) * min Δ (M ^ (53:ℝ)) :=
    mul_nonneg (mul_nonneg (mul_nonneg (Real.rpow_nonneg hZpos.le _) (Real.rpow_nonneg hΔpos.le _))
      (add_nonneg (Real.rpow_nonneg hZpos.le _) (Real.rpow_nonneg hΔpos.le _)))
      (le_min hΔpos.le (Real.rpow_nonneg hMpos.le _))
  have hcore : min (CL * Z ^ (6:ℝ) * Δ ^ (3:ℝ)) (CL1 * S)
      ≤ max CL (5 * CL1)
        * (Z ^ ((9:ℝ)/2) * Δ ^ (2:ℝ) * (Z ^ ((3:ℝ)/2) + Δ ^ ((3:ℝ)/2)) * min Δ (M ^ (53:ℝ))) := by
    rcases le_total Δ (M ^ (53:ℝ)) with hle | hge
    · have hmin : min Δ (M ^ (53:ℝ)) = Δ := min_eq_left hle
      have hAc : CL * Z ^ (6:ℝ) * Δ ^ (3:ℝ)
          ≤ CL * (Z ^ ((9:ℝ)/2) * Δ ^ (2:ℝ) * (Z ^ ((3:ℝ)/2) + Δ ^ ((3:ℝ)/2)) * min Δ (M ^ (53:ℝ))) := by
        rw [hmin]; exact min_compare_good1 CL Z Δ hCL hZpos hΔpos
      calc min (CL * Z ^ (6:ℝ) * Δ ^ (3:ℝ)) (CL1 * S)
          ≤ CL * Z ^ (6:ℝ) * Δ ^ (3:ℝ) := min_le_left _ _
        _ ≤ CL * (Z ^ ((9:ℝ)/2) * Δ ^ (2:ℝ) * (Z ^ ((3:ℝ)/2) + Δ ^ ((3:ℝ)/2)) * min Δ (M ^ (53:ℝ))) := hAc
        _ ≤ max CL (5 * CL1) * (Z ^ ((9:ℝ)/2) * Δ ^ (2:ℝ) * (Z ^ ((3:ℝ)/2) + Δ ^ ((3:ℝ)/2)) * min Δ (M ^ (53:ℝ))) :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) hRnn
    · have hMle : M ^ (53:ℝ) ≤ Δ := hge
      have hmin : min Δ (M ^ (53:ℝ)) = M ^ (53:ℝ) := min_eq_right hMle
      by_cases hZ3 : Z ^ (3:ℝ) ≤ M ^ (106:ℝ) * Δ
      · have hAc : CL * Z ^ (6:ℝ) * Δ ^ (3:ℝ)
            ≤ CL * (Z ^ ((9:ℝ)/2) * Δ ^ (2:ℝ) * (Z ^ ((3:ℝ)/2) + Δ ^ ((3:ℝ)/2)) * min Δ (M ^ (53:ℝ))) := by
          rw [hmin]; exact min_compare_good2 CL Z Δ M hZ hΔ hM hCL hZ3
        calc min (CL * Z ^ (6:ℝ) * Δ ^ (3:ℝ)) (CL1 * S)
            ≤ CL * Z ^ (6:ℝ) * Δ ^ (3:ℝ) := min_le_left _ _
          _ ≤ CL * (Z ^ ((9:ℝ)/2) * Δ ^ (2:ℝ) * (Z ^ ((3:ℝ)/2) + Δ ^ ((3:ℝ)/2)) * min Δ (M ^ (53:ℝ))) := hAc
          _ ≤ max CL (5 * CL1) * (Z ^ ((9:ℝ)/2) * Δ ^ (2:ℝ) * (Z ^ ((3:ℝ)/2) + Δ ^ ((3:ℝ)/2)) * min Δ (M ^ (53:ℝ))) :=
              mul_le_mul_of_nonneg_right (le_max_left _ _) hRnn
      · have hZ3' : M ^ (106:ℝ) * Δ ≤ Z ^ (3:ℝ) := (not_le.mp hZ3).le
        have hB : CL1 * S
            ≤ (5 * CL1) * (Z ^ ((9:ℝ)/2) * Δ ^ (2:ℝ) * (Z ^ ((3:ℝ)/2) + Δ ^ ((3:ℝ)/2)) * min Δ (M ^ (53:ℝ))) := by
          rw [hmin, hS]; exact min_compare_good3 CL1 Z Δ M hZ hΔ hM hCL1 hMle hZ3'
        calc min (CL * Z ^ (6:ℝ) * Δ ^ (3:ℝ)) (CL1 * S)
            ≤ CL1 * S := min_le_right _ _
          _ ≤ (5 * CL1) * (Z ^ ((9:ℝ)/2) * Δ ^ (2:ℝ) * (Z ^ ((3:ℝ)/2) + Δ ^ ((3:ℝ)/2)) * min Δ (M ^ (53:ℝ))) := hB
          _ ≤ max CL (5 * CL1) * (Z ^ ((9:ℝ)/2) * Δ ^ (2:ℝ) * (Z ^ ((3:ℝ)/2) + Δ ^ ((3:ℝ)/2)) * min Δ (M ^ (53:ℝ))) :=
              mul_le_mul_of_nonneg_right (le_max_right _ _) hRnn
  calc min (CL * Z ^ (6:ℝ) * Δ ^ (3:ℝ) * L2) (CL1 * S * L2)
      = min (CL * Z ^ (6:ℝ) * Δ ^ (3:ℝ)) (CL1 * S) * L2 :=
        (min_mul_of_nonneg (CL * Z ^ (6:ℝ) * Δ ^ (3:ℝ)) (CL1 * S) hL2nn).symm
    _ ≤ (max CL (5 * CL1) * (Z ^ ((9:ℝ)/2) * Δ ^ (2:ℝ) * (Z ^ ((3:ℝ)/2) + Δ ^ ((3:ℝ)/2)) * min Δ (M ^ (53:ℝ)))) * L2 :=
        mul_le_mul_of_nonneg_right hcore hL2nn
    _ = max CL (5 * CL1) * Z ^ ((9:ℝ)/2) * Δ ^ (2:ℝ) * (Z ^ ((3:ℝ)/2) + Δ ^ ((3:ℝ)/2))
          * L2 * min Δ (M ^ (53:ℝ)) := by ring

end Work.HP.Q44Main
