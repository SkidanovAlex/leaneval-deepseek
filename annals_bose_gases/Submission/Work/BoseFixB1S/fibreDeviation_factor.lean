import ChallengeDeps
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Submission.Work.BoseFixB1.Up.Core
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB1S

/-- **Support of the small-box cutoff in the big cube.**  The two-factor cutoff
`χ_{B(u)} = χ(·/ℓ)·χ_M(·/(ℓd) − u)` vanishes off the cube `acube ℓ`: the `ℓ`-scale
factor `χ(·/ℓ)` already vanishes outside the ball of radius `ℓ/2`, and that ball is
contained in the cube.  (No hypothesis on `M` is needed: the support is carried by the
corpus bump alone.) -/
lemma chiSmallB_eq_zero_of_notMem_acube {M : ℕ} {ℓ d : ℝ} (hℓ : 0 < ℓ)
    (u : EuclideanSpace ℝ (Fin 3)) {y : EuclideanSpace ℝ (Fin 3)}
    (hy : y ∉ Submission.BoseGases.acube ℓ) :
    Submission.BoseGases.chiSmallB M ℓ d u y = 0 := by
  have hmem : ¬ (∀ m : Fin 3, y m ∈ Set.Icc (-ℓ / 2) (ℓ / 2)) := hy
  obtain ⟨m, hm⟩ := not_forall.mp hmem
  rw [Set.mem_Icc, not_and_or] at hm
  have habs : ℓ / 2 < |y m| := by
    rcases hm with hm | hm
    · rw [not_le] at hm
      rw [abs_of_neg (by linarith)]; linarith
    · rw [not_le] at hm
      rw [abs_of_pos (by linarith)]; linarith
  have hnorm : ℓ / 2 < ‖y‖ := lt_of_lt_of_le habs (by simpa using PiLp.norm_apply_le y m)
  have hchi : Submission.BoseGases.chiScale ℓ y = 0 := by
    rw [Submission.BoseGases.chiScale]
    apply Submission.BoseGases.chi_eq_zero_of_half_le_norm
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hℓ)]
    have h1 : (ℓ⁻¹ : ℝ) * (ℓ / 2) = 1 / 2 := by field_simp
    calc (1 : ℝ) / 2 = ℓ⁻¹ * (ℓ / 2) := h1.symm
      _ ≤ ℓ⁻¹ * ‖y‖ := mul_le_mul_of_nonneg_left (le_of_lt hnorm) (le_of_lt (inv_pos.mpr hℓ))
  rw [Submission.BoseGases.chiSmallB, hchi, zero_mul]

theorem fibreDeviation_factor {v : EuclideanSpace ℝ (Fin 3) → ℝ}
    (h : ∃ w : EuclideanSpace ℝ (Fin 3) → ℝ,
      _root_.BoseGases.IsRadial w ∧ _root_.BoseGases.IsScatteringSolution w v)
    (M : ℕ) (ℓ d : ℝ) (hℓ : 0 < ℓ) (u : EuclideanSpace ℝ (Fin 3))
    (z : EuclideanSpace ℝ (Fin 3)) :
    Submission.BoseGases.w1Fibre ℓ (Submission.BoseGases.wSmall1Pair h M ℓ d u) z
      = Submission.BoseGases.chiSmallB M ℓ d u z
        * (∫ y : EuclideanSpace ℝ (Fin 3),
            (Submission.BoseGases.wSmallScaled M (ℓ * d) (Submission.BoseGases.g0 v h) (z - y)
              / Submission.BoseGases.convScale ℓ (z - y))
            * Submission.BoseGases.chiSmallB M ℓ d u y) := by
  unfold Submission.BoseGases.w1Fibre Submission.BoseGases.wSmall1Pair
    Submission.BoseGases.wSmallPair
  have hcongr : (∫ y in Submission.BoseGases.acube ℓ,
        Submission.BoseGases.chiSmallB M ℓ d u z
          * (Submission.BoseGases.wSmallScaled M (ℓ * d) (Submission.BoseGases.g0 v h) (z - y)
              / Submission.BoseGases.convScale ℓ (z - y))
          * Submission.BoseGases.chiSmallB M ℓ d u y)
      = ∫ y in Submission.BoseGases.acube ℓ,
          Submission.BoseGases.chiSmallB M ℓ d u z
            * ((Submission.BoseGases.wSmallScaled M (ℓ * d) (Submission.BoseGases.g0 v h) (z - y)
              / Submission.BoseGases.convScale ℓ (z - y))
              * Submission.BoseGases.chiSmallB M ℓ d u y) := by
    apply MeasureTheory.integral_congr_ae; filter_upwards with y; ring
  rw [hcongr, MeasureTheory.integral_const_mul]
  congr 1
  exact MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero (by
    intro y hy
    rw [chiSmallB_eq_zero_of_notMem_acube hℓ u hy, mul_zero])

end Work.BoseFixB1S
