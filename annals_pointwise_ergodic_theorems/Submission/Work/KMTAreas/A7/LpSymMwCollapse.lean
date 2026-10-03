/-
# The collapse identity `symC − symM_win = symD` at the repaired window

The window-parametrised §6 model symbol `symMWin ρ P (loMixedU …) N 0 l₂ k₁ k₂` of the mixed range
collapses (as in the paper's `mod-approx`) onto the single-fibre sum of `m_Ẑ · m̃_{N,ℝ}` against the
two §5 bumps; subtracting it from the concrete symbol `symC` leaves the aliasing-fibre sum `symD` of
the paper's `M₀ = weylAvg − m_Ẑ m̃_{N,ℝ}`.  This is the window-parametrised analogue of
`Work.KMTPlan.A6.symC_sub_symM_eq_symD_final`, assembled from the same four inputs
(`symp_symC_eq_fibre_sum`, `weylAvg_shift_eq_halfSym`, `symMWin_collapse`,
`symp_integral_periodize_modulated_bumps`).
-/
import Mathlib
import Submission.Work.KMTAreas.A7.LoMixedWinDefs

set_option autoImplicit false
set_option maxHeartbeats 8000000

namespace Work.KMTPlan.A6

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open Work.Analysis.IonescuWainger
open Work.KMTAreas.A7
open Work.KMTContract

/-- **The collapse identity for the repaired window.**  For `1 ≤ P.natDegree`, on the band
`max k₁ k₂ + 2u + 1 ≤ Log N` (`u = loMixedU ρ P.natDegree l₂ k₁ k₂`) and under the non-aliasing of
the exact-height frequency sets at the window radii, the concrete symbol minus the
window-parametrised model symbol is the symbol difference `symD`. -/
theorem lpSymC_sub_symMWin_eq_symD (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (P : ℤ[X])
    (N l₂ k₁ k₂ : ℕ) (x y : ℝ) (hd : 1 ≤ P.natDegree) (hN : 1 ≤ N)
    (hC2 : max k₁ k₂ + 2 * Work.KMTAreas.A7.loMixedU ρ P.natDegree l₂ k₁ k₂ + 1
      ≤ (Work.Analysis.EndVar.logN N).toNat)
    (hNA₁ : NonAliasing
      (-(2 * (Work.KMTAreas.A7.loMixedU ρ P.natDegree l₂ k₁ k₂ : ℤ))) (diffFreqs ρ 0))
    (hNA₂ : NonAliasing
      (-((P.natDegree : ℤ) * 2 * (Work.KMTAreas.A7.loMixedU ρ P.natDegree l₂ k₁ k₂ : ℤ)))
      (diffFreqs ρ l₂)) :
    symC ρ P N 0 l₂ k₁ k₂ x y
      - symMWin ρ P (Work.KMTAreas.A7.loMixedU ρ P.natDegree l₂ k₁ k₂) N 0 l₂ k₁ k₂ x y
      = symD ρ P N 0 l₂ k₁ k₂ x y := by
  set u : ℕ := Work.KMTAreas.A7.loMixedU ρ P.natDegree l₂ k₁ k₂ with hu
  have hu1 : 1 ≤ u := by
    rw [hu]
    exact le_trans (symp_one_le_uScale ρ hρ.le (max (max 0 l₂) (max k₁ k₂)))
      (Work.KMTAreas.A7.uScale_le_loMixedU ρ P.natDegree l₂ k₁ k₂)
  have hk₁ : k₁ + 2 * u + 1 ≤ (Work.Analysis.EndVar.logN N).toNat := by
    rw [hu]
    exact le_trans (by omega : k₁ + 2 * Work.KMTAreas.A7.loMixedU ρ P.natDegree l₂ k₁ k₂ + 1
      ≤ max k₁ k₂ + 2 * Work.KMTAreas.A7.loMixedU ρ P.natDegree l₂ k₁ k₂ + 1) hC2
  have hk₂ : k₂ + 2 * u + 1 ≤ (Work.Analysis.EndVar.logN N).toNat := by
    rw [hu]
    exact le_trans (by omega : k₂ + 2 * Work.KMTAreas.A7.loMixedU ρ P.natDegree l₂ k₁ k₂ + 1
      ≤ max k₁ k₂ + 2 * Work.KMTAreas.A7.loMixedU ρ P.natDegree l₂ k₁ k₂ + 1) hC2
  -- (1) the concrete symbol in the `weylAvg` fibre form
  have hC' : symC ρ P N 0 l₂ k₁ k₂ x y
      = ∑ γ₁ ∈ diffFreqs ρ 0, ∑ γ₂ ∈ diffFreqs ρ l₂, ∑' m₁ : ℤ, ∑' m₂ : ℤ,
          weylAvg P N γ₁ γ₂ (x - gamR γ₁ + (m₁ : ℝ)) (y - gamR γ₂ + (m₂ : ℝ))
            * varphiN N k₁ (x - gamR γ₁ + (m₁ : ℝ))
            * varphitildeN P.natDegree N k₂ (y - gamR γ₂ + (m₂ : ℝ)) := by
    rw [symp_symC_eq_fibre_sum ρ P N 0 l₂ k₁ k₂ x y]
    refine Finset.sum_congr rfl fun γ₁ _ => Finset.sum_congr rfl fun γ₂ _ => ?_
    refine tsum_congr fun m₁ => tsum_congr fun m₂ => ?_
    rw [← weylAvg_shift_eq_halfSym P N γ₁ γ₂ x y m₁ m₂]
  -- (2) the model symbol in the same fibre form
  have hsM : symMWin ρ P u N 0 l₂ k₁ k₂ = fun x y : ℝ => ∫ t in (1 / 2 : ℝ)..1,
      symSeq2 (Work.KMTAreas.A7.arithKerMWin ρ P u 0 l₂) x y
        * symSeq (tmKer ρ 0 (varphiNt N k₁ t)) x
        * symSeq (tmKer ρ l₂ (varphitildeNt P P.natDegree N k₂ t)) y := rfl
  have hM : symMWin ρ P u N 0 l₂ k₁ k₂ x y
      = ∑ β₁ ∈ diffFreqs ρ 0, ∑ β₂ ∈ diffFreqs ρ l₂, ∑' m₁ : ℤ, ∑' m₂ : ℤ,
          mZ P (arithQ ρ (max 0 l₂)) β₁ β₂
            * mTilde P N (x - gamR β₁ + (m₁ : ℝ)) (y - gamR β₂ + (m₂ : ℝ))
            * varphiN N k₁ (x - gamR β₁ + (m₁ : ℝ))
            * varphitildeN P.natDegree N k₂ (y - gamR β₂ + (m₂ : ℝ)) := by
    rw [hsM]
    simp only
    rw [intervalIntegral.integral_congr (fun t _ =>
      symMWin_collapse ρ P u N 0 l₂ k₁ k₂ x y hu1 hd (by rw [hu]; exact hC2) hNA₁ hNA₂ t)]
    rw [intervalIntegral.integral_finsetSum]
    · refine Finset.sum_congr rfl fun β₁ _ => ?_
      rw [intervalIntegral.integral_finsetSum]
      · refine Finset.sum_congr rfl fun β₂ _ => ?_
        rw [show (fun t : ℝ => mZ P (arithQ ρ (max 0 l₂)) β₁ β₂
              * periodize (varphiNt N k₁ t) ((x : ℝ) - β₁)
              * periodize (varphitildeNt P P.natDegree N k₂ t) ((y : ℝ) - β₂))
            = fun t : ℝ => mZ P (arithQ ρ (max 0 l₂)) β₁ β₂
              * (periodize (varphiNt N k₁ t) ((x : ℝ) - β₁)
                * periodize (varphitildeNt P P.natDegree N k₂ t) ((y : ℝ) - β₂)) from
            funext fun t => by ring]
        rw [intervalIntegral.integral_const_mul,
          symp_integral_periodize_modulated_bumps P N k₁ k₂ β₁ β₂ x y, ← tsum_mul_left]
        refine tsum_congr fun m₁ => ?_
        rw [← tsum_mul_left]
        refine tsum_congr fun m₂ => ?_
        ring
      · intro β₂ _
        exact ((continuous_const.mul
            (symp_continuous_periodize_varphiNt N k₁ u hu1 hk₁ ((x : ℝ) - β₁))).mul
          (symp_continuous_periodize_varphitildeNt P P.natDegree N k₂ u hd hu1 hk₂
            ((y : ℝ) - β₂))).intervalIntegrable _ _
    · intro β₁ _
      refine Continuous.intervalIntegrable ?_ _ _
      refine continuous_finsetSum _ fun β₂ _ => ?_
      exact (continuous_const.mul
        (symp_continuous_periodize_varphiNt N k₁ u hu1 hk₁ ((x : ℝ) - β₁))).mul
        (symp_continuous_periodize_varphitildeNt P P.natDegree N k₂ u hd hu1 hk₂
          ((y : ℝ) - β₂))
  -- (3) subtract, fibre by fibre
  rw [hC', hM, symD, symp_sum_sum_sub]
  refine Finset.sum_congr rfl fun γ₁ hγ₁ => Finset.sum_congr rfl fun γ₂ hγ₂ => ?_
  have hmz := symp_mZ_eq_perQ ρ hρ hρ1 P 0 l₂ hγ₁ hγ₂
  have hφsum : Summable fun m₁ : ℤ => ‖varphiN N k₁ (x - gamR γ₁ + (m₁ : ℝ))‖ :=
    (symp_summable_varphiN_orbit N k₁ (x - gamR γ₁)).norm
  have hψsum : Summable fun m₂ : ℤ => ‖varphitildeN P.natDegree N k₂ (y - gamR γ₂ + (m₂ : ℝ))‖ :=
    (symp_summable_varphitildeN_orbit P.natDegree N k₂ (y - gamR γ₂)).norm
  have hbnd_a : ∀ m₁ m₂ : ℤ,
      ‖weylAvg P N γ₁ γ₂ (x - gamR γ₁ + (m₁ : ℝ)) (y - gamR γ₂ + (m₂ : ℝ))
        * varphiN N k₁ (x - gamR γ₁ + (m₁ : ℝ))
        * varphitildeN P.natDegree N k₂ (y - gamR γ₂ + (m₂ : ℝ))‖
      ≤ 2 * ‖varphiN N k₁ (x - gamR γ₁ + (m₁ : ℝ))‖
        * ‖varphitildeN P.natDegree N k₂ (y - gamR γ₂ + (m₂ : ℝ))‖ := by
    intro m₁ m₂
    calc ‖weylAvg P N γ₁ γ₂ (x - gamR γ₁ + (m₁ : ℝ)) (y - gamR γ₂ + (m₂ : ℝ))
          * varphiN N k₁ (x - gamR γ₁ + (m₁ : ℝ))
          * varphitildeN P.natDegree N k₂ (y - gamR γ₂ + (m₂ : ℝ))‖
        = ‖weylAvg P N γ₁ γ₂ (x - gamR γ₁ + (m₁ : ℝ)) (y - gamR γ₂ + (m₂ : ℝ))‖
          * ‖varphiN N k₁ (x - gamR γ₁ + (m₁ : ℝ))‖
          * ‖varphitildeN P.natDegree N k₂ (y - gamR γ₂ + (m₂ : ℝ))‖ := by
          rw [norm_mul, norm_mul]
      _ ≤ 2 * ‖varphiN N k₁ (x - gamR γ₁ + (m₁ : ℝ))‖
          * ‖varphitildeN P.natDegree N k₂ (y - gamR γ₂ + (m₂ : ℝ))‖ := by
          have h₁ := symp_norm_weylAvg_le_two P N hN γ₁ γ₂
            (x - gamR γ₁ + (m₁ : ℝ)) (y - gamR γ₂ + (m₂ : ℝ))
          have h₂ : (0 : ℝ) ≤ ‖varphiN N k₁ (x - gamR γ₁ + (m₁ : ℝ))‖ := norm_nonneg _
          have h₃ : (0 : ℝ) ≤ ‖varphitildeN P.natDegree N k₂ (y - gamR γ₂ + (m₂ : ℝ))‖ :=
            norm_nonneg _
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h₁ h₂) h₃
  have hbnd_b : ∀ m₁ m₂ : ℤ,
      ‖mZ P (arithQ ρ (max 0 l₂)) γ₁ γ₂ * mTilde P N (x - gamR γ₁ + (m₁ : ℝ)) (y - gamR γ₂ + (m₂ : ℝ))
        * varphiN N k₁ (x - gamR γ₁ + (m₁ : ℝ))
        * varphitildeN P.natDegree N k₂ (y - gamR γ₂ + (m₂ : ℝ))‖
      ≤ 2 * ‖varphiN N k₁ (x - gamR γ₁ + (m₁ : ℝ))‖
        * ‖varphitildeN P.natDegree N k₂ (y - gamR γ₂ + (m₂ : ℝ))‖ := by
    intro m₁ m₂
    calc ‖mZ P (arithQ ρ (max 0 l₂)) γ₁ γ₂ * mTilde P N (x - gamR γ₁ + (m₁ : ℝ)) (y - gamR γ₂ + (m₂ : ℝ))
          * varphiN N k₁ (x - gamR γ₁ + (m₁ : ℝ))
          * varphitildeN P.natDegree N k₂ (y - gamR γ₂ + (m₂ : ℝ))‖
        = ‖mZ P (arithQ ρ (max 0 l₂)) γ₁ γ₂‖
          * ‖mTilde P N (x - gamR γ₁ + (m₁ : ℝ)) (y - gamR γ₂ + (m₂ : ℝ))‖
          * ‖varphiN N k₁ (x - gamR γ₁ + (m₁ : ℝ))‖
          * ‖varphitildeN P.natDegree N k₂ (y - gamR γ₂ + (m₂ : ℝ))‖ := by
          rw [norm_mul, norm_mul, norm_mul]
      _ ≤ 2 * ‖varphiN N k₁ (x - gamR γ₁ + (m₁ : ℝ))‖
          * ‖varphitildeN P.natDegree N k₂ (y - gamR γ₂ + (m₂ : ℝ))‖ := by
          have h₁ := symp_norm_mZ_le_one P (arithQ ρ (max 0 l₂)) γ₁ γ₂
          have h₂ := symp_norm_mTilde_le_one P N (x - gamR γ₁ + (m₁ : ℝ))
            (y - gamR γ₂ + (m₂ : ℝ))
          have h₃ : (0 : ℝ) ≤ ‖varphiN N k₁ (x - gamR γ₁ + (m₁ : ℝ))‖ := norm_nonneg _
          have h₄ : (0 : ℝ) ≤ ‖varphitildeN P.natDegree N k₂ (y - gamR γ₂ + (m₂ : ℝ))‖ :=
            norm_nonneg _
          have h₅ : ‖mZ P (arithQ ρ (max 0 l₂)) γ₁ γ₂‖
              * ‖mTilde P N (x - gamR γ₁ + (m₁ : ℝ)) (y - gamR γ₂ + (m₂ : ℝ))‖ ≤ 2 := by
            nlinarith [h₁, h₂, norm_nonneg (mZ P (arithQ ρ (max 0 l₂)) γ₁ γ₂),
              norm_nonneg (mTilde P N (x - gamR γ₁ + (m₁ : ℝ)) (y - gamR γ₂ + (m₂ : ℝ)))]
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h₅ h₃) h₄
  rw [symp_tsum_tsum_sub_of_bound (hφsum.mul_left 2) hψsum hbnd_a hbnd_b]
  refine tsum_congr fun m₁ => tsum_congr fun m₂ => ?_
  rw [M0, ← hmz]
  ring

end Work.KMTPlan.A6
