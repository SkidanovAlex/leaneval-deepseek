import Mathlib
import Submission.Work.FunctionalEquations.Gap
import Submission.Work.FunctionalEquations.SeminormGrowthOfRadialGrowth

namespace Work.FunctionalEquations

open LeanEval.Analysis.CKMRVInterpolation Work.Core Work.FE Filter Topology
open scoped FourierTransform SchwartzMap

/-- A polynomial weight times a geometric sequence with ratio `t ∈ [0,1)` is summable. -/
private lemma summable_nat_add_one_pow_mul_geometric {N : ℕ} {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    Summable fun n : ℕ => ((n : ℝ) + 1) ^ N * t ^ n := by
  have htabs : ‖t‖ < 1 := by rw [Real.norm_eq_abs, abs_of_nonneg ht0]; exact ht1
  have hgeom : Summable fun n : ℕ => (n : ℝ) ^ N * t ^ n :=
    summable_pow_mul_geometric_of_norm_lt_one N htabs
  have hgeom1 : Summable fun n : ℕ => t ^ n := summable_geometric_of_norm_lt_one htabs
  have hmain : Summable fun n : ℕ => (2 : ℝ) ^ N * (((n : ℝ) ^ N * t ^ n) + t ^ n) :=
    (hgeom.add hgeom1).mul_left _
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) hmain
  have hb : ((n : ℝ) + 1) ^ N ≤ (2 : ℝ) ^ N * ((n : ℝ) ^ N + 1) := by
    have hmax : ((n : ℝ) + 1) ≤ 2 * max (n : ℝ) 1 := by
      rcases le_or_gt 1 (n : ℝ) with hh | hh
      · rw [max_eq_left hh]; linarith
      · rw [max_eq_right hh.le]; linarith
    have hstep : ((n : ℝ) + 1) ^ N ≤ (2 * max (n : ℝ) 1) ^ N :=
      pow_le_pow_left₀ (by positivity) hmax N
    have hmaxN : (max (n : ℝ) 1) ^ N ≤ (n : ℝ) ^ N + 1 := by
      rcases le_or_gt 1 (n : ℝ) with hh | hh
      · rw [max_eq_left hh]
        have : (0 : ℝ) ≤ (n : ℝ) ^ N := by positivity
        linarith
      · rw [max_eq_right hh.le]; simp
    calc ((n : ℝ) + 1) ^ N ≤ (2 * max (n : ℝ) 1) ^ N := hstep
      _ = (2 : ℝ) ^ N * (max (n : ℝ) 1) ^ N := by rw [mul_pow]
      _ ≤ (2 : ℝ) ^ N * ((n : ℝ) ^ N + 1) :=
          mul_le_mul_of_nonneg_left hmaxN (by positivity)
  calc ((n : ℝ) + 1) ^ N * t ^ n ≤ ((2 : ℝ) ^ N * ((n : ℝ) ^ N + 1)) * t ^ n :=
        mul_le_mul_of_nonneg_right hb (by positivity)
    _ = (2 : ℝ) ^ N * (((n : ℝ) ^ N * t ^ n) + t ^ n) := by ring

theorem SummableSchwartzBasisSmul {n : ℕ} [NeZero n] {k₀ : ℕ}
    (basis : SampleIdx k₀ → RSch n)
    (hgrowth : ∀ k ℓ : ℕ, ∃ C : ℝ, ∃ N : ℕ, 0 ≤ C ∧
      ∀ (m : Set.Ici k₀) (j : Fin 4) (x : E n),
        ‖x‖ ^ k * ‖radialDeriv ℓ (⇑(basis (m, j)).1) x‖ ≤ C * ((m.1 : ℝ) + 1) ^ N)
    {c : Set.Ici k₀ → ℂ} {K : ℝ} {N : ℕ} {t : ℝ}
    (hK : 0 ≤ K) (ht0 : 0 ≤ t) (ht1 : t < 1)
    (hc : ∀ m : Set.Ici k₀, ‖c m‖ ≤ K * ((m.1 : ℝ) + 1) ^ N * t ^ (m.1))
    (j : Fin 4) :
    ∀ k l : ℕ, Summable fun m : Set.Ici k₀ =>
      (SchwartzMap.seminorm ℂ k l) ((c m) • (basis (m, j)).1) := by
  intro k l
  -- Polynomial growth of the full Schwartz seminorms of the basis.
  obtain ⟨C, N', hC0, hbound⟩ := SeminormGrowthOfRadialGrowth basis hgrowth k l
  -- The geometric majorant is summable.
  have hw : Summable fun m : Set.Ici k₀ =>
      ((m.1 : ℝ) + 1) ^ (N + N') * t ^ (m.1) :=
    (summable_nat_add_one_pow_mul_geometric ht0 ht1).subtype _
  have hmaj : Summable fun m : Set.Ici k₀ =>
      (K * C) * (((m.1 : ℝ) + 1) ^ (N + N') * t ^ (m.1)) := hw.mul_left _
  refine Summable.of_nonneg_of_le (fun m => by positivity) (fun m => ?_) hmaj
  rw [map_smul_eq_mul]
  calc ‖c m‖ * (SchwartzMap.seminorm ℂ k l) (basis (m, j)).1
      ≤ (K * ((m.1 : ℝ) + 1) ^ N * t ^ (m.1)) * (C * ((m.1 : ℝ) + 1) ^ N') :=
        mul_le_mul (hc m) (hbound m j) (by positivity)
          (mul_nonneg (mul_nonneg hK (pow_nonneg (by positivity) _)) (pow_nonneg ht0 _))
    _ = K * C * (((m.1 : ℝ) + 1) ^ (N + N') * t ^ (m.1)) := by rw [pow_add]; ring

end Work.FunctionalEquations
