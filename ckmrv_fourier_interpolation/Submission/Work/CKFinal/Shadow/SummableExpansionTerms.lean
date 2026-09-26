import Submission.Work.FunctionalEquations.SummableExpansionTerms
import Submission.Work.CKFinal.Shadow.Util
import Submission.Work.CKFinal.Shadow.Basic

open scoped ContDiff
set_option linter.dupNamespace false

namespace Work.CKFinal.Shadow

namespace Work.FunctionalEquations
export _root_.Work.FunctionalEquations (SeminormGrowthOfRadialGrowth)
end Work.FunctionalEquations
namespace Work.FunctionalEquations
export _root_.Work.FunctionalEquations (summable_mul_dirichletTerm)
end Work.FunctionalEquations
namespace Work.FunctionalEquations
export _root_.Work.FunctionalEquations (summable_rate_mul_dirichletTerm)
end Work.FunctionalEquations

namespace Work.FunctionalEquations

open LeanEval.Analysis.CKMRVInterpolation Work.Core Work.FE Filter Topology
open scoped FourierTransform SchwartzMap

/-- The norm of a real number seen as a complex number. -/
private lemma norm_ofReal_complex (r : ℝ) : ‖(r : ℂ)‖ = |r| := by
  have h : ‖(r : ℂ)‖ ^ 2 = |r| ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_ofReal, sq_abs]; ring
  nlinarith [norm_nonneg (r : ℂ), abs_nonneg r]

/-- A polynomial weight times a geometric sequence with ratio `t ∈ [0,1)` is summable. -/
private lemma summable_add_one_pow_mul_geometric {N : ℕ} {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
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

theorem SummableExpansionTerms {n : ℕ} [NeZero n] (S : InterpolationSolution n) (τ : ℂ)
    (hτ : 0 < τ.im) (x : E n) :
    Summable (fun m : Set.Ici (1 : ℕ) => (S.basis (m, 0)).1 x * dirichletTerm m.1 τ) ∧
    Summable (fun m : Set.Ici (1 : ℕ) => (S.basis (m, 1)).1 x * dirichletTerm m.1 τ) ∧
    Summable (fun m : Set.Ici (1 : ℕ) =>
      (rate m.1 : ℂ) * (S.basis (m, 2)).1 x * dirichletTerm m.1 τ) ∧
    Summable (fun m : Set.Ici (1 : ℕ) =>
      (rate m.1 : ℂ) * (S.basis (m, 3)).1 x * dirichletTerm m.1 τ) := by
  obtain ⟨C, N, hC, hbound⟩ := SeminormGrowthOfRadialGrowth S.basis S.growth_radial 0 0
  have hb : ∀ (j : Fin 4) (m : Set.Ici (1 : ℕ)),
      ‖(S.basis (m, j)).1 x‖ ≤ C * ((m.1 : ℝ) + 1) ^ N := fun j m =>
    le_trans (SchwartzMap.norm_le_seminorm ℂ _ x) (hbound m j)
  exact ⟨summable_mul_dirichletTerm hC (fun m => hb 0 m) τ hτ,
    summable_mul_dirichletTerm hC (fun m => hb 1 m) τ hτ,
    summable_rate_mul_dirichletTerm hC (fun m => hb 2 m) τ hτ,
    summable_rate_mul_dirichletTerm hC (fun m => hb 3 m) τ hτ⟩

end Work.FunctionalEquations


end Work.CKFinal.Shadow
