import Mathlib.Probability.Distributions.SetBernoulli
import ChallengeDeps
import Submission.Prob
import Submission.Mono2

open ProbabilityTheory MeasureTheory unitInterval Set
open scoped ENNReal NNReal BigOperators unitInterval
open FractionalExpectationThresholds

attribute [local instance] Classical.propDecidable

namespace Submission
namespace FET

universe u

variable {X : Type u} [Fintype X]

/-- `p_c` is bounded above by any `pstar` whose measure is strictly above `1/2`. -/
lemma p_c_le_of_mu_gt_half {𝓕 : Set (Set X)} (h𝓕 : IsUpperSet 𝓕) (pstar : I)
    (hgt : (1 / 2 : ℝ) < mu pstar 𝓕) : (p_c 𝓕 : ℝ) ≤ (pstar : ℝ) := by
  classical
  by_cases hfib : ∃ p : I, (setBer(univ, p)).real (𝓕 : Set (Set X)) = 2⁻¹
  · rw [p_c]
    rw [dif_pos hfib]
    let pc : I := Classical.choose hfib
    have hspec : (setBer(univ, pc)).real (𝓕 : Set (Set X)) = 2⁻¹ := by
      simpa [pc] using (Classical.choose_spec hfib)
    by_contra h
    have hle' : (pstar : ℝ) < (pc : ℝ) := by
      simpa [pc] using (lt_of_not_ge h)
    have hle : (pstar : ℝ) ≤ (pc : ℝ) := le_of_lt hle'
    have hmono := mu_mono_p (𝓕 := 𝓕) h𝓕 pstar pc hle
    have hval : mu pc 𝓕 = 2⁻¹ := by
      simpa [mu] using hspec
    have hmul : mu pstar 𝓕 ≤ (2⁻¹ : ℝ) := by simpa [hval] using hmono
    have hhalf : (1 / 2 : ℝ) = (2⁻¹ : ℝ) := by norm_num
    nlinarith [hgt, hmul, hhalf]
  · rw [p_c]
    rw [dif_neg hfib]
    exact pstar.2.1

/-- `p_c` is at most one. -/
lemma p_c_le_one (𝓕 : Set (Set X)) : (p_c 𝓕 : ℝ) ≤ 1 := by
  exact (p_c 𝓕).2.2

end FET
end Submission
