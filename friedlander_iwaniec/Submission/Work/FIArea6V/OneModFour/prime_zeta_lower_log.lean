import Mathlib
import Mathlib.Analysis.PSeries
import Submission.Commons.NumberTheory.Mertens.primeZeta_pole
import Submission.Commons.NumberTheory.Mertens.primeZetaSum_eq_primeZetaLog_sub
import Submission.Commons.NumberTheory.Mertens.exp_primeZetaLog_eq_riemannZeta_re
import Submission.Commons.NumberTheory.FriedlanderIwaniec.chi4_prime_recip_converges
import Submission.Commons.NumberTheory.FriedlanderIwaniec.tendsto_prod_one_sub_chi4_div_prime
import Submission.Commons.Analysis.DirichletSeries.abel_tendsto_tsum_mul_rpow_conditional
import Submission.Commons.NumberTheory.DirichletCharacter.chi4_sum_div_tendsto_pi_div_four

open Filter
open scoped Topology

namespace Work.FIArea6V.OneModFour

/-- Lower bound for the prime zeta function near `s = 1`:
there is a constant `C > 0` with `Σ_p p^{-σ} ≥ log(1/(σ-1)) - C` for every `1 < σ ≤ 2`.

This is the logarithmic form of the classical pole of `Σ_p p^{-s}` at `s = 1`
(`Commons.NumberTheory.Mertens.primeZeta_pole`): the limit
`Σ_p p^{-s} + log(s-1) → -Σ_p (log(p/(p-1)) - 1/p)` as `s → 1⁺` gives the claimed
lower bound in a right neighbourhood of `1`, while away from `1` the trivial
estimate `Σ_p p^{-σ} ≥ 0` together with `log(1/(σ-1)) ≤ log(1/δ)` finishes the job. -/
theorem prime_zeta_lower_log :
    ∃ C : ℝ, 0 < C ∧ ∀ σ : ℝ, 1 < σ → σ ≤ 2 →
      Real.log (1 / (σ - 1)) - C ≤ ∑' p : Nat.Primes, ((p : ℕ) : ℝ) ^ (-σ) := by
  -- The pole at `s = 1`: the function `s ↦ Σ_p p^{-s} + log(s-1)` has a finite limit `L`.
  obtain ⟨L, hL⟩ : ∃ L : ℝ, Filter.Tendsto
      (fun s : ℝ => (∑' p : Nat.Primes, ((p : ℕ) : ℝ) ^ (-s)) + Real.log (s - 1))
      (𝓝[>] (1 : ℝ)) (𝓝 L) :=
    ⟨_, Commons.NumberTheory.Mertens.primeZeta_pole⟩
  -- Eventual lower bound by `L - 1` on the right of `1`.
  have hmem : L ∈ Set.Ioi (L - 1) := by rw [Set.mem_Ioi]; linarith
  have hg : ∀ᶠ s in 𝓝[>] (1 : ℝ),
      L - 1 < (∑' p : Nat.Primes, ((p : ℕ) : ℝ) ^ (-s)) + Real.log (s - 1) :=
    hL.eventually (isOpen_Ioi.mem_nhds hmem)
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hg
  obtain ⟨ε, hεpos, hεprop⟩ := hg
  -- A smaller radius `δ` that also keeps `1/δ ≥ 2`.
  set δ : ℝ := min ε (1 / 2) with hδdef
  have hδpos : 0 < δ := by rw [hδdef]; exact lt_min hεpos (by norm_num)
  have hδleε : δ ≤ ε := by rw [hδdef]; exact min_le_left _ _
  refine ⟨max (max (1 - L) (Real.log (1 / δ))) 1, ?_, ?_⟩
  · exact lt_of_lt_of_le one_pos (le_max_right _ _)
  · intro σ hσ1 hσ2
    rcases lt_or_ge σ (1 + δ) with hlt | hge
    · -- Inside `(1, 1+δ)`: use the limiting lower bound.
      have hdist : dist σ 1 < ε := by
        rw [Real.dist_eq]
        have habs : |σ - 1| = σ - 1 := abs_of_pos (by linarith)
        rw [habs]
        linarith
      have hbound : L - 1 < (∑' p : Nat.Primes, ((p : ℕ) : ℝ) ^ (-σ)) + Real.log (σ - 1) :=
        hεprop hdist (by rw [Set.mem_Ioi]; linarith)
      have hlog1 : Real.log (1 / (σ - 1)) = - Real.log (σ - 1) := by
        rw [one_div, Real.log_inv]
      have hCle : (1 - L) ≤ max (max (1 - L) (Real.log (1 / δ))) 1 :=
        le_trans (le_max_left _ _) (le_max_left _ _)
      have : Real.log (1 / (σ - 1)) - (1 - L) <
          ∑' p : Nat.Primes, ((p : ℕ) : ℝ) ^ (-σ) := by
        rw [hlog1]; linarith
      calc Real.log (1 / (σ - 1)) - max (max (1 - L) (Real.log (1 / δ))) 1
          ≤ Real.log (1 / (σ - 1)) - (1 - L) := by linarith
        _ ≤ ∑' p : Nat.Primes, ((p : ℕ) : ℝ) ^ (-σ) := le_of_lt this
    · -- Beyond `1 + δ`: the sum is nonnegative and `log(1/(σ-1)) ≤ log(1/δ) ≤ C`.
      have hσδ : δ ≤ σ - 1 := by linarith
      have hpos : 0 < σ - 1 := by linarith
      have hle : 1 / (σ - 1) ≤ 1 / δ := one_div_le_one_div_of_le hδpos hσδ
      have hlog := Real.log_le_log (one_div_pos.mpr hpos) hle
      have hCle : Real.log (1 / δ) ≤ max (max (1 - L) (Real.log (1 / δ))) 1 :=
        le_trans (le_max_right _ _) (le_max_left _ _)
      have hPnonneg : 0 ≤ ∑' p : Nat.Primes, ((p : ℕ) : ℝ) ^ (-σ) :=
        tsum_nonneg (fun p => Real.rpow_nonneg (by positivity) _)
      linarith

end Work.FIArea6V.OneModFour
