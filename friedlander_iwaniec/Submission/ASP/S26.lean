/-
  The companion paper's hypothesis **(R′)** for the Friedlander–Iwaniec sequence `FIa`, i.e. for
  the objects `FIr d m = A_d(m) − g(d)A(m)` of `S10` (where `A = Acount FIa`):

    `∑_{d ≤ D, ♭} τ(d)^5 |FIr d m| ≤ A(x)(log x)^{−3}`.

  The main-paper normalisation `Aseq` differs from the companion's `Acount FIa` by the pair
  `(0,0)`:  `Acount FIa m = Aseq m − 1` and `Ad FIa d m = Ad d m − 1`, whence
  `FIr d m = (Ad d m − g_d Aseq m) + (g_d − 1)`; the discrepancy `g_d − 1` contributes
  `∑_{d ≤ D,♭} τ(d)^5(g_d + 1)`, which is `≪ D(log D)^{31} ≪ x^{11/16}(log x)^{31}` — a *power*
  saving over `A(x) ≍ x^{3/4}` (because `D = ⌊x^{11/16}⌋`).  The `Aseq`-normalised (R′) with the
  slightly stronger exponent `−4` is the main input.
-/
import Mathlib
import Submission.ASP.S25
import Submission.ASP.S10
import Submission.Commons.NumberTheory.DivisorSum.sum_tau_pow_le
import Submission.Commons.Analysis.ExpLog.const_mul_log_pow_le_rpow_threshold

set_option maxHeartbeats 1600000

namespace Submission.ASP

open Finset

noncomputable section

/-- `0 ≤ g_d` in the companion's objects. -/
lemma FIg_nonneg (d : ℕ) : 0 ≤ FIg d := by
  rw [FIg]; exact_mod_cast Submission.gdens_nonneg d

/-- The `(R′)`-sum for `FIa` splits into the main-paper (R′) sum plus the discrepancy `g_d − 1`. -/
lemma RemainderSum_FIr_le (x m : ℕ) :
    RemainderSum FIr (Submission.Rcut x) m
      ≤ (∑ d ∈ (Finset.Icc 1 (Submission.Rcut x)).filter Squarefree,
            ((d.divisors.card : ℝ))^5
              * |(Submission.Ad d m : ℝ) - (Submission.gdens d : ℝ) * (Submission.Aseq m : ℝ)|)
        + (∑ d ∈ (Finset.Icc 1 (Submission.Rcut x)).filter Squarefree,
            ((d.divisors.card : ℝ))^5 * ((Submission.gdens d : ℝ) + 1)) := by
  rw [RemainderSum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun d _ => ?_
  have hc : (0:ℝ) ≤ ((d.divisors.card : ℝ))^5 := by positivity
  have hg := FIg_nonneg d
  have hg' : (0:ℝ) ≤ (Submission.gdens d : ℝ) := by
    exact_mod_cast Submission.gdens_nonneg d
  have hb : |FIr d m| ≤ |(Submission.Ad d m : ℝ) - (Submission.gdens d : ℝ) * (Submission.Aseq m : ℝ)|
      + ((Submission.gdens d : ℝ) + 1) := by
    have h3 : FIr d m = (Submission.Ad d m : ℝ) - (Submission.gdens d : ℝ) * (Submission.Aseq m : ℝ) + ((Submission.gdens d : ℝ) - 1) := by
      simpa [FIg, FIr_eq] using FIr_eq d m
    have h1 : |(Submission.Ad d m : ℝ) - (Submission.gdens d : ℝ) * (Submission.Aseq m : ℝ) + ((Submission.gdens d : ℝ) - 1)|
        ≤ |(Submission.Ad d m : ℝ) - (Submission.gdens d : ℝ) * (Submission.Aseq m : ℝ)| + |(Submission.gdens d : ℝ) - 1| :=
      abs_add_le _ _
    have h2 : |(Submission.gdens d : ℝ) - 1| ≤ (Submission.gdens d : ℝ) + 1 := by
      refine abs_le.mpr ⟨?_, ?_⟩
      · linarith
      · linarith
    rw [h3]
    linarith [h1, h2]
  calc ((d.divisors.card : ℝ))^5 * |FIr d m|
      ≤ ((d.divisors.card : ℝ))^5 * (|(Submission.Ad d m : ℝ) - (Submission.gdens d : ℝ) * (Submission.Aseq m : ℝ)|
          + ((Submission.gdens d : ℝ) + 1)) := mul_le_mul_of_nonneg_left hb hc
    _ = ((d.divisors.card : ℝ))^5 * |(Submission.Ad d m : ℝ) - (Submission.gdens d : ℝ) * (Submission.Aseq m : ℝ)|
          + ((d.divisors.card : ℝ))^5 * ((Submission.gdens d : ℝ) + 1) := by ring

end

end Submission.ASP
