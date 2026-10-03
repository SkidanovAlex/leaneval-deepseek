/-
# The variational norm of an interval integral

This file proves that the `r`-variational norm (`r ≥ 1`) of the sequence
`n ↦ ∫_{1/2}^{1} H t n x dt` of interval integrals is at most the integral of the variational
norms of the integrands,

  `‖(∫_{1/2}^{1} H t n x dt)_n‖_{V^r} ≤ ∫⁻_{t ∈ uIoc 1/2 1} ‖(H t n x)_n‖_{V^r}`.

Since `variationalNorm r a = (⨆_n ‖a n‖ₑ) + varPart r a` (`variationalNorm_eq_add`), the two
defining suprema are estimated separately:

* the sup part: `‖∫ H t n x dt‖ ≤ ∫ ‖H t n x‖` for the Bochner integral, then take `⨆ n`;
* the variation part: for a monotone selection `N` and `J : ℕ`, the increments
  `∫ H(N (i+1)) - ∫ H(N i) = ∫ (H(N (i+1)) - H(N i))` (Bochner `integral_sub`), and the
  `ℓ^r` norm of a vector-valued integral is at most the integral of the `ℓ^r` norms of the
  integrands (`norm_toLp_integral_le`, from `eval_integral_piLp` and
  `enorm_integral_le_lintegral_enorm` applied to the `WithLp r (Fin J → ℂ)`-valued integrand).

Measurability of the sup part is used once, to split the integral of the defining sum
(`lintegral_add_left`).
-/
import Mathlib
import Submission.Work.Analysis.Paraproduct.SmallScale

namespace Work.KMTPlan.A6

open MeasureTheory PointwiseErgodicTheorems
open scoped Interval ENNReal NNReal BigOperators

set_option linter.style.haveILetI false

/-- **The `ℓ^r` norm of a vector-valued integral is at most the integral of the `ℓ^r` norms.**
For `r ≥ 1`, `J : ℕ`, a scale selection `N` and a family `H` whose members are integrable on
`uIoc (1/2) 1`, the `ℓ^r` norm of the vector of integrals
`i ↦ ∫_{uIoc (1/2) 1} (H t (N (i+1)) x - H t (N i) x) dt` is at most the `lintegral` of the
`ℓ^r` norms of the integrands. -/
lemma norm_toLp_integral_le (r : ℝ≥0) (hr : 1 ≤ r) (J : ℕ) (N : ℕ → ℕ)
    (H : ℝ → ℕ → ℤ → ℂ) (x : ℤ)
    (hI : ∀ n : ℕ, Integrable (fun t : ℝ => H t n x)
      (volume.restrict (Set.uIoc (1 / 2 : ℝ) 1))) :
    ENNReal.ofReal ‖WithLp.toLp r (fun i : Fin J =>
        ∫ t, (H t (N (i + 1)) x - H t (N i) x) ∂(volume.restrict (Set.uIoc (1 / 2 : ℝ) 1)))‖
      ≤ ∫⁻ t in Set.uIoc (1 / 2 : ℝ) 1, ENNReal.ofReal ‖WithLp.toLp r (fun i : Fin J =>
          H t (N (i + 1)) x - H t (N i) x)‖ := by
  haveI : Fact (1 ≤ (r : ℝ≥0∞)) := ⟨by exact_mod_cast hr⟩
  have hcomp : ∀ i : Fin J, Integrable (fun t : ℝ => H t (N (i + 1)) x - H t (N i) x)
      (volume.restrict (Set.uIoc (1 / 2 : ℝ) 1)) :=
    fun i => (hI (N (i + 1))).sub (hI (N i))
  have hFint : Integrable
      (fun t : ℝ => WithLp.toLp r (fun i : Fin J => H t (N (i + 1)) x - H t (N i) x))
      (volume.restrict (Set.uIoc (1 / 2 : ℝ) 1)) :=
    Integrable.of_eval_piLp (fun i => by simpa using hcomp i)
  have hIntEq : ∫ t, (WithLp.toLp r (fun i : Fin J => H t (N (i + 1)) x - H t (N i) x))
        ∂(volume.restrict (Set.uIoc (1 / 2 : ℝ) 1))
      = WithLp.toLp r (fun i : Fin J =>
          ∫ t, (H t (N (i + 1)) x - H t (N i) x) ∂(volume.restrict (Set.uIoc (1 / 2 : ℝ) 1))) := by
    refine PiLp.ext (fun i => ?_)
    exact MeasureTheory.eval_integral_piLp hFint.eval_piLp i
  calc ENNReal.ofReal ‖WithLp.toLp r (fun i : Fin J =>
          ∫ t, (H t (N (i + 1)) x - H t (N i) x) ∂(volume.restrict (Set.uIoc (1 / 2 : ℝ) 1)))‖
      = ‖WithLp.toLp r (fun i : Fin J =>
          ∫ t, (H t (N (i + 1)) x - H t (N i) x) ∂(volume.restrict (Set.uIoc (1 / 2 : ℝ) 1)))‖ₑ :=
        ofReal_norm _
    _ = ‖∫ t, (WithLp.toLp r (fun i : Fin J => H t (N (i + 1)) x - H t (N i) x))
          ∂(volume.restrict (Set.uIoc (1 / 2 : ℝ) 1))‖ₑ := by rw [← hIntEq]
    _ ≤ ∫⁻ t, ‖WithLp.toLp r (fun i : Fin J => H t (N (i + 1)) x - H t (N i) x)‖ₑ
          ∂(volume.restrict (Set.uIoc (1 / 2 : ℝ) 1)) :=
        MeasureTheory.enorm_integral_le_lintegral_enorm _
    _ = ∫⁻ t in Set.uIoc (1 / 2 : ℝ) 1, ENNReal.ofReal ‖WithLp.toLp r (fun i : Fin J =>
          H t (N (i + 1)) x - H t (N i) x)‖ := by simp [ofReal_norm]

open MeasureTheory PointwiseErgodicTheorems in
open scoped Interval ENNReal NNReal BigOperators in
/-- The variational norm of an interval integral is at most the interval integral (`lintegral`) of
the variational norms of the integrands. -/
theorem varNorm_integral_le (r : ℝ≥0) (hr : 1 ≤ r) (H : ℝ → ℕ → ℤ → ℂ) (x : ℤ)
    (hint : ∀ n : ℕ, IntervalIntegrable (fun t : ℝ => H t n x) volume (1 / 2) 1)
    (hmeas : ∀ n : ℕ, Measurable fun t : ℝ => H t n x) :
    PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => ∫ t in (1 / 2 : ℝ)..1, H t n x)
      ≤ ∫⁻ t in Set.uIoc (1 / 2 : ℝ) 1,
          PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => H t n x) := by
  have hle : (1 / 2 : ℝ) ≤ 1 := by norm_num
  -- Measurability of the "sup of norms" term, needed to split the integral of the sum.
  have hA : Measurable (fun t : ℝ => ⨆ n : ℕ, ‖H t n x‖ₑ) :=
    Measurable.iSup (fun n => (hmeas n).enorm)
  -- Integrability over the (reversed) interval, in the form used by the Bochner API.
  have hsingle : ∀ n : ℕ, Integrable (fun t : ℝ => H t n x)
      (volume.restrict (Set.uIoc (1 / 2 : ℝ) 1)) := by
    intro n
    rw [Set.uIoc_of_le hle]
    exact (hint n).1
  -- Replace the sequence of interval integrals by the sequence of integrals on `uIoc (1/2) 1`.
  have hseq : (fun n : ℕ => ∫ t in (1 / 2 : ℝ)..1, H t n x)
      = (fun n : ℕ => ∫ t, H t n x ∂(volume.restrict (Set.uIoc (1 / 2 : ℝ) 1))) := by
    funext n
    show ∫ t in (1 / 2 : ℝ)..1, H t n x
      = ∫ t, H t n x ∂(volume.restrict (Set.uIoc (1 / 2 : ℝ) 1))
    rw [intervalIntegral.integral_of_le hle, ← Set.uIoc_of_le hle]
  rw [hseq]
  -- The supremum part.
  have hsup : (⨆ n : ℕ, ‖∫ t, H t n x ∂(volume.restrict (Set.uIoc (1 / 2 : ℝ) 1))‖ₑ)
      ≤ ∫⁻ t in Set.uIoc (1 / 2 : ℝ) 1, ⨆ n : ℕ, ‖H t n x‖ₑ := by
    refine iSup_le (fun n => ?_)
    exact (MeasureTheory.enorm_integral_le_lintegral_enorm (fun t : ℝ => H t n x)).trans
      (lintegral_mono (fun t => le_iSup (fun n : ℕ => ‖H t n x‖ₑ) n))
  -- The variation part.
  have hvar : Submission.PointwiseErgodicTheorems.varPart r
        (fun n : ℕ => ∫ t, H t n x ∂(volume.restrict (Set.uIoc (1 / 2 : ℝ) 1)))
      ≤ ∫⁻ t in Set.uIoc (1 / 2 : ℝ) 1,
          Submission.PointwiseErgodicTheorems.varPart r (fun n : ℕ => H t n x) := by
    unfold Submission.PointwiseErgodicTheorems.varPart
    refine iSup_le (fun J => iSup_le (fun N => iSup_le (fun hN => ?_)))
    show ENNReal.ofReal ‖WithLp.toLp r (fun i : Fin J =>
        (∫ t, H t (N (i + 1)) x ∂(volume.restrict (Set.uIoc (1 / 2 : ℝ) 1)))
          - ∫ t, H t (N i) x ∂(volume.restrict (Set.uIoc (1 / 2 : ℝ) 1)))‖ ≤ _
    have hvec : WithLp.toLp r (fun i : Fin J =>
          (∫ t, H t (N (i + 1)) x ∂(volume.restrict (Set.uIoc (1 / 2 : ℝ) 1)))
            - ∫ t, H t (N i) x ∂(volume.restrict (Set.uIoc (1 / 2 : ℝ) 1)))
        = WithLp.toLp r (fun i : Fin J =>
            ∫ t, (H t (N (i + 1)) x - H t (N i) x)
              ∂(volume.restrict (Set.uIoc (1 / 2 : ℝ) 1))) := by
      refine congrArg (WithLp.toLp r) (funext (fun i => ?_))
      exact (MeasureTheory.integral_sub (hsingle (N (i + 1))) (hsingle (N i))).symm
    rw [hvec]
    refine (norm_toLp_integral_le r hr J N H x hsingle).trans ?_
    refine lintegral_mono (fun t => ?_)
    exact le_iSup_of_le J (le_iSup_of_le N (le_iSup_of_le hN le_rfl))
  -- Split the integral of the variational norm into its two defining parts.
  have hsplit : ∫⁻ t in Set.uIoc (1 / 2 : ℝ) 1, variationalNorm r (fun n : ℕ => H t n x)
      = (∫⁻ t in Set.uIoc (1 / 2 : ℝ) 1, ⨆ n : ℕ, ‖H t n x‖ₑ)
        + ∫⁻ t in Set.uIoc (1 / 2 : ℝ) 1,
            Submission.PointwiseErgodicTheorems.varPart r (fun n : ℕ => H t n x) := by
    simp only [Submission.PointwiseErgodicTheorems.variationalNorm_eq_add]
    exact MeasureTheory.lintegral_add_left hA _
  calc variationalNorm r (fun n : ℕ => ∫ t, H t n x ∂(volume.restrict (Set.uIoc (1 / 2 : ℝ) 1)))
      = (⨆ n : ℕ, ‖∫ t, H t n x ∂(volume.restrict (Set.uIoc (1 / 2 : ℝ) 1))‖ₑ)
        + Submission.PointwiseErgodicTheorems.varPart r
            (fun n : ℕ => ∫ t, H t n x ∂(volume.restrict (Set.uIoc (1 / 2 : ℝ) 1))) :=
        Submission.PointwiseErgodicTheorems.variationalNorm_eq_add r _
    _ ≤ (∫⁻ t in Set.uIoc (1 / 2 : ℝ) 1, ⨆ n : ℕ, ‖H t n x‖ₑ)
        + ∫⁻ t in Set.uIoc (1 / 2 : ℝ) 1,
            Submission.PointwiseErgodicTheorems.varPart r (fun n : ℕ => H t n x) :=
        add_le_add hsup hvar
    _ = ∫⁻ t in Set.uIoc (1 / 2 : ℝ) 1, variationalNorm r (fun n : ℕ => H t n x) :=
        hsplit.symm

end Work.KMTPlan.A6
