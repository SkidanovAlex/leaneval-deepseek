import Mathlib
import Submission.Work.EKLC6Core.famIndicator
import Submission.Work.EKLC6Core.span_indicator_dense
import Submission.Work.EKLC6Core.famIndicatorSum
import Submission.Work.EKLC6Core.integral_sq_sub_famIndicator_le
import Submission.Work.EKLC6Core.rat_finsupp_approx

open MeasureTheory

namespace Work.EKLC6Core

/-- Rational combinations of indicators of a countable generating π-system are dense in `L²(ν)`
for every probability measure `ν`.

(The hypothesis `hgen` must be `= ‹MeasurableSpace X›`, the ambient σ-algebra, *not* `= ⊤`: the top
element of the `MeasurableSpace` lattice is the *discrete* σ-algebra.  This is exactly the
hypothesis of `Work.EKLC6Core.span_indicator_dense`.)

Proof sketch: `Work.EKLC6Core.span_indicator_dense` (module
`Submission.Work.EKLC6Core.span_indicator_dense`) gives approximation by *real* combinations:
`∃ ι : Finset ℕ, ∃ c : ℕ → ℝ, ∫ x, (f x - ∑ n ∈ ι, c n * (S n).indicator 1 x)^2 ∂ν < ε`.  Then round
the finitely many coefficients `c n` (`n ∈ ι`) to rationals `q n` with `∑ n ∈ ι, |c n - q n|` small;
since `ν` is a probability measure, the pointwise bound `|∑ n ∈ ι, (c n - q n) * 1_{S n}| ≤ ∑ n ∈ ι,
|c n - q n|` gives an `L²` error of at most that quantity, so for the rational vector
`q' := ∑ n ∈ ι, q n • Finsupp.single n 1` one has `famIndicator S q' = ∑ n ∈ ι, q n * 1_{S n}` and
`∫ (f - famIndicator S q')² ∂ν < ε`. -/
theorem famIndicator_dense {X : Type*} [MeasurableSpace X]
    (S : ℕ → Set X) (hS : ∀ n, MeasurableSet (S n))
    (hπ : ∀ m n, ∃ k, S m ∩ S n = S k) (hU : ∃ k, S k = Set.univ)
    (hgen : MeasurableSpace.generateFrom (Set.range S) = (inferInstance : MeasurableSpace X))
    (ν : MeasureTheory.Measure X) [MeasureTheory.IsProbabilityMeasure ν]
    (f : X → ℝ) (hf : MeasureTheory.MemLp f 2 ν) {ε : ℝ} (hε : 0 < ε) :
    ∃ c : ℕ →₀ ℚ, ∫ x, (f x - Work.EKLC6Core.famIndicator S c x)^2 ∂ν < ε := by
  classical
  -- Step 1: approximate `f` by a *real* finite combination of indicators.
  have hε4 : (0 : ℝ) < ε / 4 := by linarith
  obtain ⟨ι, c, hc⟩ :=
    span_indicator_dense S hS hπ hU hgen ν f hf hε4
  -- Step 2: round the coefficients off to rationals.  Rounding down the `ε/4`-threshold.
  set δ : ℝ := Real.sqrt (ε / 4) with hδdef
  have hδsq : δ ^ 2 = ε / 4 := by rw [hδdef]; exact Real.sq_sqrt (le_of_lt hε4)
  have hδpos : 0 < δ := by rw [hδdef]; exact Real.sqrt_pos_of_pos hε4
  obtain ⟨q, hqsupp, hqsum⟩ := rat_finsupp_approx ι c hδpos
  refine ⟨q, ?_⟩
  -- Abbreviations.
  set P : X → ℝ := fun x => ∑ n ∈ ι, c n * (S n).indicator (fun _ => (1 : ℝ)) x with hPdef
  set Q : X → ℝ := famIndicator S q with hQdef
  set R : ℝ := ∑ n ∈ ι, |c n - (q n : ℝ)| with hRdef
  have hRnn : 0 ≤ R := by rw [hRdef]; exact Finset.sum_nonneg (fun n _ => abs_nonneg _)
  have hRlt : R < δ := hqsum
  have hRsq : R ^ 2 < ε / 4 := by
    rw [← hδsq]
    exact pow_lt_pow_left₀ hRlt hRnn (by norm_num)
  -- `P` is in `L²`.
  have hPmem : MemLp P 2 ν := by
    rw [hPdef]
    refine memLp_finsetSum ι (fun n _ => ?_)
    exact (memLp_indicator_const 2 (hS n) (1 : ℝ)
      (Or.inr (measure_ne_top ν (S n)))).const_mul (c n)
  have hQmem : MemLp Q 2 ν := by
    rw [hQdef]; exact memLp_famIndicator S hS q ν
  -- The real combination is `ε/4`-close to `f`.
  have hc' : ∫ x, (f x - P x) ^ 2 ∂ν < ε / 4 := by rw [hPdef]; exact hc
  -- The rational combination is `ε/4`-close to the real one in `L²`.
  have hB : ∫ x, (P x - Q x) ^ 2 ∂ν < ε / 4 := by
    have h2 : ∫ x, (P x - Q x) ^ 2 ∂ν ≤ R ^ 2 := by
      rw [hRdef]
      exact integral_sq_sub_famIndicator_le S hS ν ι c q hqsupp
    exact h2.trans_lt hRsq
  -- Squaring the pointwise triangle inequality and integrating.
  have hbound : ∫ x, (f x - Q x) ^ 2 ∂ν
      ≤ 2 * (∫ x, (f x - P x) ^ 2 ∂ν) + 2 * (∫ x, (P x - Q x) ^ 2 ∂ν) := by
    have ha : Integrable (fun x => (f x - P x) ^ 2) ν := (hf.sub hPmem).integrable_sq
    have hb : Integrable (fun x => (P x - Q x) ^ 2) ν := (hPmem.sub hQmem).integrable_sq
    have hgint : Integrable (fun x => 2 * (f x - P x) ^ 2 + 2 * (P x - Q x) ^ 2) ν :=
      (ha.const_mul 2).add (hb.const_mul 2)
    have hpt : ∀ x, (f x - Q x) ^ 2 ≤ 2 * (f x - P x) ^ 2 + 2 * (P x - Q x) ^ 2 := by
      intro x
      have hr : f x - Q x = (f x - P x) + (P x - Q x) := by ring
      nlinarith [hr, sq_nonneg ((f x - P x) - (P x - Q x))]
    calc ∫ x, (f x - Q x) ^ 2 ∂ν
        ≤ ∫ x, (2 * (f x - P x) ^ 2 + 2 * (P x - Q x) ^ 2) ∂ν :=
          integral_mono_of_nonneg (Filter.Eventually.of_forall (fun x => sq_nonneg _)) hgint
            (Filter.Eventually.of_forall hpt)
      _ = 2 * (∫ x, (f x - P x) ^ 2 ∂ν) + 2 * (∫ x, (P x - Q x) ^ 2 ∂ν) := by
          rw [integral_add (ha.const_mul 2) (hb.const_mul 2), integral_const_mul,
            integral_const_mul]
  calc ∫ x, (f x - Q x) ^ 2 ∂ν
      ≤ 2 * (∫ x, (f x - P x) ^ 2 ∂ν) + 2 * (∫ x, (P x - Q x) ^ 2 ∂ν) := hbound
    _ < ε := by linarith

end Work.EKLC6Core
