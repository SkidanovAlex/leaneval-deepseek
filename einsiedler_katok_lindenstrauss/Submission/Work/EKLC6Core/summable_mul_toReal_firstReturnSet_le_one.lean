import Mathlib
import Submission.Work.EKLC6Core.towerDefs
import Submission.Work.EKLC6Core.firstReturn_partition
import Submission.Work.EKLC6Core.returnTimeDefs
import Submission.Work.EKLC6Core.summable_succ_mul_of_measureDecay
import Submission.Work.EKLC6Core.firstHitSet_measurable_and_sum_le_one
import Submission.Work.EKLC6Core.toReal_firstReturnSet_eq_sub_firstHitSet

/-!
# `Work.EKLC6Core.summable_mul_toReal_firstReturnSet_le_one` — Kac's inequality

For a probability measure `μ` on `X₃ = SL₃(ℝ)/SL₃(ℤ)` preserved by the diagonal map
`φ_t = (aDiag t ·)` and a measurable set `Ω ⊆ X₃`, let

`Q i = firstReturnSet t Ω i`  (`i ≥ 1`)

be the set of points of `Ω` whose first return to `Ω` happens at time `i` (the partition `Q̃` of
Pisa 7.49).  Then the return times are summable with

`∑_{n ≥ 0} (n+1) · μ (Q (n+1)) ≤ 1`,

which is Kac's inequality in the indexing used by the entropy bookkeeping of Pisa 7.50/7.52
(`μ (Q (n+1))` is the mass of the `(n+1)`-st level of the return-time tower).

The proof is the classical Kac argument, in the form of a telescoping identity.  Write

`D n = firstHitSet φ_t Ω n = {x | φ_t^[n] x ∈ Ω ∧ ∀ j < n, φ_t^[j] x ∉ Ω}`

for the `n`-th *entrance* (first-hit) set of `Ω`.  Then

* `φ_t ⁻¹' (D n) = D (n+1) ⊔ Q (n+1)`: the points whose image under `φ_t` first hits `Ω` at time
  `n`, split according to whether they already lie in `Ω`
  (`Q (n+1) = Ω ∩ φ_t ⁻¹' D n`, `D (n+1) = Ωᶜ ∩ φ_t ⁻¹' D n`);
* hence `μ (Q (n+1)) = μ (D n) - μ (D (n+1))`, because `μ` is `φ_t`-invariant
  (`Work.EKLC6Core.toReal_firstReturnSet_eq_sub_firstHitSet`);
* the entrance sets are pairwise disjoint, so `∑_{m < N} μ (D m) ≤ μ X₃ = 1`
  (`Work.EKLC6Core.firstHitSet_measurable_and_sum_le_one`);
* Abel summation (`Work.EKLC6Core.summable_succ_mul_of_measureDecay`) turns the last two facts
  into `∑_{n < N} (n+1) μ (Q (n+1)) = ∑_{m < N} μ (D m) - N · μ (D N) ≤ 1` for every `N`, whence
  the series is summable with sum at most `1`.

Note that no recurrence (Poincaré) is needed: the inequality holds for every measure-preserving
self-map of a probability space.  (The equality `∑ i μ (Q i) = 1` does need it, via
`Work.EKLC6Core.neverReturnSet_null`.) -/

namespace Work.EKLC6Core

open MeasureTheory Set
open scoped ENNReal

/-- The self-map `x ↦ aDiag t • x` of `X₃`. -/
noncomputable abbrev diagMapKac (t : Fin 3 → ℝ) : Work.EKLContract.X3 → Work.EKLContract.X3 :=
  fun x => Work.EKLContract.aDiag t • x

/-- **Kac's inequality** for the return-time partition of `Ω` (Pisa 7.49/7.50): the return times
`n + 1` weighted by the masses of the first-return sets form a summable family of total mass at
most `1`. -/
theorem summable_mul_toReal_firstReturnSet_le_one {μ : MeasureTheory.Measure Work.EKLContract.X3}
    [MeasureTheory.IsProbabilityMeasure μ] {t : Fin 3 → ℝ}
    (hmp : MeasureTheory.MeasurePreserving
      (fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t • x) μ μ)
    {Ω : Set Work.EKLContract.X3} (hΩ : MeasurableSet Ω) :
    Summable (fun n : ℕ => ((n : ℝ) + 1) *
        (μ (Work.EKLC6Core.firstReturnSet t Ω (n + 1))).toReal) ∧
      (∑' n : ℕ, ((n : ℝ) + 1) *
        (μ (Work.EKLC6Core.firstReturnSet t Ω (n + 1))).toReal) ≤ 1 := by
  -- the (shifted) entrance masses are bounded by `1`
  obtain ⟨-, -, hupper⟩ := firstHitSet_measurable_and_sum_le_one (T := diagMapKac t) hmp hΩ
  have hupper' : ∀ N : ℕ,
      ∑ m ∈ Finset.range N, (μ (firstHitSet (diagMapKac t) Ω m)).toReal ≤ 1 := by
    intro N
    simpa only [Measure.real_def] using hupper N
  -- consecutive entrance masses differ by the mass of the first-return set
  have hstep : ∀ n : ℕ,
      (μ (firstHitSet (diagMapKac t) Ω n)).toReal =
        (μ (firstHitSet (diagMapKac t) Ω (n + 1))).toReal +
          (μ (firstReturnSet t Ω (n + 1))).toReal := by
    intro n
    have h := toReal_firstReturnSet_eq_sub_firstHitSet (t := t) hmp hΩ n
    linarith
  -- Abel summation
  exact summable_succ_mul_of_measureDecay
    (a := fun n => (μ (firstReturnSet t Ω n)).toReal)
    (b := fun n => (μ (firstHitSet (diagMapKac t) Ω n)).toReal)
    (fun n => ENNReal.toReal_nonneg) (fun n => ENNReal.toReal_nonneg) hstep hupper'

end Work.EKLC6Core
