import Submission.Work.ConeSwitch.MathlibNoHG
import Submission.Work.Deep.Prob.Basic
import Submission.Work.Deep.Prob.Spaces

/-!
# Expectation of a weighted sum of indicators

`expect_sum_indicators`: the expectation (with respect to an arbitrary `FinProbSpace`) of
`∑ i, w i • 1[A i]` is `∑ i, w i * P.prob (A i)`.  This is the linearity-of-expectation
identity underlying first-moment computations for weighted sums of events; no independence
is required.

The proof is two steps: interchange the `ω`- and `i`-sums via `FinProbSpace.expect_sum`,
then evaluate the expectation of each weighted indicator, which is the content of the
helper `expect_indicator_weight` below.
-/

namespace Work.Deep.Prob.Chernoff

/-- The expectation of a weighted indicator `1[A] * c` is `P.prob A * c`. -/
theorem expect_indicator_weight {Ω : Type*} [Fintype Ω] (P : FinProbSpace Ω) (A : Set Ω)
    (c : ℝ) :
    P.expect (fun ω => A.indicator (fun _ => c) ω) = P.prob A * c := by
  -- Pointwise, `mass ω * (c if ω ∈ A else 0) = (mass ω if ω ∈ A else 0) * c`.
  have h : ∀ ω ∈ (Finset.univ : Finset Ω),
      P.mass ω * A.indicator (fun _ => c) ω = A.indicator P.mass ω * c := by
    intro ω _
    by_cases hA : ω ∈ A
    · rw [Set.indicator_of_mem hA, Set.indicator_of_mem hA]
    · rw [Set.indicator_of_notMem hA, Set.indicator_of_notMem hA]
      ring
  calc P.expect (fun ω => A.indicator (fun _ => c) ω)
      = ∑ ω : Ω, P.mass ω * A.indicator (fun _ => c) ω := rfl
    _ = ∑ ω : Ω, A.indicator P.mass ω * c := Finset.sum_congr rfl h
    _ = P.prob A * c := by rw [FinProbSpace.prob, Finset.sum_mul]

/-- **Linearity of expectation for weighted sums of indicators.**  The expectation of
`∑ i, w i • 1[A i]` equals `∑ i, w i * ℙ[A i]`, with no independence hypothesis. -/
theorem expect_sum_indicators {Ω : Type*} [Fintype Ω] (P : FinProbSpace Ω) {ι : Type*}
    [Fintype ι] (A : ι → Set Ω) (w : ι → ℝ) :
    P.expect (fun ω => ∑ i, (A i).indicator (fun _ => w i) ω) = ∑ i, P.prob (A i) * w i := by
  -- Swap the two finite sums, then apply `expect_indicator_weight` to each summand.
  have hsum : P.expect (fun ω => ∑ i, (A i).indicator (fun _ => w i) ω)
      = ∑ i, P.expect (fun ω => (A i).indicator (fun _ => w i) ω) :=
    P.expect_sum (fun i ω => (A i).indicator (fun _ => w i) ω)
  rw [hsum]
  exact Finset.sum_congr rfl fun i _ => expect_indicator_weight P (A i) (w i)

end Work.Deep.Prob.Chernoff
