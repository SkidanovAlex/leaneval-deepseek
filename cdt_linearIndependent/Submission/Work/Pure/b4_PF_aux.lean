/-
# Auxiliary definitions for `Work.Pure.b4_PF_facts`

The descent `Θ = (x − φ)(Li₂(x) − Li₂(φ))` of the pure function `B₄`
(Calegari–Dimitrov–Tang, arXiv:2408.15403) is written, in the paper, as the
explicit finite weight sum

`b4F = Σ_{k≥1} k⁻²·Q_k`,  `Q_k = P_{k+1} − y·P_{k-1}`   (`Work.Pure.b4F`),

and the first task is to identify its substitution `b4F.subst sympY` with
`b4Theta = (x − φ)(Li₂(x) − Li₂(φ))` (`Work.Pure.b4Theta`).  Both sides are
coefficientwise finite sums; the bookkeeping uses

* the weight `w_k = 1/(k+1)²` (`b4wt`), matching the index convention of
  `Work.Pure.b4F`, whose `k`-th summand carries `b4Q (k+1)` with weight
  `1/(k+1)²`;
* the series `D = Σ_{k≥1} k⁻²·(x^k − φ^k)`, realised by the explicit partial
  sums `b4Ds` (`coeff n b4Ds = Σ_{k ≤ n} w_k·coeff n (x^{k+1} − φ^{k+1})`,
  the terms with `k+1 > n` having zero coefficient at `n`); the identity
  `b4Li2 − b4Li2.subst sympPhi = b4Ds` is proved in
  `Submission.Work.Pure.b4_PF_D`.

All declarations here are definitions (no proofs).
-/
import Mathlib
import Submission.Work.Pure.b4_defs

namespace Work.Pure

open PowerSeries

noncomputable section

/-- the weight `w k = 1/(k+1)²` carried by `b4Q (k+1)` in the descent `b4F`.
(Indexed so that `b4wt k` is the weight of `Q_{k+1}`, matching the
definition of `Work.Pure.b4F`.) -/
def b4wt (k : ℕ) : ℚ := 1 / (((k + 1 : ℕ)) : ℚ) ^ 2

/-- `D = Σ_{k≥1} k⁻²·(x^k − φ^k)` in truncated (`n`-th coefficient) form:
`coeff n b4Ds = Σ_{k ≤ n} w_k·coeff n (x^{k+1} − sympPhi^{k+1})`. -/
def b4Ds : PowerSeries ℚ :=
  PowerSeries.mk fun n =>
    ∑ k ∈ Finset.range (n + 1),
      b4wt k * PowerSeries.coeff n (X ^ (k + 1) - Submission.CDT.sympPhi ^ (k + 1))

@[simp] lemma b4wt_eq (k : ℕ) : b4wt k = 1 / (((k + 1 : ℕ)) : ℚ) ^ 2 := rfl

@[simp] lemma coeff_b4Ds (n : ℕ) :
    PowerSeries.coeff n b4Ds =
      ∑ k ∈ Finset.range (n + 1),
        b4wt k * PowerSeries.coeff n (X ^ (k + 1) - Submission.CDT.sympPhi ^ (k + 1)) := by
  rw [b4Ds, PowerSeries.coeff_mk]

end

end Work.Pure
