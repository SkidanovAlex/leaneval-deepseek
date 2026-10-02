/-
# The bad-event probability bound for the naive colouring procedure

`Work.Deep.Sparse.bad_event_bound` is the per-vertex bad-event bound of the naive colouring
procedure: if the threshold `d(v) + 1 - k` is at most half of

`μ = (|nonAdjPairs G v|/2)·(1/k)·((k-1)/k)^(2D)·(1 - D/(3k))`

(hypothesis `hreq`), then the probability that the partial colouring `ofColoring G f` has
fewer than `d(v) + 1 - k` repeated colours at `v` is at most `1/(4 D^6)`.

The deterministic half is the inclusion–exclusion inequality
`PartialColoring.colMinusDist_ge_pair_sub_triple` (`Submission/Work/Deep/Sparse/Basic.lean`):
for *every* partial colouring, `P_v - T_v ≤ Col(v) - Dist(v)`.  Hence the bad event
`{Col(v) - Dist(v) < d(v) + 1 - k}` is contained in the event `{P_v - T_v < μ/2}` that
`hreq` points at.

The probabilistic half is `Work.Deep.Sparse.concentration_ncp` (the formalisation of the
Bruhn–Joos / Bonamy–Perrett–Postle concentration of the naive colouring procedure, resting on
`Work.Deep.Sparse.ncp_lower_tail` and `Work.Deep.Sparse.ncp_concentration`), which bounds that
event by `1/(4 D^6)`.  The claim then follows by monotonicity of the probability.
-/
import Submission.Work.Deep.Sparse.Prelude
import Submission.Work.Deep.Sparse.Basic
import Submission.Work.Deep.Sparse.ProbBasic
import Submission.Work.Deep.Sparse.ProbModel
import Submission.Work.Deep.Sparse.FiringDefs
import Submission.Work.Deep.Sparse.concentration_ncp

set_option autoImplicit false
set_option linter.unusedVariables false

open scoped BigOperators

namespace Work.Deep.Sparse

/-- The real form of `firingCard_le`: the number of firing colours is at most the number of
repeated colours of the partial colouring `ofColoring G f`. -/
theorem firingCard_le_rt {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {k : ℕ} (f : V → Fin k) (v : V) :
    (firingCard G v f : ℝ)
      ≤ ((ofColoring G f).numColored v : ℝ) - ((ofColoring G f).numDistinct v : ℝ) := by
  have h := firingCard_le G f v
  have h' := Int.cast_le (R := ℝ) |>.mpr h
  push_cast at h'
  linarith

/-- **The bad-event bound.**  See the module docstring for the two halves of the proof: the
deterministic inclusion `colMinusDist_ge_pair_sub_triple` together with the hypothesis `hreq`
puts the bad event inside `{P_v - T_v < μ/2}`, and `concentration_ncp` bounds that event by
`1/(4 D^6)`. -/
theorem bad_event_bound {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {k D : ℕ} (hk : 0 < k) (hD : 0 < D) (hDk : D ≤ 2 * k) (hkD : (k : ℝ) ≤ 2 * D)
    [Nonempty (V → Fin k)] (hdeg : ∀ x : V, G.degree x ≤ D) (v : V)
    {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (hsp : (δ / 2) * (D : ℝ) ^ 2 / 2 ≤ ((Work.Deep.Sparse.nonAdjPairs G v).card : ℝ) / 2)
    (hbig : (10 : ℝ) ^ 6 * (Real.log ((D : ℝ) + 2)) ^ 8 ≤ δ ^ 2 * (D : ℝ))
    (hreq : (G.degree v : ℝ) + 1 - k
      ≤ (1 / 2) * (((Work.Deep.Sparse.nonAdjPairs G v).card : ℝ) / 2
          * ((1 : ℝ) / (k : ℝ) * (((k : ℝ) - 1) / (k : ℝ)) ^ (2 * D))
          * (1 - (D : ℝ) / (3 * (k : ℝ))))) :
    (Work.Deep.Sparse.colSpace (V := V) k).prob
        {f | ((Work.Deep.Sparse.ofColoring G f).numColored v : ℝ)
              - ((Work.Deep.Sparse.ofColoring G f).numDistinct v : ℝ) < (G.degree v : ℝ) + 1 - k}
      ≤ 1 / (4 * (D : ℝ) ^ 6) := by
  refine le_trans (FinSpace.prob_mono (colSpace (V := V) k) ?_)
    (concentration_ncp G hk hD hDk hkD hdeg v hδ0 hδ1 hsp hbig)
  intro f hf
  simp only [Set.mem_ofPred_eq] at hf ⊢
  have h1 : ((ofColoring G f).pairTerm v : ℝ) - ((ofColoring G f).tripleTerm v : ℝ)
      ≤ ((ofColoring G f).numColored v : ℝ) - ((ofColoring G f).numDistinct v : ℝ) := by
    have h := PartialColoring.colMinusDist_ge_pair_sub_triple (φ := ofColoring G f) v
    have h' := Int.cast_le (R := ℝ) |>.mpr h
    push_cast at h'
    linarith
  linarith [h1, hf, hreq]

end Work.Deep.Sparse
