import Mathlib

/-!
Sequential compactness of [-1,1]^n (child task).

TASK: prove `exists_subseq_limit_coord` (fill in the proof).  Add helpers as
needed above it in this file.

Statement: if `a : ℕ → Fin n → ℝ` has every coordinate of every term in
`[-1,1]`, then there is a strictly increasing index map `φ` and a limit
`x : Fin n → ℝ` with coordinates in `[-1,1]` such that each coordinate of
`a (φ k)` converges to `x i` as `k → ∞`.

SUGGESTED ROUTE.
The space `X := Fin n → ℝ` with the sup-norm topology is a proper metric
space, and the set `s := {f : Fin n → ℝ | ∀ i, f i ∈ Set.Icc (-1) 1}` is
bounded (‖f‖ ≤ 1 for f ∈ s) and closed, hence equal to its closure.
Apply `tendsto_subseq_of_bounded` (in `Mathlib.Topology.MetricSpace.Sequences`):
    theorem tendsto_subseq_of_bounded {X} [PseudoMetricSpace X] [ProperSpace X]
      {s : Set X} (hs : IsBounded s) {x : ℕ → X} (hx : ∀ n, x n ∈ s) :
      ∃ a ∈ closure s, ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (x ∘ φ) atTop (𝓝 a)
to the sequence `a` in the set `s`.
  · ProperSpace instance for `Fin n → ℝ`: infer (finite-dimensional normed
    space over ℝ); if it does not synthesize, prove the result directly with
    `tendsto_subseq_of_frequently_bounded` on the closure or use
    `isSeqCompact` facts.
  · IsBounded: show `s ⊆ Metric.closedBall 0 1` (coordinate bound |f i| ≤ 1
    gives ‖f‖ ≤ 1 for the sup norm on functions) and use that a closed ball
    is bounded (or `Bornology.IsBounded.subset`/`isBounded_closedBall`).
  · s is closed: each {f | f i ∈ Icc (-1) 1} is closed
    (preimage of a closed set under the continuous evaluation `f ↦ f i`),
    and `s` is the finite intersection over `i`.  So `closure s = s`
    (`closure_eq_iff_isClosed` / `IsClosed.closure_eq`), so `a ∈ closure s`
    gives `a ∈ s`, i.e. `∀ i, a i ∈ Set.Icc (-1) 1`.
  · Coordinatewise convergence: from `Tendsto (a ∘ φ) atTop (𝓝 a)` in the
    function-space topology (metric), for each `i : Fin n` the evaluation
    `f ↦ f i` is continuous, so `Tendsto (fun k => (a (φ k)) i) atTop (𝓝 (a i))`
    (`(continuous_apply i).tendsto` or `exact (tendsto_pi_nhds.mp htendsto i)`
    if the topology is the product topology — for finite `Fin n` the two agree;
    the pi norm/metric and product topology coincide).

If proving things directly for `X := Fin n → ℝ` is awkward, you may instead
state and prove an auxiliary lemma for sequences of reals (bounded ⇒ convergent
subsequence) and iterate over `i : Fin n` by induction on n — your choice.

The file must end with a complete proof.
-/

set_option linter.style.haveILetI false

open scoped BigOperators Topology
open Filter Metric

noncomputable section

namespace Submission.Discrepancy

/-- Every sequence in [-1,1]^n has a coordinatewise-convergent subsequence. -/
lemma exists_subseq_limit_coord (n : ℕ) (a : ℕ → Fin n → ℝ)
    (ha : ∀ k : ℕ, ∀ i : Fin n, a k i ∈ Set.Icc (-1) 1) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ x : Fin n → ℝ,
      (∀ i : Fin n, x i ∈ Set.Icc (-1) 1) ∧
      (∀ i : Fin n, Tendsto (fun k : ℕ => a (φ k) i) atTop (𝓝 (x i))) := by
  let s : Set (Fin n → ℝ) := {f | ∀ i, f i ∈ Set.Icc (-1) 1}
  by_cases hn : n = 0
  · subst n
    refine ⟨fun k => k, strictMono_id, fun _ => 0, ?_, ?_⟩
    · intro i
      exact False.elim (Fin.elim0 i)
    · intro i
      exact False.elim (Fin.elim0 i)
  · have hpos : 0 < n := Nat.pos_of_ne_zero hn
    have hnonempty : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hpos
    have hmem : ∀ k : ℕ, a k ∈ s := by
      intro k
      exact ha k
    have hsub : s ⊆ Metric.closedBall (0 : Fin n → ℝ) 1 := by
      intro f hf
      simp only [Metric.mem_closedBall, dist_eq_norm, sub_zero]
      letI : Nonempty (Fin n) := hnonempty
      rw [pi_norm_le_iff_of_nonempty f]
      intro i
      have hfi : f i ∈ Set.Icc (-1) 1 := hf i
      rw [Real.norm_eq_abs, abs_le]
      exact ⟨by linarith [hfi.1], by linarith [hfi.2]⟩
    have hbounded : Bornology.IsBounded s := by
      exact Bornology.IsBounded.subset
        (Metric.isBounded_closedBall (x := (0 : Fin n → ℝ)) (r := 1)) hsub
    have hclosed : IsClosed s := by
      have hset : s = ⋂ i : Fin n, (fun f : Fin n → ℝ => f i) ⁻¹' Set.Icc (-1) 1 := by
        ext f
        simp [s]
      rw [hset]
      exact isClosed_iInter (fun i => IsClosed.preimage (continuous_apply i) isClosed_Icc)
    rcases tendsto_subseq_of_bounded hbounded hmem with ⟨a0, hcl, φ, hφmono, htendsto⟩
    have ha0mem : a0 ∈ s := by
      have hcl' : a0 ∈ closure s := hcl
      rwa [hclosed.closure_eq] at hcl'
    refine ⟨φ, hφmono, a0, ?_, ?_⟩
    · intro i
      exact ha0mem i
    · intro i
      exact (tendsto_pi_nhds.mp htendsto) i

end Discrepancy

end Submission
