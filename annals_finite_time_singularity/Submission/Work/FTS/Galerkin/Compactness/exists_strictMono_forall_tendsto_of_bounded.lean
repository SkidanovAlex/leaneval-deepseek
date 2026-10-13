import Mathlib.Topology.Metrizable.Uniformity
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Sequences
import Submission.Work.FTS.Galerkin.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.Galerkin.Compactness

/-- **Diagonal extraction.**  A sequence of real sequences that is uniformly bounded has a
subsequence converging *pointwise in the second index*.  This is the combinatorial half of the
Arzelà–Ascoli step of the compactness input of this area: applied to the values of the Galerkin
families on a countable set of points of the fake-time slab, it extracts a subsequence converging at
every one of those points (the analytic half — the bounds that make the point values bounded, and
the equicontinuity that upgrades this to locally uniform convergence — is
`Work.FTS.Galerkin.linf_of_HkNorm_four` and `Work.FTS.Galerkin.tendsto_slice_of_derivBound` in
`Compactness.lean`).

Intended proof: construct strictly monotone `φ k : ℕ → ℕ` by induction, each a subsequence of the
previous one along which `n ↦ u (φ k n) k` converges (existence from
`tendsto_subseq_of_bounded` / `IsCompact.tendsto_subseq` applied to the bounded range of the
`k`-th column); then take the diagonal `ψ n := φ n n` and show, for fixed `k`, that
`n ↦ u (ψ n) k` is eventually (from `n ≥ k`) a subsequence of `n ↦ u (φ k n) k`. -/
theorem exists_strictMono_forall_tendsto_of_bounded {u : ℕ → ℕ → ℝ} {C : ℝ}
    (h : ∀ n k, |u n k| ≤ C) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∀ k : ℕ, ∃ L : ℝ,
      Filter.Tendsto (fun n => u (ψ n) k) Filter.atTop (nhds L) := by
  classical
  -- Every column of `u` takes its values in the compact (in general empty) interval
  -- `[-C, C]`, so the sequence of columns `n ↦ (k ↦ u n k)` runs in the compact product
  -- `∏ k, Icc (-C) C`; sequential compactness of that product yields the subsequence.
  have hcomp : IsCompact (Set.univ.pi fun _ : ℕ => Set.Icc (-C) C) :=
    isCompact_univ_pi fun _ => isCompact_Icc
  have hx : ∀ n, (fun k => u n k) ∈ Set.univ.pi fun _ : ℕ => Set.Icc (-C) C := by
    intro n
    rw [Set.mem_univ_pi]
    intro k
    exact abs_le.mp (h n k)
  obtain ⟨a, -, φ, hφ, htend⟩ := hcomp.tendsto_subseq hx
  refine ⟨φ, hφ, fun k => ⟨a k, ?_⟩⟩
  have h2 := tendsto_pi_nhds.mp htend k
  simpa [Function.comp_def] using h2

end Work.FTS.Galerkin.Compactness
