import Mathlib
import Submission.Work.EKLContract.Defs

/-!
# `Work.EKLC6Core.tendsto_of_mem_V`

A sequence of `SL₃(ℝ)`-matrices whose entrywise displacement from the identity is dominated by a
sequence `u n → 0` converges to `1` in `SL₃(ℝ)`.

The sets `V δ = {g | ∀ i j, |g i j - (1 : M₃(ℝ)) i j| < δ}` (max-entry displacement from the
identity) form a basis of neighbourhoods of the identity: the topology of `M₃(ℝ)` is the product
topology (`Matrix.instTopologicalSpace` is literally `Pi.topologicalSpace`), so convergence in
`SL₃(ℝ)` is exactly convergence of the nine entries.  The hypothesis `g n ∈ V (u n)` says that
the entrywise deviation of `g n` from `1` is at most `u n → 0`, so every entry of `g n` tends to
the corresponding entry of `1` (squeeze); the `Pi`-topology then upgrades this entrywise statement
to convergence of `g n` in `SL₃(ℝ)`.

Formally the argument passes through the coercion `SL₃(ℝ) → M₃(ℝ)` (the subtype topology is the
induced topology, `tendsto_subtype_rng`) and the two nested `Pi`-topologies
(`tendsto_pi_nhds` — the index types are finite, but the product topology is the right one in
general, no finiteness is used).
-/

open Filter Topology

noncomputable section

namespace Work.EKLC6Core

open Work.EKLContract

/-- **Entrywise convergence.**  If `g n ∈ V (u n)` and `u n → 0`, then each entry of `g n`
tends to the corresponding entry of the identity matrix.  This is the squeeze
`|g n i j - 1 i j| ≤ u n → 0` followed by the identity `‖x‖ = |x|` on `ℝ`. -/
theorem tendsto_entries_of_mem_V {u : ℕ → ℝ} {g : ℕ → SL3}
    (hu : Tendsto u atTop (nhds (0 : ℝ)))
    (hg : ∀ n, g n ∈ V (u n)) (i j : Fin 3) :
    Tendsto (fun n => ((g n : SL3) : Matrix (Fin 3) (Fin 3) ℝ) i j) atTop
      (nhds (((1 : SL3) : Matrix (Fin 3) (Fin 3) ℝ) i j)) := by
  -- The deviation of the `(i,j)` entry from the identity tends to `0`.
  have hsub : Tendsto (fun n => ((g n : SL3) : Matrix (Fin 3) (Fin 3) ℝ) i j
      - (((1 : SL3) : Matrix (Fin 3) (Fin 3) ℝ) i j)) atTop (nhds 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero (fun n => abs_nonneg _) (fun n => le_of_lt ?_) hu
    simpa [Real.norm_eq_abs] using hg n i j
  -- Add back the constant.
  have := hsub.add (tendsto_const_nhds (x :=
    (((1 : SL3) : Matrix (Fin 3) (Fin 3) ℝ) i j)) (f := atTop))
  simpa using this

theorem tendsto_of_mem_V {u : ℕ → ℝ} {g : ℕ → Work.EKLContract.SL3}
    (hu : Filter.Tendsto u Filter.atTop (nhds (0 : ℝ)))
    (hg : ∀ n, g n ∈ Work.EKLContract.V (u n)) :
    Filter.Tendsto g Filter.atTop (nhds (1 : Work.EKLContract.SL3)) := by
  -- Convergence in the subtype `SL₃(ℝ)` is convergence of the underlying matrices.
  refine (tendsto_subtype_rng (f := g) (x := (1 : SL3))).2 ?_
  -- The topology of `M₃(ℝ)` is the product topology on the nine entries.
  change Tendsto (fun n => fun (i : Fin 3) (j : Fin 3) =>
      ((g n : SL3) : Matrix (Fin 3) (Fin 3) ℝ) i j) atTop
    (nhds (fun (i : Fin 3) (j : Fin 3) =>
      (((1 : SL3)) : Matrix (Fin 3) (Fin 3) ℝ) i j))
  rw [tendsto_pi_nhds]
  intro i
  rw [tendsto_pi_nhds]
  intro j
  exact tendsto_entries_of_mem_V hu hg i j

end Work.EKLC6Core

end
