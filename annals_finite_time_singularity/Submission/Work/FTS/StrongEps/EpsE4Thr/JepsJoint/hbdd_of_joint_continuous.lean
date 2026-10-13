/-
Copyright: work module for the Elgindi finite-time singularity project.

# Uniform bounds on the mixed jets of a family of profiles, from joint continuity

The chapter `EpsE4Thr` integrates the `ε`-scheme along a family of profiles
`g : ℝ → ℝ → ℝ → ℝ`, `(z, θ, τ) ↦ g z θ τ`, whose slices `slice g τ = (z, θ) ↦ g z θ τ` are
the profiles at time `τ`.  The bookkeeping of the ODE then needs a *uniform bound* on the
mixed jets

  `(τ, z, θ) ↦ D_z^k D_θ^l (slice g τ) z θ`      (`Work.Spaces.mixed k l (slice g τ) z θ`)

over `τ ∈ [0,T]`, over a *compact* set of modes `(z,θ) ∈ K ⊆ Quad`, and over all orders
`k + l ≤ N` at once.

This file supplies it.  The hypothesis is exactly the one the sibling
`mixed_fam_continuous_Icc` produces: joint continuity of each slot
`(τ, (z,θ)) ↦ D_z^j D_θ^i (slice g τ) z θ` on the closed slab `Icc 0 T ×ˢ Quad`, for every
`j + i ≤ N`.  Since there are only finitely many such slots and `Icc 0 T ×ˢ K` is compact,
each slot is bounded there; the bound is made uniform in the slot by considering the *finite
sum* of the absolute values of the slots over the finite index set
`pairSet N = {(k,l) | k + l ≤ N}` — whose continuity is again an instance of
`ContinuousOn.abs`, `continuousOn_finsetSum` — and then dominating each single slot by the
sum (`Finset.single_le_sum`).  No choice and no max over a finite family is needed.

For `T < 0` the slab `Icc 0 T ×ˢ Quad` is empty; the argument is uniform in `T` anyway
(`Set.Icc (0:ℝ) T` is compact also when empty).
-/
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Ring.Basic
import Submission.Work.FTS.StrongEps.EpsE4Thr.AesmJfamP

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr.JepsJoint

/-- The finite set of multi-indices `(k, l)` of order at most `N`. -/
private def pairSet (N : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.range (N + 1)) ×ˢ (Finset.range (N + 1))).filter (fun p => p.1 + p.2 ≤ N)

/-- Every pair of orders `(k, l)` with `k + l ≤ N` belongs to `pairSet N`. -/
private theorem mem_pairSet {N k l : ℕ} (h : k + l ≤ N) : (k, l) ∈ pairSet N := by
  simp only [pairSet, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
  omega

theorem hbdd_of_joint_continuous {g : ℝ → ℝ → ℝ → ℝ} {T : ℝ} {N : ℕ}
    (hcontAll : ∀ j i : ℕ, j + i ≤ N → ContinuousOn (fun q : ℝ × (ℝ × ℝ) =>
      Work.Spaces.mixed j i (Work.FTS.Galerkin.slice g q.1) q.2.1 q.2.2)
      (Set.Icc (0 : ℝ) T ×ˢ Work.FTS.StrongEps.Quad)) :
    ∀ K : Set (ℝ × ℝ), IsCompact K → K ⊆ Work.FTS.StrongEps.Quad → ∃ C : ℝ, 0 ≤ C ∧
      ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ (k l : ℕ), k + l ≤ N → ∀ q : ℝ × ℝ, q ∈ K →
        |Work.Spaces.mixed k l (Work.FTS.Galerkin.slice g s) q.1 q.2| ≤ C := by
  intro K hK hKQ
  classical
  -- each slot is continuous on the slab
  have hcont_each : ∀ p ∈ pairSet N, ContinuousOn (fun q : ℝ × (ℝ × ℝ) =>
      |Work.Spaces.mixed p.1 p.2 (Work.FTS.Galerkin.slice g q.1) q.2.1 q.2.2|)
      (Set.Icc (0 : ℝ) T ×ˢ Work.FTS.StrongEps.Quad) := by
    intro p hp
    have hpN : p.1 + p.2 ≤ N := (Finset.mem_filter.mp hp).2
    exact (hcontAll p.1 p.2 hpN).abs
  -- hence so is their finite sum
  have hcont_sum : ContinuousOn (fun q : ℝ × (ℝ × ℝ) =>
      ∑ p ∈ pairSet N, |Work.Spaces.mixed p.1 p.2 (Work.FTS.Galerkin.slice g q.1) q.2.1 q.2.2|)
      (Set.Icc (0 : ℝ) T ×ˢ Work.FTS.StrongEps.Quad) :=
    continuousOn_finsetSum (pairSet N) hcont_each
  -- bounded on the compact set `Icc 0 T ×ˢ K`
  have hcomp : IsCompact (Set.Icc (0 : ℝ) T ×ˢ K) := isCompact_Icc.prod hK
  obtain ⟨C, hC⟩ := hcomp.exists_bound_of_continuousOn
    (hcont_sum.mono (Set.prod_mono Subset.rfl hKQ))
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro s hs k l hkl q hq
  have hbound := hC (s, q) ⟨hs, hq⟩
  rw [Real.norm_eq_abs] at hbound
  have hnonneg : 0 ≤ ∑ p ∈ pairSet N,
      |Work.Spaces.mixed p.1 p.2 (Work.FTS.Galerkin.slice g s) q.1 q.2| :=
    Finset.sum_nonneg
      (f := fun (p : ℕ × ℕ) => |Work.Spaces.mixed p.1 p.2 (Work.FTS.Galerkin.slice g s) q.1 q.2|)
      (fun p _ => abs_nonneg _)
  have hsum_le : (∑ p ∈ pairSet N,
      |Work.Spaces.mixed p.1 p.2 (Work.FTS.Galerkin.slice g s) q.1 q.2|) ≤ C := by
    rwa [abs_of_nonneg hnonneg] at hbound
  refine le_trans ?_ (le_trans hsum_le (le_max_left C 0))
  exact Finset.single_le_sum
    (f := fun (p : ℕ × ℕ) => |Work.Spaces.mixed p.1 p.2 (Work.FTS.Galerkin.slice g s) q.1 q.2|)
    (fun p _ => abs_nonneg _) (mem_pairSet hkl)

end Work.FTS.StrongEps.EpsE4Thr.JepsJoint
