import Mathlib
import Submission.Work.BW.Minkowski2.defs
import Submission.Work.BW.minkowski_defs
import Submission.Work.BW.Minkowski2.gauge_isLatticeNorm
import Submission.Work.BW.Minkowski2.smulSet_unitBall_eq
import Submission.Work.BW.Minkowski2.succMinL_eq_succMinBody
import Submission.Work.BW.Minkowski2.mem_latOf_one
import Submission.Work.BW.basisRed_exists_indep

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Existence of linearly independent lattice vectors realising the successive minima

For a convex, symmetric, closed, bounded body `K ⊆ ℝᵈ` with nonempty interior there are integer
vectors `v 0, …, v (d-1)`, `ℝ`-linearly independent, with `v i ∈ λ_{i+1} • K`, where `λ_{i+1}` is
the `(i+1)`-st successive minimum `Work.BW.succMinBody (latOf 1) K (i+1)`.

The argument identifies `K` with the unit ball `{y | gauge K y ≤ 1}` of the Minkowski functional
of `K` (`gauge_le_one_iff_mem_closure`), transports the successive minima along
`succMinL_eq_succMinBody`, and applies the greedy construction `Work.BW.basisRed_exists_indep`,
which produces an `ℝ`-independent family of lattice vectors whose `gauge K`-values are bounded by
the successive minima.
-/

namespace Work.BW.Minkowski2

open scoped Topology

theorem exists_min_vecs {d : ℕ} (K : Set (Fin d → ℝ)) (hKc : Convex ℝ K)
    (hsym : ∀ x ∈ K, -x ∈ K) (hKcl : IsClosed K) (hKbd : Bornology.IsBounded K)
    (hKi : (interior K).Nonempty) :
    ∃ v : Fin d → Fin d → ℤ, LinearIndependent ℝ (fun i => fun j => ((v i j : ℤ) : ℝ)) ∧
      ∀ i : Fin d, (fun j => ((v i j : ℤ) : ℝ)) ∈
        Work.BW.smulSet (Work.BW.succMinBody (Work.BW.latOf 1) K (i.1 + 1)) K := by
  classical
  set F : (Fin d → ℝ) → ℝ := gauge K with hFdef
  -- `K` is a neighbourhood of `0`, hence `{gauge K ≤ 1} = closure K = K`
  have h0int : (0 : Fin d → ℝ) ∈ interior K := zero_mem_interior_of_convex_symm hKc hsym hKi
  have hKnbhd : K ∈ 𝓝 (0 : Fin d → ℝ) :=
    Filter.mem_of_superset (isOpen_interior.mem_nhds h0int) interior_subset
  have hlevel : {y : Fin d → ℝ | F y ≤ 1} = K := by
    rw [hFdef]
    ext x
    change gauge K x ≤ 1 ↔ x ∈ K
    rw [gauge_le_one_iff_mem_closure hKc hKnbhd, hKcl.closure_eq]
  have hlevelK : K = {y : Fin d → ℝ | F y ≤ 1} := hlevel.symm
  -- `gauge K` is a lattice norm
  have hF : Work.BW.IsLatticeNorm F := by
    rw [hFdef]
    exact gauge_isLatticeNorm K hKc hsym hKbd hKi
  obtain ⟨u, huind, hubd⟩ := Work.BW.basisRed_exists_indep hF
  refine ⟨u, huind, fun i => ?_⟩
  -- the successive minima agree
  have h1 : Work.BW.succMinBody (Work.BW.latOf (1 : Matrix (Fin d) (Fin d) ℤ)) K (i.1 + 1)
      = Work.BW.succMinL F (i.1 + 1) := by
    rw [hlevelK]
    exact (succMinL_eq_succMinBody F hF (Nat.succ_le_succ (Nat.zero_le i.1))).symm
  have hne : Work.BW.castVec (u i) ≠ 0 := huind.ne_zero i
  have hFne : F (Work.BW.castVec (u i)) ≠ 0 := fun h0 => hne ((hF.eq_zero _).mp h0)
  have hpos : 0 < F (Work.BW.castVec (u i)) :=
    lt_of_le_of_ne (hF.nonneg _) (Ne.symm hFne)
  have hge : F (Work.BW.castVec (u i))
      ≤ Work.BW.succMinBody (Work.BW.latOf (1 : Matrix (Fin d) (Fin d) ℤ)) K (i.1 + 1) := by
    rw [h1]; exact hubd i
  have hlampos : 0 < Work.BW.succMinBody (Work.BW.latOf (1 : Matrix (Fin d) (Fin d) ℤ)) K (i.1 + 1) :=
    lt_of_lt_of_le hpos hge
  rw [hlevelK] at hlampos hge
  rw [hlevelK, smulSet_unitBall_eq F hF hlampos]
  exact hge

end Work.BW.Minkowski2
