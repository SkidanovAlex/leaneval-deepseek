import Mathlib
import Submission.Work.Stems.Hur2c.PsiLinGenCubD
import Submission.Work.RatHurewicz.constCubeKilled
import Submission.Work.RatHurewicz.ConnectivityBridge
import Submission.Work.Stems.Hur2c.degen_cycle_mem_boundary_add_const

/-!
# `Ψ` of a degenerate `(m+2)`-cycle

**(E)** of `Submission/Work/Stems/PSI_DEG_NOTES.md`: the general-degree `T`-calculus.  The filling
`psiLinGen N m K hN` of `Work.Stems.Hur2c.PsiLinGen` kills every degenerate `(m+2)`-cycle, for `X`
with `π_i(X) = 0` for `i < m + 2`.  It is the crux `Work.RatHurewicz.DegenCycleKilled`.

## Vocabulary

The *generators* of `Work.RatHurewicz.Deg n X` are the cubes `degenProj i δ = δ ∘ π_i`, where
`π_i : I^{n+1} → I^n` is the projection dropping the coordinate `i` (this file).

## State of the proof (session notes)

* `Work.RatHurewicz.psiLinGen_single_cconst` (`constCubeKilled.lean`) — already in the tree —
  proves that `ΨLin` kills *every* constant cube, by applying `(Y)` to the tube
  `z ↦ γ (z last)`.  Hence the constant corrections are harmless.
* `psiLinGen_cubD_eq_zero` (`(Y)` in additive form) kills every cubical boundary.
* **(DET) same-direction determinacy** (route worked out, proof reduces to the topological input
  `Work.Stems.Hur2c.homotopyRel_of_boundary_eq`): for a *fixed* direction `i`, the value
  `Ψ (single (degenProj i δ) 1)` depends only on the faces of `δ`.  Proof: `π_{m+1}(X) = 0` gives a
  homotopy `H` from `δ` to `δ'` relative to `∂I^{m+1}`; the `(m+3)`-cube `τ z = H (dropᵢ z, last z)`
  has end faces `degenProj i δ`, `degenProj i δ'`, its `i`-faces cancel pairwise, and each of its
  remaining faces is determined by `δ` alone (as `H` is relative to the boundary); `(Y)` applied to
  `τ` and to the degenerate cube `u ↦ δ (dropᵢ u)` — whose face sum vanishes by the same
  cancellation — gives the equality.
* **Gap**: the *cross-direction* comparison and the assembly.  An element of `Deg (m+2) X` is a sum
  of cubes `degenProj i_j δ_j` with various directions, and the cycle condition only constrains the
  faces of the `δ_j`.  A sufficient chain-level route avoiding the filling family is

    `Deg (m+2) X ∩ ker (cubD (m+1) X) ⊆ range (cubD (m+2) X) + ⟨constant cubes⟩`,

  which the same `(Y)`-cobordism induction proves one level down at each step; `(E)` then follows
  from `(Y)` together with `psiLinGen_single_cconst`.
-/

open scoped unitInterval Topology
open Work.Stems.Cubical
open Work.RatHurewicz

namespace Work.Stems.Hur2c

noncomputable section

variable {X : Type} [TopologicalSpace X]

/-- The projection `I^{n+1} → I^n` dropping the coordinate `i`. -/
def projDrop (n : ℕ) (i : Fin (n + 1)) : C(IC (n + 1), IC n) :=
  ⟨fun t j => t (Fin.succAbove i j), continuous_pi fun _ => continuous_apply _⟩

@[simp] theorem projDrop_apply (n : ℕ) (i : Fin (n + 1)) (t : IC (n + 1)) (j : Fin n) :
    projDrop n i t j = t (Fin.succAbove i j) := rfl

/-- **The generic degenerate `(n+1)`-cube**: `δ` pulled back along the projection dropping the
coordinate `i`.  These cubes generate `Work.RatHurewicz.Deg (n+1) X`. -/
def degenProj {n : ℕ} (i : Fin (n + 1)) (δ : C(IC n, X)) : C(IC (n + 1), X) :=
  δ.comp (projDrop n i)

@[simp] theorem degenProj_apply {n : ℕ} (i : Fin (n + 1)) (δ : C(IC n, X)) (t : IC (n + 1)) :
    degenProj i δ t = δ (projDrop n i t) := rfl

theorem degenProj_indep {n : ℕ} (i : Fin (n + 1)) (δ : C(IC n, X)) :
    ∀ t t' : IC (n + 1), (∀ j : Fin (n + 1), j ≠ i → t j = t' j) →
      degenProj i δ t = degenProj i δ t' := by
  intro t t' h
  show δ (projDrop n i t) = δ (projDrop n i t')
  congr 1
  funext j
  rw [projDrop_apply, projDrop_apply]
  exact h _ (Fin.succAbove_ne i j)

theorem degenProj_mem_Deg {n : ℕ} (i : Fin (n + 1)) (δ : C(IC n, X)) :
    Finsupp.single (degenProj i δ) (1 : ℤ) ∈ Deg (n + 1) X := by
  rw [Deg]
  refine Submodule.mem_iSup_of_mem i (Submodule.subset_span ?_)
  exact ⟨degenProj i δ, degenProj_indep i δ, rfl⟩

theorem psiLinGen_degen_cycle (N m : ℕ) [Nontrivial (Fin (m + 2))] {X : Type} [TopologicalSpace X]
    {x₀ : X}
    (hconn : ∀ i : ℕ, i < m + 2 → Subsingleton (HomotopyGroup (Fin i) X x₀))
    (K : Work.RatHurewicz.Tower x₀ N) (hN : m + 1 ≤ N)
    (d : Work.Stems.Cubical.Cub (m + 2) X) (hd : d ∈ Work.RatHurewicz.Deg (m + 2) X)
    (hcyc : Work.Stems.Cubical.cubD (m + 1) X d = 0) :
    Work.Stems.Hur2c.psiLinGen N m K hN d = 0 := by
  haveI : PathConnectedSpace X :=
    Work.RatHurewicz.pathConnectedSpace_of_subsingleton_pi_zero x₀ (hconn 0 (by omega))
  have hmem := Work.Stems.Hur2c.degen_cycle_mem_boundary_add_const (m + 1) X x₀ (by omega)
    ‹PathConnectedSpace X› (fun i _ hi₂ => hconn i (by omega)) d hd hcyc
  obtain ⟨E, hE, c, hc, hsum⟩ := Submodule.mem_sup.mp hmem
  have hE' : Work.Stems.Hur2c.psiLinGen N m K hN E = 0 := by
    obtain ⟨E', rfl⟩ := hE
    exact Work.Stems.Hur2c.psiLinGen_cubD_eq_zero N m K hN E'
  have hc' : Work.Stems.Hur2c.psiLinGen N m K hN c = 0 := by
    rw [Work.RatHurewicz.ConstChain] at hc
    obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp hc
    rw [← ht, map_smul, Work.RatHurewicz.psiLinGen_single_cconst N m K hN x₀, smul_zero]
  rw [← hsum, map_add, hE', hc', add_zero]

end

end Work.Stems.Hur2c
