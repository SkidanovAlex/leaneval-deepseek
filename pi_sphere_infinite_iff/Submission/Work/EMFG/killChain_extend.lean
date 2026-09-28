import Mathlib
import Submission.Work.EMFG.killChain
import Submission.Work.EMFG.sphereMap_homotopy
import Submission.Work.EMFG.killCellsExtend
import Submission.Work.EMFG.killChainUp_pi_bijective
import Submission.Work.EMFG.killChain_pi_subsingleton

/-!
# Extending a map over the iterated "kill everything" chain

`Work.EMFG.killChain Y k` is the `k`-fold iterate of the "attach an `(m+2)`-cell along *every* map
`S^{m+1} → -`" construction: `killChain Y k = KillCells k (⋯ (KillCells 1 Y))`.  It kills
`π_2, …, π_{k+1}` and leaves `π_0`, `π_1` alone (`Work.EMFG.killChain_pi_subsingleton`,
`Work.EMFG.killChainUp_pi_bijective`).

The theorem below is the statement needed to compare two `π_1`-isomorphisms without losing the
higher degrees: **a map `φ : Y → B` into a space whose `π_i` vanish for `2 ≤ i ≤ N` extends to
`killChain Y (N-1)`**, and the extension is again a `π_0`/`π_1`-isomorphism.  The extension is
built level by level: at each stage the cells attached have dimension at most `N+1`, their
attaching maps lie in `π_i` of the current space for `i ≤ N`, and each such class dies in `B`
because `π_i (B) = 0`; the extension over one stage is `Work.EMFG.killCellsExtend`.
-/

open scoped Topology Topology.Homotopy unitInterval

namespace Work.EMFG

noncomputable section

theorem killChain_extend {Y B : Type} [TopologicalSpace Y] [TopologicalSpace B]
    (y₀ : Y) (φ : C(Y, B)) (N : ℕ)
    (hB : ∀ (p : B) (i : ℕ), 2 ≤ i → i ≤ N → Subsingleton (HomotopyGroup (Fin i) B p)) :
    ∃ φ' : C(Work.EMFG.killChain Y (N - 1), B),
      (∀ y : Y, φ' (Work.EMFG.killChainUp Y (N - 1) y) = φ y) ∧
      (∀ (i : ℕ), i ≤ 1 → ∀ p : Y,
        Function.Bijective (Work.Serre.piMapN (Work.EMFG.killChainUp Y (N - 1)) i p)) ∧
      (∀ (p : Work.EMFG.killChain Y (N - 1)) (i : ℕ), 2 ≤ i → i ≤ N →
        Subsingleton (HomotopyGroup (Fin i) (Work.EMFG.killChain Y (N - 1)) p)) := by
  classical
  -- The extension, built level by level: for every `k ≤ N - 1` the map `φ` extends to
  -- `killChain Y k`, the new cells being attached along classes of `π_{j+2}` for `j + 2 ≤ N`.
  have main : ∀ k : ℕ, k ≤ N - 1 → ∃ ψ : C(killChain Y k, B),
      ψ.comp (killChainUp Y k) = φ := by
    intro k
    induction k with
    | zero =>
        intro _
        exact ⟨φ, by ext y; rfl⟩
    | succ j ih =>
        intro hj
        obtain ⟨ψ, hψ⟩ := ih (by omega)
        obtain ⟨ψ', hψ'⟩ := killCellsExtend (j + 1) ψ
          (fun z => hB z (j + 2) (by omega) (by omega))
        refine ⟨ψ', ?_⟩
        show ψ'.comp ((Work.Serre.killIncl (j + 1) (killChain Y j)).comp (killChainUp Y j)) = φ
        rw [← ContinuousMap.comp_assoc, hψ', hψ]
  obtain ⟨Φ, hΦ⟩ := main (N - 1) le_rfl
  refine ⟨Φ, ?_, ?_, ?_⟩
  · intro y
    exact congrFun (congrArg (fun k : C(Y, B) => ⇑k) hΦ) y
  · intro i hi p
    exact killChainUp_pi_bijective (N - 1) i hi p
  · intro p i h2 hN
    exact killChain_pi_subsingleton (N - 1) p i h2 (by omega)

end

end Work.EMFG
