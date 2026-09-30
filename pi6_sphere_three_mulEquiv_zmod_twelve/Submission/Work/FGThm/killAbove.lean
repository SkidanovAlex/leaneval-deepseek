import Mathlib
import Submission.Work.PiS.Interfaces
import Submission.Work.RatHurewicz.exists_killed_tower
import Submission.Work.RatHurewicz.tower_fibre_pi_bijective
import Submission.Work.RatHurewicz.towerStepData
import Submission.Work.Serre.surjective_pimap_setIncl_of_compressRel
import Submission.Work.RatHurewicz.LESConsequences
import Submission.Work.Serre.RangeOne.piMap_bijective_of_compress
import Submission.Work.FGThm.towerState_isRangeKModel
import Submission.Work.FGThm.towerState_fibre_pi_mulEquiv

/-!
# Area FGTHM: killing `π_{>k}` up to a range `N` (the truncation step of Serre's theorem)

For a `(k-1)`-connected space `X` and `2 ≤ k ≤ N`, this module produces the truncation map
`inc : X → Z` which kills `π_j` for `k < j ≤ N + 1` (hence is a range model of `K(π_k X, k)` through
`N`) and whose homotopy fibre is `k`-connected, with `π_{n+1}(fibre) ≅ π_{n+1}(X)` in the range
`k ≤ n`, `n + 1 ≤ N`.  The map is the composite inclusion of the cell-attachment tower
`Work.RatHurewicz.towerState`, run one step *beyond* `N` so that the fibre identification is
available in the top degree as well:

* `Work.RatHurewicz.IsRangeKModel k N (inc x₀)` — `π_j(Z) = 0` for `j ≤ N`, `j ≠ k`
  (`Work.FGThm.towerState_isRangeKModel`; the degrees `j < k` come from the compression property of
  the tower, the degrees `k < j ≤ N` from the cells attached);
* the homotopy fibre of `inc` is `k`-connected (`Work.FGThm.towerState_fibre_pi_subsingleton`);
* `π_{n+1}(fibre) ≃* π_{n+1}(X)` for `k ≤ n`, `n + 1 ≤ N`
  (`Work.FGThm.towerState_fibre_pi_mulEquiv`, the exactness of the long exact sequence of the pair at
  the two degrees killed above `N`);
* `π_k(X) → π_k(Z)` is onto, since compression pushes every based `k`-cube of `Z` into the range of
  `inc` (`Work.Serre.RangeOne.piMap_bijective_of_compress`).
-/

open scoped Topology

namespace Work.FGThm

noncomputable section

/-- **The homotopy fibre of the structure map of a tower state is `k`-connected.**

The tower `Y_0 = X ⊆ Y_1 ⊆ ⋯ ⊆ Y_s` has the compression property of the pair `(Y_s, range incl)`;
compression in dimensions `≤ k+1` makes the relative homotopy groups `π_j(Y_s, X)` vanish for
`j ≤ k` (`Work.RatHurewicz.subsingleton_relPi_of_compressRel`), and since the inclusion of the
range is a homeomorphism those are exactly the homotopy groups of the homotopy fibre of `incl`
(`Work.RatHurewicz.subsingleton_relPi_of_isEmbedding`). -/
theorem towerState_fibre_pi_subsingleton {X : Type} [TopologicalSpace X] {x₀ : X} {k s : ℕ}
    (st : Work.RatHurewicz.TowerState X x₀ k s) :
    ∀ j : ℕ, j ≤ k → Subsingleton (HomotopyGroup (Fin j)
      (Work.RatHurewicz.homotopyFibre st.incl x₀)
      (Work.RatHurewicz.homotopyFibreBasepoint st.incl x₀)) := by
  intro j hj
  have hset : Subsingleton (Work.RatHurewicz.RelHomotopyGroup
      (Work.RatHurewicz.setIncl (Set.range (st.incl : X → st.Y)))
      ⟨st.incl x₀, x₀, rfl⟩ j) :=
    Work.RatHurewicz.subsingleton_relPi_of_compressRel (Y := st.Y)
      (A := Set.range (st.incl : X → st.Y)) k ⟨st.incl x₀, x₀, rfl⟩ st.compress j hj
  exact Work.RatHurewicz.subsingleton_relPi_of_isEmbedding st.incl x₀ st.emb j hset

/-- **Killing `π_{> k}` in the range `≤ N` without changing `π_{≤ k}`.**  The truncation map
produced by the cell-attachment tower: `Z` is a range model of `K(π_k X, k)` through `N`, its
homotopy fibre is `k`-connected, the fibre inclusion is an isomorphism on `π_{n+1}` for
`k ≤ n`, `n + 1 ≤ N`, and the structure map is onto in degree `k`. -/
theorem killAbove (k N : ℕ) (hk : 2 ≤ k) (hN : k ≤ N)
    (X : Type) [TopologicalSpace X] (x₀ : X)
    (hconn : ∀ j : ℕ, j < k → Subsingleton (HomotopyGroup (Fin j) X x₀)) :
    ∃ (Z : Type) (_ : TopologicalSpace Z) (inc : C(X, Z)),
      Work.RatHurewicz.IsRangeKModel k N (inc x₀) ∧
      (∀ j : ℕ, j ≤ k → Subsingleton (HomotopyGroup (Fin j)
        (Work.RatHurewicz.homotopyFibre inc x₀)
        (Work.RatHurewicz.homotopyFibreBasepoint inc x₀))) ∧
      (∀ n : ℕ, k ≤ n → n + 1 ≤ N → Nonempty (HomotopyGroup (Fin (n + 1))
        (Work.RatHurewicz.homotopyFibre inc x₀)
        (Work.RatHurewicz.homotopyFibreBasepoint inc x₀) ≃*
        HomotopyGroup (Fin (n + 1)) X x₀)) ∧
      Function.Surjective (Work.StemsB.πmap inc (k - 1) x₀) := by
  -- the truncation tower, run one step beyond `N` so that the fibre identification is available
  -- in the top degree `n + 1 = N`
  let st := Work.RatHurewicz.towerState (x₀ := x₀) (k := k) hk (N + 1 - k)
  refine ⟨st.Y, st.inst, st.incl, ?_, ?_, ?_, ?_⟩
  · exact towerState_isRangeKModel hconn st (by omega)
  · exact towerState_fibre_pi_subsingleton st
  · intro n _hn hnN
    exact Work.FGThm.towerState_fibre_pi_mulEquiv hk st (by omega) (by omega)
  · exact (Work.Serre.RangeOne.piMap_bijective_of_compress st.incl st.emb (k + 1)
      (fun d hd => st.compress d hd) (k - 1) (by omega) x₀).2

end

end Work.FGThm
