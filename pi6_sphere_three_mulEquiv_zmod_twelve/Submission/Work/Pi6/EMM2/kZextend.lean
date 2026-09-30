import Mathlib
import Submission.Work.Pi6.EMM2.kZchain
import Submission.Work.EMFG.killCellsExtend
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

/-!
# Extending a map over the "kill `π₃, …, π_M`" tower (area EMM2)

`Work.Pi6.EMM2.kZ Y k` is `Y` with `k` rounds of "attach an `(m+2)`-cell along *every* map
`S^{m+1} → −`" applied for `m = 2, …, k+1`; thus `kZ Y (k+1) = KillCells (k+2) (kZ Y k)`
definitionally, the inclusion `kZUp Y k : Y → kZ Y k` is the composite of the one-step inclusions,
and `Work.Serre.killCells_step` says that the `(k+1)`-st round kills `π_{k+3}` while preserving the
lower degrees.

The theorem below is the universal property needed to build a range model of `K(ℤ,2)` out of `Y`:
**a map `φ : Y → Z` into a space whose `π_i` vanish for `3 ≤ i ≤ M` extends over
`kZ Y (M - 2)`**.  The extension is built level by level; the extension over a single round is
`Work.EMFG.killCellsExtend` (a map into a space with `π_{m+1} = 0` extends over `KillCells m −`).
-/

open scoped Topology

namespace Work.Pi6.EMM2

noncomputable section

theorem kZextend {Y Z : Type} [TopologicalSpace Y] [TopologicalSpace Z] (M : ℕ) (hM : 3 ≤ M)
    (φ : C(Y, Z))
    (hZ : ∀ (z : Z) (i : ℕ), 3 ≤ i → i ≤ M → Subsingleton (HomotopyGroup (Fin i) Z z)) :
    ∃ φ' : C(Work.Pi6.EMM2.kZ Y (M - 2), Z),
      φ'.comp (Work.Pi6.EMM2.kZUp Y (M - 2)) = φ := by
  classical
  -- The extension, built round by round: for every `k ≤ M - 2` the map `φ` extends to `kZ Y k`.
  -- The `(k+1)`-st round attaches `(k+3)`-cells, whose attaching maps lie in `π_{k+3}` and hence
  -- die in `Z` because `k + 3 ≤ M`.
  have main : ∀ k : ℕ, k ≤ M - 2 → ∃ ψ : C(kZ Y k, Z), ψ.comp (kZUp Y k) = φ := by
    intro k
    induction k with
    | zero =>
        intro _
        exact ⟨φ, by rw [kZUp_zero]; exact ContinuousMap.comp_id φ⟩
    | succ j ih =>
        intro hj
        obtain ⟨ψ, hψ⟩ := ih (by omega)
        obtain ⟨ψ', hψ'⟩ := Work.EMFG.killCellsExtend (j + 2) ψ
          (fun z => hZ z (j + 3) (by omega) (by omega))
        refine ⟨ψ', ?_⟩
        show ψ'.comp ((Work.Serre.killIncl (j + 2) (kZ Y j)).comp (kZUp Y j)) = φ
        rw [← ContinuousMap.comp_assoc, hψ', hψ]
  exact main (M - 2) le_rfl

end

end Work.Pi6.EMM2
