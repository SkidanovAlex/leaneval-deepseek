import Mathlib
import Submission.Work.Subdivision.Level

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Subdivision

/-- Inserting an `(n+1)`-cell `a` into the index set `E` refines the `n`-th
skeletal level `cellTopMod P hdd n` in degree `n+1` exactly by adjoining the
line spanned by the new cell's generator.

In degree `n+1` the skeletal part `cellSubMod P hdd n (n+1)` is zero, so both
sides are the span of the `(n+1)`-cells of the index set; the spanning sets
differ by the single generator attached to `a`. -/
theorem cellTopMod_insert_succ (P : Work.Subdivision.PolyCW) (hdd : P.HasDdZero) (n : ℕ)
    (E : Finset P.Cell) {a : P.Cell} (ha : P.dim a = n + 1) :
    Work.Subdivision.PolyCW.cellTopMod P hdd n (insert a E) (n + 1) =
      Work.Subdivision.PolyCW.cellTopMod P hdd n E (n + 1) ⊔
        Submodule.span ℤ ({Work.Subdivision.PolyCW.cellElem P hdd (n + 1) ⟨a, ha⟩} :
          Set ((P.cellChain hdd).X (n + 1))) := by
  have hnot : ¬ (n + 1 ≤ n) := by omega
  have hbot := Work.Subdivision.PolyCW.cellSubMod_eq_bot P hdd hnot
  -- In degree `n+1` both moduli are the spans of the generators of the indexed cells.
  have hset : {y : (P.cellChain hdd).X (n + 1) |
        ∃ e : {e : P.Cell // P.dim e = n + 1},
          e.1 ∈ insert a E ∧ P.dim e.1 = n + 1 ∧
            y = Work.Subdivision.PolyCW.cellElem P hdd (n + 1) e}
      = {y : (P.cellChain hdd).X (n + 1) |
          ∃ e : {e : P.Cell // P.dim e = n + 1},
            e.1 ∈ E ∧ P.dim e.1 = n + 1 ∧
              y = Work.Subdivision.PolyCW.cellElem P hdd (n + 1) e}
        ∪ {Work.Subdivision.PolyCW.cellElem P hdd (n + 1) ⟨a, ha⟩} := by
    ext y; constructor
    · rintro ⟨e, he, hd, rfl⟩
      rcases Finset.mem_insert.mp he with h | he
      · right
        simp only [Set.mem_singleton_iff]
        exact congrArg _ (Subtype.ext h)
      · left; exact ⟨e, he, hd, rfl⟩
    · rintro (⟨e, he, hd, rfl⟩ | hy)
      · exact ⟨e, Finset.mem_insert_of_mem he, hd, rfl⟩
      · exact ⟨⟨a, ha⟩, Finset.mem_insert_self a E, ha, hy⟩
  simp only [Work.Subdivision.PolyCW.cellTopMod, hbot, bot_sup_eq]
  rw [hset, Submodule.span_union]

end Work.Subdivision
