import Mathlib
import Submission.Work.Peluse.SwapC.cStPerm

namespace Work.Peluse.SwapC

open scoped BigOperators
open Work.Peluse (symIcc)
open Work.Peluse.LadderP.Swap (avg pbox slotAt slotCard)

/-- **The state at the end of the process is the conclusion of `concatAll`.**  `cSt I q M N f L` is
the average, over all `ι : (Fin s → Bool) → I`, of the box norm of `f` with the slot list `L`;
`genuineSlots (cproc s (2^s - 1))` is the slot list of the final subdivision (all leaves of depth
`s`), which by `cgenSlotsEndpoints` is the list `slotSet s` of the target.

The content is the computation of the coefficients of a difference slot,
`cA q ι (CC.dff j a b) = q (ι a) j` and `cB q ι (CC.dff j a b) = q (ι b) j`, and of
`(List.ofFn g).get k = g (Fin.cast _ k)` (`List.get_ofFn`).

Careful with the index types: `pbox (List.ofFn g).length` has index type
`Fin (List.ofFn g).length` while the target has `Fin (slotCard s)`; these are *not* definitionally
equal (`(List.ofFn g).length` does not reduce to `slotCard s`), so use `pbox_compEquiv`
(`Submission/Work/Peluse/SwapC/cStPerm.lean`) with `finCongr (by rw [List.length_ofFn])` (or
`List.length_ofFn ▸ ·`) as the bridge. -/
theorem cStFinalIdent (I : Type) [Fintype I] [Nonempty I] (s : ℕ) (hs : 1 ≤ s)
    (q : I → Fin s → ℤ) (M N : ℕ) (f : ℤ → ℂ)
    (h : (genuineSlots (cproc s (2 ^ s - 1))).Perm
      (List.ofFn (fun k : Fin (Work.Peluse.LadderP.Swap.slotCard s) =>
        CC.dff (Work.Peluse.LadderP.Swap.slotAt s k).1
          (Work.Peluse.LadderP.Swap.slotAt s k).2.1
          (Work.Peluse.LadderP.Swap.slotAt s k).2.2))) :
    cSt I q M N f (genuineSlots (cproc s (2 ^ s - 1)))
      = Work.Peluse.LadderP.Swap.avg (fun ι : (Fin s → Bool) → I =>
          Work.Peluse.LadderP.Swap.pbox (Work.Peluse.LadderP.Swap.slotCard s)
            (fun k => q (ι (Work.Peluse.LadderP.Swap.slotAt s k).2.1)
              (Work.Peluse.LadderP.Swap.slotAt s k).1)
            (fun k => q (ι (Work.Peluse.LadderP.Swap.slotAt s k).2.2)
              (Work.Peluse.LadderP.Swap.slotAt s k).1) M (Work.Peluse.symIcc N) f) := by
  -- the two slot lists are permutations of one another
  rw [cStPerm I q M N f h, cSt_def]
  -- it remains to compare the two `avg`s pointwise in the index assignment `ι`
  congr 1
  funext ι
  -- the index types: `Fin (List.ofFn g).length` versus `Fin (slotCard s)`
  have hd : (List.ofFn (fun k : Fin (slotCard s) =>
        CC.dff (slotAt s k).1 (slotAt s k).2.1 (slotAt s k).2.2)).length = slotCard s :=
    List.length_ofFn
  -- the coefficients of a difference slot
  have hA : (fun k : Fin (List.ofFn (fun k : Fin (slotCard s) =>
        CC.dff (slotAt s k).1 (slotAt s k).2.1 (slotAt s k).2.2)).length =>
        CC.cA q ι ((List.ofFn (fun k : Fin (slotCard s) =>
          CC.dff (slotAt s k).1 (slotAt s k).2.1 (slotAt s k).2.2)).get k))
      = fun k => q (ι (slotAt s (Fin.cast hd k)).2.1) (slotAt s (Fin.cast hd k)).1 := by
    funext k
    rw [List.get_ofFn]
    rfl
  have hB : (fun k : Fin (List.ofFn (fun k : Fin (slotCard s) =>
        CC.dff (slotAt s k).1 (slotAt s k).2.1 (slotAt s k).2.2)).length =>
        CC.cB q ι ((List.ofFn (fun k : Fin (slotCard s) =>
          CC.dff (slotAt s k).1 (slotAt s k).2.1 (slotAt s k).2.2)).get k))
      = fun k => q (ι (slotAt s (Fin.cast hd k)).2.2) (slotAt s (Fin.cast hd k)).1 := by
    funext k
    rw [List.get_ofFn]
    rfl
  rw [hA, hB]
  -- transport along the equality of the index types
  rw [pbox_compEquiv (finCongr hd) _ _ M (symIcc N) f]
  have hcast : ∀ k : Fin (slotCard s), Fin.cast hd ((finCongr hd).symm k) = k := fun k => by
    rw [← finCongr_apply, Equiv.apply_symm_apply]
  simp only [hcast]

end Work.Peluse.SwapC
