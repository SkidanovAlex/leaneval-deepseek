import Mathlib
import Submission.Work.Subdivision.Level

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Adding one top cell to the refined skeletal filtration

`sdTopMod P n E` (`PolyCW.sdTopMod`, `Submission/Work/Subdivision/Level.lean`) is the
`n`-skeleton of the barycentric subdivision of `P` together with the simplices whose
*top* vertex is an `(n+1)`-cell belonging to the finset `E`.

This file computes the effect of adjoining one further `(n+1)`-cell `a` to `E`.  The
only new simplices are those whose top vertex is `a`; every vertex of such a simplex
is `≤ a`, and conversely a simplex all of whose vertices are `≤ a` has top vertex of
dimension `≤ n+1`, so it is either in the `n`-skeleton (if its top vertex has
dimension `≤ n`) or has top vertex `a` (since `a` is the unique cell below `a` of
dimension `n+1`).  Hence the new part is exactly the submodule `leSub P a k` of chains
supported below `a`:

`sdTopMod P n (insert a E) k = sdTopMod P n E k ⊔ leSub P a k`.

This is the subdivided companion of `PolyCW.cellTopMod_insert_succ`; it is the first
step in identifying the successive quotient of the refined filtration with the local
complex of the new cell.
-/

namespace Work.Subdivision

namespace PolyCW

variable (P : PolyCW)

/-- Chains supported on the set of simplices below a cell `a` of dimension `n+1` all
lie in `sdTopMod P n (insert a E) k`. -/
theorem leSub_le_sdTopMod_insert {n : ℕ} {a : P.Cell} (ha : P.dim a = n + 1)
    (E : Finset P.Cell) (k : ℕ) :
    leSub P a k ≤ sdTopMod P n (insert a E) k := by
  show Submodule.span ℤ {y : (sdChain P).X k | ∃ σ : Simplex P.Cell k,
    (∀ i, σ i ≤ a) ∧ y = sdElem P σ} ≤ sdTopMod P n (insert a E) k
  refine (Submodule.span_le).mpr ?_
  rintro y ⟨σ, hσ, rfl⟩
  have hlast : σ (Fin.last k) ≤ a := hσ (Fin.last k)
  have hdim : P.dim (σ (Fin.last k)) ≤ n + 1 := by
    rw [← ha]
    exact P.dim_le hlast
  rcases lt_or_eq_of_le hdim with hlt | heq
  · refine sdSubMod_le_sdTopMod P n (insert a E) k (sdElem_mem_sdSubMod P fun i => ?_)
    have hle : σ i ≤ σ (Fin.last k) := σ.strictMono.monotone (Fin.le_last i)
    exact le_trans (P.dim_le hle) (by omega)
  · have h_eq : σ (Fin.last k) = a := by
      by_contra hne
      have hlt' : P.dim (σ (Fin.last k)) < P.dim a := P.dim_lt hlast hne
      omega
    exact sdElem_mem_sdTopMod P n (insert a E) k σ
      (by rw [h_eq]; exact Finset.mem_insert_self a E)
      (by rw [h_eq]; exact ha)

end PolyCW

open PolyCW

theorem sdTopMod_insert (P : Work.Subdivision.PolyCW) (n : ℕ) (E : Finset P.Cell) {a : P.Cell}
    (ha : P.dim a = n + 1) (k : ℕ) :
    Work.Subdivision.PolyCW.sdTopMod P n (insert a E) k =
      Work.Subdivision.PolyCW.sdTopMod P n E k ⊔ Work.Subdivision.PolyCW.leSub P a k := by
  refine le_antisymm ?_ ?_
  · rw [sdTopMod]
    refine sup_le (le_trans le_sup_left le_sup_left) ?_
    refine (Submodule.span_le).mpr ?_
    rintro y ⟨σ, hin, hd, rfl⟩
    rcases Finset.mem_insert.mp hin with h_eq | hE
    · exact Submodule.mem_sup_right (sdElem_mem_leSub P fun i => by
        rw [← h_eq]
        exact σ.strictMono.monotone (Fin.le_last i))
    · exact Submodule.mem_sup_left
        (Submodule.mem_sup_right (Submodule.subset_span ⟨σ, hE, hd, rfl⟩))
  · refine sup_le (P.sdTopMod_mono n (Finset.subset_insert a E) k) ?_
    exact P.leSub_le_sdTopMod_insert ha E k

end Work.Subdivision
