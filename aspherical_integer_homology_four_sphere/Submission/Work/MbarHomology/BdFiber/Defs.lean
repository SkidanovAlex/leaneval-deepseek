/-
# The boundary of `M̄` on the fibres of `moCell`: definitions and generic bridges

This file prepares the proof of `Work.MbarHomology.BdFiber.mbarBd_fiber`, the "fibre at a cell"
form of the boundary compatibility of the cell atlas of `M̄`.

The geometric side of the boundary of the `e`-th cell of `M̄` in degree `n + 1` is the sparse
vector `gcol n e`: over the facets `G` of the root face `R` of that cell, the pair
`(moCell c G, qInc R G * oS (sigVec c G) G)` (with `c` the copy of the root node).  The target
statement is the `f`-th coordinate of this sparse vector, so the whole identity is the sparse
vector equality `colOk n e`; it is checked column by column (`decide`), and the per-column facts
are the chunk lemmas of `Cols.lean`.

The bridges from the `Finset.sum` of the target statement to `SVec.toFun` are generic
(`sum_filter_toFun`) and involve no computation; likewise the reindexing along the injective
`moCid n` (`toFun_map_inj`).
-/
import Mathlib
import Submission.Work.MbarHomology.BdFiber.QbarFacetList
import Submission.Work.Certificates.SVec.eqb_sound
import Submission.Work.Certificates.SVec.toFun_norm

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false

namespace Work.MbarHomology.BdFiber

open Work.Certificates

/-- **The geometric column of the boundary**: for the cell `e` of `M̄` in degree `n + 1`, the
sparse vector in `ℤ^{482}` whose `f`-th coordinate is the sum of `qInc R G * oS (sigVec c G) G`
over the facets `G` of the root face `R` with `moCell c G = moCid f`.

The branches of the `if` are dead when `n + 1 ≥ 5` (there are no such cells), but the definition
is stated without the hypothesis so that it is a function of `n` and `e` alone. -/
def gcol (n : ℕ) (e : Fin (Work.HomologyIso.Gen.mbarDim (n + 1))) : SVec 482 :=
  if _h : n + 1 < 5 then
    (qFacetL (Mbar.moRoot (Mbar.moCid ⟨n + 1, _h⟩ e))).map
      (fun G => (Mbar.moCell (Mbar.moRootC (Mbar.moCid ⟨n + 1, _h⟩ e)) G,
        qInc (Mbar.moRoot (Mbar.moCid ⟨n + 1, _h⟩ e)) G *
          oS (Mbar.sigVec (Mbar.moRootC (Mbar.moCid ⟨n + 1, _h⟩ e)) G) G))
  else []

/-- **The column of `mbarBd`**, read in the cell numbering of `M̄` in degree `n` (so that it can
be compared with `gcol`). -/
def imgCol (n : ℕ) (e : Fin (Work.HomologyIso.Gen.mbarDim (n + 1))) : SVec 482 :=
  if _h : n + 1 < 5 then
    ((Work.HomologyIso.Gen.mbarBd n).img e).map
      (fun p => (Mbar.moCid ⟨n, by omega⟩ p.1, p.2))
  else []

/-- **The sparse check of one column of the boundary compatibility.** -/
def colOk (n : ℕ) (e : Fin (Work.HomologyIso.Gen.mbarDim (n + 1))) : Bool :=
  SVec.eqb (gcol n e) (imgCol n e)

/-- A successful sparse check gives the equality of the two represented functions. -/
theorem colOk_sound {n : ℕ} {e : Fin (Work.HomologyIso.Gen.mbarDim (n + 1))}
    (h : colOk n e = true) : SVec.toFun (gcol n e) = SVec.toFun (imgCol n e) :=
  SVec.eqb_sound h

/-! ### Generic bridges -/

/-- **The filtered sum as a sparse vector.**  For a list `l` without repetitions and a target
index `t`, the sum of `w` over the elements of `l` (as a `Finset`) whose `pc`-value is `t` is
the `t`-th coordinate of the sparse vector of the pairs `(pc G, w G)`. -/
theorem sum_filter_toFun {ι : Type*} {N : ℕ} [DecidableEq ι]
    (l : List ι) (hl : l.Nodup) (pc : ι → Fin N) (w : ι → ℤ) (t : Fin N) :
    (∑ G ∈ l.toFinset.filter (fun G => pc G = t), w G)
      = SVec.toFun (l.map (fun G => (pc G, w G))) t := by
  rw [Finset.sum_filter, List.sum_toFinset (fun G => if pc G = t then w G else 0) hl]
  show (List.map (fun G => if pc G = t then w G else 0) l).sum
      = (List.map (fun p => if p.1 = t then p.2 else 0)
          (List.map (fun G => (pc G, w G)) l)).sum
  rw [List.map_map]
  congr 1

/-- **Reindexing a sparse vector along an injective map.** -/
theorem toFun_map_inj {N M : ℕ} (φ : Fin N → Fin M) (hφ : Function.Injective φ)
    (v : SVec N) (t : Fin N) :
    SVec.toFun (v.map (fun p => (φ p.1, p.2))) (φ t) = SVec.toFun v t := by
  rw [SVec.toFun, SVec.toFun, List.map_map]
  apply congrArg List.sum
  rw [List.map_congr_left (l := v)
      (f := (fun p => if p.1 = φ t then p.2 else 0) ∘ (fun p => (φ p.1, p.2)))
      (g := fun p => if p.1 = t then p.2 else 0)
      (fun a _ => by by_cases h : a.1 = t <;> simp [h, hφ.eq_iff])]

/-- `moCid n` is injective, because `moPos` is a left inverse on the cells of a fixed dimension. -/
theorem moCid_injective (n : ℕ) (hn : n < 5) :
    Function.Injective (Mbar.moCid ⟨n, hn⟩) := by
  intro f f' h
  apply Fin.ext
  have hf : Mbar.moPos (Mbar.moCid ⟨n, hn⟩ f) = f.val := (Mbar.moCid_spec ⟨n, hn⟩ f).2
  have hf' : Mbar.moPos (Mbar.moCid ⟨n, hn⟩ f') = f'.val := (Mbar.moCid_spec ⟨n, hn⟩ f').2
  rw [← hf, h, hf']

end Work.MbarHomology.BdFiber
