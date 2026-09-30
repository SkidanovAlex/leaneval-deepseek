import Mathlib
import Submission.Work.Subdivision.PieceQuot
import Submission.Work.Subdivision.subdivCpt_mem

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The subdivision respects the refined cellular filtration of a skeletal level

`PolyCW.cellTopMod P hdd n E` (`Level.lean`) is the `n`-skeleton of the cellular
chain complex together with the `(n+1)`-cells belonging to the finset `E`; its
companion `PolyCW.sdTopMod P n E` is the `n`-skeleton of the barycentric
subdivision together with the simplices whose *top* vertex is an `(n+1)`-cell of
`E`.

This file proves that the subdivision chain map `subdiv : cellChain P ⟶ sdChain P`
carries the refined cellular filtration into the refined subdivided one:

`cellTopMod P hdd n E k ≤ (sdTopMod P n E k).comap ((subdiv P hdd haug).f k).hom`.

This is the per-cell refinement of `subdivCpt_mem` and the filtration
compatibility input for the induction over the successive quotients
`sdTopMod n (insert a E) / sdTopMod n E` that computes the graded map.

## Proof

`cellTopMod` is the supremum of the `n`-skeleton and the span of the
`(n+1)`-cells of `E` (in degree `k`; if `k ≠ n+1` the second summand is zero).

* On the `n`-skeleton the claim is `subdivCpt_mem`, together with the fact that
  the `n`-skeleton of the subdivision is contained in `sdTopMod`.
* On a generator `cellElem e` with `e ∈ E`, `P.dim e = n+1`: the subdivision
  chain `subdivCell e` has all its vertices `≤ e`.  Its top vertex is a cell
  `≤ e`; either it is `e` itself — hence lies in `E` and has dimension `n+1`, so
  the simplex belongs to `sdTopMod` directly — or it is a proper face of `e`,
  in which case all vertices have dimension `≤ n` and the simplex lies in the
  `n`-skeleton.  Membership is then decided simplex by simplex via
  `PolyCW.SdTopModInf.mem_of_support`.
-/

namespace Work.Subdivision

namespace PolyCW

variable (P : PolyCW)

/-- **The subdivision chain of a cell of `E` lies in `sdTopMod`.**  For a cell
`e` of dimension `k = n+1` belonging to `E`, the subdivision chain `subdivCell e`
belongs to the refined filtration `sdTopMod P n E k`: every simplex in its
support has all vertices `≤ e`, and its top vertex is either `e` itself (so it is
an `(n+1)`-cell of `E`) or a proper face of `e` (so all vertices have dimension
`≤ n`). -/
theorem subdivCell_mem_sdTopMod (n : ℕ) (E : Finset P.Cell) (k : ℕ)
    (e : {e : P.Cell // P.dim e = k}) (he : e.1 ∈ E) (hd : P.dim e.1 = n + 1) :
    subdivCell P k e ∈ sdTopMod P n E k := by
  refine SdTopModInf.mem_of_support P n E fun σ hσ => ?_
  rcases eq_or_ne (σ (Fin.last k)) e.1 with heq | hne
  · exact Or.inr ⟨heq ▸ he, heq ▸ hd⟩
  · refine Or.inl fun i => ?_
    have hle : σ (Fin.last k) ≤ e.1 := subdivCell_support P k e σ hσ (Fin.last k)
    have hile : σ i ≤ σ (Fin.last k) := σ.strictMono.monotone (Fin.le_last i)
    have hdim : P.dim (σ (Fin.last k)) < n + 1 := by
      rw [← hd]
      exact P.dim_lt hle hne
    have hle' := P.dim_le hile
    omega

end PolyCW

theorem subdivCpt_mem_top (P : Work.Subdivision.PolyCW)
    (hdd : P.HasDdZero) (haug : P.HasAugZero) (n : ℕ) (E : Finset P.Cell) (k : ℕ) :
    Work.Subdivision.PolyCW.cellTopMod P hdd n E k ≤
      (Work.Subdivision.PolyCW.sdTopMod P n E k).comap
        ((Work.Subdivision.PolyCW.subdiv P hdd haug).f k).hom := by
  rw [PolyCW.cellTopMod]
  refine sup_le ?_ ?_
  · intro x hx
    refine Submodule.mem_comap.mpr ?_
    exact PolyCW.sdSubMod_le_sdTopMod P n E k
      (Submodule.mem_comap.mp (subdivCpt_mem P hdd haug n k hx))
  · rw [Submodule.span_le]
    rintro y ⟨e, he, hd, rfl⟩
    refine Submodule.mem_comap.mpr ?_
    show PolyCW.subdivLM P k (PolyCW.cellElem P hdd k e) ∈ PolyCW.sdTopMod P n E k
    rw [PolyCW.subdivLM_single]
    exact PolyCW.subdivCell_mem_sdTopMod P n E k e he hd

end Work.Subdivision
