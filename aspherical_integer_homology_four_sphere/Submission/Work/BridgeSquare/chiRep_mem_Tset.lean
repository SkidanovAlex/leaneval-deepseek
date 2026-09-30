import Mathlib
import Submission.Work.BridgeSquare.Data

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open scoped BigOperators

namespace Work.BridgeSquare

/-- **The characteristic map of a flag meeting the truncation meets `Tset`.**

If some constraint `c ≥ 24` of the polytope `Q̄` is tight at the top face of the flag `x.2`, then the
point of the open simplex of the flag carried by any point `w` of the standard simplex lies on the
truncation facet with index `c - 24`: the image of `x` under the characteristic map therefore lands
in the truncation set `Tset = mk '' Xtrunc` of `M̄`.

Concretely, the constraint `c = Fin.natAdd 24 v` is tight at `ptW`, so
`inner ℝ (QbarPD.nR c) (ptW) = QbarPD.bR c`, i.e. `5 * (truncNormal2 v · ptW) = 8`, which is exactly
`truncSlack v ptW = 0`. -/
theorem chiRep_mem_Tset {n : ℕ} (x : Work.MbarHomology.FlagQ n)
    (h : ∃ c : Fin 48, c ∈ Work.MbarHomology.qTight (Work.MbarHomology.Mbar.topIdx x.2) ∧ 24 ≤ c.val) :
    ∀ w : Convexity.StdSimplex ℝ (Fin (n + 1)),
      Work.MbarHomology.Mbar.chiRep x w ∈ Work.FoldInst.Tset := by
  intro w
  obtain ⟨c, hc, hcv⟩ := h
  -- a tight constraint of index `≥ 24` is the truncation constraint of `v := c - 24`
  obtain ⟨v, hv⟩ : ∃ v : Fin 24, c = Fin.natAdd 24 v := ⟨⟨c.val - 24, by omega⟩, by
    refine Fin.ext ?_
    simp [Fin.natAdd]
    omega⟩
  refine ⟨(x.1, Work.MbarHomology.Mbar.chiPt x w), ⟨v, ?_⟩, rfl⟩
  change Work.FoldInst.truncSlack v
    (Work.MbarHomology.Mbar.ptW x.2 (fun i => w.weights i)) = 0
  set y : Work.FoldInst.E4 := Work.MbarHomology.Mbar.ptW x.2 (fun i => w.weights i) with hydef
  have hc' : c ∈ Work.MbarHomology.QbarPD.tight (Work.MbarHomology.Mbar.topIdx x.2) := hc
  -- the tight set of the top face of the flag is contained in the tight set of `ptW`
  have hmem : c ∈ Work.MbarHomology.QbarPD.tightAt y := by
    rw [hydef]
    exact Work.MbarHomology.Mbar.tight_top_subset_tightAt x.2
      (fun i => w.nonneg i) (Work.MbarHomology.Mbar.sum_weights w) hc'
  -- `ptW` lies in the polytope `Q̄`
  have hPset : y ∈ Work.MbarHomology.QbarPD.Pset := by
    rw [hydef, Work.MbarHomology.QbarPD_Pset]
    exact Work.MbarHomology.Mbar.ptW_mem x.2 (fun i => w.nonneg i)
      (Work.MbarHomology.Mbar.sum_weights w)
  have hEq : inner ℝ (Work.MbarHomology.QbarPD.nR c) y = Work.MbarHomology.QbarPD.bR c :=
    (Work.ConvexCells.PolytopeData.tightAt_of_mem Work.MbarHomology.QbarPD hPset c).mp hmem
  have hbR : Work.MbarHomology.QbarPD.bR c = 8/1920 := by
    rw [hv]
    simp only [Work.ConvexCells.PolytopeData.bR, Work.MbarHomology.QbarPD_rhs,
      Work.MbarHomology.QbarPD_D, Work.MbarHomology.qRhs_natAdd]
    norm_num
  have hinner : inner ℝ (Work.MbarHomology.QbarPD.nR c) y
      = (5 * (∑ j, (Work.FoldInst.truncNormal2 v j : ℝ) * y j)) / 1920 := by
    rw [hv]
    have hf : Work.MbarHomology.QbarPD.nrm (Fin.natAdd 24 v)
        = fun k => 5 * Work.FoldInst.truncNormal2 v k := by
      funext k
      rw [Work.MbarHomology.QbarPD_nrm, Work.MbarHomology.qNrm_natAdd]
    simp only [Work.ConvexCells.PolytopeData.nR, Work.MbarHomology.QbarPD_D,
      inner_smul_left, RCLike.conj_to_real, Work.ConvexCells.inner_toE_right, inv_mul_eq_div]
    rw [hf]
    congr 1
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    push_cast
    ring
  have hkey : (∑ j, (Work.FoldInst.truncNormal2 v j : ℝ) * y j) = 8/5 := by
    have h2 := hEq
    rw [hinner, hbR] at h2
    linarith
  rw [Work.FoldInst.truncSlack, hkey]
  norm_num

end Work.BridgeSquare
