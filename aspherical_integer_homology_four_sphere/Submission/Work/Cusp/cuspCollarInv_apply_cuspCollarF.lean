import Mathlib
import Submission.Work.Cusp.CuspCollarAux

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Cusp

/-- **`cuspCollarInv` is a left inverse of `cuspCollarF` on the collar source.**  Every point
`q = (x, s)` of the collar source is recovered from its `(u,t,y)`-coordinates: the horizontal part
`x` is reassembled by `cuspX` from the perimeter coordinate `u = outerU v x` and the phase
`y = outerY v x` (`cuspX_outerU_outerY`), and the height `s` comes back from the recovered layer
parameter `t = ‖(cuspInvOuter v q).1‖∞` by inverting `collarHeight` at the ceiling
`β x` (`collarHeight_of_log`, `cuspInvOuter_nrm_fst_eq`). -/
theorem cuspCollarInv_apply_cuspCollarF (v : Fin 5) (c : Work.Cusp.E3) (δ : ℝ)
    (q : {q : Work.Cusp.E4 // q ∈ Work.Cusp.cuspCollarSource v c δ}) :
    Work.Cusp.cuspCollarInv v (Work.Cusp.cuspCollarF v c δ q) = q.1 := by
  -- Unpack the collar source hypothesis: the point lies in `cuspSource`, hence in `cuspBox`,
  -- with height in `(s₁, s_J)`.
  have hsrc : q.1 ∈ cuspSource v c δ := q.2.1
  obtain ⟨-, hs1, hsJ, -, -⟩ := q.2.1.1
  -- The height is positive, and `log (β x) ≠ log s_J` because `β x ≤ βMax < s_J`.
  have hq3pos : 0 < q.1 3 := lt_trans (by norm_num [s1]) hs1
  have hne : Real.log (beta (xOf q.1)) ≠ Real.log sJ :=
    ne_of_lt (Real.log_lt_log (beta_pos _) (lt_of_le_of_lt (beta_le_max _) betaMax_lt_sJ))
  -- Unfold both maps: the composite is the explicit reassembly of the point from its coordinates.
  have hkey : cuspCollarInv v (cuspCollarF v c δ q)
      = mkE4 (cuspX v (outerU v (xOf q.1)) (outerY v (xOf q.1)))
          (collarHeight (nrm (cuspInvOuter v q.1).1)
            (beta (cuspX v (outerU v (xOf q.1)) (outerY v (xOf q.1))))) := rfl
  -- Recover the horizontal part, then the height, then reassemble `q`.
  rw [hkey, cuspX_outerU_outerY v (xOf q.1), cuspInvOuter_nrm_fst_eq v c δ q.1 hsrc,
    collarHeight_of_log (beta (xOf q.1)) (q.1 3) hq3pos hne, mkE4_xOf_three]

end Work.Cusp
