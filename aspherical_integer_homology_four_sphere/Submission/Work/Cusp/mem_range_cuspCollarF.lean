import Mathlib
import Submission.Work.Cusp.CuspCollarAux
import Submission.Work.Cusp.collarHeight_half

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Cusp

/-- **The range of the collar coordinate is the box of `(u,y)`-coordinates.**  A point
`p = ((u,t), y)` of the collar target (with `(u,t) ∈ (0,1) × (1/2,1]`) lies in the range of
`cuspCollarF v c δ` exactly when the recovered cusp coordinate `cuspX v u y` lies in the box of
side `2δ` around `c`.

For the forward implication the horizontal part of the recovered point is
`cuspX v (outerU v x) (outerY v x) = x` for `x = xOf q`, which lies in the box because
`q ∈ cuspSource v c δ`.  For the converse the preimage of `(u,t,y)` is the point
`q = (cuspX v u y, collarHeight t (β (cuspX v u y)))`: the ceiling condition `β x ≤ q 3` is the
antitone round trip `β x = collarHeight 1 (β x) ≥ collarHeight t (β x)`, the height window
`(s₁, s_J)` follows from `collarHeight_mem` and strict antitonicity at `t = 1/2`, and the layer
parameter comes back as `t` by `cuspInvOuter_nrm_fst_eq` and `collarHeight_inv`. -/
theorem mem_range_cuspCollarF (v : Fin 5) (c : Work.Cusp.E3) (δ : ℝ)
    (p : {z : ℝ × ℝ // z ∈ Work.Cusp.collarLayerDom} × Work.Cusp.E2) :
    p ∈ Set.range (Work.Cusp.cuspCollarF v c δ) ↔
      Work.Cusp.cuspCollarCoords p ∈ Work.Cusp.cuspCollarBox v c δ := by
  constructor
  · rintro ⟨q, rfl⟩
    have h1 : cuspCollarCoords (cuspCollarF v c δ q)
        = (outerU v (xOf q.1), outerY v (xOf q.1)) := rfl
    simp only [cuspCollarBox, Set.mem_ofPred_eq]
    intro i
    rw [h1, cuspX_outerU_outerY v (xOf q.1)]
    exact q.2.1.1.1 i
  · intro hbox
    -- name the coordinates of the target point
    set z : ℝ × ℝ := (p.1 : ℝ × ℝ) with hz
    set y : E2 := p.2 with hy
    have hzmem : z ∈ collarLayerDom := by rw [hz]; exact p.1.2
    have hu0 : 0 < z.1 := hzmem.1
    have hu1 : z.1 < 1 := hzmem.2.1
    have ht12 : 1/2 < z.2 := hzmem.2.2.1
    have ht1 : z.2 ≤ 1 := hzmem.2.2.2
    have hcoord : cuspCollarCoords p = (z.1, y) := by
      simp only [cuspCollarCoords]
      simp [hz, hy]
    have hbox' : ∀ i, |(cuspX v z.1 y) i - c i| < δ := by
      simpa [cuspCollarBox, hcoord] using hbox
    -- the recovered horizontal part, ceiling and height
    set x : E3 := cuspX v z.1 y with hx
    set b : ℝ := beta x with hb
    set s : ℝ := collarHeight z.2 b with hs
    have hb_pos : 0 < b := by rw [hb]; exact beta_pos x
    have hb_lt_sJ : b < sJ := by
      rw [hb]; exact lt_of_le_of_lt (beta_le_max x) betaMax_lt_sJ
    -- the height `s` sits between the ceiling `b` and the junction `s_J`
    have hanti := collarHeight_strictAntiOn b hb_pos hb_lt_sJ
    have hbge : b ≤ s := by
      rw [hs]
      rcases lt_or_eq_of_le ht1 with hlt | heq
      · have h : collarHeight 1 b < collarHeight z.2 b :=
          hanti (Set.mem_univ z.2) (Set.mem_univ (1 : ℝ)) hlt
        rw [collarHeight_one b hb_pos] at h
        exact le_of_lt h
      · simp [heq, collarHeight_one b hb_pos]
    have hs_lt_sJ : s < sJ := by
      rw [hs]
      have h : collarHeight z.2 b < collarHeight (1/2) b :=
        hanti (Set.mem_univ (1/2 : ℝ)) (Set.mem_univ z.2) ht12
      rw [collarHeight_half b] at h
      exact h
    have hs_gt_s1 : s1 < s :=
      lt_of_lt_of_le (lt_of_lt_of_le s1_lt_betaMin (by rw [hb]; exact beta_min_le x)) hbge
    -- the preimage point
    have h_outerU : outerU v (xOf (mkE4 x s)) = z.1 := by
      rw [xOf_mkE4, hx, outerU_cuspX v z.1 y]
    have h_outerY : outerY v (xOf (mkE4 x s)) = y := by
      rw [xOf_mkE4, hx, outerY_cuspX v z.1 y]
    have hsrc : mkE4 x s ∈ cuspSource v c δ := by
      refine ⟨⟨?_, hs_gt_s1, hs_lt_sJ, ?_, ?_⟩, ?_⟩
      · intro i
        rw [xOf_mkE4]
        exact hbox' i
      · rw [h_outerU]; exact le_of_lt hu0
      · rw [h_outerU]; exact hu1
      · rw [xOf_mkE4, mkE4_apply_three, ← hb]
        exact hbge
    have hmem : mkE4 x s ∈ cuspCollarSource v c δ :=
      ⟨hsrc, by rw [h_outerU]; exact hu0⟩
    -- the layer parameter comes back
    have h_nrm : nrm (cuspInvOuter v (mkE4 x s)).1 = z.2 := by
      rw [cuspInvOuter_nrm_fst_eq v c δ (mkE4 x s) hsrc]
      rw [mkE4_apply_three, xOf_mkE4, ← hb]
      exact (collarHeight_inv z.2 b s hb_pos (ne_of_lt hb_lt_sJ) hs).symm
    -- assemble the equality of coordinates
    have h_fst : (cuspCollarF v c δ ⟨mkE4 x s, hmem⟩).1 = ⟨(z.1, z.2), hzmem⟩ := by
      apply Subtype.ext
      rw [cuspCollarF_fst]
      exact Prod.ext h_outerU h_nrm
    have h_snd : (cuspCollarF v c δ ⟨mkE4 x s, hmem⟩).2 = y := by
      rw [cuspCollarF_snd]
      exact h_outerY
    refine ⟨⟨mkE4 x s, hmem⟩, ?_⟩
    refine Prod.ext ?_ ?_
    · rw [h_fst]
    · rw [h_snd, hy]

end Work.Cusp
