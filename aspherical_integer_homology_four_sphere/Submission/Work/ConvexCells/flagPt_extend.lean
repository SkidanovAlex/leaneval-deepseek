import Mathlib
import Submission.Work.ConvexCells.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.ConvexCells

/-- Barycentric extension of a flag point: if `f` is a proper superface of the top face of the
flag underlying `s`, then the point `(1 - μ) • posR f + μ • s.toE'` on the segment joining the
new vertex `posR f` to `s.toE'` is again the realization of a flag point (namely the flag `s`
with `f` appended and weights `μ` on the old faces and `1 - μ` on `f`). -/
theorem flagPt_extend {d : ℕ} (P : PolytopeData d) (s : P.FlagPt) (f : Fin P.K)
    (hsub : P.SubFace s.topFace f) {μ : ℝ} (hμ0 : 0 < μ) (hμ1 : μ < 1) :
    ∃ s' : P.FlagPt, s'.toE' = (1 - μ) • P.posR f + μ • s.toE' := by
  classical
  have hlen : (s.flag ++ [f]).length = s.flag.length + 1 := List.length_append
  have hpos1 : 0 < 1 - μ := sub_pos.mpr hμ1
  -- the master weight function on `ℕ`
  let W : ℕ → ℝ := fun k => if h : k < s.flag.length then μ * s.wt ⟨k, h⟩ else 1 - μ
  have hW_lt : ∀ (k : ℕ) (h : k < s.flag.length), W k = μ * s.wt ⟨k, h⟩ := by
    intro k h; dsimp only [W]; exact dite_eq_left h
  have hW_ge : ∀ (k : ℕ) (h : ¬ k < s.flag.length), W k = 1 - μ := by
    intro k h; dsimp only [W]; exact dite_eq_right h
  -- the weight function of the new flag point
  let w : Fin (s.flag ++ [f]).length → ℝ := fun i => W i.val
  have hw_pos : ∀ i, 0 < w i := by
    intro i
    by_cases h : (i : ℕ) < s.flag.length
    · rw [show w i = μ * s.wt ⟨(i:ℕ), h⟩ from by
          show W (i:ℕ) = μ * s.wt ⟨(i:ℕ), h⟩; exact hW_lt (i:ℕ) h]
      exact mul_pos hμ0 (s.wt_pos _)
    · rw [show w i = 1 - μ from by
          show W (i:ℕ) = 1 - μ; exact hW_ge (i:ℕ) h]
      exact hpos1
  have hw_sum : ∑ i, w i = 1 := by
    change ∑ i : Fin (s.flag ++ [f]).length, W ↑i = 1
    rw [Fin.sum_univ_eq_sum_range W (s.flag ++ [f]).length, hlen, Finset.sum_range_succ]
    have h2 : ∑ i ∈ Finset.range (s.flag.length), W i = μ := by
      rw [← Fin.sum_univ_eq_sum_range W (s.flag.length)]
      calc ∑ i : Fin s.flag.length, W ↑i = ∑ i : Fin s.flag.length, μ * s.wt i :=
            Finset.sum_congr rfl fun i _ => hW_lt i.val i.isLt
        _ = μ * ∑ i : Fin s.flag.length, s.wt i := by rw [Finset.mul_sum]
        _ = μ := by rw [s.wt_sum, mul_one]
    rw [h2, hW_ge s.flag.length (lt_irrefl _)]
    ring
  -- the flag condition
  have hflag : (s.flag ++ [f]).Pairwise P.SubFace := by
    rw [List.pairwise_append]
    refine ⟨s.isFlag, by simp, ?_⟩
    intro a ha b hb
    rw [List.mem_singleton] at hb
    subst hb
    have hsplit : s.flag = s.flag.dropLast ++ [s.topFace] := by
      rw [PolytopeData.FlagPt.topFace]
      exact (List.dropLast_append_getLast s.flag_ne_nil).symm
    rw [hsplit, List.mem_append, List.mem_singleton] at ha
    rcases ha with ha | ha
    · have hp := (List.pairwise_append.mp (hsplit ▸ s.isFlag)).2.2
      exact lt_trans hsub (hp a ha s.topFace (List.mem_singleton.mpr rfl))
    · subst ha
      exact hsub
  -- accessor lemmas for the appended list
  have hget : ∀ (i : ℕ) (h : i < s.flag.length) (h' : i < (s.flag ++ [f]).length),
      (s.flag ++ [f]).get ⟨i, h'⟩ = s.flag.get ⟨i, h⟩ := by
    intro i h h'
    rw [List.get_eq_getElem, List.get_eq_getElem, List.getElem_append_left h]
  -- the total function realising `toE'`
  let F : ℕ → E d := fun k =>
    if h : k < (s.flag ++ [f]).length then W k • P.posR ((s.flag ++ [f]).get ⟨k, h⟩) else 0
  have hF_lt : ∀ (k : ℕ) (h : k < (s.flag ++ [f]).length),
      F k = W k • P.posR ((s.flag ++ [f]).get ⟨k, h⟩) := by
    intro k h; dsimp only [F]; exact dite_eq_left h
  have hpt : ∀ (i : ℕ) (hi : i < s.flag.length),
      F i = μ • (s.wt ⟨i, hi⟩ • P.posR (s.flag.get ⟨i, hi⟩)) := by
    intro i hi
    have h' : i < (s.flag ++ [f]).length := by rw [hlen]; omega
    rw [hF_lt i h', hW_lt i hi, hget i hi h']
    exact (smul_smul μ (s.wt ⟨i, hi⟩) (P.posR (s.flag.get ⟨i, hi⟩))).symm
  have hFm : F s.flag.length = (1 - μ) • P.posR f := by
    have h' : s.flag.length < (s.flag ++ [f]).length := by rw [hlen]; omega
    have hg : (s.flag ++ [f]).get ⟨s.flag.length, h'⟩ = f := by
      rw [List.get_eq_getElem]; exact List.getElem_concat_length rfl _
    rw [hF_lt s.flag.length h', hW_ge s.flag.length (lt_irrefl _), hg]
  have hFr : ∑ i ∈ Finset.range (s.flag.length), F i = μ • s.toE' := by
    rw [← Fin.sum_univ_eq_sum_range F (s.flag.length)]
    trans ∑ i : Fin s.flag.length, μ • (s.wt i • P.posR (s.flag.get i))
    · exact Finset.sum_congr rfl fun i _ => hpt i i.isLt
    · show (∑ i : Fin s.flag.length, μ • (s.wt i • P.posR (s.flag.get i)))
        = μ • ∑ i : Fin s.flag.length, s.wt i • P.posR (s.flag.get i)
      exact (Finset.smul_sum).symm
  refine ⟨{ flag := s.flag ++ [f], isFlag := hflag, wt := w, wt_pos := hw_pos, wt_sum := hw_sum },
    ?_⟩
  show (∑ i : Fin (s.flag ++ [f]).length, w i • P.posR ((s.flag ++ [f]).get i))
      = (1 - μ) • P.posR f + μ • s.toE'
  have step1 : (∑ i : Fin (s.flag ++ [f]).length, w i • P.posR ((s.flag ++ [f]).get i))
      = ∑ i : Fin (s.flag ++ [f]).length, F i.val := by
    refine Finset.sum_congr rfl fun i _ => ?_
    show W i.val • P.posR ((s.flag ++ [f]).get ⟨i.val, i.isLt⟩) = F i.val
    rw [hF_lt i.val i.isLt]
  rw [step1, Fin.sum_univ_eq_sum_range F (s.flag ++ [f]).length, hlen,
    Finset.sum_range_succ, hFr, hFm, add_comm]

end Work.ConvexCells
