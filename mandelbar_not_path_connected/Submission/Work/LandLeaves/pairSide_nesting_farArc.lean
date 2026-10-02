import Mathlib
import Submission.Work.ELTop.All
import Submission.Work.TopJordan.Main
import Submission.Work.LandLeaves.TypeGeometry
import Submission.Work.LandLeaves.ccBet_v2_defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The nesting of the *far* sides of co-landing pairs: `ccBet u v w ⟹ pairSide (u,w) ⊆ pairSide (u,v)`

This file proves `Work.LandLeaves.pairSide_nesting_farArc`, the `⟹` direction of ingredient
(G1) of `NOTES_ccBet_v2_geometric_core.md`:

if the three rays of angles `u`, `v`, `w` all land at the same point `y` and the angle `w` lies
on the counterclockwise arc `(u, v)` (`Work.LandLeaves.ccBet u v w`), then the far side of the
pair `(u, w)` is contained in the far side of the pair `(u, v)`.

Equivalently, the far sides of the co-landing pairs `P_{uv}` form a *nesting* which encodes the
cyclic order of the landing angles.

## The argument

Write `P = (u, w, y)` and `Q = (u, v, y)`.

* `w ∈ (u, v)` means `v ∈ (w, u + 1)`, the *near* arc of `P`; hence the whole ray `R_v` lies in
  the near side `pairSideNear P` (`Work.ELTop.paramRay_subset_pairSideNear`).  As the two sides of
  `P` are disjoint (`Work.ELTop.pairSides_decomposition`, which needs no normalisation), the far
  side of `P` misses `R_v`; it also misses `R_u ∪ {y}` because those lie on the curve of `P`.
  So `pairSide P` misses the whole curve `pairCurve Q = R_u ∪ {y} ∪ R_v`, i.e.
  `pairSide P ⊆ (pairCurve Q)ᶜ`.

* The reference point `refP = rayPt (u + arcLen u w / 2) 2` of the far side of `P` has an angle in
  the arc `(u, w) ⊆ (u, v)`, so its ray lies in `pairSide Q`
  (`Work.ELTop.paramRay_subset_pairSide`); in particular `refP ∈ pairSide Q`.

* Since `pairSide P` is preconnected (`isPreconnected_connectedComponentIn`) and contained in
  `(pairCurve Q)ᶜ`, it is contained in the connected component of `(pairCurve Q)ᶜ` through `refP`,
  which is `connectedComponentIn (pairCurve Q)ᶜ refQ = pairSide Q`
  (`connectedComponentIn_eq`).

No normalisation of the pairs is needed: every ingredient is invariant under the translation of
an angle by an integer.
-/
namespace Work.LandLeaves

open Classical
open scoped Topology

noncomputable section

theorem pairSide_nesting_farArc {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ)
    (hJ : Work.Top.JordanForm) {u v w : ℝ} {y : ℂ}
    (hu : Work.EL.LandsN hN u y) (hv : Work.EL.LandsN hN v y) (hw : Work.EL.LandsN hN w y)
    (h : Work.LandLeaves.ccBet u v w) :
    Work.EL.pairSide (Work.LandLeaves.mkPair hN hu hw) ⊆ Work.EL.pairSide (Work.LandLeaves.mkPair hN hu hv) := by
  classical
  set P : Work.EL.CoPair hN := Work.LandLeaves.mkPair hN hu hw with hPdef
  set Q : Work.EL.CoPair hN := Work.LandLeaves.mkPair hN hu hv with hQdef
  have hPa : P.a = u := by rw [hPdef]; simp
  have hPb : P.b = w := by rw [hPdef]; simp
  have hPy : P.y = y := by rw [hPdef]; rfl
  have hQa : Q.a = u := by rw [hQdef]; simp
  have hQb : Q.b = v := by rw [hQdef]; simp
  have hQy : Q.y = y := by rw [hQdef]; rfl
  set mA : ℝ := u + Work.EL.arcLen u w / 2 with hmA
  set mB : ℝ := u + Work.EL.arcLen u v / 2 with hmB
  set refP : ℂ := Work.EL.rayPt hN mA 2 with hrefP
  set refQ : ℂ := Work.EL.rayPt hN mB 2 with hrefQ
  have harc_pos : 0 < Work.EL.arcLen u w := h.1
  have hhalf_pos : 0 < Work.EL.arcLen u w / 2 := by linarith
  have hhalf_lt : Work.EL.arcLen u w / 2 < 1 := by linarith [Work.EL.arcLen_lt_one u w]
  have hmA_sub : mA - u = Work.EL.arcLen u w / 2 := by rw [hmA]; ring
  have hfract_mA : Int.fract (mA - u) = Work.EL.arcLen u w / 2 := by
    rw [hmA_sub, Int.fract_eq_self.mpr ⟨le_of_lt hhalf_pos, hhalf_lt⟩]
  have hlt_uw_uv : Work.EL.arcLen u w / 2 < Work.EL.arcLen u v := by
    have h2 := h.2
    simp only [Work.EL.arcLen] at h2 ⊢
    linarith [h.1, h2]
  have hmA_far : Work.EL.InArc mA u v :=
    ⟨by rw [hfract_mA]; exact hhalf_pos, by rw [hfract_mA]; exact hlt_uw_uv⟩
  -- `v` lies on the near arc of `P`: `InArc v w (u + 1)`
  have hv_near : Work.EL.InArc v w (u + 1) := by
    have h1 : 0 < Int.fract (v - w) := by
      rw [Work.LandLeaves.fract_sub_fract_of_le (le_of_lt h.2)]
      linarith [h.1, h.2]
    have h2 : Int.fract (v - w) < Work.EL.arcLen w (u + 1) := by
      rw [Work.LandLeaves.fract_sub_fract_of_le (le_of_lt h.2)]
      show Int.fract (v - u) - Int.fract (w - u) < Int.fract (u + 1 - w)
      rw [show u + 1 - w = (u - w) + 1 by ring, Int.fract_add_one]
      rw [show u - w = -(w - u) by ring, Work.LandLeaves.fract_neg_eq (ne_of_gt h.1)]
      linarith [Int.fract_lt_one (v - u)]
    exact ⟨h1, h2⟩
  have hndP : Work.EL.arcLen P.a P.b ≠ 0 := by
    rw [hPa, hPb]
    exact ne_of_gt h.1
  have hdisj_P : Disjoint (Work.EL.pairSide P) (Work.EL.pairSideNear P) :=
    (Work.ELTop.pairSides_decomposition hN hJ P hndP).2.1
  have hrayv : Work.EL.paramRay hN v ⊆ Work.EL.pairSideNear P :=
    Work.ELTop.paramRay_subset_pairSideNear hN hJ P (by rw [hPb, hPa]; exact hv_near)
  -- the far side of `P` misses the curve of `Q`
  have hsubP_complQ : Work.EL.pairSide P ⊆ (Work.EL.pairCurve Q)ᶜ := by
    intro z hz
    rw [Set.mem_compl_iff]
    intro hzQ
    rw [Work.EL.mem_pairCurve_iff] at hzQ
    rw [hQa, hQb, hQy] at hzQ
    have hzPc : z ∈ (Work.EL.pairCurve P)ᶜ := connectedComponentIn_subset _ _ hz
    rw [Set.mem_compl_iff] at hzPc
    rcases hzQ with h1 | h2 | h3
    · exact hzPc ((Work.EL.mem_pairCurve_iff P z).mpr (Or.inl (by rw [hPa]; exact h1)))
    · exact hzPc ((Work.EL.mem_pairCurve_iff P z).mpr (Or.inr (Or.inl (by rw [hPy]; exact h2))))
    · exact (Set.disjoint_left.mp hdisj_P) hz (hrayv h3)
  -- the reference point of the far side of `P` lies in the far side of `P`
  have hrefP_P : refP ∈ Work.EL.pairSide P := by
    have h1 : P.a < mA := by rw [hPa, hmA]; linarith
    have h2 : mA < P.a + Work.EL.arcLen P.a P.b := by
      rw [hPa, hPb, hmA]
      linarith
    have h3 := Work.ELTop.rayPt_mem_pairSide hN P h1 h2 (by norm_num : (1:ℝ) < 2)
    simpa [hrefP] using h3
  -- ... and in the far side of `Q`
  have hrefP_Q : refP ∈ Work.EL.pairSide Q := by
    have hsub := Work.ELTop.paramRay_subset_pairSide hN hJ Q (θ := mA)
      (by rw [hQa, hQb]; exact hmA_far)
    exact hsub (by rw [hrefP]; exact Work.EL.rayPt_mem_paramRay hN (by norm_num))
  have hsideQ : Work.EL.pairSide Q = connectedComponentIn (Work.EL.pairCurve Q)ᶜ refQ := by
    have h1 : Work.EL.pairSide Q
        = connectedComponentIn (Work.EL.RawPair.curve hN Q.toRawPair)ᶜ
            (Work.EL.rayPt hN (Q.a + Work.EL.arcLen Q.a Q.b / 2) 2) := rfl
    have h2 : Work.EL.pairCurve Q = Work.EL.RawPair.curve hN Q.toRawPair := rfl
    rw [h1, h2, hrefQ, hmB, hQa, hQb]
  intro z hz
  have hrefP_Q' : refP ∈ connectedComponentIn (Work.EL.pairCurve Q)ᶜ refQ := by
    rw [← hsideQ]; exact hrefP_Q
  have hzmem : z ∈ connectedComponentIn (Work.EL.pairCurve Q)ᶜ refP :=
    IsPreconnected.subset_connectedComponentIn isPreconnected_connectedComponentIn
      hrefP_P hsubP_complQ hz
  have heq := connectedComponentIn_eq hrefP_Q'
  rw [hsideQ, heq]
  exact hzmem

end

end Work.LandLeaves
