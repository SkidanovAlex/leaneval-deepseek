import Mathlib
import Submission.Work.FIArea7.SumChiDefs
import Submission.Work.FIArea7.card_gBox_filter_mod

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.FIArea7

/-- The points of the box that are units modulo `Q` and lie in the class `⟨(u,v), _⟩` of
`G = (ℤ[i]/Q)^*` are exactly the points of the box whose two coordinates are the residues `u`, `v`.
Indeed the class map is the reduction `(z.re, z.im)` modulo `Q`. -/
private lemma fib_subset_gBox_res {Pa : Work.FITop.Params} {Q : ℕ} [NeZero Q]
    (u v : ZMod Q) (h : IsUnit (gaussNorm (u, v))) :
    ((uniUnitBox Pa Q).filter
        (fun z => unitClassD Q z = (⟨(u, v), h⟩ : GaussUnit Q)))
      ⊆ ((Work.FIPlan.gBox (Work.FITop.radN Pa)).filter
          (fun z => (z.re : ZMod Q) = u ∧ (z.im : ZMod Q) = v)) := by
  classical
  intro z hz
  simp only [Finset.mem_filter, uniUnitBox] at hz ⊢
  obtain ⟨⟨hzbox, hcop⟩, hcls⟩ := hz
  refine ⟨hzbox, ?_⟩
  have hcoord : gaussCoord Q z = (u, v) := by
    have h1 : unitClassD Q z = gaussUnitOf Q z hcop := unitClassD_eq Q z hcop
    have h2 : gaussUnitOf Q z hcop = (⟨(u, v), h⟩ : GaussUnit Q) := h1 ▸ hcls
    have h3 : (gaussUnitOf Q z hcop).1 = (u, v) := congrArg Subtype.val h2
    rwa [gaussUnitOf_val] at h3
  simp only [gaussCoord, Prod.mk.injEq] at hcoord
  exact hcoord

/-- **The box fibre count for the §17 class function.** Every class `a` of
`G = (ℤ[i]/Q)^*` is met by at most `((2R+1)/Q + 1)²` points `z` of the box `gBox R`
(`R = radN Pa`) that are units modulo `Q`. -/
theorem card_uniClassFn_fibre_le (Pa : Work.FITop.Params) (Q : ℕ) [NeZero Q]
    (a : Work.FIArea7.GaussUnit Q) :
    ((Work.FIArea7.uniUnitBox Pa Q).filter (fun z => Work.FIArea7.unitClassD Q z = a)).card
      ≤ ((2 * Work.FITop.radN Pa + 1).toNat / Q + 1)
          * ((2 * Work.FITop.radN Pa + 1).toNat / Q + 1) := by
  classical
  obtain ⟨⟨u, v⟩, h⟩ := a
  refine le_trans (Finset.card_le_card (fib_subset_gBox_res u v h)) ?_
  have hcastu : (((u.val : ℕ) : ℤ) : ZMod Q) = u := by
    rw [Int.cast_natCast, ZMod.natCast_zmod_val]
  have hcastv : (((v.val : ℕ) : ℤ) : ZMod Q) = v := by
    rw [Int.cast_natCast, ZMod.natCast_zmod_val]
  have hg := Work.FIArea7.card_gBox_filter_mod (Work.FITop.radN Pa) Q (NeZero.pos Q)
    ((u.val : ℕ) : ℤ) ((v.val : ℕ) : ℤ)
  simp only [hcastu, hcastv] at hg
  exact hg

end Work.FIArea7
