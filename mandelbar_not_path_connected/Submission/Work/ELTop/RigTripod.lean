/-
# ELTop discharges the tripod input `Work.EL.TripodSides` of the ELRig area

The ELRig area phrases "the three rays of angles `22/63`, `25/63`, `37/63` land at `b₂` and cut
the plane into three arms" as the structure `Work.EL.TripodSides hN y`, taking it as an explicit
hypothesis until ELTop supplies it.  This file supplies it, assembling the ELTop lemmas
`isOpen_pairSide`, `tripodArms_disjoint` and `tripodArms_cover` (and `pairSides` for the three
bounding pairs).
-/
import Submission.Work.ELRig.Defs
import Submission.Work.ELTop.tripodArms_disjoint
import Submission.Work.ELTop.tripodArms_cover
import Submission.Work.ELTop.RigInput

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Classical Filter Set
open scoped Topology

set_option linter.unusedVariables false

noncomputable section

namespace Work.ELTop

/-- The arm `A` of `Work.EL` is the arm `A` of `Work.EL.Tripod`. -/
theorem armA_eq {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ) {y : ℂ}
    (h₁ : Work.EL.LandsN hN Work.EL.b2a y) (h₂ : Work.EL.LandsN hN Work.EL.b2b y)
    (h₃ : Work.EL.LandsN hN Work.EL.b2c y) (h₁' : Work.EL.LandsN hN (Work.EL.b2a + 1) y) :
    Work.EL.armA hN y h₁ h₂ =
      Work.EL.Tripod.armA ⟨y, (by simpa only [Work.EL.b2a] using h₁),
        (by simpa only [Work.EL.b2b] using h₂), (by simpa only [Work.EL.b2c] using h₃),
        (by simpa only [Work.EL.b2a] using h₁')⟩ := by
  unfold Work.EL.armA Work.EL.armPairA Work.EL.Tripod.armA Work.EL.Tripod.pairA
    Work.EL.pairSide Work.EL.pairSideThroughArc Work.EL.RawPair.sideThrough Work.EL.RawPair.curve
    Work.EL.b2a Work.EL.b2b
  rfl

/-- The arm `B` of `Work.EL` is the arm `B` of `Work.EL.Tripod`. -/
theorem armB_eq {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ) {y : ℂ}
    (h₁ : Work.EL.LandsN hN Work.EL.b2a y) (h₂ : Work.EL.LandsN hN Work.EL.b2b y)
    (h₃ : Work.EL.LandsN hN Work.EL.b2c y) (h₁' : Work.EL.LandsN hN (Work.EL.b2a + 1) y) :
    Work.EL.armB hN y h₂ h₃ =
      Work.EL.Tripod.armB ⟨y, (by simpa only [Work.EL.b2a] using h₁),
        (by simpa only [Work.EL.b2b] using h₂), (by simpa only [Work.EL.b2c] using h₃),
        (by simpa only [Work.EL.b2a] using h₁')⟩ := by
  unfold Work.EL.armB Work.EL.armPairB Work.EL.Tripod.armB Work.EL.Tripod.pairB
    Work.EL.pairSide Work.EL.pairSideThroughArc Work.EL.RawPair.sideThrough Work.EL.RawPair.curve
    Work.EL.b2b Work.EL.b2c
  rfl

/-- The arm `C` of `Work.EL` is the arm `C` of `Work.EL.Tripod`. -/
theorem armC_eq {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ) {y : ℂ}
    (h₁ : Work.EL.LandsN hN Work.EL.b2a y) (h₂ : Work.EL.LandsN hN Work.EL.b2b y)
    (h₃ : Work.EL.LandsN hN Work.EL.b2c y) (h₁' : Work.EL.LandsN hN (Work.EL.b2a + 1) y) :
    Work.EL.armC hN y h₃ h₁' =
      Work.EL.Tripod.armC ⟨y, (by simpa only [Work.EL.b2a] using h₁),
        (by simpa only [Work.EL.b2b] using h₂), (by simpa only [Work.EL.b2c] using h₃),
        (by simpa only [Work.EL.b2a] using h₁')⟩ := by
  unfold Work.EL.armC Work.EL.armPairC Work.EL.Tripod.armC Work.EL.Tripod.pairC
    Work.EL.pairSide Work.EL.pairSideThroughArc Work.EL.RawPair.sideThrough Work.EL.RawPair.curve
    Work.EL.b2c Work.EL.b2a
  rfl

/-- The tripod curve of `Work.EL` is the tripod curve of `Work.EL.Tripod`. -/
theorem curve_eq {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ) {y : ℂ}
    (h₁ : Work.EL.LandsN hN Work.EL.b2a y) (h₂ : Work.EL.LandsN hN Work.EL.b2b y)
    (h₃ : Work.EL.LandsN hN Work.EL.b2c y) (h₁' : Work.EL.LandsN hN (Work.EL.b2a + 1) y) :
    Work.EL.Tripod.curve ⟨y, (by simpa only [Work.EL.b2a] using h₁),
        (by simpa only [Work.EL.b2b] using h₂), (by simpa only [Work.EL.b2c] using h₃),
        (by simpa only [Work.EL.b2a] using h₁')⟩ = Work.EL.tripodCurve hN y := by
  ext z
  simp only [Work.EL.Tripod.curve, Work.EL.tripodCurve, Work.EL.b2a, Work.EL.b2b, Work.EL.b2c,
    Set.mem_union, Set.mem_singleton_iff]
  tauto

/-- **The three arms of the tripod at `b₂` are the three sectors cut out by its rays**: the
tripod input `Work.EL.TripodSides` of the ELRig area, assembled from the ELTop lemmas
`isOpen_pairSide`, `tripodArms_disjoint`, `tripodArms_cover` and `pairSides`. -/
theorem tripodSides {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ) (hJ : Work.Top.JordanForm) {y : ℂ}
    (h₁ : Work.EL.LandsN hN Work.EL.b2a y) (h₂ : Work.EL.LandsN hN Work.EL.b2b y)
    (h₃ : Work.EL.LandsN hN Work.EL.b2c y) (h₁' : Work.EL.LandsN hN (Work.EL.b2a + 1) y) :
    Work.EL.TripodSides hN y := by
  let T : Work.EL.Tripod hN :=
    ⟨y, (by simpa only [Work.EL.b2a] using h₁), (by simpa only [Work.EL.b2b] using h₂),
      (by simpa only [Work.EL.b2c] using h₃), (by simpa only [Work.EL.b2a] using h₁')⟩
  have hA := armA_eq hN h₁ h₂ h₃ h₁'
  have hB := armB_eq hN h₁ h₂ h₃ h₁'
  have hC := armC_eq hN h₁ h₂ h₃ h₁'
  have hcurve := curve_eq hN h₁ h₂ h₃ h₁'
  have hndA : Work.EL.arcLen (Work.EL.armPairA hN y h₁ h₂).a
      (Work.EL.armPairA hN y h₁ h₂).b ≠ 0 := by
    unfold Work.EL.armPairA Work.EL.b2a Work.EL.b2b Work.EL.arcLen
    norm_num
  have hndB : Work.EL.arcLen (Work.EL.armPairB hN y h₂ h₃).a
      (Work.EL.armPairB hN y h₂ h₃).b ≠ 0 := by
    unfold Work.EL.armPairB Work.EL.b2b Work.EL.b2c Work.EL.arcLen
    norm_num
  have hndC : Work.EL.arcLen (Work.EL.armPairC hN y h₃ h₁').a
      (Work.EL.armPairC hN y h₃ h₁').b ≠ 0 := by
    unfold Work.EL.armPairC Work.EL.b2c Work.EL.b2a Work.EL.arcLen
    rw [show (22:ℝ)/63 + 1 - 37/63 = 48/63 by norm_num]
    norm_num
  exact
    { lands_a := h₁
      lands_b := h₂
      lands_c := h₃
      lands_a' := h₁'
      isOpen_A := by rw [hA]; exact (isOpen_pairSide hN (Work.EL.Tripod.pairA T)).1
      isOpen_B := by rw [hB]; exact (isOpen_pairSide hN (Work.EL.Tripod.pairB T)).1
      isOpen_C := by rw [hC]; exact (isOpen_pairSide hN (Work.EL.Tripod.pairC T)).1
      disjoint_AB := by rw [hA, hB]; exact (tripodArms_disjoint hN hJ T).1
      disjoint_AC := by rw [hA, hC]; exact ((tripodArms_disjoint hN hJ T).2.2).symm
      disjoint_BC := by rw [hB, hC]; exact (tripodArms_disjoint hN hJ T).2.1
      union_eq := by
        rw [hA, hB, hC, ← Set.union_assoc, ← hcurve]
        exact tripodArms_cover hN hJ T
      sides_A := pairSides hN hJ (Work.EL.armPairA hN y h₁ h₂) hndA
      sides_B := pairSides hN hJ (Work.EL.armPairB hN y h₂ h₃) hndB
      sides_C := pairSides hN hJ (Work.EL.armPairC hN y h₃ h₁') hndC
      preconnected_A := by rw [hA]; exact isPreconnected_connectedComponentIn
      preconnected_B := by rw [hB]; exact isPreconnected_connectedComponentIn
      preconnected_C := by rw [hC]; exact isPreconnected_connectedComponentIn }

end Work.ELTop
