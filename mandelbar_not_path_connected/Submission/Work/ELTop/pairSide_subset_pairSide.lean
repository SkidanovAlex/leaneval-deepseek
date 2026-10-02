/-
# `Work.ELTop.pairSide_subset_pairSide`

The sibling of `Work.ELTop.pairSide_subset_pairSideNear`, for the **far** side of the second pair:
two co-landing pairs `P`, `Q` of external rays of the dynamical plane whose curves are disjoint
and whose arcs satisfy "the far arc of `P` is contained in the far arc of `Q`" satisfy
`pairSide P ⊆ pairSide Q`.

## The reduction

`pairSide Q` is the far side of `Q`, the component of `(pairCurve Q)ᶜ` reached through `Q`'s own
arc `(Q.a, Q.b)`.  Replacing `Q` by its **reverse** `Q̃ = (Q.b, Q.a + 1, Q.y)` does not change the
curve — `R(Q.a + 1) = R(Q.a)` — but exchanges the two arcs: the near arc
`(Q̃.b, Q̃.a + 1) = (Q.a + 1, Q.b + 1)` of `Q̃` is the far arc `(Q.a, Q.b)` of `Q`, up to the
translation by `1`.  Consequently

* `pairCurve Q̃ = pairCurve Q`,
* `pairSideNear Q̃ = pairSide Q` (the two reference angles differ by the period `1`),

so the statement for the far side of `Q` is exactly the statement for the near side of `Q̃`, i.e.
`Work.ELTop.pairSide_subset_pairSideNear`.  The arc hypothesis transports because `InArc` depends
on the endpoints only modulo `1` (`Work.ELTop.PolyCurve.InArc_add_int_pair`).
-/
import Mathlib
import Submission.Work.ELTop.Defs
import Submission.Work.ELTop.pairSide_subset_pairSideNear
import Submission.Work.ELTop.PolyCurve.Blocks
import Submission.Work.ELTop.PolyCurve.image_cycParam
import Submission.Work.ELTop.rayPt_add_int
import Submission.Work.ELTop.paramRay_subset_pairSide

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Classical Filter Set
open scoped Topology

set_option maxHeartbeats 800000

noncomputable section

namespace Work.ELTop

open Work.EL

/-! ## The reversed pair -/

/-- A ray landing at `y` also lands at `y` after shifting its angle by `1`. -/
theorem landsN_add_one {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ) {θ : ℝ} {y : ℂ}
    (h : Work.EL.LandsN hN θ y) : Work.EL.LandsN hN (θ + 1) y := by
  have := LandsN_add_int hN h (1 : ℤ)
  simpa using this

/-- The pair obtained from `P` by keeping its landing point and replacing the two angles by `P.b`
and `P.a + 1`: it has the same curve, and its near side is the far side of `P`. -/
def reversePair {c : ℂ} {φ : ℂ → ℂ} {hN : Work.EL.DynB c φ} (P : Work.EL.CoPair hN) :
    Work.EL.CoPair hN where
  toRawPair := ⟨P.b, P.a + 1, P.y⟩
  lands_a := P.lands_b
  lands_b := landsN_add_one hN P.lands_a

@[simp] theorem reversePair_a {c : ℂ} {φ : ℂ → ℂ} {hN : Work.EL.DynB c φ}
    (P : Work.EL.CoPair hN) : (reversePair P).a = P.b := rfl

@[simp] theorem reversePair_b {c : ℂ} {φ : ℂ → ℂ} {hN : Work.EL.DynB c φ}
    (P : Work.EL.CoPair hN) : (reversePair P).b = P.a + 1 := rfl

@[simp] theorem reversePair_y {c : ℂ} {φ : ℂ → ℂ} {hN : Work.EL.DynB c φ}
    (P : Work.EL.CoPair hN) : (reversePair P).y = P.y := rfl

theorem paramRay_add_one_of {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ) (θ : ℝ) :
    Work.EL.paramRay hN (θ + 1) = Work.EL.paramRay hN θ := by
  have h1 : θ + (1 : ℝ) = θ + ((1 : ℤ) : ℝ) := by norm_num
  rw [h1]
  exact paramRay_add_int hN θ 1

/-- Reversing the pair does not change its curve. -/
theorem pairCurve_reversePair {c : ℂ} {φ : ℂ → ℂ} {hN : Work.EL.DynB c φ}
    (P : Work.EL.CoPair hN) : Work.EL.pairCurve (reversePair P) = Work.EL.pairCurve P := by
  have h : Work.EL.paramRay hN ((reversePair P).b) = Work.EL.paramRay hN P.a := by
    rw [reversePair_b]
    exact paramRay_add_one_of hN P.a
  ext z
  rw [Work.EL.mem_pairCurve_iff, Work.EL.mem_pairCurve_iff]
  rw [h, reversePair_a, reversePair_y]
  tauto

/-- The near side of the reversed pair is the far side of the pair. -/
theorem pairSideNear_reversePair {c : ℂ} {φ : ℂ → ℂ} {hN : Work.EL.DynB c φ}
    (P : Work.EL.CoPair hN) :
    Work.EL.pairSideNear (reversePair P) = Work.EL.pairSide P := by
  have hcurve : Work.EL.pairCurve (reversePair P) = Work.EL.pairCurve P := pairCurve_reversePair P
  have harc : Work.EL.arcLen ((reversePair P).b) ((reversePair P).a) = Work.EL.arcLen P.a P.b := by
    rw [reversePair_b, reversePair_a]
    unfold Work.EL.arcLen
    rw [show P.b - (P.a + 1) = (P.b - P.a) - (1 : ℤ) by push_cast; ring, Int.fract_sub_intCast]
  have href : Work.EL.rayPt hN
        ((reversePair P).b + Work.EL.arcLen ((reversePair P).b) ((reversePair P).a) / 2) 2
      = Work.EL.rayPt hN (P.a + Work.EL.arcLen P.a P.b / 2) 2 := by
    have harg : (reversePair P).b
          + Work.EL.arcLen ((reversePair P).b) ((reversePair P).a) / 2
        = (P.a + Work.EL.arcLen P.a P.b / 2) + ((1 : ℤ) : ℝ) := by
      rw [harc, reversePair_b]
      push_cast
      ring
    rw [harg]
    exact rayPt_add_int hN (P.a + Work.EL.arcLen P.a P.b / 2) 2 1
  have hcurve' : Work.EL.RawPair.curve hN (reversePair P).toRawPair
      = Work.EL.RawPair.curve hN P.toRawPair := hcurve
  rw [Work.EL.pairSideNear, Work.EL.pairSide, Work.EL.pairSideThroughArc,
    Work.EL.pairSideThroughArc, Work.EL.RawPair.sideThrough, Work.EL.RawPair.sideThrough,
    hcurve', href]

/-! ## The main theorem -/

theorem pairSide_subset_pairSide {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ)
    (hJ : Work.Top.JordanForm) (P Q : Work.EL.CoPair hN)
    (hdisj : Disjoint (Work.EL.pairCurve P) (Work.EL.pairCurve Q))
    (harc : ∀ θ : ℝ, Work.EL.InArc θ P.a P.b → Work.EL.InArc θ Q.a Q.b) :
    Work.EL.pairSide P ⊆ Work.EL.pairSide Q := by
  have hcurve : Work.EL.pairCurve (reversePair Q) = Work.EL.pairCurve Q :=
    pairCurve_reversePair Q
  have hside : Work.EL.pairSideNear (reversePair Q) = Work.EL.pairSide Q :=
    pairSideNear_reversePair Q
  have hdisj' : Disjoint (Work.EL.pairCurve P) (Work.EL.pairCurve (reversePair Q)) := by
    rw [hcurve]
    exact hdisj
  have harc' : ∀ θ : ℝ, Work.EL.InArc θ P.a P.b →
      Work.EL.InArc θ (reversePair Q).b ((reversePair Q).a + 1) := by
    intro θ hθ
    have h1 : Work.EL.InArc θ Q.a Q.b := harc θ hθ
    have h2 : Work.EL.InArc θ (Q.a + ((1 : ℤ) : ℝ)) (Q.b + ((1 : ℤ) : ℝ)) :=
      (Work.ELTop.PolyCurve.InArc_add_int_pair θ Q.a Q.b (1 : ℤ)).mpr h1
    rw [reversePair_b, reversePair_a]
    simpa using h2
  have hres := pairSide_subset_pairSideNear hN hJ P (reversePair Q) hdisj' harc'
  rwa [hside] at hres

end Work.ELTop
