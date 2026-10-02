import Mathlib
import Submission.Work.Thom.naturalModelClass_punct
import Submission.Work.Thom.isOrientedOver_of_det_pos
import Submission.Work.Thom.MixedCup
import Submission.Work.Thom.stepDefs
import Submission.Work.Thom.step_natural
import Submission.Work.Thom.Cohomology
import Submission.Work.Cohomology.h0Evaluation

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false

namespace Work.Whitney

open Work.Thom

noncomputable section

/-- The inclusion of a subset into the ambient space. -/
def setIncl {Y : Type} [TopologicalSpace Y] (W : Set Y) : C(↥W, Y) :=
  ⟨fun z => (z : Y), continuous_subtype_val⟩

/-- **A degree-zero class whose restriction to every point is zero is zero.**  A class of `H⁰(Y;ℤ)`
is determined by its values at the points of `Y`: this is `Work.Thom.h0_eq_oneH_of_point_incl`
applied to the complement of the class. -/
theorem h0_eq_zero_of_point_incl {Y : Type} [TopologicalSpace Y] (c : Coh ℤ 0 Y)
    (h : ∀ x : Y, (CohMap (setIncl ({x} : Set Y)) ℤ 0).hom c = 0) :
    c = 0 := by
  let e : Coh ℤ 0 Y := Work.Cohomology.oneH ℤ (TopCat.toSSet.obj (TopCat.of Y))
  have h' : ∀ x : Y, (CohMap (setIncl ({x} : Set Y)) ℤ 0).hom (e - c)
      = Work.Cohomology.oneH ℤ (TopCat.toSSet.obj (TopCat.of ↥({x} : Set Y))) := by
    intro x
    rw [map_sub, h x, sub_zero]
    exact CohMap_oneH (setIncl ({x} : Set Y))
  have hmain := h0_eq_oneH_of_point_incl (e - c) h'
  exact sub_eq_self.mp hmain

/-- **Restriction of the model class to a base `W ⊆ Y`.**  Pulling `π^*(a) ⌣ Mpun n Y` back to
`W × ℝⁿ` gives `π^*(a|_W) ⌣ Mpun n W`: the mixed cup is natural
(`Work.Thom.mixedCupC_pairNatural`) and `Mpun` is natural in the base
(`Work.Thom.Mpun_natural`). -/
theorem baseIncl_mixedCup_Mpun {Y : Type} [TopologicalSpace Y] (n : ℕ) (W : Set Y)
    (a : Coh ℤ 0 Y) :
    (relCohMap (baseIncl Y W n) (Punct W n) (Punct Y n) (fun _ hp => hp) ℤ (0 + n)).hom
        ((mixedCupC ℤ (Punct Y n) 0 n) ((CohMap (projFstA Y n) ℤ 0).hom a) (Mpun n Y))
      = (mixedCupC ℤ (Punct W n) 0 n)
          ((CohMap (projFstA W n) ℤ 0).hom ((CohMap (setIncl W) ℤ 0).hom a))
          (Mpun n W) := by
  rw [mixedCupC_pairNatural (baseIncl Y W n) (Punct W n) (Punct Y n) (fun _ hp => hp) 0 n
    ((CohMap (projFstA Y n) ℤ 0).hom a) (Mpun n Y)]
  have hX : (CohMap (baseIncl Y W n) ℤ 0).hom ((CohMap (projFstA Y n) ℤ 0).hom a)
      = (CohMap (projFstA W n) ℤ 0).hom ((CohMap (setIncl W) ℤ 0).hom a) := by
    rw [CohMap_comp_apply (baseIncl Y W n) (projFstA Y n) ℤ 0 a,
      CohMap_comp_apply (projFstA W n) (setIncl W) ℤ 0 a]
    have hmap : (projFstA Y n).comp (baseIncl Y W n) = (setIncl W).comp (projFstA W n) := by
      apply ContinuousMap.ext
      intro p
      rfl
    rw [CohMap_congr hmap ℤ 0]
  have hZ : (relCohMap (baseIncl Y W n) (Punct W n) (Punct Y n) (fun _ hp => hp) ℤ n).hom
      (Mpun n Y) = Mpun n W :=
    Mpun_natural n Y W
  rw [hX, hZ]

/-- **The punctured model class is detected by its restrictions to the fibres.**  If two classes in
`H^n(Y × ℝⁿ, Y × (ℝⁿ∖0); ℤ)` agree after restriction to every fibre `{y} × ℝⁿ`, then they are equal.
This is the "separation" principle that reduces any identity between model Thom classes over a base
`Y` to the corresponding identity over a point: by `Work.Thom.Mpun_isModel` (the case `k = 0`) any
class is `π^*(a) ⌣ Mpun n Y` for a unique `a ∈ H⁰(Y;ℤ)`, the fibre restriction of the mixed cup is
the mixed cup of the restrictions (`Work.Thom.mixedCupC_pairNatural`, `Work.Thom.Mpun_natural`), and
`H⁰(Y;ℤ)` is detected by its values at points (`Work.Thom.h0_eq_oneH_of_point_incl`, applied to
`1 - a`).  Note the degree cast `0 + n = n` (`Nat.zero_add`) must be handled explicitly
(`Work.Thom.cohTransport`, `relCohMap_cast`), exactly as in
`Work.Thom.Mpun_gaugeEnd_invariant`. -/
theorem Mpun_eq_of_fibrewise {n : ℕ} (hn : 1 ≤ n) {Y : Type} [TopologicalSpace Y]
    (P Q : Work.Thom.RelCoh ℤ n (Y × EuclideanSpace ℝ (Fin n)) (Work.Thom.Punct Y n))
    (h : ∀ y : Y,
      (Work.Thom.relCohMap (Work.Thom.baseIncl Y ({y} : Set Y) n)
        (Work.Thom.Punct ↥({y} : Set Y) n) (Work.Thom.Punct Y n) (fun _ hp => hp) ℤ n).hom P
      = (Work.Thom.relCohMap (Work.Thom.baseIncl Y ({y} : Set Y) n)
        (Work.Thom.Punct ↥({y} : Set Y) n) (Work.Thom.Punct Y n) (fun _ hp => hp) ℤ n).hom Q) :
    P = Q := by
  have _hn : 1 ≤ n := hn
  classical
  obtain ⟨a, ha⟩ := (Mpun_isModel n Y 0).2 ((Nat.zero_add n).symm ▸ P)
  obtain ⟨b, hb⟩ := (Mpun_isModel n Y 0).2 ((Nat.zero_add n).symm ▸ Q)
  -- the pointwise statement: the restrictions of `a` and `b` to each point agree
  have hpt : ∀ y : Y, (CohMap (setIncl ({y} : Set Y)) ℤ 0).hom a
      = (CohMap (setIncl ({y} : Set Y)) ℤ 0).hom b := by
    intro y
    -- the restriction of the two model decompositions to the fibre over `y`
    have keyP := congrArg (fun z => (relCohMap (baseIncl Y ({y} : Set Y) n)
      (Punct ↥({y} : Set Y) n) (Punct Y n) (fun _ hp => hp) ℤ (0 + n)).hom z) ha
    have keyQ := congrArg (fun z => (relCohMap (baseIncl Y ({y} : Set Y) n)
      (Punct ↥({y} : Set Y) n) (Punct Y n) (fun _ hp => hp) ℤ (0 + n)).hom z) hb
    -- the degree cast `0 + n = n` is transported across the restriction
    have hmid : (relCohMap (baseIncl Y ({y} : Set Y) n)
        (Punct ↥({y} : Set Y) n) (Punct Y n) (fun _ hp => hp) ℤ (0 + n)).hom
          ((Nat.zero_add n).symm ▸ P)
        = (relCohMap (baseIncl Y ({y} : Set Y) n)
        (Punct ↥({y} : Set Y) n) (Punct Y n) (fun _ hp => hp) ℤ (0 + n)).hom
          ((Nat.zero_add n).symm ▸ Q) := by
      rw [relCohMap_cast (baseIncl Y ({y} : Set Y) n) (Punct ↥({y} : Set Y) n)
            (Punct Y n) (fun _ hp => hp) (h := (Nat.zero_add n).symm) P,
          relCohMap_cast (baseIncl Y ({y} : Set Y) n) (Punct ↥({y} : Set Y) n)
            (Punct Y n) (fun _ hp => hp) (h := (Nat.zero_add n).symm) Q,
          h y]
    have hLa := baseIncl_mixedCup_Mpun n ({y} : Set Y) a
    have hLb := baseIncl_mixedCup_Mpun n ({y} : Set Y) b
    refine (Mpun_isModel n ↥({y} : Set Y) 0).1 ?_
    exact hLa.symm.trans (keyP.trans (hmid.trans (keyQ.symm.trans hLb)))
  -- a degree-zero class whose point restrictions all vanish is zero
  have hzero : ∀ y : Y, (CohMap (setIncl ({y} : Set Y)) ℤ 0).hom (a - b) = 0 := by
    intro y
    rw [map_sub, hpt y, sub_self]
  have hab : a = b := sub_eq_zero.mp (h0_eq_zero_of_point_incl (a - b) hzero)
  rw [hab] at ha
  exact eq_of_cast_eq (α := fun k => RelCoh ℤ k (Y × EuclideanSpace ℝ (Fin n)) (Punct Y n))
    (h := (Nat.zero_add n).symm) (ha.symm.trans hb)

end

end Work.Whitney
