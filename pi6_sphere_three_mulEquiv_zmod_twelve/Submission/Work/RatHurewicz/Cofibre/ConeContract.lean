import Mathlib
import Submission.Work.Stems.Cone

/-!
# The contraction of the cone (a self-contained copy)

The module `Work.Stems.subsingleton_homotopyGroup_cone` provides the contraction of the cone and
the triviality of its homotopy groups, but its declaration `Work.Stems.homotopic_const` clashes
with the declaration of the same name in `Work.Stems.subsingleton_of_infinite`; the two modules
cannot be imported into the same file.  This file re-proves the contraction, and the triviality of
the homotopy groups of the cone, under fresh names, so that it can be combined with the range
Whitehead machinery (`Submission.Work.Serre.rangeWhiteheadInclInt`, which lies on the other side of
the clash).
-/

open scoped Topology Topology.Homotopy unitInterval
open ContinuousMap

namespace Work.RatHurewicz

noncomputable section

/-- The linear path on the unit interval from `t` to `1` at parameter `s`: `(1-s)*t + s`. -/
def pt (s t : unitInterval) : unitInterval :=
  ⟨(1 - (s : ℝ)) * (t : ℝ) + (s : ℝ), by
    constructor <;> nlinarith [s.2.1, s.2.2, t.2.1, t.2.2]⟩

@[simp]
theorem pt_zero (t : unitInterval) : pt 0 t = t := by
  apply Subtype.ext; simp [pt]

@[simp]
theorem pt_one (t : unitInterval) : pt 1 t = 1 := by
  apply Subtype.ext; simp [pt]

@[simp]
theorem pt_right_one (s : unitInterval) : pt s 1 = 1 := by
  apply Subtype.ext; simp [pt]

/-- The contraction of the cone, on representatives: `(s, [a,t]) ↦ [a, (1-s)*t + s]`. -/
def coneContractFun {X : Type*} [TopologicalSpace X]
    (p : unitInterval × Work.Stems.Cone X) : Work.Stems.Cone X :=
  Quotient.liftOn p.2
    (fun q : X × unitInterval => Quotient.mk'' (q.1, pt p.1 q.2))
    (by
      intro a b hab
      rcases hab with hab | ⟨ha, hb⟩
      · subst hab; rfl
      · apply Quotient.sound
        right
        exact ⟨by rw [ha]; exact pt_right_one p.1, by rw [hb]; exact pt_right_one p.1⟩)

/-- The cone is contractible: a continuous deformation of the identity to the constant map at the
apex, fixing the apex. -/
def coneContractC {X : Type*} [TopologicalSpace X] :
    C(unitInterval × Work.Stems.Cone X, Work.Stems.Cone X) where
  toFun := coneContractFun
  continuous_toFun := by
    apply Topology.IsQuotientMap.continuous_lift_prod_right
      (f := @Quotient.mk (X × unitInterval) (Work.Stems.coneSetoid X))
      isQuotientMap_quotient_mk'
    simp only [coneContractFun, Quotient.liftOn_mk]
    refine continuous_quotient_mk'.comp (Continuous.prodMk ?_ ?_)
    · fun_prop
    · apply Continuous.subtype_mk
      fun_prop

@[simp]
theorem coneContractC_zero {X : Type*} [TopologicalSpace X] (z : Work.Stems.Cone X) :
    coneContractC (0, z) = z := by
  induction z using Quotient.inductionOn with
  | h q =>
    change coneContractFun (0, Quotient.mk'' q) = Quotient.mk'' q
    simp only [coneContractFun, Quotient.liftOn_mk, pt_zero]

@[simp]
theorem coneContractC_one {X : Type*} [TopologicalSpace X] (x : X) (z : Work.Stems.Cone X) :
    coneContractC (1, z) = Work.Stems.coneApex x := by
  induction z using Quotient.inductionOn with
  | h q =>
    change coneContractFun (1, Quotient.mk'' q) = Work.Stems.coneApex x
    simp only [coneContractFun, Quotient.liftOn_mk, pt_one]
    exact Work.Stems.coneApex_eq q.1 x

@[simp]
theorem coneContractC_apex {X : Type*} [TopologicalSpace X] (x : X) (s : unitInterval) :
    coneContractC (s, Work.Stems.coneApex x) = Work.Stems.coneApex x := by
  change coneContractFun (s, Quotient.mk'' (x, (1 : unitInterval))) = Work.Stems.coneApex x
  simp only [coneContractFun, Quotient.liftOn_mk, pt_right_one]
  rfl

/-- Every generalized loop in the cone is null-homotopic relative to the boundary. -/
theorem homotopic_const_cone {N X : Type*} [TopologicalSpace X] (x : X)
    (p : Ω^ N (Work.Stems.Cone X) (Work.Stems.coneApex x)) :
    GenLoop.Homotopic p (GenLoop.const : Ω^ N (Work.Stems.Cone X) (Work.Stems.coneApex x)) := by
  refine ⟨{ toFun := fun q => coneContractC (q.1, p.1 q.2),
            continuous_toFun := ?_,
            map_zero_left := ?_,
            map_one_left := ?_,
            prop' := ?_ }⟩
  · exact coneContractC.continuous.comp
      (continuous_fst.prodMk (p.1.continuous.comp continuous_snd))
  · intro y; exact coneContractC_zero (p.1 y)
  · intro y; exact coneContractC_one x (p.1 y)
  · intro t y hy
    show coneContractC (t, p.1 y) = p.1 y
    rw [p.2 y hy]
    exact coneContractC_apex x t

/-- **The homotopy groups of the cone are trivial.** -/
theorem subsingleton_homotopyGroup_cone {N X : Type*} [TopologicalSpace X] (x : X) :
    Subsingleton (HomotopyGroup N (Work.Stems.Cone X) (Work.Stems.coneApex x)) := by
  change Subsingleton (Quotient (GenLoop.Homotopic.setoid N (Work.Stems.coneApex x)))
  refine ⟨fun a b => ?_⟩
  induction a using Quotient.inductionOn with
  | h p =>
    induction b using Quotient.inductionOn with
    | h q =>
      exact Quotient.sound (GenLoop.Homotopic.trans (homotopic_const_cone x p)
        (GenLoop.Homotopic.symm (homotopic_const_cone x q)))

/-- **A contraction to a point `b` makes the homotopy groups at `b` trivial.** -/
theorem subsingleton_homotopyGroup_of_contraction {N : Type*} {X : Type} [TopologicalSpace X]
    (H : C(X × unitInterval, X)) (b : X) (h0 : ∀ x, H (x, 0) = x) (h1 : ∀ x, H (x, 1) = b)
    (hb : ∀ t, H (b, t) = b) : Subsingleton (HomotopyGroup N X b) := by
  have key : ∀ f : GenLoop N X b, GenLoop.Homotopic f (GenLoop.const : GenLoop N X b) := by
    intro f
    refine ⟨{ toFun := fun q => H (f.1 q.2, q.1),
              continuous_toFun := H.continuous.comp
                ((f.1.continuous.comp continuous_snd).prodMk continuous_fst),
              map_zero_left := ?_, map_one_left := ?_, prop' := ?_ }⟩
    · intro y
      show H (f.1 y, 0) = f.1 y
      rw [h0]
    · intro y
      show H (f.1 y, 1) = b
      rw [h1]
    · intro t y hy
      show H (f.1 y, t) = f.1 y
      rw [f.2 y hy]
      exact hb t
  refine ⟨fun a b' => ?_⟩
  induction a using Quotient.inductionOn with
  | h p =>
    induction b' using Quotient.inductionOn with
    | h q =>
      exact Quotient.sound (GenLoop.Homotopic.trans (key p) (GenLoop.Homotopic.symm (key q)))

end

end Work.RatHurewicz
