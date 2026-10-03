import Mathlib
import Submission.Work.ORLocInd.Howie.Case2Bridge
import Submission.Work.ORLocInd.Howie.Case2Labelling
import Submission.Work.ORLocInd.Howie.C2.pathSum_restrictSide_reach_eq_zero_of_avoids

set_option linter.unusedVariables false

namespace Work.ORLocInd.Howie.C2

open Quiver

/-- If both sides of the bridge `e` are indicable, then `P` itself has an indicable labelling.

The proof is the combination argument of the bridge case of Howie's Case 2.  Let `L₁`, `L₂` be
labellings vanishing on all relators `≠ m`, nonzero on a closed path `β₁` inside the `ReachRight`
side / `β₂` inside the `ReachLeft` side.  Restricting `L₁` to the right side and `L₂` to the left
side (both restrictions still vanish on all relators `≠ m`, because every relator `≠ m` avoids `e`
and hence lies inside one component of `Γ ∖ e`) and writing `aᵢ` for the value on `P.path m`, the
labelling `a₂ θ₁ - a₁ θ₂` vanishes on *all* relators and is still nonzero on `β₁` (as `a₂ ≠ 0`),
because `θ₂` is supported on the left side, whence it vanishes on `β₁`.  If `a₁` or `a₂` is `0`,
one of `θ₁`, `θ₂` already vanishes on all relators. -/
theorem hasIndicableLabelling_of_both_sides {V : Type*} [Quiver V]
    [Quiver.HasInvolutiveReverse V]
    (P : Work.ORLocInd.Howie.Presentation V) (hsep : P.CodeSeparates) (m : P.ι)
    (e : Quiver.Total V)
    (hbr : ∀ q : Quiver.Path e.right e.left, Work.ORLocInd.Howie.Avoids P e q → False)
    (hbrl : ∀ i : P.ι, i ≠ m → Work.ORLocInd.Howie.Avoids P e (P.path i))
    (h1 : Work.ORLocInd.Howie.SideIndicable P m e (Work.ORLocInd.Howie.ReachRight P e))
    (h2 : Work.ORLocInd.Howie.SideIndicable P m e (Work.ORLocInd.Howie.ReachLeft P e)) :
    P.HasIndicableLabelling := by
  classical
  obtain ⟨L1, x1, β1, hv1, hsl1, hβ1⟩ := h1
  obtain ⟨L2, x2, β2, hv2, hsl2, hβ2⟩ := h2
  -- the labelling of the right side / of the left side
  let θ1 : Labelling V := restrictSide P e (ReachRight P e) L1
  let θ2 : Labelling V := restrictSide P e (ReachLeft P e) L2
  -- both still vanish on every relator other than `m`
  have hθ1 : ∀ i, i ≠ m → pathSum θ1.toFun (P.path i) = 0 := by
    intro i him
    exact pathSum_restrictSide_reach_eq_zero_of_avoids P e e.right L1 (P.path i)
      (hbrl i him) (hv1 i him)
  have hθ2 : ∀ i, i ≠ m → pathSum θ2.toFun (P.path i) = 0 := by
    intro i him
    exact pathSum_restrictSide_reach_eq_zero_of_avoids P e e.left L2 (P.path i)
      (hbrl i him) (hv2 i him)
  -- the right side labelling is nonzero on the right loop
  have hθ1β1 : pathSum θ1.toFun β1 ≠ 0 := by
    show pathSum (restrictSide P e (ReachRight P e) L1).toFun β1 ≠ 0
    rw [pathSum_restrictSide P e (ReachRight P e) L1 β1 hsl1]
    exact hβ1
  -- the two sides of the bridge are disjoint
  have hdisj : ∀ y : V, ReachRight P e y → ReachLeft P e y → False := by
    rintro y ⟨q1, hq1⟩ ⟨q2, hq2⟩
    exact hbr (q1.comp q2.reverse)
      ((avoids_comp_iff P e q1 q2.reverse).mpr ⟨hq1, avoids_reverse P e hq2⟩)
  -- the left side labelling is supported on the left side, so it vanishes on `β₁`
  have hθ2β1 : pathSum θ2.toFun β1 = 0 := by
    show pathSum (restrictSide P e (ReachLeft P e) L2).toFun β1 = 0
    refine pathSum_restrictSide_eq_zero P e (ReachLeft P e) L2 β1 (fun g hg hc => ?_)
    exact hdisj g.left (hsl1 g hg).1 hc.1
  by_cases ha1 : pathSum θ1.toFun (P.path m) = 0
  · -- `θ₁` already vanishes on everything
    refine ⟨θ1, ?_, x1, β1, hθ1β1⟩
    intro i
    by_cases h : i = m
    · subst h; exact ha1
    · exact hθ1 i h
  · by_cases ha2 : pathSum θ2.toFun (P.path m) = 0
    · -- `θ₂` already vanishes on everything
      refine ⟨θ2, ?_, x2, β2, ?_⟩
      · intro i
        by_cases h : i = m
        · subst h; exact ha2
        · exact hθ2 i h
      · show pathSum (restrictSide P e (ReachLeft P e) L2).toFun β2 ≠ 0
        rw [pathSum_restrictSide P e (ReachLeft P e) L2 β2 hsl2]
        exact hβ2
    · -- the combination `a₂ θ₁ - a₁ θ₂`
      refine ⟨Labelling.comb (pathSum θ2.toFun (P.path m))
        (- pathSum θ1.toFun (P.path m)) θ1 θ2, ?_, x1, β1, ?_⟩
      · intro i
        by_cases h : i = m
        · subst h
          rw [Labelling.pathSum_comb]
          ring
        · rw [Labelling.pathSum_comb, hθ1 i h, hθ2 i h]
          ring
      · rw [Labelling.pathSum_comb, hθ2β1]
        simp only [mul_zero, add_zero]
        exact mul_ne_zero ha2 hθ1β1

end Work.ORLocInd.Howie.C2
