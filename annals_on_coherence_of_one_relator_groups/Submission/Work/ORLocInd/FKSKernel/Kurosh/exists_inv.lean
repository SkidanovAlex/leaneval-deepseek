import Mathlib
import Submission.Work.ORLocInd.FKSKernel.Kurosh.BSWalk

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Work.ORLocInd.FKSKernel.Kurosh

open Work.ORBassSerre
open Work.ORBassSerre.Action

/-!
# The reversed path word

Given a path word `W` in the quotient graph of a cocompact `G`-tree, we build the *reversed*
path word `PathWord.revPW W`, running the walk backwards with the inverse letters, and show that
the element it defines in `Γ = Gamma d D` is the inverse of the element defined by `W`:

* `PathWord.revPW W` has the same length as `W`,
* `(PathWord.revPW W).orb 0 = W.orb W.len` and `(PathWord.revPW W).orb W.len = W.orb 0`,
* `(PathWord.revPW W).elt D = (W.elt D)⁻¹` for every `D : d.PresData`.

The last assertion is the content of `PathWord.revPW_elt`, and the three together give
`exists_inv`.
-/

section

variable {G : Type*} {V : Type*} [Group G] [Quiver V] [Quiver.HasInvolutiveReverse V]
  [MulAction G V] [Work.ORBassSerre.GraphAction G V]

namespace TreeDatum

/-- The letter with the inverse group element. -/
noncomputable def Letter.inv {d : TreeDatum G V} (l : d.Letter) : d.Letter :=
  ⟨l.1, ⟨(l.2 : G)⁻¹, inv_mem l.2.2⟩⟩

/-- The `Γ`-element of the inverse letter is the inverse. -/
theorem Letter.gam_inv {d : TreeDatum G V} (l : d.Letter) (D : d.PresData)
     :
    Letter.gam (Letter.inv l) D = (Letter.gam l D)⁻¹ := by
  show d.gEltHom D l.1 (Letter.inv l).2 = (d.gEltHom D l.1 l.2)⁻¹
  have h : (Letter.inv l).2 = (l.2)⁻¹ := Subtype.ext rfl
  rw [h, map_inv]

/-- Reversing the direction of a step inverts its `Γ`-element. -/
theorem stepGam_not {d : TreeDatum G V} (D : d.PresData)
    
    (E : Work.ORBassSerre.orbitE G V) (b : Bool) :
    stepGam D E (!b) = (stepGam D E b)⁻¹ := by
  by_cases h : d.IsTreeEdge E
  · rw [stepGam, dif_pos h, stepGam, dif_pos h, inv_one]
  · rw [stepGam, dif_neg h, stepGam, dif_neg h]
    cases b <;> simp

end TreeDatum

/-- The source of the reversed move is the target of the move. -/
theorem moveSrc_not (E : Work.ORBassSerre.orbitE G V) (b : Bool) :
    TreeDatum.moveSrc E (!b) = TreeDatum.moveTgt E b := by cases b <;> rfl

/-- The target of the reversed move is the source of the move. -/
theorem moveTgt_not (E : Work.ORBassSerre.orbitE G V) (b : Bool) :
    TreeDatum.moveTgt E (!b) = TreeDatum.moveSrc E b := by cases b <;> rfl

namespace TreeDatum


/-- **The reversed path word**: the same walk run backwards, with inverse vertex-group letters. -/
noncomputable def PathWord.revPW {d : TreeDatum G V} (W : d.PathWord) : d.PathWord where
  len := W.len
  orb := fun k => W.orb (W.len - k)
  letter := fun k => Letter.inv (W.letter (W.len - k))
  letter_orbit := fun k _ => W.letter_orbit (W.len - k) (Nat.sub_le _ _)
  stepE := fun k => W.stepE (W.len - (k+1))
  stepB := fun k => !(W.stepB (W.len - (k+1)))
  step_src := fun k _ => by
    show TreeDatum.moveSrc (W.stepE (W.len - (k+1))) (!(W.stepB (W.len - (k+1)))) =
      W.orb (W.len - k)
    rw [moveSrc_not, W.step_tgt (W.len - (k+1)) (by omega)]
    congr 1
    omega
  step_tgt := fun k _ => by
    show TreeDatum.moveTgt (W.stepE (W.len - (k+1))) (!(W.stepB (W.len - (k+1)))) =
      W.orb (W.len - (k+1))
    rw [moveTgt_not]
    exact W.step_src (W.len - (k+1)) (by omega)

/-- The `tpre` of the reversed word: running backwards through the word inverts the product. -/
theorem PathWord.revPW_tpre {d : TreeDatum G V} (W : d.PathWord) (D : d.PresData) :
    ∀ m, m ≤ W.len →
      (PathWord.revPW W).tpre D m =
        (W.elt D)⁻¹ * (W.tpre D (W.len - m) * Letter.gam (W.letter (W.len - m)) D) := by
  intro m hm
  have key : ∀ n, n ≤ W.len →
      (PathWord.revPW W).tpre D n =
        (W.elt D)⁻¹ * (W.tpre D (W.len - n) * Letter.gam (W.letter (W.len - n)) D) := by
    intro n
    induction n with
    | zero =>
      intro _
      rw [PathWord.tpre_zero]
      rw [show W.elt D = W.tpre D W.len * Letter.gam (W.letter W.len) D from rfl]
      simp only [Nat.sub_zero]
      group
    | succ m ih =>
      intro hn
      rw [PathWord.tpre_succ, ih (Nat.le_of_succ_le hn)]
      rw [show Letter.gam ((PathWord.revPW W).letter m) D =
        (Letter.gam (W.letter (W.len - m)) D)⁻¹ from Letter.gam_inv _ D]
      rw [show stepGam D ((PathWord.revPW W).stepE m) ((PathWord.revPW W).stepB m) =
        (stepGam D (W.stepE (W.len - (m+1))) (W.stepB (W.len - (m+1))))⁻¹ from
          stepGam_not (d := d) D (W.stepE (W.len - (m+1))) (W.stepB (W.len - (m+1)))]
      have hP : W.tpre D (W.len - m) =
          W.tpre D (W.len - (m+1)) * Letter.gam (W.letter (W.len - (m+1))) D *
            stepGam D (W.stepE (W.len - (m+1))) (W.stepB (W.len - (m+1))) := by
        rw [show W.len - m = W.len - (m + 1) + 1 from by omega]
        rw [PathWord.tpre_succ]
      rw [hP]
      group
  exact key m hm

/-- The element of `Γ` defined by the reversed word is the inverse. -/
theorem PathWord.revPW_elt {d : TreeDatum G V} (W : d.PathWord) (D : d.PresData) :
    (PathWord.revPW W).elt D = (W.elt D)⁻¹ := by
  have h := PathWord.revPW_tpre W D W.len le_rfl
  show (PathWord.revPW W).tpre D W.len * Letter.gam ((PathWord.revPW W).letter W.len) D =
    (W.elt D)⁻¹
  rw [h]
  rw [show (PathWord.revPW W).letter W.len = Letter.inv (W.letter (W.len - W.len)) from rfl]
  rw [Nat.sub_self]
  rw [Letter.gam_inv]
  rw [PathWord.tpre_zero]
  group

end TreeDatum

end

theorem exists_inv {G : Type*} {V : Type*}
    [Group G] [Quiver V] [Quiver.HasInvolutiveReverse V] [MulAction G V]
    [Work.ORBassSerre.GraphAction G V]
    {d : Work.ORLocInd.FKSKernel.Kurosh.TreeDatum G V}
    
    (W : Work.ORLocInd.FKSKernel.Kurosh.TreeDatum.PathWord d) :
    ∃ W' : Work.ORLocInd.FKSKernel.Kurosh.TreeDatum.PathWord d,
      W'.len = W.len ∧ W'.orb 0 = W.orb W.len ∧ W'.orb W'.len = W.orb 0 ∧
      (∀ (D : d.PresData), W'.elt D = (W.elt D)⁻¹) := by
  refine ⟨TreeDatum.PathWord.revPW W, rfl, ?_, ?_,
    fun D => TreeDatum.PathWord.revPW_elt W D⟩
  · show W.orb (W.len - 0) = W.orb W.len
    rw [Nat.sub_zero]
  · show W.orb (W.len - W.len) = W.orb 0
    rw [Nat.sub_self]

end Work.ORLocInd.FKSKernel.Kurosh
