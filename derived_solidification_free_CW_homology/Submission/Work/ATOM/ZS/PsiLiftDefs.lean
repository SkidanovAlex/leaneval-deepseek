import Mathlib
import Submission.Work.ATOM.ZS.Topo.Maps
import Submission.Work.ATOM.ZS.Topo.TSpace

/-!
# AREA ATOM / `ℤ[S]`: auxiliary maps for the identity `h₁`

The identity `h₁` of `REFS/03 §1` (`(1-S) ⊗ id ≫ F = G ≫ g̃`) is checked after pulling back along
the epimorphism `EA S : ℤ[(ℕ∪{∞}) × S] ⟶ P ⊗ ℤ[S]`.  On `(ℕ∪{∞}) × S` both sides then involve the
two maps defined here:

* `shiftNS S : (ℕ∪{∞}) × S ⟶ (ℕ∪{∞}) × S`, the shift `(k,x) ↦ (k+1,x)` (with `∞ ↦ ∞`) on the
  first coordinate — this is the map whose `zmap` appears when `(1 - S) ⊗ id` is moved past the
  tensor comparison isomorphism `zfree (ℕ∪{∞}) ⊗ zfree S ≅ zfree ((ℕ∪{∞}) × S)`;
* `eShift S = ePred S ∘ shiftNS S : (ℕ∪{∞}) × S ⟶ S`, the map `(k,x) ↦ e_k x` (`ẽ` without the
  shift, with `(∞,x) ↦ x`).
-/

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed
open OnePoint

noncomputable section

namespace Work.ATOM

/-- The shift `(k,x) ↦ (k+1,x)` on `(ℕ∪{∞}) ⊗ S`, `∞ ↦ ∞`.  This is `whiskerRight shift S`. -/
abbrev shiftNS (S : LightProfinite.{0}) : NS S ⟶ NS S :=
  MonoidalCategory.whiskerRight LightProfinite.shift S

/-- `eShift(k,x) = e_k x` (with `eShift(∞,x) = x`): the composite `ẽ ∘ shift`. -/
abbrev eShift (S : LightProfinite.{0}) [Infinite S] : NS S ⟶ S := shiftNS S ≫ ePred S

/-- The pointwise description of `shiftNS`: it shifts the first coordinate. -/
lemma shiftNS_apply (S : LightProfinite.{0}) (p : ↥(NS S)) :
    shiftNS S p = (LightProfinite.shift p.1, p.2) := by
  refine Prod.ext ?_ ?_
  · have h := ConcreteCategory.congr_hom
      (CartesianMonoidalCategory.whiskerRight_fst LightProfinite.shift S) p
    rw [ConcreteCategory.comp_apply] at h
    exact h
  · have h := ConcreteCategory.congr_hom
      (CartesianMonoidalCategory.whiskerRight_snd LightProfinite.shift S) p
    rw [ConcreteCategory.comp_apply] at h
    exact h

section

variable (S : LightProfinite.{0}) [Infinite S]

/-- `shiftNS` fixes the second coordinate, so `pr₂N ∘ shiftNS = pr₂N`. -/
lemma shiftNS_pr₂N : shiftNS S ≫ pr₂N S = pr₂N S := by
  apply ConcreteCategory.hom_ext
  intro p
  have h := ConcreteCategory.congr_hom
    (CartesianMonoidalCategory.whiskerRight_snd LightProfinite.shift S) p
  rw [ConcreteCategory.comp_apply] at h
  exact h

/-- `eShift = ePred ∘ shiftNS` by definition. -/
lemma eShift_eq : eShift S = shiftNS S ≫ ePred S := rfl

/-- `eShift(∞,x) = x`. -/
@[simp] lemma eShift_infty (x : ↥S) : eShift S (mkNS S (∞ : ℕ∪{∞}) x) = x := by
  rw [eShift, ConcreteCategory.comp_apply, shiftNS_apply]
  rfl

/-- `eShift(k,x) = e_k x` for a finite `k`. -/
@[simp] lemma eShift_some (k : ℕ) (x : ↥S) :
    eShift S (mkNS S ((k : ℕ) : ℕ∪{∞}) x) = e S k x := by
  rw [eShift, ConcreteCategory.comp_apply, shiftNS_apply]
  rw [show LightProfinite.shift ((k : ℕ) : ℕ∪{∞}) = (((k + 1 : ℕ) : ℕ) : ℕ∪{∞}) from rfl]
  exact ePredFun_succ k x

end

end Work.ATOM
