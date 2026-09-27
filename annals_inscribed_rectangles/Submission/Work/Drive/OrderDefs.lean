import Mathlib
import Submission.Work.Drive.Interfaces
import Submission.Work.Theorem3Endgame

/-!
# Shared definitions for the order-split core (`orderSplit_model`)

The geometric content of Hugelmeyer's Theorem 3 splits into

* an **openness** statement about the non-collision set `NonColl γ` (equivalently: closedness of
  `GoodC γ`), and
* an **order witness**: a `ZMod 2`-valued function on the non-collision angles that is locally
  constant, antisymmetric, and additive while the sum stays in the non-collision set.  This function
  is `u ↦ [M ≺ u·M]` where `≺` is the total order (Theorem 2 of the paper) on disjoint homologically
  nontrivial projective planes in `ℝ × ℝP³` (Lemmas 3 and 4).

`orderSplit_of_witness` (in `orderSplit_model`) turns these two inputs into `OrderSplitHolds γ`.
-/

namespace Work.Drive

open Manifold
open scoped Manifold ContDiff

/-- The non-collision set of angles: the complement of `GoodC γ`. -/
def NonColl (γ : Circle → ℝ × ℝ) : Set UnitAddCircle := (Submission.Configuration.GoodC γ)ᶜ

/-- Every element of `ZMod 2` is `0` or `1`. -/
lemma zmod2_eq_zero_or_one (x : ZMod 2) : x = 0 ∨ x = 1 := by
  have hlt : x.val < 2 := ZMod.val_lt x
  have : x.val = 0 ∨ x.val = 1 := by omega
  rcases this with h | h
  · left; exact ZMod.val_injective 2 (by rw [h]; rfl)
  · right; exact ZMod.val_injective 2 (by rw [h]; rfl)

/-- `NonColl γ` is invariant under `u ↦ -u`. -/
lemma neg_mem_nonColl (γ : Circle → ℝ × ℝ) (u : UnitAddCircle) :
    -u ∈ NonColl γ ↔ u ∈ NonColl γ := by
  have h : Submission.Configuration.GoodC γ = -Submission.Configuration.GoodC γ :=
    Submission.Configuration.GoodC_neg γ
  have hiff : (-u ∈ Submission.Configuration.GoodC γ) ↔
      (u ∈ Submission.Configuration.GoodC γ) := by
    rw [← Set.mem_neg (s := Submission.Configuration.GoodC γ) (a := u)]
    exact (Iff.of_eq (congrArg (fun S => u ∈ S) h)).symm
  simp only [NonColl, Set.mem_compl_iff]
  exact not_congr hiff

lemma nonColl_eq_neg (γ : Circle → ℝ × ℝ) : NonColl γ = -NonColl γ := by
  unfold NonColl
  calc (Submission.Configuration.GoodC γ)ᶜ = (-(Submission.Configuration.GoodC γ))ᶜ :=
        congrArg Set.compl (Submission.Configuration.GoodC_neg γ)
    _ = -((Submission.Configuration.GoodC γ)ᶜ) := by
        ext u; simp only [Set.mem_compl_iff, Set.mem_neg]

/-- **The residual content.**  A parity function on the non-collision angles which is locally
constant, antisymmetric, and additive whenever the sum stays in the non-collision set.  This is
exactly `u ↦ [M ≺ u·M]` where `≺` is Hugelmeyer's total order on disjoint projective planes. -/
def OrderWitness (γ : Circle → ℝ × ℝ) : Prop :=
  ∃ b : UnitAddCircle → ZMod 2,
    (∀ u ∈ NonColl γ, ∃ U : Set UnitAddCircle, IsOpen U ∧ u ∈ U ∧
      ∀ v ∈ U, v ∈ NonColl γ → b v = b u) ∧
    (∀ u ∈ NonColl γ, b (-u) = 1 - b u) ∧
    (∀ a ∈ NonColl γ, ∀ c ∈ NonColl γ, a + c ∈ NonColl γ →
      b a = 1 → b c = 1 → b (a + c) = 1)

end Work.Drive
