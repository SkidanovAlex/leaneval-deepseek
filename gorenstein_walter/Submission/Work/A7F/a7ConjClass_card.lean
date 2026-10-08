/-
The conjugacy class of the model involution `t = (0 1)(2 3)` of `A₇` has `105` elements.

The count is done the structural way, so that nothing is evaluated by the kernel: the Finset
`a7ConjClass t = {g * t * g⁻¹ | g ∈ A₇}` is the conjugacy class of `t`, whose cardinality is the
index of the centralizer `[A₇ : C_{A₇}(t)] = 2520 / 24 = 105`
(`Work.A7F.card_centralizer_a7Invol` computes `|C_{A₇}(t)| = 24`).
-/
import Mathlib
import Submission.Work.A7.Defs
import Submission.Work.A7F.Defs
import Submission.Work.A7F.card_centralizer_a7Invol
import Submission.OddOrder.GroupTheory.ConjClassCardinality

namespace Work.A7F

open Subgroup

/-- The Finset of conjugates `g * x * g⁻¹` of an element `x` of a finite group has as many
elements as the index of the centralizer of `x`: it is the conjugacy class of `x`, whose
cardinality is `[G : C_G(x)]` by orbit--stabilizer.

`OddOrder.RepresentationTheory.card_class_eq_index_centralizer` gives the cardinality of the
conjugacy class as a subtype of `G` (via `ConjClasses`); here we identify that subtype with the
subtype of `G` cut out by membership in the Finset of conjugates. -/
theorem card_image_conj_eq_index {G : Type*} [Group G] [Fintype G] [DecidableEq G] (x : G) :
    (Finset.univ.image (fun g : G => g * x * g⁻¹)).card
      = (Subgroup.centralizer ({x} : Set G)).index := by
  classical
  -- Membership in the Finset of conjugates is exactly `ConjClasses.mk · = ConjClasses.mk x`.
  have hiff : ∀ y : G, (ConjClasses.mk y = ConjClasses.mk x) ↔
      y ∈ Finset.univ.image (fun g : G => g * x * g⁻¹) := by
    intro y
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    rw [ConjClasses.mk_eq_mk_iff_isConj, isConj_comm, isConj_iff]
  have h1 : Nat.card {y : G // ConjClasses.mk y = ConjClasses.mk x}
      = Nat.card {y : G // y ∈ Finset.univ.image (fun g : G => g * x * g⁻¹)} :=
    Nat.card_congr (Equiv.subtypeEquivRight hiff)
  rw [← OddOrder.RepresentationTheory.card_class_eq_index_centralizer x, h1,
    Nat.card_eq_fintype_card, Fintype.card_coe]

/-- The centralizer in `A₇` of the model involution has index `105`: `2520 / 24`. -/
theorem index_centralizer_a7Invol :
    (Subgroup.centralizer ({a7Invol} : Set (alternatingGroup (Fin 7)))).index = 105 := by
  have hmul :=
    (Subgroup.centralizer ({a7Invol} : Set (alternatingGroup (Fin 7)))).index_mul_card
  rw [card_centralizer_a7Invol, Work.A7.card_alternatingGroup_seven] at hmul
  omega

/-- The `A₇`-conjugacy class of the model involution `t = (0 1)(2 3)` has `105` elements. -/
theorem a7ConjClass_card : (a7ConjClass a7Invol).card = 105 := by
  rw [a7ConjClass, card_image_conj_eq_index, index_centralizer_a7Invol]

end Work.A7F
