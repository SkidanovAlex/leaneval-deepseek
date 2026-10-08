import Mathlib
import Submission.Work.ZassenhausSuzuki.SingerAux

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Conjugacy-class counting vocabulary

Small definitions used by the count of Suzuki 1962 §8, p. 118 (the `q/2` class count that pins
down `C_G(S.V)` and `|N_G(S.V)|`).
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.ZassenhausSuzuki

variable {G : Type}

/-- `x` is a product of two involutions (Suzuki's *strongly real* elements). -/
def IsStronglyReal [Group G] (x : G) : Prop :=
  ∃ a b : G, a * a = 1 ∧ b * b = 1 ∧ a * b = x

/-- The non-identity elements of a subgroup, as a set: `S#`. -/
def nonzero [Mul G] [One G] (S : Set G) : Set G := {x | x ∈ S ∧ x ≠ 1}

@[simp] theorem mem_nonzero [Mul G] [One G] {S : Set G} {x : G} :
    x ∈ nonzero S ↔ x ∈ S ∧ x ≠ 1 := Iff.rfl

/-- The set of conjugacy classes of `G` that meet the set `X`. -/
noncomputable def classesMeeting [Group G] (X : Set G) : Set (ConjClasses G) :=
  {C | (C.carrier ∩ X).Nonempty}

@[simp] theorem mem_classesMeeting [Group G] {X : Set G} {C : ConjClasses G} :
    C ∈ classesMeeting X ↔ (C.carrier ∩ X).Nonempty := Iff.rfl

/-- The number of conjugacy classes of `G` that meet the set `X`. -/
noncomputable def numClasses [Group G] (X : Set G) : ℕ :=
  Nat.card {C : ConjClasses G // (C.carrier ∩ X).Nonempty}

/-- A class of `G` is either a subset of `classesMeeting X` or disjoint from it: the counting
form of "the classes meeting `X` are the classes of the elements of `X`". -/
theorem numClasses_eq_card_range [Group G] [Finite G] {X : Set G} :
    numClasses X =
      Nat.card (Set.range (fun x : {x : G // x ∈ X} => (ConjClasses.mk x.1 : ConjClasses G))) := by
  refine Nat.card_congr
    { toFun := fun C =>
        ⟨C.1, ?_⟩
      invFun := fun C =>
        ⟨C.1, ?_⟩
      left_inv := fun C => Subtype.ext rfl
      right_inv := fun C => Subtype.ext rfl }
  · obtain ⟨x, hx1, hx2⟩ := C.2
    exact ⟨⟨x, hx2⟩, ConjClasses.mem_carrier_iff_mk_eq.mp hx1⟩
  · obtain ⟨x, hx⟩ := C.2
    exact ⟨x.1, by rw [← hx]; exact ConjClasses.mem_carrier_mk, x.2⟩

end Work.ZassenhausSuzuki
