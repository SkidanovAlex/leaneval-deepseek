import Mathlib
import Submission.Work.ZassenhausSuzuki.SzSetting
import Submission.Work.ThmF.ChV12.L5Base
import Submission.Work.ZassenhausSuzuki.Shadow.L5Struct

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.ThmF.ChV12.L5Aux` — small assembly lemmas for Lemma 5

`Q₀sub H` is an elementary abelian `2`-group (Ch. V §1 Prop. 1 (c)), hence
`Q₀sub H` and its image `(Q₀sub H).subgroupOf (X5 H t)` are `2`-groups and abelian, and the two
have the same cardinality.  Together with `GaloisField.card` this is what turns the coordination
`e : (Q₀sub H).subgroupOf (X5 H t) ≃* Multiplicative (GF(2ⁿ))` produced by
`Work.ZassenhausPSL2.ZData.psl2_coords` into `Nat.card ↥(Q₀sub H) = 2 ^ n`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open LeanEval.GroupTheory.Defs

namespace Work.ZassenhausSuzuki.Shadow.L5
open Submission.Blueprint

open Work.ThmF.L5
/-- A finite group of exponent `2` is a `2`-group. -/
theorem isPGroup_two_of_exp_two {A : Type} [Group A] [Finite A]
    (h : ∀ x : A, x * x = 1) : IsPGroup 2 A := by
  haveI : Fintype A := Fintype.ofFinite A
  -- a group of exponent `2` is abelian, hence a `ZMod 2`-module
  have hinv : ∀ x : A, x⁻¹ = x := fun x => inv_eq_of_mul_eq_one_right (h x)
  have hcomm : ∀ x y : A, x * y = y * x := by
    intro x y
    have h2 : (x * y)⁻¹ = y⁻¹ * x⁻¹ := mul_inv_rev x y
    rw [hinv (x * y), hinv y, hinv x] at h2
    exact h2
  letI : CommGroup A := { (inferInstance : Group A) with mul_comm := hcomm }
  have hexp : ∀ x : Additive A, 2 • x = 0 := by
    intro x
    rw [two_nsmul]
    exact Additive.ext (show (x + x).toMul = (0 : Additive A).toMul from h x.toMul)
  letI : Module (ZMod 2) (Additive A) := AddCommGroup.zmodModule hexp
  refine IsPGroup.iff_card.mpr ⟨Module.finrank (ZMod 2) (Additive A), ?_⟩
  show Nat.card (Additive A) = 2 ^ Module.finrank (ZMod 2) (Additive A)
  rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := ZMod 2) (V := Additive A),
    ZMod.card 2]

variable {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t s : G}

/-- `Q₀sub H` is a `2`-group. -/
theorem isPGroup_two_Q0sub (hcomm : ∀ a ∈ involutions (H : Set G),
    ∀ b ∈ involutions (H : Set G), a * b = b * a) :
    IsPGroup 2 ↥(Work.ThmF.Q0sub H) := by
  obtain ⟨h1, -, -⟩ := Q0sub_elementary (H := H) hcomm
  exact isPGroup_two_of_exp_two (A := ↥(Work.ThmF.Q0sub H))
    (fun x => Subtype.ext (by simpa using h1 (x : G) x.2))

/-- `Q₀sub H` is abelian. -/
theorem isAbelianSubgroup_Q0sub (hcomm : ∀ a ∈ involutions (H : Set G),
    ∀ b ∈ involutions (H : Set G), a * b = b * a) :
    IsAbelianSubgroup (Work.ThmF.Q0sub H) := by
  obtain ⟨-, h2, -⟩ := Q0sub_elementary (H := H) hcomm
  exact fun a ha b hb => h2 a ha b hb

/-- `Q₀sub H` is contained in `X5 H t`. -/
theorem Q0sub_le_X5 : Work.ThmF.Q0sub H ≤ Work.ThmF.Lemma5.X5 H t :=
  (Subgroup.closure_le _).mpr (fun z hz => Work.ThmF.Lemma5.Q0_subset_X5 H t hz)

/-- The image of `Q₀sub H` in `X5 H t` has the same cardinality as `Q₀sub H`. -/
theorem card_subgroupOf_Q0sub :
    Nat.card ↥((Work.ThmF.Q0sub H).subgroupOf (Work.ThmF.Lemma5.X5 H t)) =
      Nat.card ↥(Work.ThmF.Q0sub H) :=
  Nat.card_congr (Subgroup.subgroupOfEquivOfLe (H := Work.ThmF.Q0sub H)
    (K := Work.ThmF.Lemma5.X5 H t) Q0sub_le_X5).toEquiv

/-- The image of `Q₀sub H` in `X5 H t` is a `2`-group. -/
theorem isPGroup_two_Q0sub_sub (hcomm : ∀ a ∈ involutions (H : Set G),
    ∀ b ∈ involutions (H : Set G), a * b = b * a) :
    IsPGroup 2 ↥((Work.ThmF.Q0sub H).subgroupOf (Work.ThmF.Lemma5.X5 H t)) := by
  have h2 := isPGroup_two_Q0sub (H := H) hcomm
  rw [IsPGroup.iff_card] at h2 ⊢
  obtain ⟨n, hn⟩ := h2
  exact ⟨n, by rw [card_subgroupOf_Q0sub]; exact hn⟩

/-- The image of `Q₀sub H` in `X5 H t` is abelian. -/
theorem isAbelianSubgroup_Q0sub_sub (hcomm : ∀ a ∈ involutions (H : Set G),
    ∀ b ∈ involutions (H : Set G), a * b = b * a) :
    IsAbelianSubgroup ((Work.ThmF.Q0sub H).subgroupOf (Work.ThmF.Lemma5.X5 H t)) := by
  obtain ⟨-, h2, -⟩ := Q0sub_elementary (H := H) hcomm
  intro a ha b hb
  have ha' : (a : ↥(Work.ThmF.Lemma5.X5 H t)).1 ∈ Work.ThmF.Q0sub H :=
    Subgroup.mem_subgroupOf.mp ha
  have hb' : (b : ↥(Work.ThmF.Lemma5.X5 H t)).1 ∈ Work.ThmF.Q0sub H :=
    Subgroup.mem_subgroupOf.mp hb
  exact Subtype.ext
    (h2 ((a : ↥(Work.ThmF.Lemma5.X5 H t)) : G) ha' ((b : ↥(Work.ThmF.Lemma5.X5 H t)) : G) hb')

/-- `Nat.card (Multiplicative (GF(2ⁿ))) = 2ⁿ`. -/
theorem card_multiplicative_galoisField (n : ℕ) (hn : n ≠ 0) :
    Nat.card (Multiplicative (GaloisField 2 n)) = 2 ^ n :=
  GaloisField.card 2 n hn

end Work.ZassenhausSuzuki.Shadow.L5
