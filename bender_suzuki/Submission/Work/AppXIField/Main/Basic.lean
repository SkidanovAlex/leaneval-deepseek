import Mathlib
import Submission.Work.AppXIField.Defs
import Submission.Work.ThmF.ChV3.Ctx

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedVariables false
noncomputable section
open Classical LeanEval.GroupTheory.Defs Submission.Blueprint
open scoped commutatorElement

namespace Work.AppXIField

open Work.ThmF.ChV3

/-! ## Cardinality of the near-field quotient `R/N` -/

/-- `|N.subgroupOf R| = |N|` for `N ≤ R`. -/
theorem card_subgroupOf {G : Type} [Group G] (R N : Subgroup G) (hNR : N ≤ R) :
    Nat.card ↥(N.subgroupOf R) = Nat.card ↥N := by
  refine Nat.card_congr ⟨fun x => ⟨(x : G), x.2⟩, fun y => ⟨⟨(y : G), hNR y.2⟩, y.2⟩, ?_, ?_⟩
  · intro x; exact Subtype.ext rfl
  · intro y; exact Subtype.ext rfl

/-- `|R/N| = f ^ m` from `|R| = |N| * f ^ m`. -/
theorem card_quot_eq {G : Type} [Group G] [Finite G] (R N : Subgroup G) (hNR : N ≤ R) {f m : ℕ}
    (h : Nat.card ↥R = Nat.card ↥N * f ^ m) :
    Nat.card (↥R ⧸ N.subgroupOf R) = f ^ m := by
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (N.subgroupOf R)
  rw [card_subgroupOf R N hNR, h] at h1
  have h2 : f ^ m * Nat.card ↥N = Nat.card (↥R ⧸ N.subgroupOf R) * Nat.card ↥N := by
    rw [mul_comm (f ^ m) (Nat.card ↥N), h1]
  exact Nat.mul_right_cancel (Nat.card_pos (α := ↥N)) h2.symm

/-! ## Commutativity of `R/N` -/

/-- `R/N` is commutative when all commutators of `R` lie in `N`. -/
theorem isMulCommutative_quot {G : Type} [Group G] (R N : Subgroup G)
    [(N.subgroupOf R).Normal]
    (h : ∀ x ∈ R, ∀ y ∈ R, x * y * x⁻¹ * y⁻¹ ∈ N) :
    IsMulCommutative (↥R ⧸ N.subgroupOf R) := by
  rw [isMulCommutative_iff]
  intro a b
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (N.subgroupOf R) a
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (N.subgroupOf R) b
  rw [← commutatorElement_eq_one_iff_mul_comm, ← map_commutatorElement,
    QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  simpa only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv] using h x x.2 y y.2

/-! ## The fixed points of an automorphism of `C_Q(P)` by conjugation -/

/-- The elements of `C_Q(P)` fixed by a conjugation automorphism are exactly the elements
commuting with the conjugating element. -/
theorem card_fixedSubtype_CQ {G : Type} [Group G] {Q P : Subgroup G} (w : G)
    (φw : MulAut ↥(CQ Q P))
    (hw : ∀ a : ↥(CQ Q P), ((φw a : ↥(CQ Q P)) : G) = w * (a : G) * w⁻¹) :
    Nat.card ↥{a : ↥(CQ Q P) | φw a = a} =
      Nat.card ↥(CQ Q P ⊓ Subgroup.centralizer ({w} : Set G)) := by
  refine Nat.card_congr ⟨fun a => ⟨(a.1 : G), ⟨a.1.2, ?_⟩⟩,
    fun b => ⟨⟨(b : G), (Subgroup.mem_inf.mp b.2).1⟩, ?_⟩, ?_, ?_⟩
  · refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
    have h : (a.1 : G) = w * (a.1 : G) * w⁻¹ := by
      conv_lhs => rw [← congrArg (fun z : ↥(CQ Q P) => (z : G)) a.2]
      exact hw a.1
    calc (a.1 : G) * w = (w * (a.1 : G) * w⁻¹) * w := by conv_lhs => rw [h]
      _ = w * (a.1 : G) := by group
  · refine Subtype.ext ?_
    show ((φw ⟨(b : G), (Subgroup.mem_inf.mp b.2).1⟩ : ↥(CQ Q P)) : G) = (b : G)
    rw [hw ⟨(b : G), (Subgroup.mem_inf.mp b.2).1⟩]
    have hcb : (b : G) * w = w * (b : G) :=
      Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp b.2).2
    calc w * (b : G) * w⁻¹ = (b : G) * w * w⁻¹ := by rw [hcb]
      _ = (b : G) := by group
  · intro a; exact Subtype.ext rfl
  · intro b; exact Subtype.ext rfl

/-! ## Plumbing for the additive action on `Additive Q` -/

/-- The value of the action built by `distribMulActionAdditiveOfHom`. -/
theorem smul_additiveOfHom_apply {A Q : Type*} [Monoid A] [Monoid Q] (f : A →* MulAut Q)
    (a : A) (x : Additive Q) :
    @SMul.smul _ _ (smulAdditiveOfHom A Q f) a x = Additive.ofMul (f a (Additive.toMul x)) := rfl

theorem toMul_ne_one_iff {Q : Type*} [MulOneClass Q] (x : Additive Q) :
    (Additive.toMul x ≠ 1) ↔ x ≠ 0 := by
  have h0 : (0 : Additive Q) = Additive.ofMul 1 := rfl
  rw [h0]
  exact Additive.ofMul.symm.injective.ne_iff

end Work.AppXIField
