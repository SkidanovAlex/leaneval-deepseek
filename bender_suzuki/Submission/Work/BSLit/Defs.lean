import Mathlib
import Submission.Blueprint.Interfaces
import Submission.Work.ThmF.Tools.External

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.BSLit` — elementary literature inputs of ThmF / NormalComplement

This is the vocabulary module of the subproject `BSLit` (chain-audit item 4).  It fixes the two
notions used by the three deliverables of the area:

* `Work.BSLit.ArithmeticNineTwoSeven` — Huppert–Blackburn IX (2-7), `Work.ThmF.ArithmeticNineTwoSeven`;
* `Work.BSLit.WielandtFixedPoint` — Wielandt's fixed-point formula, `Work.ThmF.WielandtFixedPoint`;
* `Work.BSLit.BenderModelFacts2Prop` — the lead's clause, `Submission.Blueprint.BenderModelFacts2Prop`.

For Wielandt's formula we work with a group `F` of automorphisms of a finite group `Q`, given
through a monoid homomorphism `ρ : F →* MulAut Q`.  The two fixed-point objects are
`fixedBy ρ H ≤ Q` (subgroup of fixed points of `H ≤ F`) and, in the linear case,
`fixedSubmodule ρ H ≤ V`.
-/

set_option autoImplicit false

namespace Work.BSLit

/-! ## Fixed points of a group of automorphisms -/

/-- `fixedBy ρ H` is the subgroup of `Q` consisting of the points fixed by every element of the
subgroup `H ≤ F`, where `F` acts on `Q` through `ρ`. -/
def fixedBy {F Q : Type*} [Group F] [Group Q] (ρ : F →* MulAut Q) (H : Subgroup F) :
    Subgroup Q where
  carrier := {q | ∀ g ∈ H, ρ g q = q}
  one_mem' := by intro g _; exact map_one _
  mul_mem' := by
    intro a b ha hb g hg
    rw [map_mul, ha g hg, hb g hg]
  inv_mem' := by
    intro a ha g hg
    rw [map_inv, ha g hg]

@[simp]
theorem mem_fixedBy {F Q : Type*} [Group F] [Group Q] {ρ : F →* MulAut Q} {H : Subgroup F}
    {q : Q} : q ∈ fixedBy ρ H ↔ ∀ g ∈ H, ρ g q = q :=
  Iff.rfl

theorem fixedBy_bot {F Q : Type*} [Group F] [Group Q] (ρ : F →* MulAut Q) :
    fixedBy ρ (⊥ : Subgroup F) = ⊤ := by
  refine le_antisymm le_top fun q _ g hg => ?_
  rw [Subgroup.mem_bot.mp hg, map_one]
  rfl

theorem fixedBy_mono {F Q : Type*} [Group F] [Group Q] {ρ : F →* MulAut Q}
    {H₁ H₂ : Subgroup F} (h : H₁ ≤ H₂) : fixedBy ρ H₂ ≤ fixedBy ρ H₁ :=
  fun _ hq g hg => hq g (h hg)

/-- The fixed points of a conjugate subgroup `x H x⁻¹` are the images of the fixed points of `H`
under the automorphism `ρ x`. -/
theorem fixedBy_map_conj {F Q : Type*} [Group F] [Group Q] (ρ : F →* MulAut Q)
    (H : Subgroup F) (x : F) :
    fixedBy ρ (H.map (MulAut.conj x).toMonoidHom)
      = (fixedBy ρ H).map (ρ x).toMonoidHom := by
  ext q
  constructor
  · intro hq
    refine ⟨(ρ x)⁻¹ q, fun g hg => ?_, by simp⟩
    have hmem : x * g * x⁻¹ ∈ H.map (MulAut.conj x).toMonoidHom := by
      have h := Subgroup.mem_map_of_mem (MulAut.conj x).toMonoidHom hg
      simpa [MulAut.conj_apply] using h
    have h := hq (x * g * x⁻¹) hmem
    have h2 : ρ x (ρ g ((ρ x)⁻¹ q)) = q := by
      simpa only [map_mul, map_inv, MulAut.mul_apply] using h
    have h'' := congrArg (fun w => (ρ x)⁻¹ w) h2
    simpa using h''
  · rintro ⟨y, hy, rfl⟩ g hg
    obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hg
    have h3 : ρ k y = y := hy k hk
    change ρ (x * k * x⁻¹) (ρ x y) = ρ x y
    simp only [map_mul, map_inv, MulAut.mul_apply]
    simp [h3]

/-- The cardinality of the fixed point subgroup, as a `Set.ncard` (the form in which the
blueprint states Wielandt's formula). -/
theorem card_fixedBy_eq_ncard {F Q : Type*} [Group F] [Group Q] (ρ : F →* MulAut Q)
    (H : Subgroup F) :
    Nat.card (fixedBy ρ H) = (Set.ncard {q : Q | ∀ g ∈ H, ρ g q = q}) := by
  have h : (↑(fixedBy ρ H) : Set Q) = {q : Q | ∀ g ∈ H, ρ g q = q} := rfl
  rw [← h]
  exact Nat.card_coe_set_eq _

/-! ## Fixed spaces of a linear action -/

section LinearAction

variable {k V F : Type*} [Field k] [AddCommGroup V] [Module k V] [Group F]

/-- The fixed subspace of `H ≤ F` under the linear action `ρ` of `F` on `V`. -/
def fixedSubmodule (ρ : F →* (V ≃ₗ[k] V)) (H : Subgroup F) : Submodule k V where
  carrier := {v | ∀ g ∈ H, ρ g v = v}
  zero_mem' := by intro g _; exact map_zero _
  add_mem' := by
    intro a b ha hb g hg
    rw [map_add, ha g hg, hb g hg]
  smul_mem' := by
    intro c a ha g hg
    rw [map_smul, ha g hg]

@[simp]
theorem mem_fixedSubmodule {ρ : F →* (V ≃ₗ[k] V)} {H : Subgroup F} {v : V} :
    v ∈ fixedSubmodule ρ H ↔ ∀ g ∈ H, ρ g v = v :=
  Iff.rfl

theorem fixedSubmodule_mono {ρ : F →* (V ≃ₗ[k] V)} {H₁ H₂ : Subgroup F} (h : H₁ ≤ H₂) :
    fixedSubmodule ρ H₂ ≤ fixedSubmodule ρ H₁ :=
  fun _ hv g hg => hv g (h hg)

end LinearAction

/-! ## The induced action on a normal invariant quotient -/

section Quotient

variable {F Q : Type*} [Group F] [Group Q]

/-- The action induced by `ρ` on the quotient `Q ⧸ N` of a normal `F`-invariant subgroup `N`. -/
noncomputable def quotientAction (ρ : F →* MulAut Q) (N : Subgroup Q) [N.Normal]
    (hN : ∀ g : F, N.map (ρ g) = N) : F →* MulAut (Q ⧸ N) where
  toFun g := QuotientGroup.congr N N (ρ g) (hN g)
  map_one' := by
    ext x
    refine QuotientGroup.induction_on x ?_
    intro q
    simp
  map_mul' := by
    intro g h
    ext x
    refine QuotientGroup.induction_on x ?_
    intro q
    simp [MulAut.mul_apply, map_mul]

@[simp]
theorem quotientAction_mk (ρ : F →* MulAut Q) (N : Subgroup Q) [N.Normal]
    (hN : ∀ g : F, N.map (ρ g) = N) (g : F) (q : Q) :
    quotientAction ρ N hN g (QuotientGroup.mk q) = QuotientGroup.mk (ρ g q) := by
  simp [quotientAction, QuotientGroup.congr_mk]

end Quotient

/-! ## The two clauses of `BenderModelFacts2Prop`

These are the two conjuncts of `Submission.Blueprint.BenderModelFacts2Prop`, packaged as
definitions so that they can be transported along a group isomorphism. -/

section BenderClauses

/-- First clause of `BenderModelFacts2Prop`: every `2`-element of `H` has order dividing `4`. -/
def TwoElementClause (Y : Type*) [Group Y] (H : Subgroup Y) : Prop :=
  ∀ x ∈ H, (∃ k : ℕ, orderOf x = 2 ^ k) → x ^ 4 = 1

/-- Second clause of `BenderModelFacts2Prop`: if `H` is Zassenhaus, then for `u ∈ Inv H` and an
involution `t ∉ H` the centraliser of `u * t` is cyclic, inverted by `u`, and has order `≥ 6`
as soon as `|Inv H| ≥ 127`. -/
def ZassenhausCentralizerClause (Y : Type*) [Group Y] (H : Subgroup Y) : Prop :=
  Submission.Blueprint.IsZassenhaus H →
    ∀ u ∈ Submission.Blueprint.involutions (H : Set Y), ∀ t : Y, orderOf t = 2 → t ∉ H →
      IsCyclic ↥(Subgroup.centralizer ({u * t} : Set Y)) ∧
      (∀ y ∈ Subgroup.centralizer ({u * t} : Set Y), u * y * u⁻¹ = y⁻¹) ∧
      (127 ≤ (Submission.Blueprint.involutions (H : Set Y)).ncard →
        6 ≤ Nat.card ↥(Subgroup.centralizer ({u * t} : Set Y)))

/-- The body of `Submission.Blueprint.BenderModelFacts2Prop` for a fixed group `Y`. -/
def BenderModelFacts2For (Y : Type*) [Group Y] : Prop :=
  ∀ H : Subgroup Y, LeanEval.GroupTheory.Defs.IsStronglyEmbedded H →
    TwoElementClause Y H ∧ ZassenhausCentralizerClause Y H

end BenderClauses

/-! ## Group algebra sums over subgroups

The sums `1_H = Σ_{h ∈ H} h` over a subgroup are packaged as definitions, so that statements never
have to carry `Fintype ↥H` or decidability instances explicitly. -/

section GroupAlgebra

open Classical

variable {F : Type*} [Group F] [Fintype F]

/-- `1_H = Σ_{h ∈ H} h`, the sum of the elements of `H`, in the integral group algebra `ℤ[F]`. -/
noncomputable def groupSum (H : Subgroup F) : MonoidAlgebra ℤ F :=
  ∑ h : H, MonoidAlgebra.single (h : F) (1 : ℤ)

/-- `Σ_{x ∈ K} 1_{x P x⁻¹}` in `ℤ[F]`: the sum of the element-sums of the conjugates of `P` by
the elements of `K`. -/
noncomputable def conjSum (K P : Subgroup F) : MonoidAlgebra ℤ F :=
  ∑ x : K, groupSum (P.map (MulAut.conj (x : F)))

/-- `Σ_{H ∈ S} n H · 1_H` in `ℤ[F]`. -/
noncomputable def relSum (S : Finset (Subgroup F)) (n : Subgroup F → ℤ) : MonoidAlgebra ℤ F :=
  ∑ H ∈ S, n H • groupSum H

/-- `Σ_{H ∈ S, H ≤ A} n H · |H|`: the part of a relation `relSum S n = 0` carried by the subgroups
contained in `A`. -/
noncomputable def subSum (A : Subgroup F) (S : Finset (Subgroup F)) (n : Subgroup F → ℤ) : ℤ :=
  ∑ H ∈ S, if H ≤ A then n H * (Nat.card H : ℤ) else 0

end GroupAlgebra

end Work.BSLit
