import Mathlib
import Submission.Work.PStable.conjData
import Submission.Work.ThmF.Prove.S3.ConjRep

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.S3.EllCorrDefs` — elementary-abelian subgroups vs. submodules

Let `M ≤ G` be a commutative subgroup of exponent dividing `n` (in the applications `M` is an
elementary abelian `ℓ`-group, `n = ℓ`).  Then `Additive ↥M` is canonically a `ZMod n`-module and
its `ZMod n`-submodules are in bijection with the subgroups of `G` contained in `M`, by

* `subOfSubmodule W` — the subgroup `{g ∈ M | g ∈ W}` of `G` cut out by `W`;
* `submoduleOfSub N` — the submodule `N ⊓ M` of `Additive ↥M` cut out by `N`.

Everything here is general algebra; the file exists so that the correspondence can be used by
several lemmas about the `ℓ`-submodules of a minimal invariant subgroup.
-/

set_option linter.unusedVariables false

namespace Work.S3

open scoped IsMulCommutative

variable {G : Type*} [Group G]

/-- The subgroup of `G` cut out by a `ZMod n`-submodule of `Additive ↥M`. -/
def subOfSubmodule (M : Subgroup G) [IsMulCommutative ↥M] {n : ℕ}
    [Fact (∀ x : ↥M, x ^ n = 1)] (W : Submodule (ZMod n) (Additive ↥M)) : Subgroup G where
  carrier := {g | ∃ (hg : g ∈ M), Additive.ofMul (⟨g, hg⟩ : ↥M) ∈ W}
  one_mem' := ⟨M.one_mem, by
    have h : (⟨(1 : G), M.one_mem⟩ : ↥M) = 1 := Subtype.ext rfl
    rw [h]; exact W.zero_mem⟩
  mul_mem' := by
    rintro a b ⟨ha, h1⟩ ⟨hb, h2⟩
    refine ⟨M.mul_mem ha hb, ?_⟩
    have h : (⟨a * b, M.mul_mem ha hb⟩ : ↥M) = ⟨a, ha⟩ * ⟨b, hb⟩ := Subtype.ext rfl
    rw [h]
    exact W.add_mem h1 h2
  inv_mem' := by
    rintro a ⟨ha, h1⟩
    refine ⟨M.inv_mem ha, ?_⟩
    have h : (⟨a⁻¹, M.inv_mem ha⟩ : ↥M) = ⟨a, ha⟩⁻¹ := Subtype.ext rfl
    rw [h]
    exact W.neg_mem h1

@[simp] theorem subOfSubmodule_mem (M : Subgroup G) [IsMulCommutative ↥M] {n : ℕ}
    [Fact (∀ x : ↥M, x ^ n = 1)] (W : Submodule (ZMod n) (Additive ↥M)) (g : G) :
    g ∈ subOfSubmodule M W ↔ ∃ (hg : g ∈ M), Additive.ofMul (⟨g, hg⟩ : ↥M) ∈ W := Iff.rfl

theorem subOfSubmodule_le (M : Subgroup G) [IsMulCommutative ↥M] {n : ℕ}
    [Fact (∀ x : ↥M, x ^ n = 1)] (W : Submodule (ZMod n) (Additive ↥M)) :
    subOfSubmodule M W ≤ M := fun _ hg => hg.1

/-- Membership of a multiplicative element of `M` in `subOfSubmodule M W`. -/
theorem ofMul_mem_subOfSubmodule (M : Subgroup G) [IsMulCommutative ↥M] {n : ℕ}
    [Fact (∀ x : ↥M, x ^ n = 1)] (W : Submodule (ZMod n) (Additive ↥M)) (m : ↥M) :
    Additive.ofMul m ∈ W ↔ (m : G) ∈ subOfSubmodule M W := by
  constructor
  · intro hm
    exact ⟨m.2, by convert hm using 2⟩
  · rintro ⟨hg, hm⟩
    convert hm using 2

/-- The `ZMod n`-submodule of `Additive ↥M` cut out by a subgroup of `G`. -/
def submoduleOfSub (M : Subgroup G) [IsMulCommutative ↥M] {n : ℕ}
    [Fact (∀ x : ↥M, x ^ n = 1)] (N : Subgroup G) : Submodule (ZMod n) (Additive ↥M) :=
  AddSubgroup.toZModSubmodule n ((N.subgroupOf M).toAddSubgroup)

@[simp] theorem submoduleOfSub_mem (M : Subgroup G) [IsMulCommutative ↥M] {n : ℕ}
    [Fact (∀ x : ↥M, x ^ n = 1)] (N : Subgroup G) (x : Additive ↥M) :
    x ∈ submoduleOfSub (n := n) M N ↔ ((Additive.toMul x : ↥M) : G) ∈ N := by
  simp [submoduleOfSub, Subgroup.mem_subgroupOf]

theorem submoduleOfSub_mono (M : Subgroup G) [IsMulCommutative ↥M] {n : ℕ}
    [Fact (∀ x : ↥M, x ^ n = 1)] {N₁ N₂ : Subgroup G} (h : N₁ ≤ N₂) :
    submoduleOfSub (n := n) M N₁ ≤ submoduleOfSub (n := n) M N₂ := by
  intro x hx
  rw [submoduleOfSub_mem] at hx ⊢
  exact h hx

theorem subOfSubmodule_mono (M : Subgroup G) [IsMulCommutative ↥M] {n : ℕ}
    [Fact (∀ x : ↥M, x ^ n = 1)] {W₁ W₂ : Submodule (ZMod n) (Additive ↥M)} (h : W₁ ≤ W₂) :
    subOfSubmodule M W₁ ≤ subOfSubmodule M W₂ := by
  intro g hg
  rw [subOfSubmodule_mem] at hg ⊢
  exact ⟨hg.1, h hg.2⟩

theorem submoduleOfSub_subOfSubmodule (M : Subgroup G) [IsMulCommutative ↥M] {n : ℕ}
    [Fact (∀ x : ↥M, x ^ n = 1)] (W : Submodule (ZMod n) (Additive ↥M)) :
    submoduleOfSub (n := n) M (subOfSubmodule M W) = W := by
  ext x
  rw [submoduleOfSub_mem, subOfSubmodule_mem]
  constructor
  · rintro ⟨hg, hw⟩
    convert hw using 2
    exact Subtype.ext rfl
  · intro hx
    exact ⟨(Additive.toMul x).2, by convert hx using 2; exact Subtype.ext rfl⟩

theorem subOfSubmodule_submoduleOfSub (M : Subgroup G) [IsMulCommutative ↥M] {n : ℕ}
    [Fact (∀ x : ↥M, x ^ n = 1)] (N : Subgroup G) :
    subOfSubmodule M (submoduleOfSub (n := n) M N) = N ⊓ M := by
  ext g
  rw [subOfSubmodule_mem, Subgroup.mem_inf]
  constructor
  · rintro ⟨hg, hw⟩
    rw [submoduleOfSub_mem] at hw
    refine ⟨?_, hg⟩
    convert hw using 2
    rfl
  · rintro ⟨hN, hM⟩
    exact ⟨hM, by rw [submoduleOfSub_mem]; convert hN using 2; rfl⟩

theorem submoduleOfSub_self (M : Subgroup G) [IsMulCommutative ↥M] {n : ℕ}
    [Fact (∀ x : ↥M, x ^ n = 1)] : submoduleOfSub (n := n) M M = ⊤ := by
  ext x
  simp [submoduleOfSub_mem]

theorem submoduleOfSub_top (M : Subgroup G) [IsMulCommutative ↥M] {n : ℕ}
    [Fact (∀ x : ↥M, x ^ n = 1)] : submoduleOfSub (n := n) M ⊤ = ⊤ := by
  ext x
  simp [submoduleOfSub_mem]

theorem submoduleOfSub_bot (M : Subgroup G) [IsMulCommutative ↥M] {n : ℕ}
    [Fact (∀ x : ↥M, x ^ n = 1)] : submoduleOfSub (n := n) M ⊥ = ⊥ := by
  ext x
  rw [submoduleOfSub_mem, Submodule.mem_bot, Subgroup.mem_bot]
  constructor
  · intro h
    have h2 : (Additive.toMul x : ↥M) = 1 := Subtype.ext h
    calc x = Additive.ofMul (Additive.toMul x) := rfl
      _ = Additive.ofMul (1 : ↥M) := by rw [h2]
      _ = 0 := rfl
  · intro h
    rw [h]
    rfl

theorem subOfSubmodule_top (M : Subgroup G) [IsMulCommutative ↥M] {n : ℕ}
    [Fact (∀ x : ↥M, x ^ n = 1)] : subOfSubmodule M (⊤ : Submodule (ZMod n) (Additive ↥M)) = M := by
  refine le_antisymm (subOfSubmodule_le M ⊤) ?_
  intro g hg
  exact ⟨hg, by simp⟩

theorem subOfSubmodule_bot (M : Subgroup G) [IsMulCommutative ↥M] {n : ℕ}
    [Fact (∀ x : ↥M, x ^ n = 1)] : subOfSubmodule M (⊥ : Submodule (ZMod n) (Additive ↥M)) = ⊥ := by
  refine le_antisymm ?_ bot_le
  intro g hg
  rw [subOfSubmodule_mem] at hg
  obtain ⟨hgM, hw⟩ := hg
  rw [Submodule.mem_bot] at hw
  rw [Subgroup.mem_bot]
  have h2 : (⟨g, hgM⟩ : ↥M) = 1 := congrArg Additive.toMul hw
  exact congrArg Subtype.val h2

theorem subOfSubmodule_eq_bot_iff (M : Subgroup G) [IsMulCommutative ↥M] {n : ℕ}
    [Fact (∀ x : ↥M, x ^ n = 1)] (W : Submodule (ZMod n) (Additive ↥M)) :
    subOfSubmodule M W = ⊥ ↔ W = ⊥ := by
  constructor
  · intro h
    rw [← submoduleOfSub_subOfSubmodule (n := n) M W, h, submoduleOfSub_bot]
  · intro h
    rw [h]
    exact subOfSubmodule_bot M

theorem subOfSubmodule_eq_M_iff (M : Subgroup G) [IsMulCommutative ↥M] {n : ℕ}
    [Fact (∀ x : ↥M, x ^ n = 1)] (W : Submodule (ZMod n) (Additive ↥M)) :
    subOfSubmodule M W = M ↔ W = ⊤ := by
  constructor
  · intro h
    rw [← submoduleOfSub_subOfSubmodule (n := n) M W, h, submoduleOfSub_self]
  · intro h
    rw [h]
    exact subOfSubmodule_top M

theorem card_subOfSubmodule (M : Subgroup G) [IsMulCommutative ↥M] {n : ℕ}
    [Fact (∀ x : ↥M, x ^ n = 1)] (W : Submodule (ZMod n) (Additive ↥M)) :
    Nat.card ↥(subOfSubmodule M W) = Nat.card ↥W :=
  Nat.card_congr
    { toFun := fun g =>
        ⟨Additive.ofMul ⟨(g : G), subOfSubmodule_le M W g.2⟩,
          (ofMul_mem_subOfSubmodule M W ⟨(g : G), subOfSubmodule_le M W g.2⟩).mpr g.2⟩
      invFun := fun x =>
        ⟨((Additive.toMul x : ↥M) : G),
          (ofMul_mem_subOfSubmodule M W (Additive.toMul x)).mp x.2⟩
      left_inv := fun g => Subtype.ext rfl
      right_inv := fun x => Subtype.ext rfl }

end Work.S3
