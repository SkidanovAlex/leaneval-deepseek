import Mathlib
import Submission.Work.AppXIField.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `L0.isSimpleModule_actSubring`: irreducibility of `V` as a module over the action ring

Let `V` be a finite additive group and `A` a finite commutative group acting on `V` by additive
automorphisms, fixed-point freely on `V \ {0}` (i.e. `a • v = v` with `v ≠ 0` forces `a = 1`), with
`|V| ≤ 2|A| + 1`.  Then `V` is a **simple** module over
`R := Work.AppXIField.actSubring A V = Subring.closure (Set.range (actEnd A V))`.

This is the irreducibility step of Appendix XI Prop. 2 (cf. the docstring of
`Submission/Work/AppXIField/Defs.lean`, "Irreducibility").  The `R`-submodules of `V` are in
particular `A`-invariant additive subgroups, so every nonzero `R`-submodule `W` is a union of `A`-orbits
of nonzero elements, each of size exactly `|A|` by `hfree`; hence `|W| ≥ |A| + 1`.  If `W ≠ ⊤` then
`[V : W] ≥ 2`, so `|V| ≥ 2|W| ≥ 2|A| + 2 > 2|A| + 1 ≥ |V|`, a contradiction.  Note that the oddness
of `|V|` (present in the graded statement of L0) is *not* needed here.
-/

namespace Work.AppXIDickson.L0

open Work.AppXIField

theorem isSimpleModule_actSubring {V A : Type} [AddCommGroup V] [Finite V] [CommGroup A]
    [Finite A] [DistribMulAction A V] (hV : 1 < Nat.card V)
    (hfree : ∀ (a : A) (v : V), v ≠ 0 → a • v = v → a = 1)
    (hbig : Nat.card V ≤ 2 * Nat.card A + 1) :
    IsSimpleModule ↥(Work.AppXIField.actSubring A V) V := by
  classical
  haveI : Fintype V := Fintype.ofFinite V
  haveI : Fintype A := Fintype.ofFinite A
  rw [isSimpleModule_iff]
  -- `⊥ ≠ ⊤` for the lattice of `R`-submodules, from `1 < |V|`
  haveI : Nontrivial (Submodule ↥(actSubring A V) V) := by
    refine ⟨⊥, ⊤, fun h => ?_⟩
    haveI : Subsingleton V := ⟨fun x y => by
      have hx : x ∈ (⊥ : Submodule ↥(actSubring A V) V) := by rw [h]; trivial
      have hy : y ∈ (⊥ : Submodule ↥(actSubring A V) V) := by rw [h]; trivial
      rw [Submodule.mem_bot] at hx hy
      rw [hx, hy]⟩
    have : Nat.card V = 1 := Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, ⟨0⟩⟩
    omega
  refine IsSimpleOrder.of_forall_eq_top fun W hWne => ?_
  by_contra hWn
  -- a nonzero element of `W`
  obtain ⟨v, hvW, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hWne
  -- the orbit map `a ↦ a • v` is injective (`hfree`)
  have key : ∀ a b : A, a • v = b • v → a = b := by
    intro a b hab
    have h1 : (b⁻¹ * a) • v = v := by
      calc (b⁻¹ * a) • v = b⁻¹ • (a • v) := mul_smul b⁻¹ a v
        _ = b⁻¹ • (b • v) := by rw [hab]
        _ = (b⁻¹ * b) • v := (mul_smul b⁻¹ b v).symm
        _ = (1 : A) • v := by rw [inv_mul_cancel]
        _ = v := one_smul A v
    exact (inv_mul_eq_one.mp (hfree (b⁻¹ * a) v hv0 h1)).symm
  -- and its image avoids `0`
  have hne : ∀ a : A, a • v ≠ 0 := by
    intro a h
    apply hv0
    calc v = (1 : A) • v := (one_smul A v).symm
      _ = (a⁻¹ * a) • v := by rw [inv_mul_cancel]
      _ = a⁻¹ • (a • v) := mul_smul a⁻¹ a v
      _ = a⁻¹ • (0 : V) := by rw [h]
      _ = 0 := smul_zero a⁻¹
  -- `W` is `A`-invariant (it is an `R`-submodule and `actEnd A V a ∈ R`)
  have hmem : ∀ a : A, a • v ∈ W := by
    intro a
    have hsm : (⟨actEnd A V a, actEnd_mem_actSubring A V a⟩ : ↥(actSubring A V)) • v = a • v := rfl
    rw [← hsm]
    exact W.smul_mem _ hvW
  -- hence `|A| ≤ |W ∖ {0}|`
  have hcardA : Nat.card A ≤ Nat.card {w : ↥W // w ≠ 0} := by
    let f : A → {w : ↥W // w ≠ 0} := fun a => ⟨⟨a • v, hmem a⟩, by
      intro h
      exact hne a (by simpa using congrArg Subtype.val h)⟩
    have hf : Function.Injective f := by
      intro a b hab
      have h1 : (⟨a • v, hmem a⟩ : ↥W) = ⟨b • v, hmem b⟩ := congrArg Subtype.val hab
      exact key a b (congrArg Subtype.val h1)
    exact Nat.card_le_card_of_injective f hf
  have hsub : Nat.card {w : ↥W // w ≠ 0} + 1 = Nat.card ↥W := by
    have hc : Fintype.card {w : ↥W // w ≠ 0} = Fintype.card ↥W - 1 := by
      have h := Fintype.card_subtype_compl (α := ↥W) (p := fun w => w = 0)
      rw [Fintype.card_subtype_eq] at h
      simpa using h
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, hc]
    exact Nat.sub_add_cancel
      (by have : 0 < Fintype.card ↥W := Fintype.card_pos_iff.mpr ⟨0⟩; omega)
  have hA : Nat.card A + 1 ≤ Nat.card ↥W := by
    rw [← hsub]
    exact Nat.add_le_add_right hcardA 1
  -- and `W ≠ ⊤` forces `[V : W] ≥ 2`, whence `|V| ≥ 2|W|`
  have hcardW : Nat.card ↥W.toAddSubgroup = Nat.card ↥W := rfl
  have hB : 2 * Nat.card ↥W ≤ Nat.card V := by
    have hidx : 2 ≤ W.toAddSubgroup.index := by
      have htop : W.toAddSubgroup ≠ ⊤ := fun h => hWn (Submodule.toAddSubgroup_eq_top.mp h)
      have h1 := AddSubgroup.one_lt_index_of_ne_top htop
      omega
    calc 2 * Nat.card ↥W = Nat.card ↥W * 2 := by rw [Nat.mul_comm]
      _ ≤ Nat.card ↥W * W.toAddSubgroup.index := Nat.mul_le_mul_left _ hidx
      _ = Nat.card ↥W.toAddSubgroup * W.toAddSubgroup.index := by rw [hcardW]
      _ = Nat.card V := W.toAddSubgroup.card_mul_index
  omega

end Work.AppXIDickson.L0
