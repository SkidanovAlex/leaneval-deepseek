import Mathlib
import Submission.Work.ORBassSerre.Action.Basic
import Submission.Work.ORBassSerre.Action.Cocompact
import Submission.Work.ORBassSerre.Tree.IsTreeAPI
import Submission.Work.ORLocInd.FKSKernel.Kurosh.bool_list_parity

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.ORLocInd.FKSKernel.Kurosh

open Work.ORBassSerre

open Quiver

variable {G : Type*} {V : Type*} [Group G] [Quiver V] [Quiver.HasInvolutiveReverse V]
  [MulAction G V] [Work.ORBassSerre.GraphAction G V]

/-- In a tree, an arrow has no loops: `v ≠ w` for `e : v ⟶ w`. -/
theorem ne_of_arrow (hT : Work.ORBassSerre.IsTree V) {v w : V} (e : v ⟶ w) : v ≠ w := by
  intro hvw
  subst hvw
  have hred : (e.toPath : Quiver.Path v v).IsReduced :=
    Quiver.Path.IsReduced.of_length_lt_two (by simp)
  have := hT.2 v e.toPath hred
  have hlen := congrArg Quiver.Path.length this
  simp at hlen

/-- Stabilizer of an arrow is contained in the stabilizer of its source. -/
theorem stabilizer_edge_le_left (u : Quiver.Total V) :
    MulAction.stabilizer G u ≤ MulAction.stabilizer G u.left := by
  obtain ⟨a, b, f⟩ := u
  intro g hg
  rw [MulAction.mem_stabilizer_iff] at hg ⊢
  have := congrArg Quiver.Total.left hg
  simpa using this

/-- Stabilizer of an arrow is contained in the stabilizer of its target. -/
theorem stabilizer_edge_le_right (u : Quiver.Total V) :
    MulAction.stabilizer G u ≤ MulAction.stabilizer G u.right := by
  obtain ⟨a, b, f⟩ := u
  intro g hg
  rw [MulAction.mem_stabilizer_iff] at hg ⊢
  have := congrArg Quiver.Total.right hg
  simpa using this

/-- Reversing an arrow does not change its stabilizer. -/
theorem stabilizer_reverse (u : Quiver.Total V) :
    MulAction.stabilizer G u.reverse = MulAction.stabilizer G u := by
  have hinj : Function.Injective (Quiver.Total.reverse : Quiver.Total V → Quiver.Total V) :=
    Function.Involutive.injective (fun e => Quiver.Total.reverse_reverse e)
  ext g
  rw [MulAction.mem_stabilizer_iff, MulAction.mem_stabilizer_iff, GraphAction.smul_reverse_apply,
    hinj.eq_iff]

/-- If `S` and `T` are complementary subsets of a group, `1 ∈ S`, `1 ∈ T`, and `x` lies in both,
then `x = 1`. -/
theorem eq_one_of_isComplement {S T : Set G} (h : Subgroup.IsComplement S T) (h1S : 1 ∈ S)
    (h1T : 1 ∈ T) {x : G} (hxS : x ∈ S) (hxT : x ∈ T) : x = 1 := by
  have h1 : ((⟨x, hxS⟩, ⟨1, h1T⟩) : S × T) = (⟨1, h1S⟩, ⟨x, hxT⟩) := by
    apply h.1
    simp
  have : (⟨x, hxS⟩ : S) = ⟨1, h1S⟩ := congrArg Prod.fst h1
  exact Subtype.ext_iff.mp this

/-- `List.IsChain` is preserved by mapping, when the relation is transported along the map. -/
theorem List.isChain_map {α β : Type*} {R : α → α → Prop} {S : β → β → Prop} {l : List α}
    (h : l.IsChain R) (f : α → β) (hf : ∀ a b, R a b → S (f a) (f b)) :
    (l.map f).IsChain S := by
  induction h with
  | nil => exact List.IsChain.nil
  | singleton a => exact List.IsChain.singleton (f a)
  | cons_cons hab _ ih => exact List.IsChain.cons_cons (hf _ _ hab) ih
/-- The `Fin`-indexed `get` of a mapped list. -/
theorem get_map_snd {α β : Type*} (f : α → β) (l : List α)
    (i : Fin (l.map f).length) :
    (l.map f).get i = f (l.get ⟨i.val, by simpa using i.isLt⟩) := by
  rw [List.get_eq_getElem, List.getElem_map, List.get_eq_getElem]
/-- Membership in `HNNExtension.toSubgroup` for the subgroups `A.subgroupOf X` and
`(A.map (MulAut.conj σ)).subgroupOf X`, expressed back in `G`. -/
theorem hnn_letter_mem_iff {G : Type*} [Group G] (X A : Subgroup G) (σ : G) (x : ↥X)
    (u : ℤˣ) :
    x ∈ HNNExtension.toSubgroup (A.subgroupOf X)
          ((A.map (MulAut.conj σ).toMonoidHom).subgroupOf X) u
      ↔ (x : G) ∈ (if u = 1 then A else A.map (MulAut.conj σ).toMonoidHom) := by
  rw [HNNExtension.toSubgroup]
  split_ifs with h
  · rw [Subgroup.mem_subgroupOf]
  · rw [Subgroup.mem_subgroupOf]
/-- The `get` of a mapped list, in terms of the original list. -/
theorem get_map_get {α β : Type*} (g : α → β) (L : List α) (i : Fin L.length) :
    (L.map g).get ⟨i.val, by simpa using i.isLt⟩ = g (L.get i) := by
  rw [List.get_eq_getElem, List.getElem_map, List.get_eq_getElem]

/-- Parity bookkeeping, phrased with a projection to `Bool`. -/
theorem bool_list_parity_map {α : Type*} (L : List α) (g : α → Bool)
    (h : (L.map g).IsChain (fun a b => a ≠ b)) (i j : Fin L.length) :
    g (L.get i) = g (L.get j) ↔ i.val % 2 = j.val % 2 := by
  have h1 := bool_list_parity (L.map g) h ⟨i.val, by simpa using i.isLt⟩
    ⟨j.val, by simpa using i.isLt⟩
  simpa [get_map_snd] using h1
/-- A `Fin`-indexed statement follows from the corresponding `ℕ`-indexed `getElem` statement. -/
theorem fin_get_of_getElem {α : Type*} (l : List α) (P : α → Prop)
    (h : ∀ (i : ℕ) (hi : i < l.length), P l[i]) : ∀ i : Fin l.length, P (l.get i) := by
  intro i
  rw [List.get_eq_getElem]
  exact h i.val i.isLt

/-- Parity bookkeeping with `ℕ` indices. -/
theorem bool_list_parity_elem {α : Type*} (L : List α) (g : α → Bool)
    (h : (L.map g).IsChain (fun a b => a ≠ b)) :
    ∀ (i j : ℕ) (hi : i < L.length) (hj : j < L.length),
      g L[i] = g L[j] ↔ i % 2 = j % 2 := by
  intro i j hi hj
  have h1 := bool_list_parity_map L g h ⟨i, hi⟩ ⟨j, hj⟩
  simpa [List.get_eq_getElem] using h1
/-- The two vertex groups of an amalgam, indexed by `Bool`. -/
def AmalgamFamily {G : Type*} [Group G] (X Y : Subgroup G) : Bool → Type _ :=
  fun b => match b with | true => ↥X | false => ↥Y

instance amalgamFamilyGroup {G : Type*} [Group G] (X Y : Subgroup G) :
    ∀ b, Group (AmalgamFamily X Y b) :=
  fun b => Bool.casesOn b Y.toGroup X.toGroup

/-- The image in `G` of a letter of an amalgam normal form. -/
def amalgamLetter {G : Type*} [Group G] (X Y : Subgroup G) :
    (Σ b : Bool, AmalgamFamily X Y b) → G :=
  fun l => Bool.casesOn l.1 Y.subtype X.subtype l.2

end Work.ORLocInd.FKSKernel.Kurosh
