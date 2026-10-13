/-
  Area C2 (WilC2): the vocabulary of *cut types*.

  For a subset `X` of a linear order:
  * `comp X u` is the component of `u` in `X` (the points of `X` connected to `u` by an
    interval contained in `X`);
  * `maxSet X` is the set of points of `X` which are the maximum of their component;
  * `supSet X` is the set of points outside `X` which are the supremum of a component of `X`
    (i.e. approached arbitrarily closely from below by points of `X`).

  These two "endpoint" sets are the ones whose elements, in the application
  `Work.WilC2.type_determined_by_cut`, are shown to lie in `Dcl A`: they are `A`-definable and
  finite (finitely many components), hence their elements are `A`-definable.

  This file contains only order-theoretic material; the definability and finiteness statements
  live in the modules under `Submission/Work/WilC2/`.
-/
import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section
open Classical
namespace Work.WilC2

variable {M : Type*} [LinearOrder M]

/-- The component of `u` in `X`: the points `x` of `X` such that the whole segment between `x`
and `u` is contained in `X`.  This is the maximal convex subset of `X` containing `u` (when
`u ∈ X`). -/
def comp (X : Set M) (u : M) : Set M :=
  {x | x ∈ X ∧ (∀ z, x ≤ z → z ≤ u → z ∈ X) ∧ (∀ z, u ≤ z → z ≤ x → z ∈ X)}

/-- The points of `X` which are the maximum of their component: there is no point of `X` just
above them inside `X`. -/
def maxSet (X : Set M) : Set M :=
  {x | x ∈ X ∧ ∀ y, y ∈ X → x < y → ∃ z, x < z ∧ z < y ∧ z ∉ X}

/-- The points outside `X` which are the supremum of a component of `X`: they are approached
arbitrarily closely from below by points of `X` and are not in `X`. -/
def supSet (X : Set M) : Set M :=
  {x | x ∉ X ∧ (∃ y, y ∈ X ∧ y < x) ∧ ∀ z, z < x → ∃ y, y ∈ X ∧ z < y ∧ y < x}

@[simp] lemma mem_comp {X : Set M} {u x : M} :
    x ∈ comp X u ↔ x ∈ X ∧ (∀ z, x ≤ z → z ≤ u → z ∈ X) ∧
      (∀ z, u ≤ z → z ≤ x → z ∈ X) := Iff.rfl

@[simp] lemma mem_maxSet {X : Set M} {x : M} :
    x ∈ maxSet X ↔ x ∈ X ∧ ∀ y, y ∈ X → x < y → ∃ z, x < z ∧ z < y ∧ z ∉ X := Iff.rfl

@[simp] lemma mem_supSet {X : Set M} {x : M} :
    x ∈ supSet X ↔ x ∉ X ∧ (∃ y, y ∈ X ∧ y < x) ∧
      ∀ z, z < x → ∃ y, y ∈ X ∧ z < y ∧ y < x := Iff.rfl

lemma comp_subset (X : Set M) (u : M) : comp X u ⊆ X := fun _ h => h.1

lemma maxSet_subset (X : Set M) : maxSet X ⊆ X := fun _ h => h.1

lemma supSet_notMem (X : Set M) {x : M} (h : x ∈ supSet X) : x ∉ X := h.1

lemma mem_comp_self {X : Set M} {u : M} (h : u ∈ X) : u ∈ comp X u := by
  refine ⟨h, ?_, ?_⟩
  · intro z h1 h2
    have hzu : z = u := le_antisymm h2 h1
    rw [hzu]; exact h
  · intro z h1 h2
    have hzu : z = u := le_antisymm h2 h1
    rw [hzu]; exact h

lemma comp_ordConnected (X : Set M) (u : M) : (comp X u).OrdConnected := by
  refine Set.OrdConnected.mk ?_
  intro x hx y hy z hz
  obtain ⟨hxz, hzy⟩ := hz
  refine ⟨?_, ?_, ?_⟩
  · rcases le_total z u with h | h
    · exact hx.2.1 z hxz h
    · exact hy.2.2 z h hzy
  · intro w h1 h2
    exact hx.2.1 w (le_trans hxz h1) h2
  · intro w h1 h2
    exact hy.2.2 w h1 (le_trans h2 hzy)

lemma comp_mono {X Y : Set M} (h : X ⊆ Y) (u : M) : comp X u ⊆ comp Y u := by
  intro x hx
  refine ⟨h hx.1, ?_, ?_⟩
  · intro z h1 h2; exact h (hx.2.1 z h1 h2)
  · intro z h1 h2; exact h (hx.2.2 z h1 h2)

/-- Two points of the same component have the same component. -/
lemma comp_eq_of_mem {X : Set M} {u v : M} (h : v ∈ comp X u) : comp X v = comp X u := by
  ext x
  constructor
  · intro hx
    refine ⟨hx.1, ?_, ?_⟩
    · intro z h1 h2
      rcases le_total z v with hzv | hvz
      · exact hx.2.1 z h1 hzv
      · exact h.2.1 z hvz h2
    · intro z h1 h2
      rcases le_total z v with hzv | hvz
      · exact h.2.2 z h1 hzv
      · exact hx.2.2 z hvz h2
  · intro hx
    refine ⟨hx.1, ?_, ?_⟩
    · intro z h1 h2
      rcases le_total z u with hzu | huz
      · exact hx.2.1 z h1 hzu
      · exact h.2.2 z huz h2
    · intro z h1 h2
      rcases le_total z u with hzu | huz
      · exact h.2.1 z h1 hzu
      · exact hx.2.2 z huz h2

/-- A point of `X` which is the maximum of its component lies in `maxSet X`. -/
lemma mem_maxSet_of_max_comp {X : Set M} {u : M} (huX : u ∈ X)
    (hmax : ∀ x ∈ comp X u, x ≤ u) : u ∈ maxSet X := by
  refine ⟨huX, fun y hyX huy => ?_⟩
  by_contra hcon
  push_neg at hcon
  have hycomp : y ∈ comp X u := by
    refine ⟨hyX, ?_, ?_⟩
    · intro z h1 h2
      exact absurd (le_trans h1 h2) (not_le.mpr huy)
    · intro z h1 h2
      rcases eq_or_lt_of_le h1 with h | h
      · rw [← h]; exact huX
      · rcases eq_or_lt_of_le h2 with h' | h'
        · rw [h']; exact hyX
        · exact hcon z h h'
  exact absurd (hmax y hycomp) (not_le.mpr huy)

/-- A point strictly below the supremum of a set is below some point of the set. -/
lemma exists_lt_of_isLUB {s : Set M} {β : M} (h : IsLUB s β) {z : M} (hz : z < β) :
    ∃ y ∈ s, z < y := by
  by_contra hc
  push_neg at hc
  exact absurd (h.2 (mem_upperBounds.mpr hc)) (not_le.mpr hz)

/-- If `β` is the supremum of the component of `u ∈ X` and `β ∈ X`, then `β ∈ maxSet X`. -/
lemma mem_maxSet_of_isLUB_comp {X : Set M} {u β : M} (huX : u ∈ X)
    (hJ : IsLUB (comp X u) β) (hβX : β ∈ X) : β ∈ maxSet X := by
  have huJ : u ∈ comp X u := mem_comp_self huX
  have hle : u ≤ β := mem_upperBounds.mp hJ.1 u huJ
  have hβcomp : β ∈ comp X u := by
    refine ⟨hβX, ?_, ?_⟩
    · intro z h1 h2
      have hzu : z = u := le_antisymm h2 (le_trans hle h1)
      rw [hzu]; exact huX
    · intro z h1 h2
      rcases eq_or_lt_of_le h1 with h | h
      · rw [← h]; exact huX
      · rcases eq_or_lt_of_le h2 with h' | h'
        · rw [h']; exact hβX
        · -- `u < z < β`: `z` lies between `u` and an element of `comp X u` above it
          obtain ⟨y, hyJ, hyz⟩ := exists_lt_of_isLUB hJ h'
          exact comp_subset X u (comp_ordConnected X u |>.out huJ hyJ ⟨le_of_lt h, le_of_lt hyz⟩)
  have hmax' : ∀ x ∈ comp X β, x ≤ β := by
    rw [comp_eq_of_mem hβcomp]
    exact fun x hx => mem_upperBounds.mp hJ.1 x hx
  exact mem_maxSet_of_max_comp hβX hmax'

/-- If `β` is the supremum of the component of `u ∈ X` and `β ∉ X`, then `β ∈ supSet X`. -/
lemma mem_supSet_of_isLUB_comp {X : Set M} {u β : M} (huX : u ∈ X)
    (hJ : IsLUB (comp X u) β) (hβX : β ∉ X) (huβ : u < β) : β ∈ supSet X := by
  refine ⟨hβX, ⟨u, huX, huβ⟩, ?_⟩
  intro z hz
  obtain ⟨y, hyJ, hyz⟩ := exists_lt_of_isLUB hJ hz
  refine ⟨y, comp_subset X u hyJ, hyz, ?_⟩
  exact lt_of_le_of_ne (mem_upperBounds.mp hJ.1 y hyJ) (fun h => hβX (h ▸ comp_subset X u hyJ))

end Work.WilC2
