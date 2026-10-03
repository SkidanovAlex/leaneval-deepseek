import Mathlib
import Submission.Work.OROneRel.graded_hnn_coset
import Submission.Work.OROneRel.coset_lev

/-!
# The distance from the base in the coset graph `G ⧸ H`

`GradedHNN.distToBase H t hgen x` is the minimal length of a path from the base vertex to `x` in
the coset graph `GradedHNN.Coset H t` (vertices `G ⧸ H`, edges `{gH, gtH}`), and
`GradedHNN.IsParent hgen x y` says that `y` is a neighbour of `x` with distance one less.

The main facts proved here:

* `distToBase_baseC`, `distToBase_eq_zero`: distance `0` characterises the base;
* `distToBase_le`: minimality;
* `exists_two_mul_lev_sub_dist`, `abs_lev_le_dist`: the level of a vertex has the same parity as its
  distance and is bounded by it (so that `distToBase_adj_ne` holds);
* `distToBase_adj_le`, `distToBase_adj_ne`: along an edge the distance changes by exactly one;
* `exists_isParent`: every non-base vertex has a parent.

The *uniqueness* of the parent (`Work.OROneRel.parent_unique`, in `cosetGraphIsTree.lean`) is the
remaining obligation: together with the facts here it yields `IsTree (Coset H t)`.
-/

set_option autoImplicit false

namespace Work.OROneRel

universe u

namespace GradedHNN

open Quiver

variable {G : Type u} [Group G] (H : Subgroup G) (t : G)
  (φbar : G →* Multiplicative ℤ) (hH : ∀ h : H, φbar (h : G) = 1)

theorem lev_adj' (ht : φbar t = Multiplicative.ofAdd 1) {x y : Coset H t}
    (e : x ⟶ y) : lev H t φbar hH y = lev H t φbar hH x + 1 ∨
      lev H t φbar hH x = lev H t φbar hH y + 1 :=
  lev_adj H t φbar hH ht e.down

/-- The level difference across an arrow has absolute value `1`. -/
theorem abs_lev_adj (ht : φbar t = Multiplicative.ofAdd 1) {x y : Coset H t} (e : x ⟶ y) :
    |lev H t φbar hH y - lev H t φbar hH x| = 1 := by
  rcases lev_adj' H t φbar hH ht e with h | h
  · rw [h]; simp
  · rw [h]; simp

/-- Parity: along any path the level difference minus the length is even. -/
theorem exists_two_mul_lev_sub (ht : φbar t = Multiplicative.ofAdd 1) {a b : Coset H t}
    (p : Quiver.Path a b) :
    ∃ k : ℤ, lev H t φbar hH b - lev H t φbar hH a = (p.length : ℤ) + 2 * k := by
  induction p with
  | nil => exact ⟨0, by simp⟩
  | cons p e ih =>
    rename_i b c
    obtain ⟨k, hk⟩ := ih
    have hstep := lev_adj' H t φbar hH ht e
    rw [show (p.cons e).length = p.length + 1 from rfl]
    push_cast
    rcases hstep with hs | hs
    · exact ⟨k, by rw [hs]; linarith⟩
    · exact ⟨k - 1, by rw [hs] at hk; linarith⟩

/-- The absolute value of the level difference is at most the length of the path. -/
theorem abs_lev_sub_le_length (ht : φbar t = Multiplicative.ofAdd 1) {a b : Coset H t}
    (p : Quiver.Path a b) :
    |lev H t φbar hH b - lev H t φbar hH a| ≤ (p.length : ℤ) := by
  induction p with
  | nil => simp
  | cons p e ih =>
    rename_i b c
    have hab : |lev H t φbar hH c - lev H t φbar hH b| = 1 := abs_lev_adj H t φbar hH ht e
    rw [show (p.cons e).length = p.length + 1 from rfl]
    push_cast
    calc |lev H t φbar hH c - lev H t φbar hH a|
        = |(lev H t φbar hH c - lev H t φbar hH b) + (lev H t φbar hH b - lev H t φbar hH a)| := by
          congr 1; ring
      _ ≤ |lev H t φbar hH c - lev H t φbar hH b| + |lev H t φbar hH b - lev H t φbar hH a| :=
          abs_add_le _ _
      _ ≤ (p.length : ℤ) + 1 := by rw [hab]; linarith

theorem lev_baseC : lev H t φbar hH (baseC H t) = 0 := by
  rw [baseC, cmk, lev_cmk, map_one]; rfl

/-! ## The distance from the base vertex -/

theorem exists_path_length (hgen : H ⊔ Subgroup.closure ({t} : Set G) = ⊤) (x : Coset H t) :
    ∃ n : ℕ, ∃ p : Quiver.Path (baseC H t) x, p.length = n :=
  ⟨_, (connected_coset H t hgen (baseC H t) x).some, rfl⟩

/-- The distance from the base vertex: the minimal length of a path from `baseC` to `x`. -/
noncomputable def distToBase (hgen : H ⊔ Subgroup.closure ({t} : Set G) = ⊤)
    (x : Coset H t) : ℕ := by
  classical
  exact Nat.find (exists_path_length H t hgen x)

theorem distToBase_spec (hgen : H ⊔ Subgroup.closure ({t} : Set G) = ⊤) (x : Coset H t) :
    ∃ p : Quiver.Path (baseC H t) x, p.length = distToBase H t hgen x := by
  classical
  exact Nat.find_spec (exists_path_length H t hgen x)

theorem distToBase_le (hgen : H ⊔ Subgroup.closure ({t} : Set G) = ⊤) {x : Coset H t}
    (p : Quiver.Path (baseC H t) x) : distToBase H t hgen x ≤ p.length := by
  classical
  exact Nat.find_min' (exists_path_length H t hgen x) ⟨p, rfl⟩

theorem distToBase_baseC (hgen : H ⊔ Subgroup.closure ({t} : Set G) = ⊤) :
    distToBase H t hgen (baseC H t) = 0 := by
  have h := distToBase_le H t hgen (Quiver.Path.nil : Quiver.Path (baseC H t) (baseC H t))
  exact Nat.eq_zero_of_le_zero h

theorem distToBase_eq_zero {hgen : H ⊔ Subgroup.closure ({t} : Set G) = ⊤} {x : Coset H t}
    (h : distToBase H t hgen x = 0) : x = baseC H t := by
  obtain ⟨p, hp⟩ := distToBase_spec H t hgen x
  rw [h] at hp
  have h0 : p.length = 0 := hp
  cases p with
  | nil => rfl
  | cons p e => simp at h0

/-- The level of a vertex has the same parity as its distance from the base. -/
theorem exists_two_mul_lev_sub_dist (hgen : H ⊔ Subgroup.closure ({t} : Set G) = ⊤)
    (ht : φbar t = Multiplicative.ofAdd 1) (x : Coset H t) :
    ∃ k : ℤ, lev H t φbar hH x = (distToBase H t hgen x : ℤ) + 2 * k := by
  obtain ⟨p, hp⟩ := distToBase_spec H t hgen x
  obtain ⟨k, hk⟩ := exists_two_mul_lev_sub H t φbar hH ht p
  have hbase : lev H t φbar hH (baseC H t) = 0 := lev_baseC H t φbar hH
  refine ⟨k, ?_⟩
  rw [← hp]
  linarith

/-- The absolute value of the level is at most the distance from the base. -/
theorem abs_lev_le_dist (hgen : H ⊔ Subgroup.closure ({t} : Set G) = ⊤)
    (ht : φbar t = Multiplicative.ofAdd 1) (x : Coset H t) :
    |lev H t φbar hH x| ≤ (distToBase H t hgen x : ℤ) := by
  obtain ⟨p, hp⟩ := distToBase_spec H t hgen x
  have h := abs_lev_sub_le_length H t φbar hH ht p
  have hbase : lev H t φbar hH (baseC H t) = 0 := lev_baseC H t φbar hH
  rw [← hp]
  rw [hbase, sub_zero] at h
  exact h

/-- Adjacent vertices have distances differing by at most one. -/
theorem distToBase_adj_le (hgen : H ⊔ Subgroup.closure ({t} : Set G) = ⊤) {x y : Coset H t}
    (e : x ⟶ y) : distToBase H t hgen y ≤ distToBase H t hgen x + 1 := by
  obtain ⟨p, hp⟩ := distToBase_spec H t hgen x
  have h := distToBase_le H t hgen (p.cons e)
  rw [show (p.cons e).length = p.length + 1 from rfl, hp] at h
  exact h

/-- Adjacent vertices have different distances from the base. -/
theorem distToBase_adj_ne (hH : ∀ h : H, φbar (h : G) = 1)
    (hgen : H ⊔ Subgroup.closure ({t} : Set G) = ⊤)
    (ht : φbar t = Multiplicative.ofAdd 1) {x y : Coset H t} (e : x ⟶ y) :
    distToBase H t hgen x ≠ distToBase H t hgen y := by
  intro hxy
  obtain ⟨k₁, h₁⟩ := exists_two_mul_lev_sub_dist H t φbar hH hgen ht x
  obtain ⟨k₂, h₂⟩ := exists_two_mul_lev_sub_dist H t φbar hH hgen ht y
  have habs : |lev H t φbar hH y - lev H t φbar hH x| = 1 := abs_lev_adj H t φbar hH ht e
  have hd : lev H t φbar hH y - lev H t φbar hH x = 2 * (k₂ - k₁) := by
    rw [h₁, h₂, hxy]; ring
  have h2 : |2 * (k₂ - k₁)| = 1 := by rw [← hd]; exact habs
  have h4 : 2 * (k₂ - k₁) = 0 := by
    have := abs_le.mp (le_of_eq h2); omega
  rw [h4] at h2
  simp at h2

/-- `y` is a *parent* of `x`: a neighbour of `x` one step closer to the base. -/
def IsParent (hgen : H ⊔ Subgroup.closure ({t} : Set G) = ⊤) (x y : Coset H t) : Prop :=
  (Nonempty (y ⟶ x) ∨ Nonempty (x ⟶ y)) ∧ distToBase H t hgen y + 1 = distToBase H t hgen x

/-- Every vertex other than the base has a parent. -/
theorem exists_isParent (hH : ∀ h : H, φbar (h : G) = 1)
    (hgen : H ⊔ Subgroup.closure ({t} : Set G) = ⊤)
    (ht : φbar t = Multiplicative.ofAdd 1) {x : Coset H t} (hx : x ≠ baseC H t) :
    ∃ y : Coset H t, IsParent (H := H) (t := t) hgen x y := by
  obtain ⟨p, hp⟩ := distToBase_spec H t hgen x
  have hlen : p.length ≠ 0 := by
    intro h0
    exact hx (distToBase_eq_zero (H := H) (t := t) (hgen := hgen) (x := x) (by rw [← hp, h0]))
  obtain ⟨c, q, e, rfl⟩ := (Path.length_ne_zero_iff_eq_cons p).mp hlen
  refine ⟨c, Or.inl ⟨e⟩, ?_⟩
  have hle : distToBase H t hgen c ≤ q.length := distToBase_le H t hgen q
  have hge : distToBase H t hgen c + 1 ≤ distToBase H t hgen x := by
    rw [← hp]; exact Nat.succ_le_succ hle
  have hne : distToBase H t hgen c ≠ distToBase H t hgen x :=
    distToBase_adj_ne H t φbar hH hgen ht e
  have hle2 : distToBase H t hgen x ≤ distToBase H t hgen c + 1 := distToBase_adj_le H t hgen e
  omega

end GradedHNN

