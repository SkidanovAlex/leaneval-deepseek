/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The zig-zag path argument for the amalgam normal form

Let `G` act on a graph `V` (a quiver with involutive reversal) and let `v ≠ w` be adjacent
vertices with `e : v ⟶ w`.  Write `A = Stab(v)`, `B = Stab(w)` and `C = Stab(v ⟶ w)` (the
stabiliser of the oriented edge, as an element of `Quiver.Total V`).

Given a list `L = [ℓ₁, …, ℓₙ]` of elements of `G` with `ℓᵢ ∈ A` for even `i` and `ℓᵢ ∈ B` for
odd `i`, one builds the *zig-zag walk*

`v = z₀ — z₁ — z₂ — … `,  `z_k = ℓ₁⋯ℓ_k · (v if k even else w)`,

whose `k`-th edge is the translate `ℓ₁⋯ℓ_k • e` of the base edge (reversed for even `k`).  If
additionally no `ℓᵢ` lies in `C`, then consecutive edges of this walk are not mutually inverse,
so the walk is a *reduced* path of the graph.  This is the combinatorial heart of the normal form
theorem for an amalgamated product `A *_C B` acting on its Bass–Serre tree; it is used in
`Submission/Work/ORBassSerre/Action/Structure/amalgam_reduced_word_ne_one.lean`.

## Main definitions

* `Work.ORBassSerre.Action.Structure.LastArrow` : `F` is the last arrow of a path
* `…AmalgamZigzag.letter`, `…pre` : the letters of the word and their prefix products
* `…AmalgamZigzag.zz`, `…edge` : the vertices and (total) edges of the zig-zag walk
* `…AmalgamZigzag.arrow`, `…zpath` : the arrows and the path itself

## Main results

* `…AmalgamZigzag.edge_succ_ne` : consecutive edges of the zig-zag are not mutually inverse
* `…AmalgamZigzag.zpath_reduced` : the zig-zag path is reduced
* `Work.ORBassSerre.IsTree.length_eq_zero_of_isReduced_of_eq` : a reduced path of a tree whose
  endpoints coincide has length `0`
-/
import Mathlib
import Submission.Work.ORBassSerre.Action.Basic
import Submission.Work.ORBassSerre.Action.orbitPrefunctor_mapPath_smul_heq
import Submission.Work.ORBassSerre.Action.Structure.smul_eq_smul_stabilizer
import Submission.Work.ORBassSerre.Tree.IsTreeAPI
import Submission.Work.ORBassSerre.Tree.Reduction.isReduced_cons_iff

set_option autoImplicit false
set_option linter.unusedSectionVars false

universe u v

namespace Work.ORBassSerre

open Quiver

section TreeLength

variable {V : Type v} [Quiver V] [Quiver.HasInvolutiveReverse V]

/-- A reduced path of a tree whose endpoints coincide has length `0`. -/
theorem IsTree.length_eq_zero_of_isReduced_of_eq (hT : IsTree V) {a b : V} (hab : a = b)
    (p : Quiver.Path a b) (hp : p.IsReduced) : p.length = 0 := by
  subst hab
  rw [hT.2 a p hp]
  rfl

end TreeLength

end Work.ORBassSerre

namespace Work.ORBassSerre.Action.Structure

open Quiver

/-! ## The last arrow of a path -/

section LastArrow

variable {V : Type v} [Quiver V]

/-- `LastArrow P F` says that the total arrow `F` is the last arrow of the path `P`: every
decomposition `P = q.cons f` of `P` as a path followed by an arrow has `f` as its last arrow. -/
def LastArrow {a x : V} (P : Quiver.Path a x) (F : Quiver.Total V) : Prop :=
  ∀ (u : V) (q : Quiver.Path a u) (f : u ⟶ x), P = q.cons f → Quiver.Total.mk u x f = F

/-- Total arrows whose hom components are heterogeneously equal and whose sources agree are
equal. -/
theorem total_mk_of_heq {x y u : V} {γ : x ⟶ y} {f : u ⟶ y} (h : x = u) (hh : HEq γ f) :
    Quiver.Total.mk u y f = Quiver.Total.mk x y γ :=
  Quiver.Total.ext h.symm rfl hh.symm

/-- The last arrow of `P.cons e` is `e`. -/
theorem lastArrow_cons {a x y : V} (P : Quiver.Path a x) (e : x ⟶ y) :
    LastArrow (P.cons e) (Quiver.Total.mk x y e) := by
  intro u q f hq
  exact total_mk_of_heq (Quiver.Path.obj_eq_of_cons_eq_cons hq)
    (Quiver.Path.hom_heq_of_cons_eq_cons hq)

end LastArrow

namespace AmalgamZigzag

/-! ## The letters of the word and their prefix products -/

section Letter

variable {G : Type u} [Monoid G]

/-- The `k`-th letter of the word `L`, extended by `1` past the end of the list. -/
def letter (L : List G) (k : ℕ) : G := L.getD k 1

/-- The product of the first `k` letters of the word. -/
noncomputable def pre (L : List G) : ℕ → G
  | 0 => 1
  | k + 1 => pre L k * letter L k

theorem pre_succ (L : List G) (k : ℕ) : pre L (k + 1) = pre L k * letter L k := rfl

theorem pre_zero (L : List G) : pre L 0 = 1 := rfl

theorem letter_get (L : List G) (i : Fin L.length) : letter L i.val = L.get i := by
  rw [letter]
  exact List.getD_eq_get L 1 i

theorem letter_eq_one (L : List G) {k : ℕ} (hk : L.length ≤ k) : letter L k = 1 := by
  rw [letter]
  exact List.getD_eq_default L 1 hk

theorem pre_take (L : List G) : ∀ k, k ≤ L.length → pre L k = (L.take k).prod := by
  intro k
  induction k with
  | zero => intro _; rfl
  | succ k ih =>
    intro hk
    rw [pre_succ, ih (Nat.le_of_succ_le hk), List.prod_take_succ L k hk]
    congr 1
    exact letter_get L ⟨k, hk⟩

theorem pre_length (L : List G) : pre L L.length = L.prod := by
  rw [pre_take L L.length le_rfl, List.take_length]

end Letter

/-! ## Parity lemmas for `ℕ` -/

lemma odd_succ {k : ℕ} (h : Even k) : Odd (k + 1) := by
  rw [← Nat.not_even_iff_odd, Nat.even_add_one]
  exact not_not.mpr h

lemma even_succ {k : ℕ} (h : Odd k) : Even (k + 1) := by
  rw [Nat.even_add_one]
  exact Nat.not_even_iff_odd.mpr h

lemma notOdd_succ {k : ℕ} (h : Odd k) : ¬ Odd (k + 1) := by
  rw [Nat.odd_add_one]
  exact not_not.mpr h

lemma notEven_succ {k : ℕ} (h : Even k) : ¬ Even (k + 1) := by
  rw [Nat.even_add_one]
  exact not_not.mpr h

lemma even_zero : Even (0 : ℕ) := ⟨0, rfl⟩

/-! ## The zig-zag walk -/

section Zigzag

variable {G : Type u} {V : Type v} [Group G] [Quiver V] [Quiver.HasInvolutiveReverse V]
  [MulAction G V] [GraphAction G V]

/-- The vertex on the side of position `k` of the word: `v` for even `k`, `w` for odd `k`. -/
noncomputable def sv (v w : V) (k : ℕ) : V := if Even k then v else w

/-- The base edge `e : v ⟶ w`, as an element of `Quiver.Total V`. -/
abbrev ez (v w : V) (e : v ⟶ w) : Quiver.Total V := Quiver.Total.mk v w e

/-- The `k`-th vertex of the zig-zag walk. -/
noncomputable def zz (v w : V) (L : List G) : ℕ → V
  | 0 => v
  | k + 1 => pre L (k + 1) • sv v w (k + 1)

/-- The `k`-th edge of the zig-zag walk, as a total arrow: the translate `pre L k • e` of the
base edge, reversed when `k` is even. -/
noncomputable def edge (v w : V) (e : v ⟶ w) (L : List G) (k : ℕ) : Quiver.Total V :=
  if Odd k then pre L k • ez v w e else (pre L k • ez v w e).reverse

lemma zz_eq (v w : V) (L : List G) : ∀ k, zz v w L k = pre L k • sv v w k
  | 0 => by
    show v = pre L 0 • sv v w 0
    rw [pre_zero, sv, if_pos even_zero]
    exact (one_smul G v).symm
  | k + 1 => rfl

lemma sv_even (v w : V) {k : ℕ} (h : Even k) : sv v w k = v := by rw [sv, if_pos h]

lemma sv_odd (v w : V) {k : ℕ} (h : Odd k) : sv v w k = w := by
  rw [sv, if_neg (Nat.not_even_iff_odd.mpr h)]

lemma zz_even (v w : V) (L : List G) {k : ℕ} (h : Even k) : zz v w L k = pre L k • v := by
  rw [zz_eq v w L k, sv_even v w h]

lemma zz_odd (v w : V) (L : List G) {k : ℕ} (h : Odd k) : zz v w L k = pre L k • w := by
  rw [zz_eq v w L k, sv_odd v w h]

lemma edge_odd (v w : V) (e : v ⟶ w) (L : List G) {k : ℕ} (h : Odd k) :
    edge v w e L k = pre L k • ez v w e := by rw [edge, if_pos h]

lemma edge_even (v w : V) (e : v ⟶ w) (L : List G) {k : ℕ} (h : Even k) :
    edge v w e L k = (pre L k • ez v w e).reverse := by
  rw [edge, if_neg (Nat.not_odd_iff_even.mpr h)]

/-- The source of the `(k+1)`-st edge is the `k`-th vertex. -/
lemma edge_left (v w : V) (e : v ⟶ w) (L : List G) (k : ℕ) :
    (edge v w e L (k + 1)).left = pre L (k + 1) • sv v w k := by
  rw [edge]
  by_cases h : Even k
  · rw [if_pos (odd_succ h), sv_even v w h]
    simp [ez]
  · rw [if_neg (notOdd_succ (Nat.not_even_iff_odd.mp h)),
      sv_odd v w (Nat.not_even_iff_odd.mp h)]
    simp [ez]

/-- The target of the `(k+1)`-st edge is the `(k+1)`-st vertex. -/
lemma edge_right (v w : V) (e : v ⟶ w) (L : List G) (k : ℕ) :
    (edge v w e L (k + 1)).right = pre L (k + 1) • sv v w (k + 1) := by
  rw [edge]
  by_cases h : Even k
  · rw [if_pos (odd_succ h), sv_odd v w (odd_succ h)]
    simp [ez]
  · rw [if_neg (notOdd_succ (Nat.not_even_iff_odd.mp h)),
      sv_even v w (even_succ (Nat.not_even_iff_odd.mp h))]
    simp [ez]

/-- The `k`-th letter fixes the vertex on the side of position `k`. -/
lemma letter_sv (v w : V) (L : List G)
    (hA : ∀ k, Even k → letter L k ∈ MulAction.stabilizer G v)
    (hB : ∀ k, Odd k → letter L k ∈ MulAction.stabilizer G w) (k : ℕ) :
    letter L k • sv v w k = sv v w k := by
  by_cases h : Even k
  · rw [sv_even v w h]
    exact MulAction.mem_stabilizer_iff.mp (hA k h)
  · rw [sv_odd v w (Nat.not_even_iff_odd.mp h)]
    exact MulAction.mem_stabilizer_iff.mp (hB k (Nat.not_even_iff_odd.mp h))

/-- The source of the `(k+1)`-st edge is the `k`-th vertex of the zig-zag. -/
lemma arrow_left (v w : V) (e : v ⟶ w) (L : List G)
    (hA : ∀ k, Even k → letter L k ∈ MulAction.stabilizer G v)
    (hB : ∀ k, Odd k → letter L k ∈ MulAction.stabilizer G w) (k : ℕ) :
    (edge v w e L (k + 1)).left = zz v w L k := by
  rw [edge_left v w e L k, zz_eq v w L k, pre_succ, mul_smul, letter_sv v w L hA hB k]

/-- The target of the `(k+1)`-st edge is the `(k+1)`-st vertex of the zig-zag. -/
lemma arrow_right (v w : V) (e : v ⟶ w) (L : List G)
    (hA : ∀ k, Even k → letter L k ∈ MulAction.stabilizer G v)
    (hB : ∀ k, Odd k → letter L k ∈ MulAction.stabilizer G w) (k : ℕ) :
    (edge v w e L (k + 1)).right = zz v w L (k + 1) := by
  rw [edge_right v w e L k, zz_eq v w L (k + 1)]

/-- The `k`-th arrow of the zig-zag walk, from the `k`-th vertex to the `(k+1)`-st. -/
noncomputable def arrow (v w : V) (e : v ⟶ w) (L : List G)
    (hA : ∀ k, Even k → letter L k ∈ MulAction.stabilizer G v)
    (hB : ∀ k, Odd k → letter L k ∈ MulAction.stabilizer G w) (k : ℕ) :
    zz v w L k ⟶ zz v w L (k + 1) :=
  Quiver.homOfEq (edge v w e L (k + 1)).hom (arrow_left v w e L hA hB k)
    (arrow_right v w e L hA hB k)

/-- The total arrow of the `k`-th arrow is the `(k+1)`-st edge. -/
lemma total_arrow (v w : V) (e : v ⟶ w) (L : List G)
    (hA : ∀ k, Even k → letter L k ∈ MulAction.stabilizer G v)
    (hB : ∀ k, Odd k → letter L k ∈ MulAction.stabilizer G w) (k : ℕ) :
    Quiver.Total.mk (zz v w L k) (zz v w L (k + 1)) (arrow v w e L hA hB k) =
      edge v w e L (k + 1) := by
  refine Quiver.Total.ext (arrow_left v w e L hA hB k).symm
    (arrow_right v w e L hA hB k).symm ?_
  exact Quiver.homOfEq_heq (arrow_left v w e L hA hB k)
    (arrow_right v w e L hA hB k) (edge v w e L (k + 1)).hom

/-- Consecutive edges of the zig-zag walk are not mutually inverse, provided no letter lies in
the stabiliser of the base edge. -/
lemma edge_succ_ne (v w : V) (e : v ⟶ w) (L : List G)
    (hC : ∀ k, k < L.length → letter L k ∉ MulAction.stabilizer G (ez v w e)) {k : ℕ}
    (hk : k < L.length) : edge v w e L (k + 1) ≠ (edge v w e L k).reverse := by
  intro hcon
  refine hC k hk ?_
  by_cases hpar : Even k
  · have h1 : edge v w e L (k + 1) = pre L (k + 1) • ez v w e :=
      edge_odd v w e L (k := k + 1) (odd_succ hpar)
    have h2 : (edge v w e L k).reverse = pre L k • ez v w e := by
      rw [edge_even v w e L hpar, Quiver.Total.reverse_reverse]
    have h3 : pre L (k + 1) • ez v w e = pre L k • ez v w e := by rw [← h1, hcon, h2]
    have h4 := (smul_eq_smul_stabilizer (ez v w e) (pre L (k + 1)) (pre L k)).mp h3
    rwa [pre_succ, ← mul_assoc, inv_mul_cancel, one_mul] at h4
  · have hodd : Odd k := Nat.not_even_iff_odd.mp hpar
    have h1 : edge v w e L (k + 1) = (pre L (k + 1) • ez v w e).reverse :=
      edge_even v w e L (k := k + 1) (even_succ hodd)
    have h2 : (edge v w e L k).reverse = (pre L k • ez v w e).reverse := by
      rw [edge_odd v w e L hodd]
    have h3 : (pre L (k + 1) • ez v w e).reverse = (pre L k • ez v w e).reverse := by
      rw [← h1, hcon, h2]
    have h4 : pre L (k + 1) • ez v w e = pre L k • ez v w e := by
      have := congrArg Quiver.Total.reverse h3
      simpa [Quiver.Total.reverse_reverse] using this
    have h5 := (smul_eq_smul_stabilizer (ez v w e) (pre L (k + 1)) (pre L k)).mp h4
    rwa [pre_succ, ← mul_assoc, inv_mul_cancel, one_mul] at h5

/-- The zig-zag path: the path from `v` through the vertices `zz 1, zz 2, …`. -/
noncomputable def zpath (v w : V) (e : v ⟶ w) (L : List G)
    (hA : ∀ k, Even k → letter L k ∈ MulAction.stabilizer G v)
    (hB : ∀ k, Odd k → letter L k ∈ MulAction.stabilizer G w) :
    (k : ℕ) → Quiver.Path v (zz v w L k)
  | 0 => Quiver.Path.nil
  | k + 1 => (zpath v w e L hA hB k).cons (arrow v w e L hA hB k)

lemma zpath_succ (v w : V) (e : v ⟶ w) (L : List G)
    (hA : ∀ k, Even k → letter L k ∈ MulAction.stabilizer G v)
    (hB : ∀ k, Odd k → letter L k ∈ MulAction.stabilizer G w) (k : ℕ) :
    zpath v w e L hA hB (k + 1) = (zpath v w e L hA hB k).cons (arrow v w e L hA hB k) := rfl

lemma zpath_length (v w : V) (e : v ⟶ w) (L : List G)
    (hA : ∀ k, Even k → letter L k ∈ MulAction.stabilizer G v)
    (hB : ∀ k, Odd k → letter L k ∈ MulAction.stabilizer G w) :
    ∀ k, (zpath v w e L hA hB k).length = k
  | 0 => rfl
  | k + 1 => by
    rw [zpath_succ, Quiver.Path.length_cons, zpath_length v w e L hA hB k]

/-- **The zig-zag path is reduced**: if no letter of the word lies in the stabiliser of the base
edge, the walk through the translates of that edge is a reduced path of the graph. -/
theorem zpath_reduced (v w : V) (e : v ⟶ w) (L : List G)
    (hA : ∀ k, Even k → letter L k ∈ MulAction.stabilizer G v)
    (hB : ∀ k, Odd k → letter L k ∈ MulAction.stabilizer G w)
    (hC : ∀ k, k < L.length → letter L k ∉ MulAction.stabilizer G (ez v w e)) :
    ∀ k ≤ L.length, (zpath v w e L hA hB k).IsReduced ∧
      LastArrow (zpath v w e L hA hB k) (edge v w e L k) := by
  intro k
  induction k with
  | zero =>
    intro _
    exact ⟨Quiver.Path.IsReduced.nil v,
      fun u q f hq => absurd hq (Quiver.Path.nil_ne_cons q f)⟩
  | succ k ih =>
    intro hk
    have hk' : k ≤ L.length := Nat.le_of_succ_le hk
    have hklt : k < L.length := hk
    obtain ⟨hred, hlast⟩ := ih hk'
    refine ⟨?_, ?_⟩
    · rw [zpath_succ]
      refine (Work.ORBassSerre.Tree.Reduction.isReduced_cons_iff (zpath v w e L hA hB k) (arrow v w e L hA hB k)).mpr
        ⟨hred, ?_⟩
      rintro p' e' hpe he'
      have h1 : Quiver.Total.mk (zz v w L (k + 1)) (zz v w L k) e' = edge v w e L k :=
        hlast (zz v w L (k + 1)) p' e' hpe
      have h2 : edge v w e L (k + 1) = (edge v w e L k).reverse := by
        rw [← total_arrow v w e L hA hB k, he', ← Quiver.Total.reverse_mk e', ← h1]
      exact edge_succ_ne v w e L hC hklt h2
    · intro u q f hq
      have hq' : (zpath v w e L hA hB k).cons (arrow v w e L hA hB k) = q.cons f :=
        (zpath_succ v w e L hA hB k).symm.trans hq
      rw [← total_arrow v w e L hA hB k]
      exact total_mk_of_heq (Quiver.Path.obj_eq_of_cons_eq_cons hq')
        (Quiver.Path.hom_heq_of_cons_eq_cons hq')

end Zigzag

end AmalgamZigzag

end Work.ORBassSerre.Action.Structure
