/-
  WilG4c — vocabulary for `Work.WilG4c.StepFiberEnds` (BNZ §2.3, "fibre ends").

  Fix a set `Z ⊆ ℝ^{p+1}`, read with the last coordinate `x` distinguished: a point is
  `Fin.snoc l x` with `l : Fin p → ℝ` the parameter and `x` the fibre coordinate.  The fibre
  over `l` is `fibre p Z l = {x | Fin.snoc l x ∈ Z}`.  This file builds, for each `Z`, the two
  sets `A_lo p Z, A_hi p Z ⊆ ℝ^{p+1}` whose graphs are the pointwise infimum and supremum of
  the fibre.

  The *bad* sets first (`∃`-conditions, realised by a projection of a pullback intersected with
  a coordinate comparison, then complemented):

  * `NE1 p Z` : `(l,y) ↦ ∃x ∈ Z_l` (the fibre is nonempty; independent of `y`);
  * `LBb p Z` : `∃x ∈ Z_l, x < y`   (so `LB1 = LBbᶜ` says `y` is a lower bound of `Z_l`);
  * `UBb p Z` : `∃x ∈ Z_l, y < x`   (so `UB1 = UBbᶜ` says `y` is an upper bound);
  * `GLBb p Z`: `∃u > y`, `u` a lower bound of `Z_l` (so `GLB1 = GLBbᶜ` says no larger `u`
                is a lower bound, i.e. together with `LB1` that `y` is the *greatest* lower
                bound);
  * `LUBb p Z`: `∃u < y`, `u` an upper bound of `Z_l` (dual of `GLBb`);
  * `yZero p`  : the coordinate `y` is `0` (the fallback value on the empty fibre).

  Then `A_lo p Z = (NE1 ∩ LB1 ∩ GLB1) ∪ (NE1ᶜ ∩ yZero)`,
  `A_hi p Z = (NE1 ∩ UB1 ∩ LUB1) ∪ (NE1ᶜ ∩ yZero)`, and (proved in the modules above this one)
  `A_lo p Z = graphOf (loOf p Z)` resp. `A_hi p Z = graphOf (hiOf p Z)`.  The companion lemmas
  `mem_A_lo_snoc` and `mem_A_hi_snoc` give the defining first-order conditions, and
  `A_lo_mem`/`A_hi_mem` (in the sibling modules) give the `Ω`-membership.

  The two pullbacks `pull2`/`pull3` are the substitution atoms of the `Ω`-calculus (along the
  coordinate embeddings `iota1`, `iota2`), and all the comparisons `<` are `SOMin`-definable
  (`midLtLast` etc.).  Each set above is therefore `Ω`-definable with a format depending only
  on `p, F0` and a degree affine in `D`; collecting them costs a bounded number of operations.

  Conventions used throughout:
  * `ℝ^{p+2}` is read as `(l, y, t)` or as `(l, y, u)`: coordinates `0,…,p-1` are `l`,
    coordinate `p` is the middle one (either `y` or `u`) and the last coordinate is `t`;
  * `ℝ^{p+3}` is read as `(l, y, u, t)` with coordinates `p, p+1, p+2` in that order.
-/
import Mathlib
import Submission.Work.WilG0.Subst
import Submission.Work.WilG1.Calc.lt_mem

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilG4c

open WilkiesDesign

/-! ## 0. The two point constructors

`Fin.snoc` is the *dependent* tuple constructor, so nesting it leaves the codomain family
undetermined and the term needs a type ascription.  All the lemmas below are phrased through
these two abbreviations. -/

/-- The point `(l, y, t)` of `ℝ^{p+2}`. -/
def pt2 (p : ℕ) (l : Fin p → ℝ) (y t : ℝ) : Fin (p + 2) → ℝ :=
  (Fin.snoc (Fin.snoc (l : Fin p → ℝ) y : Fin (p + 1) → ℝ) t : Fin (p + 2) → ℝ)

/-- The point `(l, y, u, t)` of `ℝ^{p+3}`. -/
def pt3 (p : ℕ) (l : Fin p → ℝ) (y u t : ℝ) : Fin (p + 3) → ℝ :=
  (Fin.snoc (Fin.snoc (Fin.snoc (l : Fin p → ℝ) y : Fin (p + 1) → ℝ) u : Fin (p + 2) → ℝ) t :
    Fin (p + 3) → ℝ)

/-- `pt2` is the nested `Fin.snoc`. -/
theorem pt2_eq (p : ℕ) (l : Fin p → ℝ) (y t : ℝ) :
    pt2 p l y t = (Fin.snoc (Fin.snoc l y) t : Fin (p + 2) → ℝ) := rfl

/-- `pt3` is the nested `Fin.snoc`. -/
theorem pt3_eq (p : ℕ) (l : Fin p → ℝ) (y u t : ℝ) :
    pt3 p l y u t = (Fin.snoc (Fin.snoc (Fin.snoc l y) u) t : Fin (p + 3) → ℝ) := rfl

/-! ## 1. Coordinate embeddings -/

/-- The embedding recording where the coordinates of `Z` sit inside `ℝ^{p+2}` read as
`(l, y, t)`: the `l`-coordinates keep their position, the distinguished fibre coordinate goes
to the last coordinate. -/
def iota1 (p : ℕ) : Fin (p + 1) → Fin (p + 2) :=
  Fin.snoc (fun j : Fin p => Fin.castSucc (Fin.castSucc j)) (Fin.last (p + 1))

/-- The same embedding into `ℝ^{p+3}` read as `(l, y, u, t)`. -/
def iota2 (p : ℕ) : Fin (p + 1) → Fin (p + 3) :=
  Fin.snoc (fun j : Fin p => Fin.castSucc (Fin.castSucc (Fin.castSucc j)))
    (Fin.last (p + 2))

/-- Reading off `iota1`: the coordinates of `w : ℝ^{p+2}` at the positions of `Z` are
`(l, w (last))`. -/
theorem comp_iota1 (p : ℕ) (w : Fin (p + 2) → ℝ) :
    (fun i : Fin (p + 1) => w (iota1 p i)) =
      Fin.snoc (Fin.init (Fin.init w)) (w (Fin.last (p + 1))) := by
  funext i
  rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
  · simp only [iota1, Fin.snoc_castSucc]
    rfl
  · simp only [iota1, Fin.snoc_last]

/-- Reading off `iota2`. -/
theorem comp_iota2 (p : ℕ) (v : Fin (p + 3) → ℝ) :
    (fun i : Fin (p + 1) => v (iota2 p i)) =
      Fin.snoc (Fin.init (Fin.init (Fin.init v))) (v (Fin.last (p + 2))) := by
  funext i
  rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
  · simp only [iota2, Fin.snoc_castSucc]
    rfl
  · simp only [iota2, Fin.snoc_last]

/-! ## 2. The fibre and the two pullbacks -/

/-- The fibre of `Z ⊆ ℝ^{p+1}` over the parameter `l`. -/
def fibre (p : ℕ) (Z : Set (Fin (p + 1) → ℝ)) (l : Fin p → ℝ) : Set ℝ :=
  {x | Fin.snoc l x ∈ Z}

/-- `Z` pulled back to `ℝ^{p+2}` read as `(l, y, t)`: `(l,t) ∈ Z`, with `y` free. -/
def pull2 (p : ℕ) (Z : Set (Fin (p + 1) → ℝ)) : Set (Fin (p + 2) → ℝ) :=
  {w | w ∘ iota1 p ∈ Z}

/-- `Z` pulled back to `ℝ^{p+3}` read as `(l, y, u, t)`: `(l,t) ∈ Z`, with `y, u` free. -/
def pull3 (p : ℕ) (Z : Set (Fin (p + 1) → ℝ)) : Set (Fin (p + 3) → ℝ) :=
  {w | w ∘ iota2 p ∈ Z}

/-! ## 3. Coordinate comparisons -/

/-- In `ℝ^{p+2}` read as `(l, y, t)` (or `(l, y, u)`): the middle coordinate is less than the
last one, i.e. `y < t` (resp. `y < u`). -/
def midLtLast (p : ℕ) : Set (Fin (p + 2) → ℝ) :=
  {w | w (Fin.castSucc (Fin.last p)) < w (Fin.last (p + 1))}

/-- In `ℝ^{p+2}`: the last coordinate is less than the middle one, i.e. `t < y` (resp.
`u < y`). -/
def lastLtMid (p : ℕ) : Set (Fin (p + 2) → ℝ) :=
  {w | w (Fin.last (p + 1)) < w (Fin.castSucc (Fin.last p))}

/-- In `ℝ^{p+3}` read as `(l, y, u, t)`: `t < u`. -/
def lastLtMid3 (p : ℕ) : Set (Fin (p + 3) → ℝ) :=
  {w | w (Fin.last (p + 2)) < w (Fin.castSucc (Fin.last (p + 1)))}

/-- In `ℝ^{p+3}`: `u < t`. -/
def midLtLast3 (p : ℕ) : Set (Fin (p + 3) → ℝ) :=
  {w | w (Fin.castSucc (Fin.last (p + 1))) < w (Fin.last (p + 2))}

/-- The hyperplane `y = 0` in `ℝ^{p+1}` (the fallback value of the fibre ends on an empty
fibre). -/
def yZero (p : ℕ) : Set (Fin (p + 1) → ℝ) :=
  {z | z (Fin.last p) = 0}

/-! ## 4. The fibre-end sets -/

/-- `(l,y)`: the fibre over `l` is nonempty (independent of `y`). -/
def NE1 (p : ℕ) (Z : Set (Fin (p + 1) → ℝ)) : Set (Fin (p + 1) → ℝ) :=
  projLast (pull2 p Z)

/-- `(l,y)`: some `x ∈ Z_l` lies below `y`, i.e. `y` is *not* a lower bound of the fibre. -/
def LBb (p : ℕ) (Z : Set (Fin (p + 1) → ℝ)) : Set (Fin (p + 1) → ℝ) :=
  projLast (pull2 p Z ∩ lastLtMid p)

/-- `(l,y)`: `y` is a lower bound of the fibre over `l`. -/
def LB1 (p : ℕ) (Z : Set (Fin (p + 1) → ℝ)) : Set (Fin (p + 1) → ℝ) :=
  (LBb p Z)ᶜ

/-- `(l,y)`: some `x ∈ Z_l` lies above `y`, i.e. `y` is *not* an upper bound of the fibre. -/
def UBb (p : ℕ) (Z : Set (Fin (p + 1) → ℝ)) : Set (Fin (p + 1) → ℝ) :=
  projLast (pull2 p Z ∩ midLtLast p)

/-- `(l,y)`: `y` is an upper bound of the fibre over `l`. -/
def UB1 (p : ℕ) (Z : Set (Fin (p + 1) → ℝ)) : Set (Fin (p + 1) → ℝ) :=
  (UBb p Z)ᶜ

/-- `(l,y)`: some `u > y` is a lower bound of the fibre over `l` (so `y` fails to be the
greatest lower bound). -/
def GLBb (p : ℕ) (Z : Set (Fin (p + 1) → ℝ)) : Set (Fin (p + 1) → ℝ) :=
  projLast ((projLast (pull3 p Z ∩ lastLtMid3 p))ᶜ ∩ midLtLast p)

/-- `(l,y)`: no `u > y` is a lower bound of the fibre over `l`; together with `LB1` this says
that `y` is the greatest lower bound. -/
def GLB1 (p : ℕ) (Z : Set (Fin (p + 1) → ℝ)) : Set (Fin (p + 1) → ℝ) :=
  (GLBb p Z)ᶜ

/-- `(l,y)`: some `u < y` is an upper bound of the fibre over `l` (so `y` fails to be the
least upper bound). -/
def LUBb (p : ℕ) (Z : Set (Fin (p + 1) → ℝ)) : Set (Fin (p + 1) → ℝ) :=
  projLast ((projLast (pull3 p Z ∩ midLtLast3 p))ᶜ ∩ lastLtMid p)

/-- `(l,y)`: no `u < y` is an upper bound of the fibre over `l`; together with `UB1` this says
that `y` is the least upper bound. -/
def LUB1 (p : ℕ) (Z : Set (Fin (p + 1) → ℝ)) : Set (Fin (p + 1) → ℝ) :=
  (LUBb p Z)ᶜ

/-- The graph of `l ↦ inf Z_l`, with the value `0` on empty fibres. -/
def A_lo (p : ℕ) (Z : Set (Fin (p + 1) → ℝ)) : Set (Fin (p + 1) → ℝ) :=
  (NE1 p Z ∩ LB1 p Z ∩ GLB1 p Z) ∪ ((NE1 p Z)ᶜ ∩ yZero p)

/-- The graph of `l ↦ sup Z_l`, with the value `0` on empty fibres. -/
def A_hi (p : ℕ) (Z : Set (Fin (p + 1) → ℝ)) : Set (Fin (p + 1) → ℝ) :=
  (NE1 p Z ∩ UB1 p Z ∩ LUB1 p Z) ∪ ((NE1 p Z)ᶜ ∩ yZero p)

/-! ## 5. The two ends as functions -/

/-- The pointwise infimum of the fibre `Z_l`, and `0` on an empty fibre. -/
def loOf (p : ℕ) (Z : Set (Fin (p + 1) → ℝ)) (l : Fin p → ℝ) : ℝ :=
  if (fibre p Z l).Nonempty then sInf (fibre p Z l) else 0

/-- The pointwise supremum of the fibre `Z_l`, and `0` on an empty fibre. -/
def hiOf (p : ℕ) (Z : Set (Fin (p + 1) → ℝ)) (l : Fin p → ℝ) : ℝ :=
  if (fibre p Z l).Nonempty then sSup (fibre p Z l) else 0

/-! ## 6. Membership of `Fin.snoc` in the basic sets -/

/-- Membership in the fibre, unfolded. -/
theorem mem_fibre (p : ℕ) (Z : Set (Fin (p + 1) → ℝ)) (l : Fin p → ℝ) (x : ℝ) :
    x ∈ fibre p Z l ↔ Fin.snoc l x ∈ Z := Iff.rfl

/-- Membership in `projLast`, unfolded. -/
theorem mem_projLast (p : ℕ) (A : Set (Fin (p + 2) → ℝ)) (z : Fin (p + 1) → ℝ) :
    z ∈ projLast A ↔ ∃ t : ℝ, Fin.snoc z t ∈ A := Iff.rfl

theorem mem_pull2_snoc (p : ℕ) (Z : Set (Fin (p + 1) → ℝ)) (l : Fin p → ℝ) (y t : ℝ) :
    Fin.snoc (Fin.snoc l y) t ∈ pull2 p Z ↔ Fin.snoc l t ∈ Z := by
  show (fun i : Fin (p + 1) => pt2 p l y t (iota1 p i)) ∈ Z ↔ Fin.snoc l t ∈ Z
  rw [comp_iota1 p (pt2 p l y t)]
  simp only [pt2, Fin.init_snoc, Fin.snoc_last]

theorem mem_pull3_snoc (p : ℕ) (Z : Set (Fin (p + 1) → ℝ)) (l : Fin p → ℝ) (y u t : ℝ) :
    Fin.snoc (Fin.snoc (Fin.snoc l y) u) t ∈ pull3 p Z ↔ Fin.snoc l t ∈ Z := by
  show (fun i : Fin (p + 1) => pt3 p l y u t (iota2 p i)) ∈ Z ↔ Fin.snoc l t ∈ Z
  rw [comp_iota2 p (pt3 p l y u t)]
  simp only [pt3, Fin.init_snoc, Fin.snoc_last]

theorem mem_midLtLast (p : ℕ) (l : Fin p → ℝ) (y t : ℝ) :
    Fin.snoc (Fin.snoc l y) t ∈ midLtLast p ↔ y < t := by
  simp [midLtLast, pt2]

theorem mem_lastLtMid (p : ℕ) (l : Fin p → ℝ) (y t : ℝ) :
    Fin.snoc (Fin.snoc l y) t ∈ lastLtMid p ↔ t < y := by
  simp [lastLtMid, pt2]

theorem mem_lastLtMid3 (p : ℕ) (l : Fin p → ℝ) (y u t : ℝ) :
    Fin.snoc (Fin.snoc (Fin.snoc l y) u) t ∈ lastLtMid3 p ↔ t < u := by
  simp [lastLtMid3, pt3]

theorem mem_midLtLast3 (p : ℕ) (l : Fin p → ℝ) (y u t : ℝ) :
    Fin.snoc (Fin.snoc (Fin.snoc l y) u) t ∈ midLtLast3 p ↔ u < t := by
  simp [midLtLast3, pt3]

theorem mem_yZero (p : ℕ) (l : Fin p → ℝ) (y : ℝ) :
    Fin.snoc l y ∈ yZero p ↔ y = 0 := by
  simp [yZero]

/-- Membership of `Fin.snoc l y` in `NE1`: the fibre over `l` is nonempty. -/
theorem mem_NE1_snoc (p : ℕ) (Z : Set (Fin (p + 1) → ℝ)) (l : Fin p → ℝ) (y : ℝ) :
    Fin.snoc l y ∈ NE1 p Z ↔ (fibre p Z l).Nonempty := by
  show (∃ t : ℝ, Fin.snoc (Fin.snoc l y) t ∈ pull2 p Z) ↔ (fibre p Z l).Nonempty
  constructor
  · rintro ⟨t, ht⟩
    exact ⟨t, (mem_pull2_snoc p Z l y t).mp ht⟩
  · rintro ⟨t, ht⟩
    exact ⟨t, (mem_pull2_snoc p Z l y t).mpr ht⟩

/-- Membership in `LBb`: some element of the fibre lies below `y`. -/
theorem mem_LBb_snoc (p : ℕ) (Z : Set (Fin (p + 1) → ℝ)) (l : Fin p → ℝ) (y : ℝ) :
    Fin.snoc l y ∈ LBb p Z ↔ ∃ t : ℝ, Fin.snoc l t ∈ Z ∧ t < y := by
  show (∃ t : ℝ, Fin.snoc (Fin.snoc l y) t ∈ pull2 p Z ∧
      Fin.snoc (Fin.snoc l y) t ∈ lastLtMid p) ↔ ∃ t : ℝ, Fin.snoc l t ∈ Z ∧ t < y
  simp only [mem_pull2_snoc, mem_lastLtMid]

/-- Membership in `UBb`: some element of the fibre lies above `y`. -/
theorem mem_UBb_snoc (p : ℕ) (Z : Set (Fin (p + 1) → ℝ)) (l : Fin p → ℝ) (y : ℝ) :
    Fin.snoc l y ∈ UBb p Z ↔ ∃ t : ℝ, Fin.snoc l t ∈ Z ∧ y < t := by
  show (∃ t : ℝ, Fin.snoc (Fin.snoc l y) t ∈ pull2 p Z ∧
      Fin.snoc (Fin.snoc l y) t ∈ midLtLast p) ↔ ∃ t : ℝ, Fin.snoc l t ∈ Z ∧ y < t
  simp only [mem_pull2_snoc, mem_midLtLast]

/-- Membership in `GLBb`: some `u > y` is a lower bound of the fibre. -/
theorem mem_GLBb_snoc (p : ℕ) (Z : Set (Fin (p + 1) → ℝ)) (l : Fin p → ℝ) (y : ℝ) :
    Fin.snoc l y ∈ GLBb p Z ↔
      ∃ u : ℝ, (∀ t : ℝ, Fin.snoc l t ∈ Z → u ≤ t) ∧ y < u := by
  show (∃ u : ℝ, ¬(∃ t : ℝ, Fin.snoc (Fin.snoc (Fin.snoc l y) u) t ∈ pull3 p Z ∧
      Fin.snoc (Fin.snoc (Fin.snoc l y) u) t ∈ lastLtMid3 p) ∧
      Fin.snoc (Fin.snoc l y) u ∈ midLtLast p) ↔
    ∃ u : ℝ, (∀ t : ℝ, Fin.snoc l t ∈ Z → u ≤ t) ∧ y < u
  simp only [mem_pull3_snoc, mem_lastLtMid3, mem_midLtLast, not_exists, not_and, not_lt]

/-- Membership in `LUBb`: some `u < y` is an upper bound of the fibre. -/
theorem mem_LUBb_snoc (p : ℕ) (Z : Set (Fin (p + 1) → ℝ)) (l : Fin p → ℝ) (y : ℝ) :
    Fin.snoc l y ∈ LUBb p Z ↔
      ∃ u : ℝ, (∀ t : ℝ, Fin.snoc l t ∈ Z → t ≤ u) ∧ u < y := by
  show (∃ u : ℝ, ¬(∃ t : ℝ, Fin.snoc (Fin.snoc (Fin.snoc l y) u) t ∈ pull3 p Z ∧
      Fin.snoc (Fin.snoc (Fin.snoc l y) u) t ∈ midLtLast3 p) ∧
      Fin.snoc (Fin.snoc l y) u ∈ lastLtMid p) ↔
    ∃ u : ℝ, (∀ t : ℝ, Fin.snoc l t ∈ Z → t ≤ u) ∧ u < y
  simp only [mem_pull3_snoc, mem_midLtLast3, mem_lastLtMid, not_exists, not_and, not_lt]

/-- Membership in `LB1`: `y` is a lower bound of the fibre. -/
theorem mem_LB1_snoc (p : ℕ) (Z : Set (Fin (p + 1) → ℝ)) (l : Fin p → ℝ) (y : ℝ) :
    Fin.snoc l y ∈ LB1 p Z ↔ ∀ t : ℝ, Fin.snoc l t ∈ Z → y ≤ t := by
  show ¬(Fin.snoc l y ∈ LBb p Z) ↔ ∀ t : ℝ, Fin.snoc l t ∈ Z → y ≤ t
  rw [mem_LBb_snoc]
  simp only [not_exists, not_and, not_lt]

/-- Membership in `UB1`: `y` is an upper bound of the fibre. -/
theorem mem_UB1_snoc (p : ℕ) (Z : Set (Fin (p + 1) → ℝ)) (l : Fin p → ℝ) (y : ℝ) :
    Fin.snoc l y ∈ UB1 p Z ↔ ∀ t : ℝ, Fin.snoc l t ∈ Z → t ≤ y := by
  show ¬(Fin.snoc l y ∈ UBb p Z) ↔ ∀ t : ℝ, Fin.snoc l t ∈ Z → t ≤ y
  rw [mem_UBb_snoc]
  simp only [not_exists, not_and, not_lt]

/-- Membership in `GLB1`: no `u > y` is a lower bound of the fibre. -/
theorem mem_GLB1_snoc (p : ℕ) (Z : Set (Fin (p + 1) → ℝ)) (l : Fin p → ℝ) (y : ℝ) :
    Fin.snoc l y ∈ GLB1 p Z ↔
      ∀ u : ℝ, (∀ t : ℝ, Fin.snoc l t ∈ Z → u ≤ t) → u ≤ y := by
  show ¬(Fin.snoc l y ∈ GLBb p Z) ↔
    ∀ u : ℝ, (∀ t : ℝ, Fin.snoc l t ∈ Z → u ≤ t) → u ≤ y
  rw [mem_GLBb_snoc]
  simp only [not_exists, not_and, not_lt]

/-- Membership in `LUB1`: no `u < y` is an upper bound of the fibre. -/
theorem mem_LUB1_snoc (p : ℕ) (Z : Set (Fin (p + 1) → ℝ)) (l : Fin p → ℝ) (y : ℝ) :
    Fin.snoc l y ∈ LUB1 p Z ↔
      ∀ u : ℝ, (∀ t : ℝ, Fin.snoc l t ∈ Z → t ≤ u) → y ≤ u := by
  show ¬(Fin.snoc l y ∈ LUBb p Z) ↔
    ∀ u : ℝ, (∀ t : ℝ, Fin.snoc l t ∈ Z → t ≤ u) → y ≤ u
  rw [mem_LUBb_snoc]
  simp only [not_exists, not_and, not_lt]

/-- The defining condition of `A_lo`. -/
theorem mem_A_lo_snoc (p : ℕ) (Z : Set (Fin (p + 1) → ℝ)) (l : Fin p → ℝ) (y : ℝ) :
    Fin.snoc l y ∈ A_lo p Z ↔
      ((fibre p Z l).Nonempty ∧
          (∀ t : ℝ, Fin.snoc l t ∈ Z → y ≤ t) ∧
          (∀ u : ℝ, (∀ t : ℝ, Fin.snoc l t ∈ Z → u ≤ t) → u ≤ y)) ∨
        (¬(fibre p Z l).Nonempty ∧ y = 0) := by
  rw [A_lo]
  simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_compl_iff, mem_NE1_snoc, mem_LB1_snoc,
    mem_GLB1_snoc, mem_yZero, and_assoc]

/-- The defining condition of `A_hi`. -/
theorem mem_A_hi_snoc (p : ℕ) (Z : Set (Fin (p + 1) → ℝ)) (l : Fin p → ℝ) (y : ℝ) :
    Fin.snoc l y ∈ A_hi p Z ↔
      ((fibre p Z l).Nonempty ∧
          (∀ t : ℝ, Fin.snoc l t ∈ Z → t ≤ y) ∧
          (∀ u : ℝ, (∀ t : ℝ, Fin.snoc l t ∈ Z → t ≤ u) → y ≤ u)) ∨
        (¬(fibre p Z l).Nonempty ∧ y = 0) := by
  rw [A_hi]
  simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_compl_iff, mem_NE1_snoc, mem_UB1_snoc,
    mem_LUB1_snoc, mem_yZero, and_assoc]

end Work.WilG4c
