/-
  WilG4a : `Work.WilG4a.NoStripDefs`.

  The `sInf`/`sSup` of a fibre carry no hypothesis at all: the fibre `Z_l = {x | (l,x) ∈ Z}`
  may be empty, and it may be unbounded below (resp. above).  On `ℝ` the convention is
  `sInf ∅ = 0` and `sInf s = 0` for a set that is not bounded below, so the graph of the
  pointwise infimum of the fibres is *not* `A_lo p Z` of `fiber_defs` (that description
  records only the case "fibre nonempty and bounded below").  The correct description is

    `graphOf (l ↦ inf Z_l) = (LB1 ∩ GLB1) ∪ ((NE1ᶜ ∪ unbBelow1) ∩ yZero1)`,

  where
  * `LB1`, `GLB1`, `NE1`, `yZero1` are the sets of `fiber_defs`
    (`LB1` = "`y` is a lower bound of the fibre", `GLB1` = "no smaller number is one",
    `NE1` = "the fibre is nonempty", `yZero1` = "the last coordinate is `0`"), and
  * `unbBelow1` = "the fibre is unbounded below", obtained from `LB1` by one projection and
    one complement:  `l` has *no* lower bound iff `(l,y) ∉ LB1` for every `y`.

  The three cases are:
  * fibre empty: `sInf = 0`, `LB1` holds (vacuously) and `GLB1` fails, `NE1ᶜ` holds;
  * fibre nonempty but not bounded below: `sInf = 0`, `LB1` fails and `GLB1` holds,
    `unbBelow1` holds;
  * fibre nonempty and bounded below: `LB1 ∩ GLB1` is exactly `{sInf}` and `unbBelow1` fails.

  The same statement holds with `UB1`, `LUB1`, `unbAbove1` for `sSup`, giving `A_hi_ns`.
-/
import Mathlib
import Submission.Work.WilG4a.fiber_defs
import Submission.Work.WilG4a.fiber_endpoints

set_option autoImplicit false
noncomputable section
open Classical
namespace Work.WilG4a

open WilkiesDesign WilkiesConjecture

/-! ## 1. The fibre conditions in `Fin.snoc` normal form -/

theorem mem_LB1' (p : ℕ) (Z : Set (Fin (p + 1) → ℝ)) (l : Fin p → ℝ) (y : ℝ) :
    Fin.snoc l y ∈ LB1 p Z ↔ ∀ x : ℝ, Fin.snoc l x ∈ Z → y ≤ x := by
  rw [mem_LB1]; simp only [Fin.init_snoc, Fin.snoc_last]

theorem mem_GLB1' (p : ℕ) (Z : Set (Fin (p + 1) → ℝ)) (l : Fin p → ℝ) (y : ℝ) :
    Fin.snoc l y ∈ GLB1 p Z ↔ ∀ u : ℝ, y < u → ∃ x : ℝ, Fin.snoc l x ∈ Z ∧ x < u := by
  rw [mem_GLB1]; simp only [Fin.init_snoc, Fin.snoc_last]

theorem mem_UB1' (p : ℕ) (Z : Set (Fin (p + 1) → ℝ)) (l : Fin p → ℝ) (y : ℝ) :
    Fin.snoc l y ∈ UB1 p Z ↔ ∀ x : ℝ, Fin.snoc l x ∈ Z → x ≤ y := by
  rw [mem_UB1]; simp only [Fin.init_snoc, Fin.snoc_last]

theorem mem_LUB1' (p : ℕ) (Z : Set (Fin (p + 1) → ℝ)) (l : Fin p → ℝ) (y : ℝ) :
    Fin.snoc l y ∈ LUB1 p Z ↔ ∀ u : ℝ, u < y → ∃ x : ℝ, Fin.snoc l x ∈ Z ∧ u < x := by
  rw [mem_LUB1]; simp only [Fin.init_snoc, Fin.snoc_last]

theorem mem_NE1' (p : ℕ) (Z : Set (Fin (p + 1) → ℝ)) (l : Fin p → ℝ) (y : ℝ) :
    Fin.snoc l y ∈ NE1 p Z ↔ ∃ x : ℝ, Fin.snoc l x ∈ Z := by
  rw [mem_NE1]; simp only [Fin.init_snoc]

theorem mem_yZero1' (p : ℕ) (l : Fin p → ℝ) (y : ℝ) :
    Fin.snoc l y ∈ yZero1 p ↔ y = 0 := by
  rw [mem_yZero1]; simp only [Fin.snoc_last]

/-! ## 2. Fibres unbounded below / above -/

/-- `z` sits over a parameter whose fibre is unbounded below: no `y` is a lower bound. -/
def unbBelow1 (p : ℕ) (Z : Set (Fin (p + 1) → ℝ)) : Set (Fin (p + 1) → ℝ) :=
  {z | Fin.init z ∈ (projLast (LB1 p Z))ᶜ}

/-- `z` sits over a parameter whose fibre is unbounded above: no `y` is an upper bound. -/
def unbAbove1 (p : ℕ) (Z : Set (Fin (p + 1) → ℝ)) : Set (Fin (p + 1) → ℝ) :=
  {z | Fin.init z ∈ (projLast (UB1 p Z))ᶜ}

theorem mem_unbBelow1 (p : ℕ) (Z : Set (Fin (p + 1) → ℝ)) (z : Fin (p + 1) → ℝ) :
    z ∈ unbBelow1 p Z ↔
      ∀ y : ℝ, ∃ x : ℝ, Fin.snoc (Fin.init z) x ∈ Z ∧ x < y := by
  simp only [unbBelow1, Set.mem_ofPred_eq, Set.mem_compl_iff, projLast, Set.mem_ofPred_eq,
    not_exists, mem_LB1']
  constructor
  · intro h y
    by_contra hcon
    push Not at hcon
    exact h y hcon
  · intro h y hcon
    obtain ⟨x, hx, hxy⟩ := h y
    exact absurd (hcon x hx) (not_le.mpr hxy)

theorem mem_unbAbove1 (p : ℕ) (Z : Set (Fin (p + 1) → ℝ)) (z : Fin (p + 1) → ℝ) :
    z ∈ unbAbove1 p Z ↔
      ∀ y : ℝ, ∃ x : ℝ, Fin.snoc (Fin.init z) x ∈ Z ∧ y < x := by
  simp only [unbAbove1, Set.mem_ofPred_eq, Set.mem_compl_iff, projLast, Set.mem_ofPred_eq,
    not_exists, mem_UB1']
  constructor
  · intro h y
    by_contra hcon
    push Not at hcon
    exact h y hcon
  · intro h y hcon
    obtain ⟨x, hx, hxy⟩ := h y
    exact absurd (hcon x hx) (not_le.mpr hxy)

/-! ## 3. The two graphs, with the empty/unbounded fibres taken into account -/

/-- The graph of `l ↦ sInf (Z_l)` (junk value `sInf s = 0` for empty or unbounded-below
fibres). -/
def A_lo_ns (p : ℕ) (Z : Set (Fin (p + 1) → ℝ)) : Set (Fin (p + 1) → ℝ) :=
  (LB1 p Z ∩ GLB1 p Z) ∪ (((NE1 p Z)ᶜ ∪ unbBelow1 p Z) ∩ yZero1 p)

/-- The graph of `l ↦ sSup (Z_l)` (junk value `sSup s = 0` for empty or unbounded-above
fibres). -/
def A_hi_ns (p : ℕ) (Z : Set (Fin (p + 1) → ℝ)) : Set (Fin (p + 1) → ℝ) :=
  (UB1 p Z ∩ LUB1 p Z) ∪ (((NE1 p Z)ᶜ ∪ unbAbove1 p Z) ∩ yZero1 p)

theorem mem_A_lo_ns (p : ℕ) (Z : Set (Fin (p + 1) → ℝ)) (z : Fin (p + 1) → ℝ) :
    z ∈ A_lo_ns p Z ↔
      (((∀ x : ℝ, Fin.snoc (Fin.init z) x ∈ Z → z (Fin.last p) ≤ x) ∧
          (∀ u : ℝ, z (Fin.last p) < u →
            ∃ x : ℝ, Fin.snoc (Fin.init z) x ∈ Z ∧ x < u))
        ∨ ((¬ (∃ x : ℝ, Fin.snoc (Fin.init z) x ∈ Z) ∨
              (∀ y : ℝ, ∃ x : ℝ, Fin.snoc (Fin.init z) x ∈ Z ∧ x < y)) ∧
            z (Fin.last p) = 0)) := by
  simp only [A_lo_ns, Set.mem_union, Set.mem_inter_iff, Set.mem_compl_iff, mem_NE1, mem_LB1,
    mem_GLB1, mem_yZero1, mem_unbBelow1]

theorem mem_A_hi_ns (p : ℕ) (Z : Set (Fin (p + 1) → ℝ)) (z : Fin (p + 1) → ℝ) :
    z ∈ A_hi_ns p Z ↔
      (((∀ x : ℝ, Fin.snoc (Fin.init z) x ∈ Z → x ≤ z (Fin.last p)) ∧
          (∀ u : ℝ, u < z (Fin.last p) →
            ∃ x : ℝ, Fin.snoc (Fin.init z) x ∈ Z ∧ u < x))
        ∨ ((¬ (∃ x : ℝ, Fin.snoc (Fin.init z) x ∈ Z) ∨
              (∀ y : ℝ, ∃ x : ℝ, Fin.snoc (Fin.init z) x ∈ Z ∧ y < x)) ∧
            z (Fin.last p) = 0)) := by
  simp only [A_hi_ns, Set.mem_union, Set.mem_inter_iff, Set.mem_compl_iff, mem_NE1, mem_UB1,
    mem_LUB1, mem_yZero1, mem_unbAbove1]

end Work.WilG4a
