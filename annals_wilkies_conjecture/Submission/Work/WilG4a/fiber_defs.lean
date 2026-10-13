/-
  WilG4a : definitional layer for `Work.WilG4a.fiber_endpoints`.

  Given a set `Z ⊆ ℝ^{p+1}` (coordinates `(l, y)` with `l : Fin p`), we build the two sets
  whose graphs are the pointwise infimum and supremum of the fibre `{y | (l,y) ∈ Z}` over `l`.
  The infimum is characterised, entirely in first-order terms, by

    `y = inf Z_l  ↔  (∀ t ∈ Z_l, y ≤ t) ∧ (∀ u > y, ∃ t ∈ Z_l, t < u)`,

  i.e. `y` is a lower bound and no larger number is one.  Each of the two conjuncts is a
  first-order condition involving at most two quantifiers, and `SOMin.Ω` is closed under
  projections, complements, products and hypersurfaces, so both are `Ω`-definable with a
  format independent of the degree `D` and a degree polynomial in `D`; the union over the
  (one) case distinction `fibre ≠ ∅` / `fibre = ∅` is `Ω`-definable as well.

  The ambient spaces are chosen so that the auxiliary coordinates sit at the end:
  * `z : Fin (p+1) → ℝ` carries `(l, y)` (`l = Fin.init z`, `y = z (Fin.last p)`);
  * `w : Fin (p+2) → ℝ` carries `(l, y, t)`;
  * `v : Fin (p+3) → ℝ` carries `(l, y, u, t)`.

  `iota1`/`iota2` select the coordinates `(l, t)` of the bigger ambient, i.e. they express
  "`(l,t) ∈ Z`".
-/
import Mathlib
import Submission.Work.WilG5.Basic

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilG4a

open WilkiesDesign WilkiesConjecture

/-- The embedding `Fin (p+1) → Fin (p+2)` sending `i < p` to the coordinate `i` and the last
coordinate `p` to the last coordinate `p+1` (so the coordinate `p` is `y`). -/
def iota1 (p : ℕ) : Fin (p + 1) → Fin (p + 2) :=
  Fin.snoc (fun j : Fin p => (Fin.castSucc (Fin.castSucc j))) (Fin.last (p + 1))

/-- The embedding `Fin (p+1) → Fin (p+3)` sending `i < p` to the coordinate `i` and the last
coordinate `p` to the last coordinate `p+2` (so the coordinates `p`, `p+1` are `y` and `u`). -/
def iota2 (p : ℕ) : Fin (p + 1) → Fin (p + 3) :=
  Fin.snoc (fun j : Fin p => (Fin.castSucc (Fin.castSucc (Fin.castSucc j)))) (Fin.last (p + 2))

/-- `pullZ2 p Z` is the balanced reindexing of `liftFirst 1 Z` along this function:
`pullZ2 p Z = {x | x ∘ sigma1 p ∈ liftFirst 1 Z}` (only the values of `sigma1` on the first
`p+1` coordinates matter). -/
def sigma1 (p : ℕ) : Fin (p + 2) → Fin (p + 2) :=
  Fin.snoc (iota1 p) (Fin.last (p + 1))

/-- The analogue of `sigma1` one dimension up: `pullZ3 p Z = {x | x ∘ sigma2 p ∈ liftFirst 2 Z}`. -/
def sigma2 (p : ℕ) : Fin (p + 3) → Fin (p + 3) :=
  Fin.snoc (Fin.snoc (iota2 p) (Fin.last (p + 2))) (Fin.last (p + 2))

/-- The values of `iota1` are read off by `Fin.snoc`/`Fin.init`. -/
theorem comp_iota1 (p : ℕ) (w : Fin (p + 2) → ℝ) :
    (fun i : Fin (p + 1) => w (iota1 p i)) =
      Fin.snoc (Fin.init (Fin.init w)) (w (Fin.last (p + 1))) := by
  funext i
  rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
  · simp only [iota1, Fin.snoc_castSucc]
    rfl
  · simp only [iota1, Fin.snoc_last]

/-- The values of `iota2` are read off by `Fin.snoc`/`Fin.init`. -/
theorem comp_iota2 (p : ℕ) (v : Fin (p + 3) → ℝ) :
    (fun i : Fin (p + 1) => v (iota2 p i)) =
      Fin.snoc (Fin.init (Fin.init (Fin.init v))) (v (Fin.last (p + 2))) := by
  funext i
  rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
  · simp only [iota2, Fin.snoc_castSucc]
    rfl
  · simp only [iota2, Fin.snoc_last]

/-- `{w : (l,y,t) | t < y}`. -/
def tLtY (p : ℕ) : Set (Fin (p + 2) → ℝ) :=
  {w | w (Fin.last (p + 1)) < w (Fin.castSucc (Fin.last p))}

/-- `{w : (l,y,t) | y < t}` (also read as `y < u` in the `(l,y,u)` ambient). -/
def yLtT (p : ℕ) : Set (Fin (p + 2) → ℝ) :=
  {w | w (Fin.castSucc (Fin.last p)) < w (Fin.last (p + 1))}

/-- `{v : (l,y,u,t) | t < u}`. -/
def tLtU (p : ℕ) : Set (Fin (p + 3) → ℝ) :=
  {v | v (Fin.last (p + 2)) < v (Fin.castSucc (Fin.last (p + 1)))}

/-- `{v : (l,y,u,t) | u < t}`. -/
def uLtT (p : ℕ) : Set (Fin (p + 3) → ℝ) :=
  {v | v (Fin.castSucc (Fin.last (p + 1))) < v (Fin.last (p + 2))}

/-- The pullback of `Z` to the `(l,y,t)` ambient along `(l,t)`. -/
def pullZ2 (p : ℕ) (Z : Set (Fin (p + 1) → ℝ)) : Set (Fin (p + 2) → ℝ) :=
  {w | (fun i : Fin (p + 1) => w (iota1 p i)) ∈ Z}

/-- The pullback of `Z` to the `(l,y,u,t)` ambient along `(l,t)`. -/
def pullZ3 (p : ℕ) (Z : Set (Fin (p + 1) → ℝ)) : Set (Fin (p + 3) → ℝ) :=
  {w | (fun i : Fin (p + 1) => w (iota2 p i)) ∈ Z}

/-- `∃ t, (l,t) ∈ Z`. -/
def NE1 (p : ℕ) (Z : Set (Fin (p + 1) → ℝ)) : Set (Fin (p + 1) → ℝ) :=
  projLast (pullZ2 p Z)

/-- `∃ t, (l,t) ∈ Z ∧ t < y`. -/
def In3lo (p : ℕ) (Z : Set (Fin (p + 1) → ℝ)) : Set (Fin (p + 3) → ℝ) :=
  pullZ3 p Z ∩ tLtU p

/-- `∃ t, (l,t) ∈ Z ∧ u < t`. -/
def In3hi (p : ℕ) (Z : Set (Fin (p + 1) → ℝ)) : Set (Fin (p + 3) → ℝ) :=
  pullZ3 p Z ∩ uLtT p

/-- `¬ ∃ t, (l,t) ∈ Z ∧ t < y` (`y` is a lower bound of the fibre). -/
def LB1 (p : ℕ) (Z : Set (Fin (p + 1) → ℝ)) : Set (Fin (p + 1) → ℝ) :=
  (projLast (pullZ2 p Z ∩ tLtY p))ᶜ

/-- `¬ ∃ t, (l,t) ∈ Z ∧ y < t` (`y` is an upper bound of the fibre). -/
def UB1 (p : ℕ) (Z : Set (Fin (p + 1) → ℝ)) : Set (Fin (p + 1) → ℝ) :=
  (projLast (pullZ2 p Z ∩ yLtT p))ᶜ

/-- `(l,y,u) ↦ ∀ t, (l,t) ∈ Z → u ≤ t`. -/
def NIn2lo (p : ℕ) (Z : Set (Fin (p + 1) → ℝ)) : Set (Fin (p + 2) → ℝ) :=
  (projLast (In3lo p Z))ᶜ

/-- `(l,y,u) ↦ ∀ t, (l,t) ∈ Z → t ≤ u`. -/
def NIn2hi (p : ℕ) (Z : Set (Fin (p + 1) → ℝ)) : Set (Fin (p + 2) → ℝ) :=
  (projLast (In3hi p Z))ᶜ

/-- `(l,y,u) : (∀ t, (l,t) ∈ Z → u ≤ t) ∧ y < u`. -/
def GLBb (p : ℕ) (Z : Set (Fin (p + 1) → ℝ)) : Set (Fin (p + 2) → ℝ) :=
  NIn2lo p Z ∩ yLtT p

/-- `(l,y,u) : (∀ t, (l,t) ∈ Z → t ≤ u) ∧ u < y`. -/
def LUBb (p : ℕ) (Z : Set (Fin (p + 1) → ℝ)) : Set (Fin (p + 2) → ℝ) :=
  NIn2hi p Z ∩ tLtY p

/-- `y` is the greatest lower bound of the fibre. -/
def GLB1 (p : ℕ) (Z : Set (Fin (p + 1) → ℝ)) : Set (Fin (p + 1) → ℝ) :=
  (projLast (GLBb p Z))ᶜ

/-- `y` is the least upper bound of the fibre. -/
def LUB1 (p : ℕ) (Z : Set (Fin (p + 1) → ℝ)) : Set (Fin (p + 1) → ℝ) :=
  (projLast (LUBb p Z))ᶜ

/-- The last coordinate is `0`. -/
def yZero1 (p : ℕ) : Set (Fin (p + 1) → ℝ) :=
  {z | z (Fin.last p) = 0}

/-- The graph of `l ↦ inf (Z_l)` (with value `0` on the empty fibres). -/
def A_lo (p : ℕ) (Z : Set (Fin (p + 1) → ℝ)) : Set (Fin (p + 1) → ℝ) :=
  (NE1 p Z ∩ LB1 p Z ∩ GLB1 p Z) ∪ ((NE1 p Z)ᶜ ∩ yZero1 p)

/-- The graph of `l ↦ sup (Z_l)` (with value `0` on the empty fibres). -/
def A_hi (p : ℕ) (Z : Set (Fin (p + 1) → ℝ)) : Set (Fin (p + 1) → ℝ) :=
  (NE1 p Z ∩ UB1 p Z ∩ LUB1 p Z) ∪ ((NE1 p Z)ᶜ ∩ yZero1 p)

end Work.WilG4a
