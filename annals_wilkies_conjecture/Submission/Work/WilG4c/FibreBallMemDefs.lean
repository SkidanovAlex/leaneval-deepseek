/-
  WilG4c / `FibreBallMemDefs` — the vocabulary for the lemma `Work.WilkG4c.FibreBallMem`.

  `FibreBallMem` says: given `V ⊆ ℝ^{p+(n+1)}` (the parameter + cube coordinates of a family),
  the set of `z : ℝ^{p+(n+1)+1}` whose *fibre* over `Fin.init z` contains a whole Euclidean
  ball is `Ω`-definable, with a format `F + A` and a degree `D + C` where `A, C` depend only on
  `p, n`.

  The fibre of `V` at `w` is `{y | fibPt w y ∈ V}`, and the condition "contains a ball" is

      `∃ y₀ ε, 0 < ε ∧ ∀ y, dist y y₀ < ε → fibPt w y ∈ V`.

  This is *not* a positive condition — the inner `∀ y` is what makes it a complement of a
  projection.  Over `ℝ` the condition `dist y y₀ < ε` is the same as
  `0 < ε ∧ ∀ j, (y j - y₀ j)² < ε²`, and the `∀ y` is `¬∃ y`, so the set is built by
  complement + projection, exactly as in `FibreLimitPi*`.

  ## The layout

  The big space `ℝ^{FBN}` carries

  * `0 … FBa-1`     : `w` (the base point; parameters then cube coordinates),
  * `FBa … FBa+FBk-1` : `y₀` (the centre of the ball),
  * `FBa+FBk`       : `ε` (the radius),
  * `FBa+FBk+1 …`   : `y` (the running cube point),

  where `FBa = p + (n+1)`, `FBk = n+1` and `FBN = FBa + FBk + 1 + FBk`.

  The chain of `Ω`-operations is then

  * `FibreBallBad` — `ε > 0`, the ball condition, and `fibPt w y ∉ V` (the "bad" big set);
  * `FB_D1 = projLastIter (FBa+FBk+1) FBk FibreBallBad`   — forget `y`  (`∃y`),
  * `FB_D2 = {ε > 0} ∩ (FB_D1)ᶜ`                          — negate,
  * `FB_D3 = projLast FB_D2`                              — forget `ε`  (`∃ε`),
  * `FB_W  = projLastIter FBa FBk FB_D3`                  — forget `y₀` (`∃y₀`),
  * `{z | Fin.init z ∈ FB_W}`                             — re-attach the unused last coordinate.

  `fbSigma` is the coordinate selection `w ++ y` of the big space (the coordinates of
  `fibPt w y`), so that `FibreBallBad` is the pullback of `Vᶜ` along a coordinate map and is
  therefore `Ω`-definable by `Work.WilG4a.subst_mem`.
-/
import Mathlib
import Submission.Work.WilG4c.AlSliceBase
import Submission.Work.WilG1.Basic
import Submission.Work.WilG0.projLastIter_eq
import Submission.Work.WilkiesH.Omega.omega_poly_lt
import Submission.Work.WilkiesH.Omega.omega_poly_le
import Submission.Work.WilkiesH.Omega.omega_poly_ne
import Submission.Work.WilG4a.subst_mem

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Classical

namespace Work.WilkG4c

open WilkiesDesign

/-! ## 1  Dimensions -/

/-- `FBa p n = p + (n+1)`: the dimension of the set `V` (parameters plus cube). -/
abbrev FBa (p n : ℕ) : ℕ := p + (n + 1)
/-- `FBk n = n + 1`: the number of cube coordinates. -/
abbrev FBk (n : ℕ) : ℕ := n + 1
/-- `FBN p n`: the dimension of the big space `(w, y₀, ε, y)`. -/
abbrev FBN (p n : ℕ) : ℕ := FBa p n + FBk n + 1 + FBk n

/-! ## 2  The coordinates of the big space -/

/-- The `i`-th coordinate of the base point `w`. -/
def fbW (p n : ℕ) (i : Fin (FBa p n)) : Fin (FBN p n) :=
  ⟨(i : ℕ), by simp only [FBN, FBa, FBk]; omega⟩

/-- The `i`-th coordinate of the ball centre `y₀`. -/
def fbY0 (p n : ℕ) (i : Fin (FBk n)) : Fin (FBN p n) :=
  ⟨FBa p n + (i : ℕ), by simp only [FBN, FBa, FBk]; omega⟩

/-- The coordinate of the radius `ε`. -/
def fbE (p n : ℕ) : Fin (FBN p n) :=
  ⟨FBa p n + FBk n, by simp only [FBN, FBa, FBk]; omega⟩

/-- The `i`-th coordinate of the running cube point `y`. -/
def fbY (p n : ℕ) (i : Fin (FBk n)) : Fin (FBN p n) :=
  ⟨FBa p n + FBk n + 1 + (i : ℕ), by simp only [FBN, FBa, FBk]; omega⟩

/-- The coordinate of `ε` inside the smaller space `(w, y₀, ε)`. -/
def fbE1 (p n : ℕ) : Fin (FBa p n + FBk n + 1) :=
  ⟨FBa p n + FBk n, by simp only [FBa, FBk]; omega⟩

/-- The coordinate map `w ++ y ↦ fibPt w y`: parameters come from the first `p` coordinates of
`w`, cube coordinates from `y`. -/
def fbSigma (p n : ℕ) (j : Fin (FBa p n)) : Fin (FBN p n) :=
  if h : (j : ℕ) < p then ⟨(j : ℕ), by simp only [FBN, FBa, FBk]; omega⟩
  else ⟨FBa p n + FBk n + 1 + ((j : ℕ) - p), by
    simp only [FBN, FBa, FBk] at h ⊢; omega⟩

/-! ## 3  The big point -/

/-- The point `(w, y₀, ε, y)` of the big space. -/
def fbBig (p n : ℕ) (w : Fin (FBa p n) → ℝ) (y₀ : Fin (FBk n) → ℝ) (ε : ℝ)
    (y : Fin (FBk n) → ℝ) : Fin (FBN p n) → ℝ :=
  Fin.append (Fin.snoc (Fin.append w y₀) ε) y

/-! ## 4  The chain of sets -/

/-- The big "bad" set: `ε > 0`, the ball condition, and `fibPt w y ∉ V`. -/
def FibreBallBad (p n : ℕ) (V : Set (Fin (FBa p n) → ℝ)) : Set (Fin (FBN p n) → ℝ) :=
  {z | 0 < z (fbE p n) ∧
    (∀ j : Fin (FBk n), (z (fbY p n j) - z (fbY0 p n j)) ^ 2 < (z (fbE p n)) ^ 2) ∧
    (fun j : Fin (FBa p n) => z (fbSigma p n j)) ∉ V}

/-- Forget the running point `y` (the `∃y`). -/
def FB_D1 (p n : ℕ) (V : Set (Fin (FBa p n) → ℝ)) : Set (Fin (FBa p n + FBk n + 1) → ℝ) :=
  Work.WilG0.projLastIter (FBa p n + FBk n + 1) (FBk n) (FibreBallBad p n V)

/-- Negate (`∀y …`), retaining `ε > 0`. -/
def FB_D2 (p n : ℕ) (V : Set (Fin (FBa p n) → ℝ)) : Set (Fin (FBa p n + FBk n + 1) → ℝ) :=
  {ξ | 0 < ξ (fbE1 p n)} ∩ (FB_D1 p n V)ᶜ

/-- Forget the radius `ε` (the `∃ε`). -/
def FB_D3 (p n : ℕ) (V : Set (Fin (FBa p n) → ℝ)) : Set (Fin (FBa p n + FBk n) → ℝ) :=
  WilkiesDesign.projLast (FB_D2 p n V)

/-- Forget the centre `y₀` (the `∃y₀`). -/
def FB_W (p n : ℕ) (V : Set (Fin (FBa p n) → ℝ)) : Set (Fin (FBa p n) → ℝ) :=
  Work.WilG0.projLastIter (FBa p n) (FBk n) (FB_D3 p n V)

/-- The semantic set: the base points whose fibre over `w` contains a ball. -/
def FB_Sem (p n : ℕ) (V : Set (Fin (FBa p n) → ℝ)) : Set (Fin (FBa p n) → ℝ) :=
  {w | ∃ (y₀ : Fin (FBk n) → ℝ) (ε : ℝ), 0 < ε ∧
    ∀ y : Fin (FBk n) → ℝ, dist y y₀ < ε → fibPt w y ∈ V}

end Work.WilkG4c
