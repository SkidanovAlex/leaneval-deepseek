/-
  Work.WilE2 — area E2.  Shared definitions for `kho_sphere`.

  `kho_sphere` is the "properness-removal" / sphere step of the Khovanskii induction:
  from a system `S, F` in `n` variables with `s+1` chain functions and a finite set `T` of
  nondegenerate zeros, it produces a system in `n+1` variables, still with `s+1` chain
  functions, whose *lifted* system map is a proper map, and a finite set `T'` of nondegenerate
  zeros with `2 * T.card ≤ T'.card` and total degree at most `∑ deg F i + 2`.

  The construction is the paper's "sphere": the new coordinate `x_n` and the last chain
  function `ψ_s` are used in the quadratic equation
  `∑ x_k² + ψ_s² = c`, and the old equations are transported along `Fin.castSucc`.  Choosing
  `c > ‖x‖² + ψ_s(x)²` for every `x ∈ T` gives the two solutions `x_n = ±√(c - ‖x‖² - ψ_s(x)²)`
  per old zero, and makes the extra component coercive, hence the lifted system map proper.

  This module only contains the *vocabulary*; the lemmas about it live in the sibling modules.
-/
import Mathlib
import Submission.Work.WilE2.KhoGood
import Submission.Work.WilE2.RegSol

set_option autoImplicit false

noncomputable section
open Classical
namespace Work.WilE2

open WilkiesDesign WilkiesDesign.E WilkiesConjecture

variable {n s : ℕ}

/-- Reindex an EA polynomial in `n` ambient coordinates as one in `n+1` ambient coordinates
(the extra coordinate does not occur).  The chain functions are untouched. -/
def embedP {n r : ℕ} (P : EPoly n r) : EPoly (n + 1) r :=
  MvPolynomial.rename (Sum.map Fin.castSucc id) P

/-- `fT S x = ‖x‖² + ψ_{s+1}(x)²`: the quantity that the sphere constant has to dominate
on the finite set `T`. -/
def fT (S : ESys n (s + 1)) (x : Fin n → ℝ) : ℝ :=
  (∑ k : Fin n, (x k) ^ 2) + (S.psi (Fin.last s) x) ^ 2

/-- The radius-squared of the sphere: one more than the sum of `fT` over `T`. -/
def khoC (S : ESys n (s + 1)) (T : Finset (Fin n → ℝ)) : ℝ :=
  1 + ∑ x ∈ T, fT S x

/-- The "sphere" equation `∑ x_k² + ψ_s² - c` in `n+1` ambient coordinates and `s+1` chain
functions. -/
def spherePoly (c : ℝ) : EPoly (n + 1) (s + 1) :=
  (∑ k : Fin (n + 1), MvPolynomial.X (Sum.inl k) * MvPolynomial.X (Sum.inl k))
    + MvPolynomial.X (Sum.inr (Fin.last s)) * MvPolynomial.X (Sum.inr (Fin.last s))
    + MvPolynomial.C (-c)

/-- The transport of `F` to `n+1` coordinates, together with the sphere equation as last
component. -/
def newF (F : Fin n → EPoly n (s + 1)) (c : ℝ) : Fin (n + 1) → EPoly (n + 1) (s + 1) :=
  Fin.lastCases (spherePoly (n := n) (s := s) c) (fun i => embedP (F i))

/-- The first of the two points over an old zero `x` of `F`. -/
def khoPt (S : ESys n (s + 1)) (c : ℝ) (x : Fin n → ℝ) : Fin (n + 1) → ℝ :=
  Fin.snoc x (Real.sqrt (c - fT S x))

/-- The second of the two points over an old zero `x` of `F`. -/
def khoPt' (S : ESys n (s + 1)) (c : ℝ) (x : Fin n → ℝ) : Fin (n + 1) → ℝ :=
  Fin.snoc x (- Real.sqrt (c - fT S x))

/-- The new finite set of nondegenerate zeros: two points over each element of `T`. -/
def newT (S : ESys n (s + 1)) (T : Finset (Fin n → ℝ)) (c : ℝ) : Finset (Fin (n + 1) → ℝ) :=
  T.biUnion (fun x => {khoPt S c x, khoPt' S c x})

@[simp] theorem embedP_C {n r : ℕ} (c : ℝ) :
    (embedP (n := n) (r := r) (MvPolynomial.C c)) = MvPolynomial.C c := by
  simp [embedP]

@[simp] theorem embedP_X_inl {n r : ℕ} (i : Fin n) :
    (embedP (n := n) (r := r) (MvPolynomial.X (Sum.inl i))) =
      MvPolynomial.X (Sum.inl (Fin.castSucc i)) := by
  simp [embedP]

@[simp] theorem embedP_X_inr {n r : ℕ} (j : Fin r) :
    (embedP (n := n) (r := r) (MvPolynomial.X (Sum.inr j))) =
      MvPolynomial.X (Sum.inr j) := by
  simp [embedP]

@[simp] theorem embedP_add {n r : ℕ} (P Q : EPoly n r) :
    embedP (n := n) (r := r) (P + Q) = embedP P + embedP Q := by
  simp [embedP]

@[simp] theorem embedP_mul {n r : ℕ} (P Q : EPoly n r) :
    embedP (n := n) (r := r) (P * Q) = embedP P * embedP Q := by
  simp [embedP]

@[simp] theorem embedP_zero {n r : ℕ} : embedP (n := n) (r := r) (0 : EPoly n r) = 0 := by
  simp [embedP]

@[simp] theorem newF_castSucc (F : Fin n → EPoly n (s + 1)) (c : ℝ) (i : Fin n) :
    newF (n := n) (s := s) F c (Fin.castSucc i) = embedP (F i) := by
  simp [newF]

@[simp] theorem newF_last (F : Fin n → EPoly n (s + 1)) (c : ℝ) :
    newF (n := n) (s := s) F c (Fin.last n) = spherePoly (n := n) (s := s) c := by
  simp [newF]

end Work.WilE2
