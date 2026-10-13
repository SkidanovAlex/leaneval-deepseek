/-
  WilE6 (area E6): fibrewise closure and frontier of EA sets (Gabrielov 1998).

  This file: the definitions used by the closure half of `E6_fiber_closure`, i.e. the assembly
  of the Taylor criterion (E3b) with the effective semialgebraic fibrewise closure (E4), via
  the criterion encoding `critSA` of `CritSA.lean`, the witnesses of `norm_witness_iff`, and
  the pullback `saPullback` of `Base.lean`.

  * `sliceMap`, `saSlice` : slicing an `SA (m+n)`-set at the origin of its `n`-dimensional
    fibre, by *substituting* `0` for the fibre coordinates.  This is legitimate here because at
    the fibre origin of `critSA` every witness is determined and equals `0`.
  * `critCond` : the Taylor-criterion conditions of the (merged) basic set, in the shifted
    variables `z' = z + u` (with `t := dist u 0`).
  * `canonT`, `canonWm`, `canonW0`, `canonWb`, `canonWe` : the canonical witnesses realising
    `critCond` (all of them vanish at the fibre origin).

  The two implications relating `critCond` and `critFibreCond`, and the slice lemmas, are proved
  in sibling files: `mem_saSlice_iff.lean`, `critFibreCond_imp_critCond.lean`,
  `critCond_imp_exists_witness.lean`.
-/
import Submission.Work.WilE6.Base
import Submission.Work.WilE6.CritSA
import Submission.Work.WilE6.norm_witness_iff

set_option autoImplicit false
noncomputable section
open Classical Topology
namespace Work.WilE6
open WilkiesConjecture WilkiesDesign WilkiesDesign.E

variable {k r p : ℕ}

/-! ## §1. Slicing an `SA` set at the origin of its fibre -/

/-- The substitution keeping the first `m` coordinates and sending the last `n` to `0`. -/
def sliceMap (m n : ℕ) : Fin (m + n) → MvPolynomial (Fin m) ℝ :=
  fun i => if h : i.1 < m then MvPolynomial.X ⟨i.1, h⟩ else 0

/-- Undo `saPoly`: view an `SA m`-polynomial as a polynomial in `m` variables. -/
def saUnpoly (m : ℕ) (Q : EAPoly m 0) : MvPolynomial (Fin m) ℝ :=
  MvPolynomial.rename (sumFin0Equiv m) Q

/-- The substitution of the slice, on `SA`-polynomials. -/
def sliceHom (m n : ℕ) (Q : EAPoly (m + n) 0) : EAPoly m 0 :=
  saPoly m (MvPolynomial.eval₂Hom (MvPolynomial.C : ℝ →+* MvPolynomial (Fin m) ℝ)
    (sliceMap m n) (saUnpoly (m + n) Q))

/-- Slice an `SA (m+n)`-set at the origin of its `n`-dimensional fibre. -/
def saSlice (m n : ℕ) (X : SA (m + n)) : SA m where
  basics := X.basics.map fun B =>
    ⟨B.eqs.map (sliceHom m n), B.pos.map (sliceHom m n)⟩

/-! ## §2. The criterion conditions -/

/-- The Taylor-criterion conditions for a (merged) basic set whose equation has Taylor
polynomial `P` and whose positivity atoms have Taylor polynomials `Gs`, in the shifted
variables `z' = z + u`, at the point `z` with chain values `h`.  The first `p` coordinates of
`z` are the base coordinates: the frozen-base atoms `z'_i - z_i = 0` contribute the conditions
`|u_i| ≤ dist^{κ²}`. -/
def critCond (hp : p ≤ k) (κ : ℕ) (P : MvPolynomial (Fin k ⊕ Fin (k + r)) ℝ)
    (Gs : List (MvPolynomial (Fin k ⊕ Fin (k + r)) ℝ)) (z : Fin k → ℝ) (h : Fin r → ℝ)
    (u : Fin k → ℝ) : Prop :=
  |MvPolynomial.eval (Sum.elim u (Fin.append z h)) P| ≤ dist u 0 ^ (κ ^ 2) ∧
  (∀ i : Fin p, |u ⟨i.1, lt_of_lt_of_le i.2 hp⟩| ≤ dist u 0 ^ (κ ^ 2)) ∧
  (∀ G ∈ Gs, dist u 0 ^ κ < MvPolynomial.eval (Sum.elim u (Fin.append z h)) G)

/-! ## §3. The canonical witnesses -/

/-- The canonical distance `t = dist u 0`. -/
def canonT (k : ℕ) (u : Fin k → ℝ) : ℝ := dist u 0

/-- The canonical witness for `u_i^2 ≤ t^2`. -/
def canonWm (k : ℕ) (u : Fin k → ℝ) (i : Fin k) : ℝ :=
  Real.sqrt (dist u 0 ^ 2 - u i ^ 2)

/-- The canonical witness for `0 ≤ t`. -/
def canonW0 (k : ℕ) (u : Fin k → ℝ) : ℝ := Real.sqrt (dist u 0)

/-- The canonical witness for the base-fixing atom conditions `±u_i ≤ t^{κ²}` (even `b` gives
`+u`, odd `b` gives `-u`). -/
def canonWb (k p : ℕ) (hp : p ≤ k) (κ : ℕ) (u : Fin k → ℝ) (b : Fin (2 * p)) : ℝ :=
  Real.sqrt (dist u 0 ^ (κ ^ 2) - (if b.1 % 2 == 0 then u ⟨b.1 / 2, div2_lt hp b⟩
    else -u ⟨b.1 / 2, div2_lt hp b⟩))

/-- The canonical witness for the equation conditions `±P ≤ t^{κ²}`. -/
def canonWe (k r : ℕ) (κ : ℕ) (P : MvPolynomial (Fin k ⊕ Fin (k + r)) ℝ) (z : Fin k → ℝ)
    (h : Fin r → ℝ) (u : Fin k → ℝ) (e : Fin 2) : ℝ :=
  Real.sqrt (dist u 0 ^ (κ ^ 2) - (if e = 0 then
    MvPolynomial.eval (Sum.elim u (Fin.append z h)) P
    else -MvPolynomial.eval (Sum.elim u (Fin.append z h)) P))

end Work.WilE6
