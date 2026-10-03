/-
# Definitions for the formalisation of Friedlander–Iwaniec, Proposition 11.1

This module sets up the vocabulary for the proof of `Work.FIArea4.prop_11_1`, the global
Jacobi-twisted variance estimate (11.14) of *The polynomial X² + Y⁴ captures its primes*.

The variance `V(D) = Work.FIPlan.Vvar R S D α` is a sum over moduli `d ∈ (D,2D]` and residue
classes `a (mod d)` of the squared modulus of the "class sum"

`c_{d,a} = Σ_{r,s : s ≡ r a (d)} α r s · (r | d')`,   `d' = oddPart d`.

Writing `M (d,a) (r,s)` for the matrix of this linear map (indicator of the class condition times
the Jacobi symbol, see `Mentry`), we have

`V(D) = ‖M α‖²`, and the *dual* form is `W(D) = ‖M * γ‖²`, see `Vmat` and `Wform`.

The duality principle (`V_sup ≤ W_sup`) is proved in `prop_11_1_dual`.
-/
import Mathlib
import Submission.Work.FIPlan.Interface

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.FIArea4

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## The matrix of the local variance -/

/-- The entry `M ((d,a),(r,s))` of the variance matrix: the indicator of `(r,d) = 1` and
`s ≡ r a (mod d)`, times the Jacobi symbol `(r | d')`, `d' = oddPart d`. -/
def Mentry (d a r s : ℕ) : ℂ :=
  if Nat.Coprime r d ∧ ((s : ZMod d) = (r : ZMod d) * (a : ZMod d))
  then (jacobiSym (r : ℤ) (Work.FIPlan.oddPart d) : ℂ) else 0

/-- The variance `V(D)` written as the squared norm of `M α`.  Equal to `Work.FIPlan.Vvar`
(`Vmat_eq_Vvar`). -/
def Vmat (R S D : ℕ) (α : ℕ → ℕ → ℂ) : ℝ :=
  ∑ d ∈ Finset.Ioc D (2 * D), ∑ a ∈ Finset.range d,
    Complex.normSq (∑ r ∈ Finset.Icc 1 (2 * R), ∑ s ∈ Finset.Icc 1 (2 * S),
      α r s * Mentry d a r s)

/-- The dual (adjoint) form of the variance: `W(D) = Σ_{r,s} |Σ_{d,a} γ_{a,d} M ((d,a),(r,s))|²`.
This is Friedlander–Iwaniec's `W(D)`, (11.18). -/
def Wform (R S D : ℕ) (γ : ℕ → ℕ → ℂ) : ℝ :=
  ∑ r ∈ Finset.Icc 1 (2 * R), ∑ s ∈ Finset.Icc 1 (2 * S),
    Complex.normSq (∑ d ∈ Finset.Ioc D (2 * D), ∑ a ∈ Finset.range d,
      γ a d * Mentry d a r s)


/-- The entries of the matrix restricted to residue classes `a` that are coprime to the modulus
(the `W*` of Friedlander–Iwaniec's (11.24)). -/
def MentryUnit (d a r s : ℕ) : ℂ :=
  if Nat.Coprime a d then Mentry d a r s else 0

/-- The dual form restricted to the classes `(a,d) = 1`. -/
def WformUnit (R S D : ℕ) (γ : ℕ → ℕ → ℂ) : ℝ :=
  ∑ r ∈ Finset.Icc 1 (2 * R), ∑ s ∈ Finset.Icc 1 (2 * S),
    Complex.normSq (∑ d ∈ Finset.Ioc D (2 * D), ∑ a ∈ Finset.range d,
      γ a d * MentryUnit d a r s)

/-! ## The dyadic variance and the Friedlander–Iwaniec brace -/

/-- The variance `V(D)` restricted to the **dyadic box** `R < r ≤ 2R`, `S < s ≤ 2S` of
Friedlander–Iwaniec (11.6). -/
def Vdyad (D R S : ℕ) (α : ℕ → ℕ → ℂ) : ℝ :=
  ∑ d ∈ Finset.Ioc D (2 * D), ∑ a ∈ Finset.range d,
    Complex.normSq (∑ r ∈ Finset.Ioc R (2 * R), ∑ s ∈ Finset.Ioc S (2 * S),
      α r s * Mentry d a r s)

/-- The dual form `W(D)` over the dyadic box. -/
def Wdyad (D R S : ℕ) (γ : ℕ → ℕ → ℂ) : ℝ :=
  ∑ r ∈ Finset.Ioc R (2 * R), ∑ s ∈ Finset.Ioc S (2 * S),
    Complex.normSq (∑ d ∈ Finset.Ioc D (2 * D), ∑ a ∈ Finset.range d,
      γ a d * Mentry d a r s)

/-- The dual form over the dyadic box, restricted to residue classes `a` coprime to the modulus
(the `W*` of (11.24)). -/
def WdyadUnit (D R S : ℕ) (γ : ℕ → ℕ → ℂ) : ℝ :=
  ∑ r ∈ Finset.Ioc R (2 * R), ∑ s ∈ Finset.Ioc S (2 * S),
    Complex.normSq (∑ d ∈ Finset.Ioc D (2 * D), ∑ a ∈ Finset.range d,
      γ a d * MentryUnit d a r s)

/-- The brace of Friedlander–Iwaniec (11.14). -/
def braceV (D R S : ℕ) (ε : ℝ) : ℝ :=
  (D : ℝ) ^ (-(1 : ℝ) / 2) * (R : ℝ) * (S : ℝ)
    + (((D : ℝ) * Real.sqrt ((R : ℝ) * (S : ℝ))
        + (R : ℝ) * (S : ℝ) ^ ((3 : ℝ) / 4)
        + (S : ℝ) * (R : ℝ) ^ ((3 : ℝ) / 4))
      * (((R : ℝ) * (S : ℝ)) ^ ε))


/-- A double sum over two `Finset`s of naturals as a sum over their product. -/
lemma sum_prod_eq {M : Type*} [AddCommMonoid M] (s t : Finset ℕ) (f : ℕ → ℕ → M) :
    (∑ a ∈ s, ∑ b ∈ t, f a b) = ∑ p ∈ s ×ˢ t, f p.1 p.2 := by
  rw [Finset.sum_product]

end

end Work.FIArea4
