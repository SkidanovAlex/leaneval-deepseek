import Mathlib
import Submission.Work.Peluse.UControl.PetChainInv
import Submission.Work.Peluse.UControl.lambdaMDShiftBound

/-!
# The initial symbolic state of the PET chain for `LambdaMD`

`petInitSym P` is the symbolic state (`PetStateSym 0`, no formal parameters yet) whose slots carry
the shifts `X^(i+1)` (`1 ≤ i ≤ d-1`, `d = P.natDegree`) and `P` itself.  Its concrete companion
(`SymState.dropC (petInitSym P)).S.toPetP H (petInitSlotF P F) (petInitBase P F)`) has, by
`petInitSym_lam`, correlation exactly `‖LambdaMD N M P F‖`, so `PetInv` at this state is the start of
the analytic PET chain (`petRun` then gives the terminal correlation bound).

Since `P.natDegree ≥ 2` makes every slot polynomial of degree `≥ 1`, no slot is constant, so
`dropC` does not remove any slot; the index type of the dropped state is the subtype of the full
index type, which is why the slot functions are given as `petInitSlotF P F j.1`.
-/

set_option autoImplicit false
open scoped BigOperators

namespace Work.Peluse.UControl

open Work.Peluse.UControl.PetStep

noncomputable section

/-- The **initial symbolic PET state** of the chain for `LambdaMD N M P F`: no formal parameters
(`nv = 0`), slots `Fin (P.natDegree - 1) ⊕ Fin 1` with shift polynomials `X^(i+1)` and `P`. -/
def petInitSym (P : Polynomial ℤ) : SymState P.natDegree where
  nv := 0
  S :=
    { ι := Fin (P.natDegree - 1) ⊕ Fin 1
      finι := inferInstance
      decι := inferInstance
      P := fun j => match j with
        | Sum.inl i => (Polynomial.X ^ (i.val + 1)).map (MvPolynomial.C)
        | Sum.inr _ => P.map (MvPolynomial.C) }
  hd := by
    rintro (i | i)
    · have h1 : ((Polynomial.X : Polynomial ℤ) ^ (i.val + 1)).natDegree = i.val + 1 :=
        Polynomial.natDegree_X_pow _
      have h2 : i.val + 1 ≤ P.natDegree := by
        have := i.isLt
        omega
      exact le_trans (Polynomial.natDegree_map_le ..) (le_trans (le_of_eq h1) h2)
    · simpa using Polynomial.natDegree_map_le (p := P) (f := MvPolynomial.C)

/-- The slot functions of the initial state: `F_{i+1}` on the `i`-th power slot and `F_d` (the last
function) on the `P` slot. -/
def petInitSlotF (P : Polynomial ℤ) (F : Fin (P.natDegree + 1) → ℤ → ℂ) :
    (petInitSym P).S.ι → ℤ → ℂ :=
  fun j => match j with
    | Sum.inl i => F ⟨i.val + 1, by have := i.isLt; omega⟩
    | Sum.inr _ => F ⟨P.natDegree, Nat.lt_succ_self _⟩

/-- The base function of the initial state: `F_0` (constant in the (trivial) parameter). -/
def petInitBase (H : ℕ) (P : Polynomial ℤ) (F : Fin (P.natDegree + 1) → ℤ → ℂ) :
    WinTower H 0 → ℤ → ℂ :=
  fun _ => F ⟨0, Nat.succ_pos _⟩

/-- The window radius used by the chain: the largest admissible value at the *last* step of the
chain.  The condition `γ' ≤ petChainLevel γ k ^ 2 / (20000 * (2 ^ k * D + 1))` is *decreasing* in
`k` (`petWindow_mono`), so it is equivalent to its value at `k = chainLen X - 1`; this is also what
makes the constant a function of `P` alone (no `A`).  For `n = 0` (no steps) the value is irrelevant
and we use the `n = 1` expression. -/
def petWindow (γ : ℝ) (D n : ℕ) : ℝ :=
  min 1 (petChainLevel γ (n - 1) ^ 2 / (20000 * (((2 ^ (n - 1) * D : ℕ) : ℝ) + 1)))

end

end Work.Peluse.UControl
