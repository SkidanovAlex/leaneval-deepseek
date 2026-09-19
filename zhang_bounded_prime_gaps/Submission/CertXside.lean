import Mathlib
import Submission.CertIndex
import Submission.CertStates

set_option maxRecDepth 1000000
set_option linter.unusedVariables false

open scoped BigOperators
open Finset

namespace Commons.NumberTheory.MaynardSieve

/-!
# The x-side of the certificate computation

The certificate computation evaluates, for each even-part signature `β` of weighted degree ≤ 24,
the x-polynomial `A^(50-|β|) · ∏_w h_w^(σ_w)` with `A = 1 + Σ_v v!·x_v` and
`h_w = w! + Σ_v (v+w)!·x_v`, and reads its coefficients at the 272 signatures `α`.  The
*combinatorial* form of that polynomial is the function `xslots` below: a slot is either an
`A`-factor or an `h_w`-factor, and `xslots L m` counts the ways of assigning to every slot in the
reversed list `L` either nothing or one part, so that the total multiplicity is `m`, weighted by
`v!` for an `A`-slot and `(v+w)!` for an `h_w`-slot.

The punch line (roadmap SESSION 45, and the next proof obligation) is the **one-sided
factorisation**

  `Ssum α β k = C(k,|β|) · |β|!/∏_w σ_w! · xslots (slotList k (mult β)) (mult α)`,

which removes the two-sided DP from the certificate computation.
-/

/-- A slot of the x-side product: an `A`-factor or an `h_w`-factor. -/
inductive CertSlot where
  | A : CertSlot
  | H : Fin 12 → CertSlot
  deriving DecidableEq, Repr

/-- The coefficient function of the product of the slots in `L` (read left to right, each slot
contributing either nothing or one part `2(v+1)`). -/
def xslots : List CertSlot → (Fin 12 → ℕ) → ℕ
  | [], m => if m = 0 then 1 else 0
  | CertSlot.A :: t, m =>
      xslots t m
      + ∑ v : Fin 12,
          if 1 ≤ m v then Nat.factorial (2 * ((v : ℕ) + 1)) * xslots t (m - evec v) else 0
  | CertSlot.H w :: t, m =>
      Nat.factorial (2 * ((w : ℕ) + 1)) * xslots t m
      + ∑ v : Fin 12,
          if 1 ≤ m v then
            Nat.factorial (2 * ((v : ℕ) + 1) + 2 * ((w : ℕ) + 1)) * xslots t (m - evec v)
          else 0

@[simp] theorem xslots_nil (m : Fin 12 → ℕ) : xslots [] m = if m = 0 then 1 else 0 := rfl

theorem xslots_cons_A (t : List CertSlot) (m : Fin 12 → ℕ) :
    xslots (CertSlot.A :: t) m
      = xslots t m
        + ∑ v : Fin 12,
            if 1 ≤ m v then Nat.factorial (2 * ((v : ℕ) + 1)) * xslots t (m - evec v) else 0 :=
  rfl

theorem xslots_cons_H (w : Fin 12) (t : List CertSlot) (m : Fin 12 → ℕ) :
    xslots (CertSlot.H w :: t) m
      = Nat.factorial (2 * ((w : ℕ) + 1)) * xslots t m
        + ∑ v : Fin 12,
            if 1 ≤ m v then
              Nat.factorial (2 * ((v : ℕ) + 1) + 2 * ((w : ℕ) + 1)) * xslots t (m - evec v)
            else 0 :=
  rfl

/-- The slot list attached to a y-side signature: `k - |n|` slots of type `A` and `n_w` slots of
type `h_w`, in a fixed (irrelevant, since the factors commute) order. -/
def slotList (k : ℕ) (n : Fin 12 → ℕ) : List CertSlot :=
  List.replicate (k - ∑ w : Fin 12, n w) CertSlot.A
    ++ (List.ofFn fun w : Fin 12 => List.replicate (n w) (CertSlot.H w)).flatten

/-- The one-sided coefficient object at level `k`, y-signature `n`, x-state `m`:
the value that `Ssum`'s factorisation produces (`C(k,|n|)·|n|!/∏n_w!·xslots`). -/
def xcoe (k : ℕ) (n : Fin 12 → ℕ) (m : Fin 12 → ℕ) : ℕ :=
  Nat.choose k (∑ w : Fin 12, n w) *
    (Nat.factorial (∑ w : Fin 12, n w) / ∏ w : Fin 12, Nat.factorial (n w)) *
    xslots (slotList k n) m

/-- The two `rfl` unfolds of the slot list. -/
theorem slotList_def (k : ℕ) (n : Fin 12 → ℕ) :
    slotList k n = List.replicate (k - ∑ w : Fin 12, n w) CertSlot.A
      ++ (List.ofFn fun w : Fin 12 => List.replicate (n w) (CertSlot.H w)).flatten := rfl

/-! ## Sanity checks of the formulation

These compare `xcoe` (the one-sided object) with the known values of `Ssum`/`slabLevel`
(`Submission/Variational.lean`, `Submission/SlabDP.lean`); they validate the *formulation* of the
factorisation before the general proof is attempted.  -/

example : xcoe 1 (mvec [2]) (mvec [2]) = 24 := by decide
example : xcoe 4 (mvec [2, 2]) (mvec [2, 2]) = 5856 := by decide
example : xcoe 5 (mvec [2, 2]) (mvec [2, 2, 2]) = 46400 := by decide
example : xcoe 3 (mvec [2]) (mvec [4, 2]) = 12672 := by decide
example : xcoe 6 (mvec [2, 2, 2, 2]) (mvec [2, 2]) = 254400 := by decide
example : xcoe 5 (mvec [2, 2]) (mvec [8, 2]) = 2748211200 := by decide
example : xcoe 8 (mvec [2, 2, 2]) (mvec [2, 2, 2, 2, 2, 2]) = 77930496 := by decide

end Commons.NumberTheory.MaynardSieve
