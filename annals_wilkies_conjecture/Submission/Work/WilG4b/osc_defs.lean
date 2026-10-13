/-
  WilG4b — vocabulary for the one-sided oscillation sets `oscR`, `oscL`.

  For `y > x`, the condition `q < dq g x y` is the positivity of the config polynomial
  `(g y - g x) - q (y - x)`, and `dq g x y < q` that of its negative.  Both are realised in
  the five coordinates `(x, δ, y, u, v)` with `u = g x`, `v = g y`:

  * `atomA`, `atomB`  : the two graph atoms `u = g x`, `v = g y`;
  * `posOf Ps`        : `x < y` (right case) or `x > y` (left case);
  * `posOf Pw`        : `y < x + δ` (right) or `x - δ < y` (left);
  * `posOf Pc`        : the strict config inequality.

  `coreP` is the conjunction of the five atoms in `ℝ⁵`; `projN 3` exists the three witnesses
  `(y,u,v)`; the final `projLast` quantifies `δ > 0` *negatively*, so that

      `(WHi g q)ᶜ = HighR g q = {x | ∀ δ > 0, ∃ y, x < y < x + δ ∧ q < dq g x y}`.

  This file fixes only the vocabulary; the semantic and `Ω`-membership lemmas live in
  `Submission/Work/WilG4b/osc_omega_mem.lean`.
-/
import Mathlib
import Submission.Work.Wilkies.Defs
import Submission.Work.WilG1.Basic
import Submission.Work.WilG1.OneDim.Defs
import Submission.Work.WilG0.Main
import Submission.Work.WilG5.Basic

set_option autoImplicit false
noncomputable section
open Classical
namespace Work.WilG4b

open WilkiesDesign WilkiesConjecture

/-! ## 1. The `ℝ⁵` coordinate layout `(x, δ, y, u, v)` -/

/-- The graph of `g` read at the coordinates `(0,3)`: `u = g x`. -/
def iotaA : Fin 2 → Fin 5 := fun j => if j = 0 then 0 else 3

/-- The graph of `g` read at the coordinates `(2,4)`: `v = g y`. -/
def iotaB : Fin 2 → Fin 5 := fun j => if j = 0 then 2 else 4

@[simp] theorem iotaA_zero : iotaA 0 = (0 : Fin 5) := by simp [iotaA]
@[simp] theorem iotaA_one : iotaA 1 = (3 : Fin 5) := by
  rw [iotaA]; rw [if_neg (by decide)]
@[simp] theorem iotaB_zero : iotaB 0 = (2 : Fin 5) := by simp [iotaB]
@[simp] theorem iotaB_one : iotaB 1 = (4 : Fin 5) := by
  rw [iotaB]; rw [if_neg (by decide)]

/-- The graph of `g : ℝ → ℝ` in the shape used by the hypothesis of `osc_omega_mem`. -/
def Ggraph (g : ℝ → ℝ) : Set (Fin 2 → ℝ) := graphOf (fun x : Fin 1 → ℝ => g (x 0))

/-! ## 2. The config polynomials -/

/-- `y - x`. -/
def sideP5 : MvPolynomial (Fin 5) ℝ := MvPolynomial.X 2 - MvPolynomial.X 0

/-- `x - y`. -/
def sideP5L : MvPolynomial (Fin 5) ℝ := MvPolynomial.X 0 - MvPolynomial.X 2

/-- `(x + δ) - y`. -/
def widthP5 : MvPolynomial (Fin 5) ℝ :=
  MvPolynomial.X 1 - MvPolynomial.X 2 + MvPolynomial.X 0

/-- `y - (x - δ)`. -/
def widthP5L : MvPolynomial (Fin 5) ℝ :=
  MvPolynomial.X 2 - MvPolynomial.X 0 + MvPolynomial.X 1

/-- `(v - u) - q (y - x)`: positive exactly when the difference quotient exceeds `q`. -/
def shiftHiP (q : ℝ) : MvPolynomial (Fin 5) ℝ :=
  MvPolynomial.X 4 - MvPolynomial.X 3 -
    MvPolynomial.C q * (MvPolynomial.X 2 - MvPolynomial.X 0)

/-- `q (y - x) - (v - u) = -(shiftHiP q)`. -/
def shiftLoP (q : ℝ) : MvPolynomial (Fin 5) ℝ :=
  MvPolynomial.C q * (MvPolynomial.X 2 - MvPolynomial.X 0) -
    (MvPolynomial.X 4 - MvPolynomial.X 3)

/-! ## 3. The atoms -/

/-- `u = g x`. -/
def atomA (g : ℝ → ℝ) : Set (Fin 5 → ℝ) := Work.WilG5.coordPre iotaA (Ggraph g)

/-- `v = g y`. -/
def atomB (g : ℝ → ℝ) : Set (Fin 5 → ℝ) := Work.WilG5.coordPre iotaB (Ggraph g)

/-- `{0 < P}`. -/
def posOf {n : ℕ} (P : MvPolynomial (Fin n) ℝ) : Set (Fin n → ℝ) :=
  {z | 0 < MvPolynomial.eval z P}

/-! ## 4. The core, the body and the negated-`δ` hull -/

/-- The conjunction of the five atoms in `ℝ⁵`. -/
def coreP (g : ℝ → ℝ) (Ps Pw Pc : MvPolynomial (Fin 5) ℝ) : Set (Fin 5 → ℝ) :=
  atomA g ∩ atomB g ∩ posOf Ps ∩ posOf Pw ∩ posOf Pc

/-- Right side, `q < dq`. -/
def coreHi (g : ℝ → ℝ) (q : ℝ) : Set (Fin 5 → ℝ) :=
  coreP g sideP5 widthP5 (shiftHiP q)

/-- Right side, `dq < q`. -/
def coreLo (g : ℝ → ℝ) (q : ℝ) : Set (Fin 5 → ℝ) :=
  coreP g sideP5 widthP5 (shiftLoP q)

/-- Left side, `q < dq` (for `y < x` this is `q (y-x) - (u-v) > 0`). -/
def coreHiL (g : ℝ → ℝ) (q : ℝ) : Set (Fin 5 → ℝ) :=
  coreP g sideP5L widthP5L (shiftLoP q)

/-- Left side, `dq < q`. -/
def coreLoL (g : ℝ → ℝ) (q : ℝ) : Set (Fin 5 → ℝ) :=
  coreP g sideP5L widthP5L (shiftHiP q)

def bodyP (g : ℝ → ℝ) (Ps Pw Pc : MvPolynomial (Fin 5) ℝ) : Set (Fin 2 → ℝ) :=
  Work.WilG5.projN 3 (coreP g Ps Pw Pc)

def bodyHi (g : ℝ → ℝ) (q : ℝ) : Set (Fin 2 → ℝ) := bodyP g sideP5 widthP5 (shiftHiP q)
def bodyLo (g : ℝ → ℝ) (q : ℝ) : Set (Fin 2 → ℝ) := bodyP g sideP5 widthP5 (shiftLoP q)
def bodyHiL (g : ℝ → ℝ) (q : ℝ) : Set (Fin 2 → ℝ) := bodyP g sideP5L widthP5L (shiftLoP q)
def bodyLoL (g : ℝ → ℝ) (q : ℝ) : Set (Fin 2 → ℝ) := bodyP g sideP5L widthP5L (shiftHiP q)

/-- `0 < δ` in the coordinates `(x, δ)`. -/
def posU2 : Set (Fin 2 → ℝ) := {w | 0 < w 1}

/-- `∃ δ > 0, ¬ body`. -/
def WHi (g : ℝ → ℝ) (q : ℝ) : Set (Fin 1 → ℝ) := projLast (posU2 ∩ (bodyHi g q)ᶜ)
def WLo (g : ℝ → ℝ) (q : ℝ) : Set (Fin 1 → ℝ) := projLast (posU2 ∩ (bodyLo g q)ᶜ)
def WHiL (g : ℝ → ℝ) (q : ℝ) : Set (Fin 1 → ℝ) := projLast (posU2 ∩ (bodyHiL g q)ᶜ)
def WLoL (g : ℝ → ℝ) (q : ℝ) : Set (Fin 1 → ℝ) := projLast (posU2 ∩ (bodyLoL g q)ᶜ)

/-! ## 5. The semantic targets -/

def HighR (g : ℝ → ℝ) (q : ℝ) : Set (Fin 1 → ℝ) :=
  {z | ∀ δ : ℝ, 0 < δ → ∃ y : ℝ, z 0 < y ∧ y < z 0 + δ ∧ q < Work.WilG1.dq g (z 0) y}

def LowR (g : ℝ → ℝ) (q : ℝ) : Set (Fin 1 → ℝ) :=
  {z | ∀ δ : ℝ, 0 < δ → ∃ y : ℝ, z 0 < y ∧ y < z 0 + δ ∧ Work.WilG1.dq g (z 0) y < q}

def HighL (g : ℝ → ℝ) (q : ℝ) : Set (Fin 1 → ℝ) :=
  {z | ∀ δ : ℝ, 0 < δ → ∃ y : ℝ, z 0 - δ < y ∧ y < z 0 ∧ q < Work.WilG1.dq g (z 0) y}

def LowL (g : ℝ → ℝ) (q : ℝ) : Set (Fin 1 → ℝ) :=
  {z | ∀ δ : ℝ, 0 < δ → ∃ y : ℝ, z 0 - δ < y ∧ y < z 0 ∧ Work.WilG1.dq g (z 0) y < q}

end Work.WilG4b
