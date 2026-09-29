import Mathlib
import Submission.Work.TMC16Core.Defs
import Submission.Work.TMC16Core.Core.geom
import Submission.Work.TMC16Core.Assembly.Consts

/-!
# The windows of the `s = 0` and resonant branches (AJ §9, Lemmas 9.4(2) and 9.5)

`I1s0`/`I2s0` are AJ's two windows for the `s = 0` case with `k_0 ≤ 4q_{n-1}/5`
(`h = q_{n-1}`, `U = ⌊19 q_{n-1}/40⌋`) and for the case `q_n ≤ 2 q_{n-1}`
(`h = q_n`, `U = ⌊q_n/4⌋`); here the windows are written as sets of *sites* `x`, the
associated phase being `θ + (x + h - 1) α` (so that the scale is `Ks0 h = 2h - 1`).

`I1s0c`/`I2s0c` are AJ's windows for the case `k_0 > 4q_{n-1}/5`, `q_n > 2 q_{n-1}`
(one block of `q_{n-1}` sites on each side), again as sets of sites.
-/

namespace Work.TMC16Core.Assembly

open Work.TMC16Core
open Work.TMC16Core.Core

noncomputable section

/-- The first `s = 0` window (as a set of sites): `h` sites centred at `-h + 3/2`. -/
def I1s0 (h U : ℕ) : Finset ℤ :=
  Finset.Icc (-((U : ℤ)) - (h : ℤ) + 2) ((U : ℤ) - (h : ℤ) + 1)

/-- The second `s = 0` window (as a set of sites): `2h - 2U` sites centred at `m qn + 1/2`. -/
def I2s0 (h U : ℕ) (m qn : ℤ) : Finset ℤ :=
  Finset.Icc (m * qn + (U : ℤ) - (h : ℤ) + 2) (m * qn + (h : ℤ) - (U : ℤ) + 1)

/-- The scale of the `s = 0` windows. -/
def Ks0 (h : ℕ) : ℕ := 2 * h - 1

/-- The first window of the third `s = 0` sub-case (`q_n > 2 q_{n-1}`): one block of `h`
sites. -/
def I1s0c (h : ℕ) : Finset ℤ :=
  Finset.Icc (-(((h / 2 : ℕ) : ℤ)) - (h : ℤ) + 2) (-(((h / 2 : ℕ) : ℤ)) + 1)

/-- The second window of the third `s = 0` sub-case: one block of `h` sites. -/
def I2s0c (h : ℕ) (m qn : ℤ) : Finset ℤ :=
  Finset.Icc (m * qn - (((h / 2 : ℕ) : ℤ)) + 2)
    (m * qn + (h : ℤ) - (((h / 2 : ℕ) : ℤ)) + 1)

/-- The scale of the third `s = 0` sub-case. -/
def Ks0c (h : ℕ) : ℕ := 2 * h - 1

/-- The two resonant windows (AJ Lemma 9.13), as sets of sites: `I₁` is centred at `-qn + 1/2`
and `I₂` at `(ℓ-1) qn + qn/2 + 1/2`; the scale is `Kr qn = 2 qn - 1`. -/
def I1r (qn : ℕ) : Finset ℤ :=
  Finset.Icc (-((((5 * qn) / 8 : ℕ) : ℤ)) - (qn : ℤ) + 1)
    ((((5 * qn) / 8 : ℕ) : ℤ) - (qn : ℤ))

/-- The second resonant window. -/
def I2r (qn : ℕ) (ℓ : ℕ) : Finset ℤ :=
  Finset.Icc (((ℓ : ℤ) - 1) * (qn : ℤ) + ((((5 * qn) / 8 : ℕ) : ℤ)) - (qn : ℤ) + 1)
    (((ℓ : ℤ) + 1) * (qn : ℤ) - ((((5 * qn) / 8 : ℕ) : ℤ)) - (qn : ℤ))

/-- The scale of the resonant windows. -/
def Kr (qn : ℕ) : ℕ := 2 * qn - 1

end

end Work.TMC16Core.Assembly
