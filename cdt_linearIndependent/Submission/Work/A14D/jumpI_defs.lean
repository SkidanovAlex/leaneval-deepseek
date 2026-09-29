import Mathlib
import Submission.Work.A14.defs
import Submission.Work.A14D.LC_setup
import Submission.Work.A14D.LC_A_defs

/-!
# `Work.A14D.jumpI_defs` — the objects of the jump identity for the integral slots

The three integral slots of the fourteen functions of Theorem A are the primitives of
`y'·y^{−i}·(G^{SU} − jets)`.  This file names the two integrands involved in the jump identity

  `JFIc a b c HU HL D i = BUi a b c HU HL i − (BUi a b c HU HL i) ∘ wC`  on `SU ∩ SL`

of `Submission.Work.A14D.jump_I_ident`:

* `jIntU a b c HU HL i` — the integrand of the `SU`-branch `BUi` (the primitive of
  `y'·y^{−i}·(HU + HL∘wC − jets)`),
* `jIntJ D i` — the integrand of the jump `JFI D i` (the primitive of `y'·y^{−i}·(D − D∘wC)`),
* `PhiI a b c HU HL D i` — the difference `(BUi i − (BUi i)∘wC) − JFI D i`, which is the function
  proved to be constant on `SU ∩ SL`.
-/

namespace Work.A14D

open Complex Metric
open scoped Topology BigOperators

noncomputable section

/-- The integrand of the `SU`-branch of the `i`-th integral entry:
`y'(z)·y(z)^{−i}·((HU + HL∘wC)(z) − Σ_{n<i}[yⁿ]G·y(z)ⁿ)`. -/
def jIntU (a b c : ℤ) (HU HL : ℂ → ℂ) (i : ℕ) : ℂ → ℂ :=
  fun z => dyC z * (yC z)⁻¹ ^ i * ((HU z + HL (wC z)) - GjetA a b c i z)

/-- The integrand of the jump of the `i`-th integral entry:
`y'(z)·y(z)^{−i}·(D − D∘wC)(z)`. -/
def jIntJ (D : ℂ → ℂ) (i : ℕ) : ℂ → ℂ :=
  fun z => dyC z * (yC z)⁻¹ ^ i * jumpH D z

/-- `(BUi i − (BUi i)∘wC) − JFI D i`; `jump_I_ident` says that this vanishes on `SU ∩ SL`. -/
def PhiI (a b c : ℤ) (HU HL D : ℂ → ℂ) (i : Fin 3) : ℂ → ℂ :=
  fun z => (BUi a b c HU HL i z - BUi a b c HU HL i (wC z)) - JFI D i z

/-- `BUi` is the sum of the value at `cSU` and the segment primitive of `jIntU`. -/
lemma BUi_eq_const_add_primSeg (a b c : ℤ) (HU HL : ℂ → ℂ) (i : Fin 3) :
    BUi a b c HU HL i = fun z => (∑' k : ℕ,
        ((PowerSeries.coeff k (Submission.CDTPlan.fourteen a b c (iIdxA i)) : ℚ) : ℂ)
          * (yC cSU) ^ k) + primSeg (jIntU a b c HU HL (i : ℕ)) cSU z := rfl

/-- `JFI` is the segment primitive of `jIntJ`. -/
lemma JFI_eq_primSeg (D : ℂ → ℂ) (i : Fin 3) :
    JFI D i = primSeg (jIntJ D (i : ℕ)) cSU := rfl

/-- Unfolding of `PhiI`. -/
lemma PhiI_def (a b c : ℤ) (HU HL D : ℂ → ℂ) (i : Fin 3) (z : ℂ) :
    PhiI a b c HU HL D i z
      = (BUi a b c HU HL i z - BUi a b c HU HL i (wC z)) - JFI D i z := rfl

end

end Work.A14D
