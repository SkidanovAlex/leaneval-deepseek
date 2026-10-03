import Mathlib
import Submission.Work.Peluse.PET.muL_abs_bound

/-!
# The vocabulary of the averaged PET step (Peluse's Lemma 4.2 iterated over parameters)

This module fixes the *definitions* used by the averaged PET step
(`Work.Peluse.UControl.PetStep.avgStep`), which is one application of Peluse's Lemma 4.2 to an
`Ω`-parametrised family of configurations, obtained by Cauchy–Schwarz in `x`, van der Corput in `y`
and the reindexing `x ↦ x + Q_{i₀}(y)`.

It is a fresh copy (with fresh names, in the sub-namespace `Work.Peluse.UControl.PetStep`) of the
definitions of `Submission/Work/Peluse/UControl/petStepAvg.lean`, whose *proof* does not compile
(Lean API drift plus a handful of genuine errors); the definitions there are the ones this
vocabulary is meant to provide, and the file is not imported by anything.

* `stepQ` — the polynomial family of the next PET state: the slot `(i,ε)` carries the shift
  `Q i (y + εh) - Q i₀ y`;
* `stepF` — the slot functions of the next state (`F i` or its conjugate);
* `stepBase` — the base function of the next state is the distinguished slot function `F i₀`.
-/

set_option autoImplicit false
open scoped BigOperators

namespace Work.Peluse.UControl.PetStep

/-- The polynomial family of the next PET state: the slot `(i, ε)` gets the shift
`Q i (y + εh) - Q i₀ y`. -/
def stepQ {Ω ι : Type*} (Q : ι → Ω → ℤ → ℤ) (i₀ : ι) :
    {j : ι × Bool // j ≠ (i₀, false)} → (Ω × ℤ) → ℤ → ℤ :=
  fun j a y => if j.1.2 then Q j.1.1 a.1 (y + a.2) - Q i₀ a.1 y
               else Q j.1.1 a.1 y - Q i₀ a.1 y

/-- The slot functions of the next PET state (the conjugation is moved outside the argument). -/
def stepF {ι : Type*} (F : ι → ℤ → ℂ) (j : ι × Bool) : ℤ → ℂ :=
  fun x => if j.2 then star (F j.1 x) else F j.1 x

/-- The base function of the next PET state is the distinguished slot function. -/
def stepBase {Ω ι : Type*} (F : ι → ℤ → ℂ) (i₀ : ι) : (Ω × ℤ) → ℤ → ℂ :=
  fun _ x => F i₀ x

end Work.Peluse.UControl.PetStep
