import Mathlib
import Submission.Work.Peluse.SwapE.Defs

/-!
# `SwapE` — auxiliary vocabulary for the linear-in-law identity

This module holds the small vocabulary layer used by `linearInLaw`
(`Submission/Work/Peluse/SwapE/linearInLaw.lean`).

* `cubeMassRaw d f n` is the un-normalised cube mass: the `∑' x : ℤ` of the definition of
  `boxMass`; `boxMass d S f n = (S.card)⁻¹ * cubeMassRaw d f n` **by definition**.
* `slotVec d q₁ q₂ M p` is the slot-difference vector of a pair of slot points
  `p = (h, h') : (Fin d → Fin M × Fin M) × (Fin d → Fin M × Fin M)`, i.e.
  `fun k => pdir (q₁ k) (q₂ k) (p.1 k) - pdir (q₁ k) (q₂ k) (p.2 k)`.  It is the only feature of
  `(h, h')` that the summand of `pboxSum` depends on.
* `pairCount d q₁ q₂ M n` is the number of pairs of slot points whose slot-difference vector is
  `n`; it is `M⁴` times the joint law of the slot values.

The linear-in-law identity then has three arithmetic ingredients, proved in sibling modules:

* `cubeMassRaw_shift` — the `∑' x` only depends on the difference of the two slot vectors;
* `pairSum_eq` — the double sum over slot points is a sum over slot vectors weighted by `pairCount`;
* `pairCount_eq_prod` — `pairCount` factors over the coordinates: it is the product of the
  one-dimensional `slotCount`s;
* `cubeMassRaw_eq_zero` — the cube mass of a vector with a coordinate of modulus `> 2N` vanishes.
-/

set_option autoImplicit false

open scoped BigOperators

namespace Work.Peluse.SwapE

noncomputable section

open Work.Peluse
open Work.Peluse.LadderP.Swap

/-- The un-normalised cube mass of the slot value `n`: the `∑' x : ℤ` appearing in the definition
of `boxMass`. -/
def cubeMassRaw (d : ℕ) (f : ℤ → ℂ) (n : Fin d → ℤ) : ℂ :=
  ∑' x : ℤ, ∏ ω : Fin d → Bool, (star^[weight ω]) (f (x + cornerShift n (0 : Fin d → ℤ) ω))

/-- `boxMass` is the normalised `cubeMassRaw` — this holds by definition. -/
theorem boxMass_eq (d : ℕ) (S : Finset ℤ) (f : ℤ → ℂ) (n : Fin d → ℤ) :
    boxMass d S f n = ((S.card : ℂ))⁻¹ * cubeMassRaw d f n := rfl

/-- The slot-difference vector of a pair of slot points:
`slotVec d q₁ q₂ M (h, h') = fun k => pdir (q₁ k) (q₂ k) (h k) − pdir (q₁ k) (q₂ k) (h' k)`. -/
def slotVec (d : ℕ) (q₁ q₂ : Fin d → ℤ) (M : ℕ)
    (p : (Fin d → Fin M × Fin M) × (Fin d → Fin M × Fin M)) : Fin d → ℤ :=
  fun k => pdir (q₁ k) (q₂ k) (p.1 k) - pdir (q₁ k) (q₂ k) (p.2 k)

/-- The number of pairs of slot points `(h, h')` whose slot-difference vector is `n`.  This is
`M⁴` times the joint law `∏_k slotLaw …` of the slot values. -/
def pairCount (d : ℕ) (q₁ q₂ : Fin d → ℤ) (M : ℕ) (n : Fin d → ℤ) : ℕ :=
  ((Finset.univ : Finset ((Fin d → Fin M × Fin M) × (Fin d → Fin M × Fin M))).filter
    (fun p => slotVec d q₁ q₂ M p = n)).card

/-- `pairCount` is the cardinality of a filtered finite set — this holds by definition. -/
theorem pairCount_eq_card (d : ℕ) (q₁ q₂ : Fin d → ℤ) (M : ℕ) (n : Fin d → ℤ) :
    pairCount d q₁ q₂ M n
      = ((Finset.univ : Finset ((Fin d → Fin M × Fin M) × (Fin d → Fin M × Fin M))).filter
          (fun p => slotVec d q₁ q₂ M p = n)).card := rfl

end

end Work.Peluse.SwapE
