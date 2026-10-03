import Mathlib
import Submission.Work.Peluse.LadderP.patJensen
-- import Submission.Work.Peluse.LadderP.bslotSum  -- (child in flight)

/-!
# The one-step lemma of the power-loss ladder: the averaging bound

The peeled (j+1)-state is an average, over `(h,h')` and over the shifts of the peeled slots, of the
level-`2^j` box-norm power of the iterated difference at the `B`-slots.  Splitting `h` into its head
and its last coordinate and replacing the box-norm power by the box norm, the inner average over the
last coordinate of `h` is exactly the box average `boxAvgA` of the Lemma 5.1 input:

`augPowState ≤ M₁^{-(2j+1)} * Σ_{h₁,h₁',h'_s} Σ_{km} Gwt * boxAvgA (… shifts …) (Gof km f)`.

Dually, the peeled j-state is the average of the box-norm powers of the *same* iterated difference
at the remaining `s'` long slots.
-/

set_option autoImplicit false
open scoped BigOperators

namespace Work.Peluse.LadderP

noncomputable section

open Work.Peluse

/-- The type of the shift tuples peeled off in the ladder step. -/
abbrev KmT (j n M₁ : ℕ) (c : ℤ) (L D : ℕ) (h₁ h₁' : Fin j → Fin M₁) : Type :=
  ((i : Fin (2^j - 1)) → ↥(ABlk0 j M₁ c L h₁ h₁' i) × ↥(ABlk0 j M₁ c L h₁ h₁' i)) ×
    ((i : Fin n) → ↥(arithIcc c D) × ↥(arithIcc c D))

/-- **The peel of the (j+1)-state**, summed over `(h,h')` and written with the shift tuples
`(k,m)` of the peeled `A`-slots and long slots. -/
theorem augPowState_peel (j n M₁ : ℕ) (c : ℤ) (L D N : ℕ) (f : ℤ → ℂ) (hf : FinSuppZ f) :
    augPowState j n M₁ c L D N f
      = ((M₁ : ℝ))⁻¹ ^ (2 * (j+1)) *
        ∑ h : Fin (j+1) → Fin M₁, ∑ h' : Fin (j+1) → Fin M₁,
          ∑ km : KmT j n M₁ c L D (headPart h) (headPart h'),
            Gwt j n M₁ c L D (headPart h) (headPart h') *
              boxNormPow (2^j) (BBlk j M₁ c L (enumAll j) h h') (symIcc N)
                (Gof j n M₁ c L D (headPart h) (headPart h') km f) := by
  rw [augPowState]
  refine congrArg (fun z => ((M₁ : ℝ))⁻¹ ^ (2 * (j+1)) * z) ?_
  refine Finset.sum_congr rfl (fun h _ => Finset.sum_congr rfl (fun h' _ => ?_))
  rw [peel_succ_inner j n M₁ c L D N f h h' hf]
  simp only [Gof, Gwt, ABlk]
  rw [Fintype.sum_prod_type, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [Finset.mul_sum]

/-- **The peel of the j-state**, summed over `(h,h')`. -/
theorem patPowState_peel (j n s' M₁ : ℕ) (hs' : 1 ≤ s') (c : ℤ) (L D N : ℕ) (f : ℤ → ℂ)
    (hf : FinSuppZ f) :
    patPowState j (n+s') M₁ c L D N f
      = ((M₁ : ℝ))⁻¹ ^ (2 * j) *
        ∑ h : Fin j → Fin M₁, ∑ h' : Fin j → Fin M₁,
          ∑ km : KmT j n M₁ c L D h h',
            Gwt j n M₁ c L D h h' * Gpow j n s' M₁ c L D N h h' km f := by
  rw [patPowState]
  refine congrArg (fun z => ((M₁ : ℝ))⁻¹ ^ (2 * j) * z) ?_
  refine Finset.sum_congr rfl (fun h _ => Finset.sum_congr rfl (fun h' _ => ?_))
  rw [peel_concl_inner j n s' M₁ c L D N f h h' hs' hf]
  simp only [Gof, Gwt, Gpow]
  rw [Fintype.sum_prod_type, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [Finset.mul_sum]


end

end Work.Peluse.LadderP
