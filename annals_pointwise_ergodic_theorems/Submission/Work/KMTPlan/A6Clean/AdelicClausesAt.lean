/-
# The clause list of the §8 adelic form at a single datum (explicit constants)

`Work.KMTPlan.A6.AdelicFormPropRange` (`A6/MdlAdelicRange.lean`) bundles, at every datum of the
model estimate, one `∃`-list of clauses involving the three constants `c` (the arithmetic gain
rate), `A` (the exponent of the loss weight) and `Cin` (the mixing constant).  This module names
that clause list once, as the predicate `AdelicClausesAt`, so that producers/consumers of the
adelic form can pass it around as a hypothesis with a *writable* type (the raw form is a nested
`∃ … ∧ …`-term whose type cannot be spelled out at a use site).

The definition is verbatim the clause list of `AdelicFormPropRange`, so the two are
definitionally equal and conversion is `exact`/`Id`.
-/
import Mathlib
import Submission.Work.KMTPlan.A6.MdlAdelicRange

-- v4.35 port: restore the v4.34 instance-unification behaviour (respectTransparency) in this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

namespace Work.KMTPlan.A6Clean

open MeasureTheory Polynomial Finset
open scoped ENNReal NNReal BigOperators
open Work.KMTAreas.A7
open Work.KMTPlan.A6

/-- **The clause list of the §8 adelic form at one datum**, with the constants `c`, `A`, `Cin`
explicit. -/
def AdelicClausesAt (P : ℤ[X]) (ρ R : ℝ) (r : NNReal)
    (a : ℕ → NNReal) (Λ : NNReal) (l₁ l₂ k₁ k₂ : ℕ) (t : ℝ)
    (j₁ j₂ : ℤ) (f g : ℤ → ℂ) (C₀ : ℕ) (c A : ℝ) (Cin : NNReal → NNReal) : Prop :=
  ∃ (F : ℕ → ℝ → ℤ → ℂ)
    (u v : ℕ → ℝ → ZMod (arithQ ρ (max l₁ l₂)) → ℂ) (M Ku Kv : ℝ),
    (∀ (n : ℕ) (ρ' : ℤ), Work.KMTAreas.A7Rep.HasRealFreqSupport (fun X : ℝ => F n X ρ')
        (Set.Icc (-(1 / (8 * (arithQ ρ (max l₁ l₂) : ℝ))))
          (1 / (8 * (arithQ ρ (max l₁ l₂) : ℝ))))) ∧
    (∀ (n : ℕ) (x : ℤ), F n (x : ℝ) (x % ((arithQ ρ (max l₁ l₂) : ℕ) : ℤ))
        = (if goodScale (arithQ ρ (max l₁ l₂)) (lcL l₁ l₂ k₁ k₂) (Nat.floor (a n)) then
            mdlSliceJ ρ P C₀ a f g l₁ l₂ k₁ k₂ j₁ j₂ t n x else 0)) ∧
    (∀ (n : ℕ) (X : ℝ) (ρ' : ℤ), F n X ρ'
        = zmodAvg (negReflect P) (arithQ ρ (max l₁ l₂)) (u n X) (v n X)
            ((ρ' : ℤ) : ZMod (arithQ ρ (max l₁ l₂)))) ∧
    (0 ≤ M ∧ ENNReal.ofReal M
        ≤ (Cin Λ : ENNReal)
          * ENNReal.ofReal ((2 : ℝ) ^ (-(c * max (l₁ : ℝ) (l₂ : ℝ))))) ∧
    (0 ≤ Ku ∧ ENNReal.ofReal Ku ≤ (Cin Λ : ENNReal)
        * ENNReal.ofReal (lossWeight A ρ l₁ l₂ k₁ k₂) * eLpNorm f 2 Measure.count) ∧
    (0 ≤ Kv ∧ ENNReal.ofReal Kv ≤ (Cin Λ : ENNReal)
        * ENNReal.ofReal (lossWeight A ρ l₁ l₂ k₁ k₂) * eLpNorm g 2 Measure.count) ∧
    (∫⁻ X : ℝ, (VrLiftDataP R (arithQ ρ (max l₁ l₂)) (fun n : ℕ => u n X)) ^ (2 : ℕ)
        ≤ ENNReal.ofReal (Ku ^ 2)) ∧
    (∫⁻ X : ℝ, (VrLiftDataP R (arithQ ρ (max l₁ l₂)) (fun n : ℕ => v n X)) ^ (2 : ℕ)
        ≤ ENNReal.ofReal (Kv ^ 2)) ∧
    (∀ (n : ℕ) (θ : ZMod (arithQ ρ (max l₁ l₂))),
        AEMeasurable (fun X : ℝ => u n X θ)) ∧
    (∀ (n : ℕ) (θ : ZMod (arithQ ρ (max l₁ l₂))),
        AEMeasurable (fun X : ℝ => v n X θ)) ∧
    (∀ (X : ℝ) (n : ℕ),
      eLpNorm (fun ρ' : ZMod (arithQ ρ (max l₁ l₂)) =>
          zmodAvg (negReflect P) (arithQ ρ (max l₁ l₂)) (u n X) (v n X) ρ') (r : ENNReal)
          (zmodProb (arithQ ρ (max l₁ l₂)))
        ≤ ENNReal.ofReal M
          * eLpNorm (u n X) 2 (zmodProb (arithQ ρ (max l₁ l₂)))
          * eLpNorm (v n X) 2 (zmodProb (arithQ ρ (max l₁ l₂)))) ∧
    (∀ (X : ℝ) (m n l : ℕ),
      eLpNorm (fun ρ' : ZMod (arithQ ρ (max l₁ l₂)) =>
          zmodAvg (negReflect P) (arithQ ρ (max l₁ l₂)) (u m X - u n X) (v l X) ρ') (r : ENNReal)
          (zmodProb (arithQ ρ (max l₁ l₂)))
        ≤ ENNReal.ofReal M
          * eLpNorm (u m X - u n X) 2 (zmodProb (arithQ ρ (max l₁ l₂)))
          * eLpNorm (v l X) 2 (zmodProb (arithQ ρ (max l₁ l₂)))) ∧
    (∀ (X : ℝ) (m n l : ℕ),
      eLpNorm (fun ρ' : ZMod (arithQ ρ (max l₁ l₂)) =>
          zmodAvg (negReflect P) (arithQ ρ (max l₁ l₂)) (u l X) (v m X - v n X) ρ') (r : ENNReal)
          (zmodProb (arithQ ρ (max l₁ l₂)))
        ≤ ENNReal.ofReal M
          * eLpNorm (u l X) 2 (zmodProb (arithQ ρ (max l₁ l₂)))
          * eLpNorm (v m X - v n X) 2 (zmodProb (arithQ ρ (max l₁ l₂))))

end Work.KMTPlan.A6Clean
