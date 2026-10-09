/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Hensel's lemma for local fields

The two delegated results `isAdicComplete_maximalIdeal` and `henselianLocalRing_intRing` show that
the ring of integers of a non-archimedean local field is a Henselian local ring.  This file
records the resulting *Hensel lifting* statements in the form used later.

## Main results

* `Work.LocalFields.hensel_lift_root` : a simple root mod `𝔪` lifts to a root.
* `Work.LocalFields.hensel_lift_root_residue` : the same, phrased with the residue field.
* `Work.LocalFields.henselian_completion` : the same for the completion `K_v` of a number field.
-/
import Submission.Work.LocalFields.Basic
import Submission.Work.LocalFields.CompletionLocalField
import Submission.Work.LocalFields.isAdicComplete_maximalIdeal
import Submission.Work.LocalFields.henselianLocalRing_intRing
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.LocalFields

open scoped NumberField Valued WithZero

variable {k : Type*} [Field k] [Valued k (WithZero (Multiplicative ℤ))] [IsLocalField k]

/-- **Hensel's lemma (simple root lifting), local field form.**  A monic polynomial over the ring
of integers of a non-archimedean local field with a simple root modulo the maximal ideal has a
root which reduces to it. -/
theorem hensel_lift_root (f : Polynomial (Valued.integer k)) (hf : f.Monic)
    (a₀ : Valued.integer k) (h₁ : f.eval a₀ ∈ IsLocalRing.maximalIdeal (Valued.integer k))
    (h₂ : IsUnit (f.derivative.eval a₀)) :
    ∃ a : Valued.integer k, f.IsRoot a ∧
      a - a₀ ∈ IsLocalRing.maximalIdeal (Valued.integer k) := by
  haveI := henselianLocalRing_intRing (k := k)
  exact HenselianLocalRing.is_henselian f hf a₀ h₁ h₂

/-- **Hensel's lemma, residue field form.**  A monic polynomial over the ring of integers of a
local field with a simple root in the residue field has a root in the ring of integers reducing to
it. -/
theorem hensel_lift_root_residue (f : Polynomial (Valued.integer k)) (hf : f.Monic)
    (a₀ : Valued.ResidueField k)
    (h₁ : Polynomial.aeval a₀ f = 0)
    (h₂ : Polynomial.aeval a₀ (Polynomial.derivative f) ≠ 0) :
    ∃ a : Valued.integer k, f.IsRoot a ∧ IsLocalRing.residue (Valued.integer k) a = a₀ := by
  haveI := henselianLocalRing_intRing (k := k)
  have h := (HenselianLocalRing.TFAE (Valued.integer k)).out 1 2
  exact h.mp inferInstance f hf a₀ h₁ h₂

/-- **Hensel's lemma for the completion of a number field.** -/
theorem henselian_completion {K : Type*} [Field K] [NumberField K] (v : FinitePrime K)
    (f : Polynomial (Valued.integer (Completion K v))) (hf : f.Monic)
    (a₀ : Valued.integer (Completion K v))
    (h₁ : f.eval a₀ ∈ IsLocalRing.maximalIdeal (Valued.integer (Completion K v)))
    (h₂ : IsUnit (f.derivative.eval a₀)) :
    ∃ a : Valued.integer (Completion K v), f.IsRoot a ∧
      a - a₀ ∈ IsLocalRing.maximalIdeal (Valued.integer (Completion K v)) :=
  hensel_lift_root f hf a₀ h₁ h₂

end Work.LocalFields
