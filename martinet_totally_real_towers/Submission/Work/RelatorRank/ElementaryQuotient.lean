import Submission.Work.RelatorRank.Consequences
import Submission.Work.RelatorRank.GeneratorRank.le_generatorRank_of_surjective_elementaryAbelian

/-!
# `Work.RelatorRank` -- lower bounds on the generator rank from elementary abelian quotients

**Namespace** `Work.RelatorRank`; module `Submission.Work.RelatorRank.ElementaryQuotient`.

The *arithmetic* route to `Submission.NumberField.GeneratorMinimal K` (no four-element generating
family of `Γ = Gal(K/ℚ)`) goes through a continuous surjection `Γ ↠ (ℤ/2)^5` coming from the
multiquadratic level.  The group-theoretic content of that step is collected here: a continuous
surjection onto the elementary abelian `2`-group of rank `d` forces `GeneratorRank Γ ≥ d`, hence
rules out dense generating families of size `< d`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace Work.RelatorRank

variable {Γ : Type*} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]

/-- **A continuous surjection onto `(ℤ/2)^d` forces `GeneratorRank Γ ≥ d`** -- the tool that turns
the multiquadratic certificate of the arithmetic side into the minimality of a generating family. -/
theorem generatorRank_ge_of_surjective_elementaryAbelian {d : ℕ}
    (f : Γ →* (Fin d → Multiplicative (ZMod 2))) (hf : Continuous f)
    (hsurj : Function.Surjective f) (hex : ∃ m : ℕ, HasDenseGeneratingFamily Γ m) :
    d ≤ GeneratorRank Γ :=
  Work.RelatorRank.GeneratorRank.le_generatorRank_of_surjective_elementaryAbelian f hf hsurj hex

/-- Consequently there is no dense generating family of size `< d`. -/
theorem not_hasDenseGeneratingFamily_of_surjective_elementaryAbelian {d d' : ℕ} (hd' : d' < d)
    (f : Γ →* (Fin d → Multiplicative (ZMod 2))) (hf : Continuous f)
    (hsurj : Function.Surjective f) (hex : ∃ m : ℕ, HasDenseGeneratingFamily Γ m) :
    ¬ HasDenseGeneratingFamily Γ d' := by
  intro hgen
  have hle : d ≤ d' :=
    le_trans (generatorRank_ge_of_surjective_elementaryAbelian f hf hsurj hex)
      (generatorRank_le_of_hasDenseGeneratingFamily hgen)
  omega

end Work.RelatorRank
