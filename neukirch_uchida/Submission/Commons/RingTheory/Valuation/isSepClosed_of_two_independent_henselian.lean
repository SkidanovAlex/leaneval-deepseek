import Mathlib
import Submission.Commons.RingTheory.Valuation.unique_extension_of_henselian_finite
import Submission.Commons.RingTheory.Valuation.two_extensions_of_independent_henselian
import Submission.Commons.FieldTheory.isSepClosed_of_no_finite_separable_extension

set_option linter.style.haveILetI false

namespace Commons.RingTheory.Valuation

/-- **Neukirch–Uchida / F. K. Schmidt.** A field carrying two *independent* Henselian valuation
subrings is separably closed.

Concretely: if `C₁ ≠ ⊤` and `C₂ ≠ ⊤` are Henselian valuation subrings of `F` and no proper
valuation subring contains both of them, then `F` has no nontrivial finite separable extension.

The proof does not need the Henselisation/decomposition-type machinery directly: it uses
* the uniqueness of the extension of a Henselian valuation to a finite separable extension
  (`unique_extension_of_henselian_finite`), and
* the fact that two independent Henselian valuations force a *non-unique* extension once the
  extension is nontrivial (`two_extensions_of_independent_henselian`). -/
theorem isSepClosed_of_two_independent_henselian {F : Type*} [Field F] (C₁ C₂ : ValuationSubring F) (h₁ : C₁ ≠ ⊤) (h₂ : C₂ ≠ ⊤) (hind : ∀ D : ValuationSubring F, C₁ ≤ D → C₂ ≤ D → D = ⊤) (hhen₁ : HenselianLocalRing C₁) (hhen₂ : HenselianLocalRing C₂) : IsSepClosed F := by
  haveI := hhen₁
  haveI := hhen₂
  refine Commons.FieldTheory.isSepClosed_of_no_finite_separable_extension (F := F) ?_
  intro F' _ _ _ _
  by_contra hcon
  rw [not_le] at hcon
  obtain ⟨B₁, B₂, hne, hB₁, hB₂⟩ :=
    two_extensions_of_independent_henselian C₁ C₂ h₁ h₂ hind hcon
  exact hne (unique_extension_of_henselian_finite C₂ B₁ B₂ hB₁ hB₂)

end Commons.RingTheory.Valuation
