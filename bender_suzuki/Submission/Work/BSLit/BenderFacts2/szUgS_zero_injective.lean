import Mathlib
import Submission.Work.BSLit.BenderFacts2.Facts2SzDefs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.BSLit.BenderFacts2

open LeanEval.GroupTheory.Defs

lemma szUgS_zero_injective (n : ℕ) :
    Function.Injective (fun b : Submission.Sz.SzField n =>
      (⟨szUgS n 0 b, szUgS_mem_U n 0 b⟩ : ↥(Submission.Sz.szTwoGroupS n))) := by
  intro b₁ b₂ h
  -- equality in the subgroup `szTwoGroupS n` gives equality of the underlying `SzModel n` points
  have h1 : (szUgS n 0 b₁ : SzModel n) = szUgS n 0 b₂ := Subtype.ext_iff.mp h
  -- which in turn gives equality of the underlying `GL` elements
  have h2 : Submission.Sz.szUg n 0 b₁ = Submission.Sz.szUg n 0 b₂ := by
    have hh := Subtype.ext_iff.mp h1
    simpa only [szUgS_coe] using hh
  -- and the parametrisation `(a, b) ↦ u(a, b)` is injective
  have h3 : ((0, b₁) : Submission.Sz.SzField n × Submission.Sz.SzField n) = (0, b₂) :=
    Submission.Sz.szUg_injective n h2
  exact (Prod.ext_iff.mp h3).2

end Work.BSLit.BenderFacts2
