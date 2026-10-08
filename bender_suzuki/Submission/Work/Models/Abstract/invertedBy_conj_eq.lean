import Mathlib
import Submission.Work.Models.Basic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Models.Abstract

/-- Conjugation transports `J(X,t)` to `J(X^g, g t g⁻¹)`; specialising `t = g⁻¹ u g` and
using `g * (g⁻¹ u g) * g⁻¹ = u` gives the stated form. -/
theorem invertedBy_conj_eq {G : Type*} [Group G] (X : Subgroup G) (g u : G) :
    Submission.Blueprint.invertedBy (Submission.Blueprint.conj g X) u
      = (fun x => g * x * g⁻¹) '' Submission.Blueprint.invertedBy X (g⁻¹ * u * g) := by
  have h := Work.Models.invertedBy_conj (X := X) (t := g⁻¹ * u * g) (g := g)
  have hg : g * (g⁻¹ * u * g) * g⁻¹ = u := by group
  rw [hg] at h
  exact h

end Work.Models.Abstract
