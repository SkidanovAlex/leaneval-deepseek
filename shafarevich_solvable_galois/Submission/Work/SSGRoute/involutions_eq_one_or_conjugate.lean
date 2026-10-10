import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Submission.Work.SSGRoute.InvAux.conjugate_of_ringEquiv
import Submission.Work.SSGRoute.InvAux.fixedFields_ringEquiv
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute

open InvAux

theorem involutions_eq_one_or_conjugate (c₁ c₂ : SSGRoute.GalQ)
    (h₁ : c₁ ^ 2 = 1) (h₂ : c₂ ^ 2 = 1) :
    c₁ = 1 ∨ c₂ = 1 ∨ ∃ σ : SSGRoute.GalQ, c₂ = σ * c₁ * σ⁻¹ := by
  by_cases hc1 : c₁ = 1
  · exact Or.inl hc1
  by_cases hc2 : c₂ = 1
  · exact Or.inr (Or.inl hc2)
  right; right
  have hc₁' : c₁.toRingEquiv * c₁.toRingEquiv = 1 := by
    ext x
    have h : (c₁ * c₁) x = (1 : SSGRoute.GalQ) x := by rw [← pow_two, h₁]
    simpa using h
  have hc₂' : c₂.toRingEquiv * c₂.toRingEquiv = 1 := by
    ext x
    have h : (c₂ * c₂) x = (1 : SSGRoute.GalQ) x := by rw [← pow_two, h₂]
    simpa using h
  have hn₁ : c₁.toRingEquiv ≠ 1 := by
    intro h
    refine hc1 (AlgEquiv.ext fun x => ?_)
    have := congrArg (fun f : SSGRoute.QBar ≃+* SSGRoute.QBar => f x) h
    simpa using this
  have hn₂ : c₂.toRingEquiv ≠ 1 := by
    intro h
    refine hc2 (AlgEquiv.ext fun x => ?_)
    have := congrArg (fun f : SSGRoute.QBar ≃+* SSGRoute.QBar => f x) h
    simpa using this
  haveI : Fact (c₁.toRingEquiv * c₁.toRingEquiv = 1) := ⟨hc₁'⟩
  haveI : Fact (c₂.toRingEquiv * c₂.toRingEquiv = 1) := ⟨hc₂'⟩
  haveI : Fact (c₁.toRingEquiv ≠ 1) := ⟨hn₁⟩
  haveI : Fact (c₂.toRingEquiv ≠ 1) := ⟨hn₂⟩
  obtain ⟨e⟩ := InvAux.fixedFields_ringEquiv (c₁ := c₁.toRingEquiv) (c₂ := c₂.toRingEquiv)
  obtain ⟨σe, hσe⟩ := InvAux.conjugate_of_ringEquiv hc₁' hc₂' hn₁ hn₂ e
  have hcomm : ∀ q : ℚ, σe (algebraMap ℚ SSGRoute.QBar q) = algebraMap ℚ SSGRoute.QBar q := by
    intro q
    simp
  let σa : SSGRoute.GalQ := AlgEquiv.ofRingEquiv (f := σe) hcomm
  refine ⟨σa, ?_⟩
  apply AlgEquiv.ext
  intro x
  have h := congrArg (fun f : SSGRoute.QBar ≃+* SSGRoute.QBar => f x) hσe
  change c₂ x = (σe * c₁.toRingEquiv * σe⁻¹) x
  exact h.symm

end Work.SSGRoute
