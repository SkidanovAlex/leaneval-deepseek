import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Work.SSGRoute.ZConstruction.ZDataInduction
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute

/-- Given a finite-dimensional `ZMod p`-vector space `E` of dimension at least `2`, there is a
decomposition `E = L ⊕ E₀` where `L` is a line (`finrank L = 1`), `E₀` is a hyperplane
(`finrank E₀ < finrank E`), together with the two linear projections fixing `E₀` resp. `L`
and summing to the identity. -/
theorem line_complement_decomposition (p : ℕ) [Fact p.Prime] (E : Type) [AddCommGroup E]
    [Module (ZMod p) E] [Finite E] (h : 2 ≤ Module.finrank (ZMod p) E) :
    ∃ (L E₀ : Submodule (ZMod p) E) (hc : IsCompl L E₀),
      Module.finrank (ZMod p) L = 1 ∧ Module.finrank (ZMod p) E₀ < Module.finrank (ZMod p) E ∧
      ∃ (π₀ : E →ₗ[ZMod p] ↥E₀) (π₁ : E →ₗ[ZMod p] ↥L),
        (∀ x : E, (π₀ x : E) + (π₁ x : E) = x) ∧
        (∀ x : E, x ∈ E₀ → (π₀ x : E) = x) ∧
        (∀ x : E, x ∈ L → (π₁ x : E) = x) := by
  -- `E` is a finite-dimensional `ZMod p`-vector space.
  haveI : FiniteDimensional (ZMod p) E := Module.Finite.of_finite
  -- Since `finrank E ≥ 2 > 0`, there is a nonzero vector.
  have hpos : 0 < Module.finrank (ZMod p) E := by omega
  obtain ⟨v, hv⟩ := Module.finrank_pos_iff_exists_ne_zero.mp hpos
  -- Take the line spanned by `v` and any complement `E₀` of it.
  obtain ⟨E₀, hc⟩ := Submodule.exists_isCompl (ZMod p ∙ v)
  refine ⟨ZMod p ∙ v, E₀, hc, finrank_span_singleton hv, ?_, ?_⟩
  · -- `E₀` is a proper subspace, hence has strictly smaller dimension.
    apply Submodule.finrank_lt
    intro hE₀
    have hL : (ZMod p ∙ v) = ⊥ := by
      have h1 := hc.inf_eq_bot
      rw [hE₀, inf_top_eq] at h1
      exact h1
    exact hv (Submodule.span_singleton_eq_bot.mp hL)
  · -- The two projections associated to the decomposition `E = L ⊕ E₀`.
    refine ⟨E₀.projectionOnto (ZMod p ∙ v) hc.symm, (ZMod p ∙ v).projectionOnto E₀ hc,
      ?_, ?_, ?_⟩
    · intro x
      rw [Submodule.coe_projectionOnto_apply, Submodule.coe_projectionOnto_apply, add_comm]
      exact Submodule.projection_add_projection_eq_self hc x
    · intro x hx
      rw [Submodule.projectionOnto_apply_of_mem_left _ hx]
    · intro x hx
      rw [Submodule.projectionOnto_apply_of_mem_left _ hx]

end Work.SSGRoute
