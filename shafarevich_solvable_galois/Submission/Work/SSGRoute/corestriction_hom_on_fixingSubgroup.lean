import Mathlib
import Submission.Work.SSGRoute.Interfaces
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute

open _root_.SSGRoute
open scoped Pointwise

/-- The formal corestriction `X δ = ∑_{s : Gal(K/k)} s • y(sec(s)⁻¹ * δ * sec(s))` (the function that
occurs in the conclusion of Theorem 13 of Schmidt-Wingberg) is additive on `G_K = K.fixingSubgroup`
whenever `y` is additive there. -/
theorem corestriction_hom_on_fixingSubgroup (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k]
    [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    [Fintype (K ≃ₐ[k] K)]
    (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E]
    (y : (Ω ≃ₐ[k] Ω) → E)
    (hy : ∀ g ∈ K.fixingSubgroup, ∀ h ∈ K.fixingSubgroup, y (g * h) = y g + y h)
    (sec : (K ≃ₐ[k] K) → (Ω ≃ₐ[k] Ω)) (hsec : ∀ s, res k K (sec s) = s) :
    ∀ g ∈ K.fixingSubgroup, ∀ h ∈ K.fixingSubgroup,
      (∑ s : K ≃ₐ[k] K, s • y ((sec s)⁻¹ * (g * h) * sec s))
        = (∑ s : K ≃ₐ[k] K, s • y ((sec s)⁻¹ * g * sec s))
          + (∑ s : K ≃ₐ[k] K, s • y ((sec s)⁻¹ * h * sec s)) := by
  -- `K.fixingSubgroup` is the kernel of the restriction `res k K : G_k →* Gal(K/k)`.
  have hker : ∀ (u : Ω ≃ₐ[k] Ω), res k K u = 1 ↔ u ∈ K.fixingSubgroup := by
    intro u
    rw [show res k K u = u.restrictNormal K from rfl, AlgEquiv.restrictNormal_eq_one_iff,
      IntermediateField.mem_fixingSubgroup_iff]
  -- `G_K` is normal in `G_k`, because `K/k` is Galois (its elements are the kernel of `res k K`).
  have hconj : ∀ (σ : Ω ≃ₐ[k] Ω) (x : Ω ≃ₐ[k] Ω), x ∈ K.fixingSubgroup →
      σ⁻¹ * x * σ ∈ K.fixingSubgroup := by
    intro σ x hx
    rw [← hker]
    have hx1 : res k K x = 1 := (hker x).mpr hx
    rw [map_mul, map_mul, map_inv, hx1]
    simp
  intro g hg h hh
  -- Termwise additivity of `y` at the conjugates of `g`, `h` by `sec s`.
  have key : ∀ s : K ≃ₐ[k] K, y ((sec s)⁻¹ * (g * h) * sec s)
      = y ((sec s)⁻¹ * g * sec s) + y ((sec s)⁻¹ * h * sec s) := by
    intro s
    have hmul : (sec s)⁻¹ * (g * h) * sec s
        = ((sec s)⁻¹ * g * sec s) * ((sec s)⁻¹ * h * sec s) := by group
    rw [hmul]
    exact hy _ (hconj (sec s) g hg) _ (hconj (sec s) h hh)
  calc (∑ s : K ≃ₐ[k] K, s • y ((sec s)⁻¹ * (g * h) * sec s))
      = ∑ s : K ≃ₐ[k] K, s • (y ((sec s)⁻¹ * g * sec s) + y ((sec s)⁻¹ * h * sec s)) :=
        Finset.sum_congr rfl (fun s _ => by rw [key s])
    _ = ∑ s : K ≃ₐ[k] K,
          (s • y ((sec s)⁻¹ * g * sec s) + s • y ((sec s)⁻¹ * h * sec s)) :=
        Finset.sum_congr rfl (fun s _ => by rw [smul_add])
    _ = (∑ s : K ≃ₐ[k] K, s • y ((sec s)⁻¹ * g * sec s))
          + (∑ s : K ≃ₐ[k] K, s • y ((sec s)⁻¹ * h * sec s)) := Finset.sum_add_distrib

end Work.SSGRoute
