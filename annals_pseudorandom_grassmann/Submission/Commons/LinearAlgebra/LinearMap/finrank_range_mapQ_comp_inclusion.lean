import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Quotient.Basic

namespace Commons.LinearAlgebra.LinearMap

/-- If `W ≤ W₂` and `W ⊔ ker X = W₂` (as submodules of the ambient space), then precomposing
`X : ↥W₂ → M` with the inclusion `↥W → ↥W₂` does not change the range. -/
theorem range_comp_submodule_inclusion_eq {R M C : Type*} [Semiring R] [AddCommMonoid M]
    [Module R M] [AddCommMonoid C] [Module R C] {W W₂ : Submodule R C} (hWW : W ≤ W₂)
    (X : ↥W₂ →ₗ[R] M) (h : W ⊔ Submodule.map W₂.subtype (LinearMap.ker X) = W₂) :
    LinearMap.range (X.comp (Submodule.inclusion hWW)) = LinearMap.range X := by
  have hrangee : Submodule.map W₂.subtype (LinearMap.range (Submodule.inclusion hWW)) = W := by
    rw [LinearMap.range_eq_map, ← Submodule.map_comp, Submodule.subtype_comp_inclusion,
      Submodule.map_subtype_top]
  have hsup : LinearMap.range (Submodule.inclusion hWW) ⊔ LinearMap.ker X = ⊤ := by
    apply Submodule.map_injective_of_injective (f := W₂.subtype) (Submodule.subtype_injective W₂)
    rw [Submodule.map_sup, hrangee, h, Submodule.map_subtype_top]
  have hkerX : Submodule.map X (LinearMap.ker X) = ⊥ := LinearMap.le_ker_iff_map.mp le_rfl
  rw [LinearMap.range_comp, ← Submodule.map_top X]
  conv_rhs => rw [← hsup]
  rw [Submodule.map_sup, hkerX, sup_bot_eq]

/-- If the kernel of `f` meets `p` trivially, then `f` is injective on `p`, so `p` and its image
have the same `finrank`. -/
theorem finrank_map_eq_of_disjoint_ker {R M N : Type*} [Ring R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] {f : M →ₗ[R] N} {p : Submodule R M}
    (h : p ⊓ LinearMap.ker f = ⊥) :
    Module.finrank R (Submodule.map f p) = Module.finrank R p := by
  have hker : LinearMap.ker (f.domRestrict p) = ⊥ := by
    rw [LinearMap.ker_domRestrict, Submodule.eq_bot_iff]
    intro x hx
    rw [Submodule.mem_comap] at hx
    have hmem : (x : M) ∈ p ⊓ LinearMap.ker f := ⟨x.2, hx⟩
    rw [h] at hmem
    have hx0 : (x : M) = 0 := by simpa using hmem
    exact Subtype.ext hx0
  have hf : Function.Injective (f.domRestrict p) := LinearMap.ker_eq_bot.mp hker
  have := LinearMap.finrank_range_of_inj hf
  rwa [LinearMap.range_domRestrict] at this

/-- **The rank is preserved when compressing a linear map to a pair of subspaces.**  Let `V₂ ≤ V₀`
be subspaces of `B` and `W ≤ W₂` subspaces of `C`, and let `X : ↥W₂ →ₗ[K] (B ⧸ V₂)`.  If
(i) `(V₀/V₂) ⊓ range X = ⊥` and (ii) `W + ker X = W₂`, then the compressed map
`mapQ V₂ V₀ ∘ X ∘ inclusion W` has the same rank as `X`. -/
theorem finrank_range_mapQ_comp_inclusion {K : Type*} [Field K] {B C : Type*}
    [AddCommGroup B] [Module K B] [Finite B] [AddCommGroup C] [Module K C] [Finite C]
    (V₂ V₀ : Submodule K B) (W W₂ : Submodule K C) (hVV : V₂ ≤ V₀) (hWW : W ≤ W₂)
    (X : ↥W₂ →ₗ[K] (B ⧸ V₂))
    (hkerV : (Submodule.map (Submodule.mkQ V₂) V₀) ⊓ LinearMap.range X = ⊥)
    (hkerW : W ⊔ Submodule.map W₂.subtype (LinearMap.ker X) = W₂) :
    Module.finrank K (LinearMap.range
        ((Submodule.mapQ V₂ V₀ LinearMap.id (by simpa using hVV)).comp
          (X.comp (Submodule.inclusion hWW))))
      = Module.finrank K (LinearMap.range X) := by
  have hqker : LinearMap.ker (Submodule.mapQ V₂ V₀ LinearMap.id (by simpa using hVV))
      = Submodule.map (Submodule.mkQ V₂) V₀ := by
    rw [Submodule.ker_mapQ, Submodule.comap_id]
  have hkerV' : LinearMap.range X
      ⊓ LinearMap.ker (Submodule.mapQ V₂ V₀ LinearMap.id (by simpa using hVV)) = ⊥ := by
    rw [inf_comm, hqker]; exact hkerV
  have hstep1 : LinearMap.range (X.comp (Submodule.inclusion hWW)) = LinearMap.range X :=
    range_comp_submodule_inclusion_eq hWW X hkerW
  have hstep2 : LinearMap.range
        ((Submodule.mapQ V₂ V₀ LinearMap.id (by simpa using hVV)).comp
          (X.comp (Submodule.inclusion hWW)))
      = Submodule.map (Submodule.mapQ V₂ V₀ LinearMap.id (by simpa using hVV))
          (LinearMap.range X) := by
    rw [LinearMap.range_comp, hstep1]
  have hstep3 : Module.finrank K
        (Submodule.map (Submodule.mapQ V₂ V₀ LinearMap.id (by simpa using hVV))
          (LinearMap.range X))
      = Module.finrank K (LinearMap.range X) :=
    finrank_map_eq_of_disjoint_ker hkerV'
  rw [hstep2, hstep3]

end Commons.LinearAlgebra.LinearMap