import Mathlib
import Submission.Work.Q44Geom.Setup

set_option autoImplicit false

open Module

namespace Work.Q44Geom

/-- The coefficientwise coercion `ℤ^5 → ℚ^5` is injective. -/
lemma toRatLM_injective : Function.Injective (toRatLM : (Fin 5 → ℤ) → (Fin 5 → ℚ)) := by
  intro u v h
  funext i
  have hh : ((u i : ℤ) : ℚ) = ((v i : ℤ) : ℚ) := congrFun h i
  exact_mod_cast hh

/-- The `ℤ`-span of a subset of a `ℚ`-vector space is contained in its `ℚ`-span. -/
lemma span_int_subset_span_rat {V : Type*} [AddCommGroup V] [Module ℚ V] (s : Set V) :
    (↑(Submodule.span ℤ s) : Set V) ⊆ ↑(Submodule.span ℚ s) := by
  intro x hx
  have hle : Submodule.span ℤ s ≤ (Submodule.span ℚ s).restrictScalars ℤ :=
    Submodule.span_le.mpr (fun y hy => Submodule.subset_span hy)
  exact hle hx

/-- For a free finite `ℤ`-module `M` and an injective `ℤ`-linear map `ψ` into a `ℚ`-vector
space `V`, the `ℚ`-span of the range of `ψ` has `ℚ`-dimension `Module.finrank ℤ M`. -/
lemma finrank_span_range_eq (M V : Type*) [AddCommGroup M] [Module ℤ M] [Module.Free ℤ M]
    [Module.Finite ℤ M] [AddCommGroup V] [Module ℚ V] (ψ : M →ₗ[ℤ] V)
    (hψ : Function.Injective ψ) :
    Module.finrank ℚ (Submodule.span ℚ (Set.range ψ)) = Module.finrank ℤ M := by
  classical
  set b : Basis (Fin (Module.finrank ℤ M)) ℤ M := Module.finBasis ℤ M
  have hliZ : LinearIndependent ℤ (fun i => ψ (b i)) :=
    b.linearIndependent.map' ψ (LinearMap.ker_eq_bot.mpr hψ)
  have hliQ : LinearIndependent ℚ (fun i => ψ (b i)) :=
    (LinearIndependent.iff_fractionRing (R := ℤ) (K := ℚ)).mp hliZ
  have hspan : Submodule.span ℚ (Set.range ψ)
      = Submodule.span ℚ (Set.range fun i => ψ (b i)) := by
    refine le_antisymm ?_ (Submodule.span_mono ?_)
    · rw [Submodule.span_le]
      have hb : Submodule.span ℤ (Set.range (⇑b)) = ⊤ := b.span_eq
      have hmap : ψ.range = Submodule.span ℤ (Set.range fun i => ψ (b i)) := by
        rw [LinearMap.range_eq_map, ← hb, LinearMap.map_span, ← Set.range_comp]
        rfl
      have hcoe : (↑ψ.range : Set V) = Set.range ψ := LinearMap.coe_range ψ
      rw [← hcoe, hmap]
      exact span_int_subset_span_rat _
    · rintro y ⟨i, rfl⟩
      exact ⟨b i, rfl⟩
  have hcard := finrank_span_eq_card hliQ
  rw [hspan, hcard]
  exact Fintype.card_fin _

theorem ratSpan_finrank (L : Submodule ℤ (Fin 5 → ℤ)) (hL : Work.HP.rk L = 3) :
    Module.finrank ℚ (Work.Q44Geom.ratSpan L) = 3 := by
  classical
  have hψ : Function.Injective (toRatLM.comp (Submodule.subtype L)) := by
    intro x y hxy
    exact Subtype.ext
      (toRatLM_injective (show toRatLM (x : Fin 5 → ℤ) = toRatLM (y : Fin 5 → ℤ) from hxy))
  have hkey := finrank_span_range_eq L (Fin 5 → ℚ) (toRatLM.comp (Submodule.subtype L)) hψ
  have hrat : Work.Q44Geom.ratSpan L
      = Submodule.span ℚ (Set.range (toRatLM.comp (Submodule.subtype L))) := rfl
  rw [hrat, hkey]
  exact hL

end Work.Q44Geom
