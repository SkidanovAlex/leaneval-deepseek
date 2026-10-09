import Mathlib
import Submission.NK.HassePrinciple.LocalUnits
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.CFTLib.Existence

open CategoryTheory in
theorem unitsRep_fixedPoints_eq_range_algebraMap {K M E : Type} [Field K] [Field M] [Field E]
    [Algebra K M] [Algebra K E] [Algebra M E] [IsScalarTower K M E] [FiniteDimensional K E]
    [IsGalois K E] (H : Subgroup (E ≃ₐ[K] E))
    (hH : ∀ σ : E ≃ₐ[K] E, σ ∈ H ↔ ∀ m : M, σ (algebraMap M E m) = algebraMap M E m)
    (u : Eˣ) :
    (∀ h : ↥H,
        (NK.HassePrinciple.unitsRep K E).ρ (h : E ≃ₐ[K] E) (Additive.ofMul u)
          = Additive.ofMul u) ↔
      ∃ v : Mˣ, Units.map (algebraMap M E).toMonoidHom v = u := by
  classical
  -- `M` inside `E`, as an intermediate field.
  set F : IntermediateField K E := (IsScalarTower.toAlgHom K M E).fieldRange with hF
  -- the hypothesis `hH` says precisely that `H` is the fixing subgroup of `F`
  have hHsub : H = F.fixingSubgroup := by
    ext σ
    rw [IntermediateField.mem_fixingSubgroup_iff]
    refine (hH σ).trans ⟨?_, ?_⟩
    · intro h x hx
      rw [hF, AlgHom.mem_fieldRange] at hx
      obtain ⟨m, rfl⟩ := hx
      exact h m
    · intro h m
      exact h _ (by rw [hF, AlgHom.mem_fieldRange]; exact ⟨m, rfl⟩)
  constructor
  · intro hfix
    -- `u` (as an element of `E`) lies in the fixed field of `H`
    have hmem : (↑u : E) ∈ IntermediateField.fixedField H := by
      rw [IntermediateField.mem_fixedField_iff]
      intro g hg
      have h2 : g • u = u := by
        have h1 := hfix ⟨g, hg⟩
        rw [show (NK.HassePrinciple.unitsRep K E).ρ g (Additive.ofMul u)
              = Additive.ofMul (g • u) from rfl] at h1
        exact Additive.ofMul.injective h1
      calc g (↑u : E) = ((g • u : Eˣ) : E) := by simp
        _ = ↑u := congrArg (fun x : Eˣ => (x : E)) h2
    -- the fixed field of `H` is exactly `F` (Galois correspondence, `E/K` finite Galois)
    rw [hHsub, IsGalois.fixedField_fixingSubgroup] at hmem
    obtain ⟨m, hm⟩ := AlgHom.mem_fieldRange.1 (hF ▸ hmem)
    refine ⟨Units.mk0 m ?_, ?_⟩
    · intro hm0
      rw [hm0, map_zero] at hm
      exact Units.ne_zero u hm.symm
    · apply Units.ext
      rw [Units.coe_map, Units.val_mk0]
      exact hm
  · rintro ⟨v, hv⟩ h
    -- `u` is in the image of `Mˣ`, hence fixed by every element of `H`
    have hg : ∀ m : M, (h : E ≃ₐ[K] E) (algebraMap M E m) = algebraMap M E m :=
      (hH _).1 h.2
    have h2 : (h : E ≃ₐ[K] E) • u = u := by
      rw [← hv]
      apply Units.ext
      show (((h : E ≃ₐ[K] E) • (Units.map (algebraMap M E).toMonoidHom v) : Eˣ) : E)
        = ((Units.map (algebraMap M E).toMonoidHom v) : E)
      rw [show (((h : E ≃ₐ[K] E) • (Units.map (algebraMap M E).toMonoidHom v) : Eˣ) : E)
            = (h : E ≃ₐ[K] E) ((Units.map (algebraMap M E).toMonoidHom v) : E) from by simp]
      rw [Units.coe_map]
      exact hg _
    rw [show (NK.HassePrinciple.unitsRep K E).ρ (h : E ≃ₐ[K] E) (Additive.ofMul u)
          = Additive.ofMul ((h : E ≃ₐ[K] E) • u) from rfl, h2]

end NK.CFTLib.Existence
