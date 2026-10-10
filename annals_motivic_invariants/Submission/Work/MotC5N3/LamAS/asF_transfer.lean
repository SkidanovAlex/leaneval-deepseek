import Mathlib
import Submission.Work.MotC5N3.LamAS.asML
import Submission.Work.MotC5N3.LamAS.Setup

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option linter.unusedSectionVars false

namespace Work.MotC5N3.LamAS

open IntermediateField

/-! ## General facts about images of intermediate fields along `K`-algebra homomorphisms -/

section General

variable {R L L' : Type} [Field R] [Field L] [Field L'] [Algebra R L] [Algebra R L']

private theorem map_top_eq_fieldRange (f : L →ₐ[R] L') :
    (⊤ : IntermediateField R L).map f = f.fieldRange := by
  ext y
  rw [IntermediateField.mem_map, AlgHom.mem_fieldRange]
  constructor
  · rintro ⟨x, -, rfl⟩; exact ⟨x, rfl⟩
  · rintro ⟨x, rfl⟩; exact ⟨x, trivial, rfl⟩

private theorem map_comap_eq_inf_fieldRange (f : L →ₐ[R] L') (S : IntermediateField R L') :
    (S.comap f).map f = S ⊓ f.fieldRange := by
  apply le_antisymm
  · refine le_inf ((IntermediateField.gc_map_comap f).l_le le_rfl) ?_
    calc (S.comap f).map f ≤ (⊤ : IntermediateField R L).map f := IntermediateField.map_mono f le_top
      _ = f.fieldRange := map_top_eq_fieldRange f
  · intro y hy
    rw [IntermediateField.mem_inf] at hy
    obtain ⟨hyS, hyR⟩ := hy
    obtain ⟨x, rfl⟩ := (AlgHom.mem_fieldRange (f := f)).mp hyR
    rw [IntermediateField.mem_map]
    exact ⟨x, hyS, rfl⟩

private theorem map_bot_eq (f : L →ₐ[R] L') : (⊥ : IntermediateField R L).map f = ⊥ := by
  apply le_antisymm
  · intro y hy
    rw [IntermediateField.mem_map] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    rw [IntermediateField.mem_bot] at hx ⊢
    obtain ⟨k, rfl⟩ := hx
    exact ⟨k, (f.commutes k).symm⟩
  · exact bot_le

private theorem map_sup_eq (f : L →ₐ[R] L') (S T : IntermediateField R L) :
    (S ⊔ T).map f = S.map f ⊔ T.map f :=
  (IntermediateField.gc_map_comap f).l_sup

private theorem map_inf_eq_of_injective (f : L →ₐ[R] L') (hf : Function.Injective f)
    (S T : IntermediateField R L) : (S ⊓ T).map f = S.map f ⊓ T.map f := by
  apply le_antisymm
  · exact le_inf (IntermediateField.map_mono f inf_le_left) (IntermediateField.map_mono f inf_le_right)
  · intro y hy
    rw [IntermediateField.mem_inf] at hy
    obtain ⟨hyS, hyT⟩ := hy
    rw [IntermediateField.mem_map] at hyS hyT ⊢
    obtain ⟨x, hxS, hx⟩ := hyS
    obtain ⟨x', hxT, hx'⟩ := hyT
    rw [← hx] at hx'
    have hxx : x' = x := hf hx'
    rw [hxx] at hxT
    exact ⟨x, ⟨hxS, hxT⟩, hx⟩

end General

variable {𝕜 : Type} [Field 𝕜] {K : Type} [Field K] [Algebra 𝕜 K]

/-- The twist field `asTwistFieldTrue D g τ σS`, pulled back to `M = L(E)` along the base-change
map `asIota`. -/
noncomputable def asF (D : Work.MotV.KleinData 𝕜) (f₁ f₂ g : K)
    (τ : OmA K D ≃ₐ[K] OmA K D)
    (σS : OmA K D ≃ₐ[KbA K] OmA K D) :
    IntermediateField K (asML D f₁ f₂) :=
  (asTwistFieldTrue D g τ σS).comap (asIota D f₁ f₂)

/-- Compatibility of `asIota` with the constant inclusions `L → M = L(E)` and `KbA K → OmA K D`. -/
theorem asIota_toAlgHom (D : Work.MotV.KleinData 𝕜) (f₁ f₂ : K)
    (l : ↥(asL2 f₁ f₂)) :
    asIota D f₁ f₂ (IsScalarTower.toAlgHom K ↥(asL2 f₁ f₂) (asML D f₁ f₂) l)
      = IsScalarTower.toAlgHom K (KbA K) (OmA K D) l := by
  rw [IsScalarTower.toAlgHom_apply, asIota_algebraMap, IsScalarTower.toAlgHom_apply]

/-- **The constants of the `L`-model map onto the constants of the `KbA K`-model.** -/
theorem asLImageM_map_asIota (D : Work.MotV.KleinData 𝕜) (f₁ f₂ : K) :
    (asLImageM D f₁ f₂).map (asIota D f₁ f₂) = LImage D (asL2 f₁ f₂) := by
  ext y
  constructor
  · intro hy
    rw [IntermediateField.mem_map] at hy
    obtain ⟨z, hz, hzy⟩ := hy
    rw [asLImageM, AlgHom.mem_fieldRange] at hz
    obtain ⟨l, hl⟩ := hz
    rw [LImage, IntermediateField.mem_map]
    refine ⟨(l : KbA K), l.2, ?_⟩
    rw [← hzy, ← hl, asIota_toAlgHom]
  · intro hy
    rw [LImage, IntermediateField.mem_map] at hy
    obtain ⟨l, hl, hly⟩ := hy
    rw [IntermediateField.mem_map]
    refine ⟨IsScalarTower.toAlgHom K ↥(asL2 f₁ f₂) (asML D f₁ f₂) ⟨l, hl⟩, ?_, ?_⟩
    · rw [asLImageM, AlgHom.mem_fieldRange]; exact ⟨⟨l, hl⟩, rfl⟩
    · rw [← hly, asIota_toAlgHom]

/-- The twist field of a class `g ∈ {f₁, f₂}` pulled back to `M = L(E)` along the base-change map
`asIota` lies in the image of `asIota`, generates `M` together with the constants `L`, and meets
`L` in `K`. -/
theorem asF_transfer (𝕜 : Type) [Field 𝕜] [CharP 𝕜 5] {K : Type} [Field K] [Algebra 𝕜 K]
    [CharP K 5] (D : Work.MotV.KleinData 𝕜)
    (hD : Work.MotV5.KleinData.ASGood D) (f₁ f₂ g : K)
    (τ : OmA K D ≃ₐ[K] OmA K D)
    (σS : OmA K D ≃ₐ[KbA K] OmA K D)
    (σ : KbA K ≃ₐ[K] KbA K)
    (h : ASTwistData 𝕜 D g τ σS σ) (hg : g = f₁ ∨ g = f₂)
    (hRange : (asIota D f₁ f₂).fieldRange =
      Work.MotC5N3.kleinField K D ⊔ LImage D (asL2 f₁ f₂)) :
    asTwistFieldTrue D g τ σS ≤ (asIota D f₁ f₂).fieldRange ∧
      asF D f₁ f₂ g τ σS ⊔ asLImageM D f₁ f₂ = ⊤ ∧
      asF D f₁ f₂ g τ σS ⊓ asLImageM D f₁ f₂ = ⊥ := by
  have hW : asRoot g ∈ asL2 f₁ f₂ := by
    rcases hg with hg | hg
    · rw [hg]; exact asRoot_mem_asL2_left f₁ f₂
    · rw [hg]; exact asRoot_mem_asL2_right f₁ f₂
  have hFle : asTwistFieldTrue D g τ σS ≤ (asIota D f₁ f₂).fieldRange := by
    rw [hRange]
    simpa only [Omega] using asTwistFieldTrue_le_Omega D g τ σS (asL2 f₁ f₂) hW
  have hFmap : (asF D f₁ f₂ g τ σS).map (asIota D f₁ f₂) = asTwistFieldTrue D g τ σS := by
    show ((asTwistFieldTrue D g τ σS).comap (asIota D f₁ f₂)).map (asIota D f₁ f₂)
      = asTwistFieldTrue D g τ σS
    rw [map_comap_eq_inf_fieldRange, inf_eq_left]
    exact hFle
  have hLmap := asLImageM_map_asIota (𝕜 := 𝕜) D f₁ f₂
  have hsup : asTwistFieldTrue D g τ σS ⊔ LImage D (asL2 f₁ f₂) =
      Work.MotC5N3.kleinField K D ⊔ LImage D (asL2 f₁ f₂) := by
    simpa only [Omega] using asTwistFieldTrue_sup_LImage D g τ σS σ h (asL2 f₁ f₂) hW
  have hinf : asTwistFieldTrue D g τ σS ⊓ LImage D (asL2 f₁ f₂) = ⊥ :=
    asTwistFieldTrue_inf_LImage D hD g τ σS σ h.hτ h.hσ (asL2 f₁ f₂)
  refine ⟨hFle, ?_, ?_⟩
  · refine (IntermediateField.map_injective (asIota D f₁ f₂)) ?_
    rw [map_sup_eq (asIota D f₁ f₂), hFmap, hLmap, map_top_eq_fieldRange, hRange]
    exact hsup
  · refine (IntermediateField.map_injective (asIota D f₁ f₂)) ?_
    rw [map_inf_eq_of_injective (asIota D f₁ f₂) (asIota_injective D f₁ f₂), hFmap, hLmap,
      map_bot_eq]
    exact hinf

end Work.MotC5N3.LamAS
