import Mathlib
import Submission.Work.MotV5.LamAS.asPsi
import Submission.Work.MotV5.LamAS.Setup

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option linter.unusedSectionVars false

namespace Work.MotV5.LamAS

open IntermediateField

/-! ## General facts about images of intermediate fields along `K`-algebra homomorphisms

The base-change map `asIota : M = L(E) → Kb(E) = Om D` is injective, and the three statements of
`asF_transfer` are translated along it.  We collect here the general field-theoretic facts that
make the translation work: `map` is a left adjoint of `comap` (so it preserves `⊔`), it computes
images of `comap`s as `S ⊓ f.fieldRange`, and it preserves `⊥` and `⊓` for an injective `f`. -/

section General

variable {K L L' : Type} [Field K] [Field L] [Field L'] [Algebra K L] [Algebra K L']

private theorem map_top_eq_fieldRange (f : L →ₐ[K] L') :
    (⊤ : IntermediateField K L).map f = f.fieldRange := by
  ext y
  rw [IntermediateField.mem_map, AlgHom.mem_fieldRange]
  constructor
  · rintro ⟨x, -, rfl⟩; exact ⟨x, rfl⟩
  · rintro ⟨x, rfl⟩; exact ⟨x, trivial, rfl⟩

private theorem map_comap_eq_inf_fieldRange (f : L →ₐ[K] L') (S : IntermediateField K L') :
    (S.comap f).map f = S ⊓ f.fieldRange := by
  apply le_antisymm
  · refine le_inf ((IntermediateField.gc_map_comap f).l_le le_rfl) ?_
    calc (S.comap f).map f ≤ (⊤ : IntermediateField K L).map f := IntermediateField.map_mono f le_top
      _ = f.fieldRange := map_top_eq_fieldRange f
  · intro y hy
    rw [IntermediateField.mem_inf] at hy
    obtain ⟨hyS, hyR⟩ := hy
    obtain ⟨x, rfl⟩ := (AlgHom.mem_fieldRange (f := f)).mp hyR
    rw [IntermediateField.mem_map]
    exact ⟨x, hyS, rfl⟩

private theorem map_bot_eq (f : L →ₐ[K] L') : (⊥ : IntermediateField K L).map f = ⊥ := by
  apply le_antisymm
  · intro y hy
    rw [IntermediateField.mem_map] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    rw [IntermediateField.mem_bot] at hx ⊢
    obtain ⟨k, rfl⟩ := hx
    exact ⟨k, (f.commutes k).symm⟩
  · exact bot_le

private theorem map_sup_eq (f : L →ₐ[K] L') (S T : IntermediateField K L) :
    (S ⊔ T).map f = S.map f ⊔ T.map f :=
  (IntermediateField.gc_map_comap f).l_sup

private theorem map_inf_eq_of_injective (f : L →ₐ[K] L') (hf : Function.Injective f)
    (S T : IntermediateField K L) : (S ⊓ T).map f = S.map f ⊓ T.map f := by
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

variable {𝕜 : Type} [Field 𝕜] [CharP 𝕜 5]

/-- Compatibility of `asIota` with the constant inclusions `L → M = L(E)` and `Kb 𝕜 → Om D`. -/
theorem asIota_toAlgHom (D : Work.MotV.KleinData 𝕜) (f₁ f₂ : RatFunc 𝕜)
    (l : ↥(asL2 (𝕜 := 𝕜) f₁ f₂)) :
    asIota D f₁ f₂ (IsScalarTower.toAlgHom (RatFunc 𝕜) ↥(asL2 (𝕜 := 𝕜) f₁ f₂) (asML D f₁ f₂) l)
      = IsScalarTower.toAlgHom (RatFunc 𝕜) (Work.MotV.Kb 𝕜) (Work.MotV.Om D) l := by
  rw [IsScalarTower.toAlgHom_apply, asIota_algebraMap, IsScalarTower.toAlgHom_apply]

/-- **The constants of the `L`-model map onto the constants of the `Kb 𝕜`-model.**  The image of
`asLImageM D f₁ f₂ = L` inside `M = L(E)` under the base-change map `asIota` is
`LImage D (asL2 f₁ f₂) = L` inside `Om D = Kb 𝕜(E)`. -/
theorem asLImageM_map_asIota (D : Work.MotV.KleinData 𝕜) (f₁ f₂ : RatFunc 𝕜) :
    (asLImageM D f₁ f₂).map (asIota D f₁ f₂) = LImage D (asL2 (𝕜 := 𝕜) f₁ f₂) := by
  ext y
  constructor
  · intro hy
    rw [IntermediateField.mem_map] at hy
    obtain ⟨z, hz, hzy⟩ := hy
    rw [asLImageM, AlgHom.mem_fieldRange] at hz
    obtain ⟨l, hl⟩ := hz
    rw [LImage, IntermediateField.mem_map]
    refine ⟨(l : Work.MotV.Kb 𝕜), l.2, ?_⟩
    rw [← hzy, ← hl, asIota_toAlgHom]
  · intro hy
    rw [LImage, IntermediateField.mem_map] at hy
    obtain ⟨l, hl, hly⟩ := hy
    rw [IntermediateField.mem_map]
    refine ⟨IsScalarTower.toAlgHom (RatFunc 𝕜) ↥(asL2 (𝕜 := 𝕜) f₁ f₂) (asML D f₁ f₂) ⟨l, hl⟩, ?_, ?_⟩
    · rw [asLImageM, AlgHom.mem_fieldRange]; exact ⟨⟨l, hl⟩, rfl⟩
    · rw [← hly, asIota_toAlgHom]

/-- The twist field of a class `g ∈ {f₁, f₂}` pulled back to `M = L(E)` along the base-change map `asIota` lies in the image of `asIota`, generates `M` together with the constants `L`, and meets `L` in `K`. -/
theorem asF_transfer (𝕜 : Type) [Field 𝕜] [CharP 𝕜 5] (D : Work.MotV.KleinData 𝕜)
    (hD : Work.MotV5.KleinData.ASGood D) (f₁ f₂ g : RatFunc 𝕜)
    (τ : Work.MotV.Om D ≃ₐ[RatFunc 𝕜] Work.MotV.Om D)
    (σS : Work.MotV.Om D ≃ₐ[Work.MotV.Kb 𝕜] Work.MotV.Om D)
    (σ : Work.MotV.Kb 𝕜 ≃ₐ[RatFunc 𝕜] Work.MotV.Kb 𝕜)
    (h : Work.MotV5.ASTwistData 𝕜 D g τ σS σ) (hg : g = f₁ ∨ g = f₂)
    (hRange : (Work.MotV5.LamAS.asIota D f₁ f₂).fieldRange =
      Work.MotV5.kleinField D ⊔ Work.MotV5.LamAS.LImage D
        (Work.MotV5.LamAS.asL2 (𝕜 := 𝕜) f₁ f₂)) :
    Work.MotV5.asTwistFieldTrue D g τ σS ≤ (Work.MotV5.LamAS.asIota D f₁ f₂).fieldRange ∧
      Work.MotV5.LamAS.asF D f₁ f₂ g τ σS ⊔ Work.MotV5.LamAS.asLImageM D f₁ f₂ = ⊤ ∧
      Work.MotV5.LamAS.asF D f₁ f₂ g τ σS ⊓ Work.MotV5.LamAS.asLImageM D f₁ f₂ = ⊥ := by
  -- `asRoot g` is one of the two Artin–Schreier roots generating `L = asL2 f₁ f₂`.
  have hW : Work.MotV5.asRoot g ∈ asL2 (𝕜 := 𝕜) f₁ f₂ := by
    rcases hg with hg | hg
    · rw [hg]; exact asRoot_mem_asL2_left f₁ f₂
    · rw [hg]; exact asRoot_mem_asL2_right f₁ f₂
  -- Part 1: the twist field lies in `Ω = kleinField D ⊔ L`, which is the range of `asIota`.
  have hFle : Work.MotV5.asTwistFieldTrue D g τ σS ≤ (asIota D f₁ f₂).fieldRange := by
    rw [hRange]
    simpa only [Omega] using asTwistFieldTrue_le_Omega D g τ σS (asL2 (𝕜 := 𝕜) f₁ f₂) hW
  -- The image of `asF` under `asIota` is the twist field itself, and the image of `asLImageM`
  -- is `LImage`; both facts are used to translate the two compositum statements.
  have hFmap : (asF D f₁ f₂ g τ σS).map (asIota D f₁ f₂) = Work.MotV5.asTwistFieldTrue D g τ σS := by
    show ((Work.MotV5.asTwistFieldTrue D g τ σS).comap (asIota D f₁ f₂)).map (asIota D f₁ f₂)
      = Work.MotV5.asTwistFieldTrue D g τ σS
    rw [map_comap_eq_inf_fieldRange, inf_eq_left]
    exact hFle
  have hLmap := asLImageM_map_asIota (𝕜 := 𝕜) D f₁ f₂
  have hsup : Work.MotV5.asTwistFieldTrue D g τ σS ⊔ LImage D (asL2 (𝕜 := 𝕜) f₁ f₂) =
      Work.MotV5.kleinField D ⊔ LImage D (asL2 (𝕜 := 𝕜) f₁ f₂) := by
    simpa only [Omega] using asTwistFieldTrue_sup_LImage D g τ σS σ h (asL2 (𝕜 := 𝕜) f₁ f₂) hW
  have hinf : Work.MotV5.asTwistFieldTrue D g τ σS ⊓ LImage D (asL2 (𝕜 := 𝕜) f₁ f₂) = ⊥ :=
    asTwistFieldTrue_inf_LImage D hD g τ σS σ h.hτ h.hσ (asL2 (𝕜 := 𝕜) f₁ f₂)
  refine ⟨hFle, ?_, ?_⟩
  · -- Part 2: apply the injective `map (asIota)` and use `F ⊔ LImage = Ω = range asIota`.
    refine (IntermediateField.map_injective (asIota D f₁ f₂)) ?_
    rw [map_sup_eq (asIota D f₁ f₂), hFmap, hLmap, map_top_eq_fieldRange, hRange]
    exact hsup
  · -- Part 3: apply the injective `map (asIota)` and use `F ⊓ LImage = ⊥`.
    refine (IntermediateField.map_injective (asIota D f₁ f₂)) ?_
    rw [map_inf_eq_of_injective (asIota D f₁ f₂) (asIota_injective D f₁ f₂), hFmap, hLmap,
      map_bot_eq]
    exact hinf

end Work.MotV5.LamAS
