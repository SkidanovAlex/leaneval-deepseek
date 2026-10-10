import Mathlib
import Submission.Work.MotV5.Defs
import Submission.Work.MotV5.ASTwistData
import Submission.Work.MotV5.asTwistFieldTrue_basic
import Submission.Work.MotV5.RigAS.twistFieldTrue_sup_asRoot
import Submission.Work.MotV5.RigAS.kleinField_le_twistFieldTrue
import Submission.Work.MotV.Defs
import Submission.Work.MotT.extend_algEquiv_of_linearDisjoint

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The ambient field `Ω = L(E)` of the AS link

For a subfield `L ⊆ Kb 𝕜` of the algebraic closure of `K = RatFunc 𝕜`, the ambient field of the LAM
node of the characteristic-`5` branch is `Ω = kleinField D ⊔ L` — the function field of the Klein
model base changed to `L` — sitting inside `Om D = Kb 𝕜(E)`.

The descent facts proved here are the two halves needed by
`Work.MotT.extend_algEquiv_of_linearDisjoint` in order to extend a `K`-algebra isomorphism of two
twist fields to an automorphism of `Ω` over `L`:

* `asTwistFieldTrue_inf_LImage` : the twist field meets the constants in `K`;
* `asTwistFieldTrue_sup_LImage` : the twist field together with `L` generates `Ω`.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Work.MotV5.LamAS

variable {𝕜 : Type} [Field 𝕜] [CharP 𝕜 5]

/-- The image of a subfield `L ⊆ Kb 𝕜` inside `Om D = Kb 𝕜(E)`. -/
noncomputable def LImage (D : Work.MotV.KleinData 𝕜)
    (L : IntermediateField (RatFunc 𝕜) (Work.MotV.Kb 𝕜)) :
    IntermediateField (RatFunc 𝕜) (Work.MotV.Om D) :=
  L.map (IsScalarTower.toAlgHom (RatFunc 𝕜) (Work.MotV.Kb 𝕜) (Work.MotV.Om D))

/-- The ambient field `Ω = L(E)` of the LAM node. -/
noncomputable def Omega (D : Work.MotV.KleinData 𝕜)
    (L : IntermediateField (RatFunc 𝕜) (Work.MotV.Kb 𝕜)) :
    IntermediateField (RatFunc 𝕜) (Work.MotV.Om D) :=
  kleinField D ⊔ LImage D L

theorem LImage_le_Omega (D : Work.MotV.KleinData 𝕜)
    (L : IntermediateField (RatFunc 𝕜) (Work.MotV.Kb 𝕜)) :
    LImage D L ≤ Omega D L := le_sup_right

theorem kleinField_le_Omega (D : Work.MotV.KleinData 𝕜)
    (L : IntermediateField (RatFunc 𝕜) (Work.MotV.Kb 𝕜)) :
    kleinField D ≤ Omega D L := le_sup_left

/-- The Artin–Schreier root lies in `LImage` as soon as it lies in `L`. -/
theorem asRoot_mem_LImage (D : Work.MotV.KleinData 𝕜) (g : RatFunc 𝕜)
    (L : IntermediateField (RatFunc 𝕜) (Work.MotV.Kb 𝕜))
    (hW : Work.MotV5.asRoot g ∈ L) :
    algebraMap (Work.MotV.Kb 𝕜) (Work.MotV.Om D) (Work.MotV5.asRoot g) ∈ LImage D L :=
  (IntermediateField.mem_map (S := L)
    (f := IsScalarTower.toAlgHom (RatFunc 𝕜) (Work.MotV.Kb 𝕜) (Work.MotV.Om D))).mpr
    ⟨Work.MotV5.asRoot g, hW, rfl⟩

/-- The twist field is contained in `Ω` as soon as the Artin–Schreier root is in `L`. -/
theorem asTwistFieldTrue_le_Omega (D : Work.MotV.KleinData 𝕜) (g : RatFunc 𝕜)
    (τ : Work.MotV.Om D ≃ₐ[RatFunc 𝕜] Work.MotV.Om D)
    (σS : Work.MotV.Om D ≃ₐ[Work.MotV.Kb 𝕜] Work.MotV.Om D)
    (L : IntermediateField (RatFunc 𝕜) (Work.MotV.Kb 𝕜))
    (hW : Work.MotV5.asRoot g ∈ L) :
    asTwistFieldTrue D g τ σS ≤ Omega D L := by
  have hKW : IntermediateField.adjoin (RatFunc 𝕜)
      {algebraMap (Work.MotV.Kb 𝕜) (Work.MotV.Om D) (Work.MotV5.asRoot g)} ≤ LImage D L :=
    IntermediateField.adjoin_le_iff.mpr (fun y hy => by
      rw [Set.mem_singleton_iff] at hy
      subst hy
      exact asRoot_mem_LImage D g L hW)
  refine le_trans (asTwistFieldTrue_le_asFieldL D g τ σS) ?_
  exact sup_le le_sup_left (hKW.trans le_sup_right)

/-- Membership in `LImage`. -/
theorem mem_LImage_iff (D : Work.MotV.KleinData 𝕜)
    (L : IntermediateField (RatFunc 𝕜) (Work.MotV.Kb 𝕜)) (x : Work.MotV.Om D) :
    x ∈ LImage D L ↔ ∃ c ∈ L, algebraMap (Work.MotV.Kb 𝕜) (Work.MotV.Om D) c = x :=
  IntermediateField.mem_map (S := L)
    (f := IsScalarTower.toAlgHom (RatFunc 𝕜) (Work.MotV.Kb 𝕜) (Work.MotV.Om D))

/-- **The descent, intersection half.**  A constant of the twist field is rational, so the twist
field meets the constants `L` only in `K`. -/
theorem asTwistFieldTrue_inf_LImage (D : Work.MotV.KleinData 𝕜) (hD : KleinData.ASGood D)
    (g : RatFunc 𝕜) (τ : Work.MotV.Om D ≃ₐ[RatFunc 𝕜] Work.MotV.Om D)
    (σS : Work.MotV.Om D ≃ₐ[Work.MotV.Kb 𝕜] Work.MotV.Om D)
    (σ : Work.MotV.Kb 𝕜 ≃ₐ[RatFunc 𝕜] Work.MotV.Kb 𝕜)
    (hτ : ∀ c : Work.MotV.Kb 𝕜,
      τ (algebraMap (Work.MotV.Kb 𝕜) (Work.MotV.Om D) c)
        = algebraMap (Work.MotV.Kb 𝕜) (Work.MotV.Om D) (σ c))
    (hσ : σ (Work.MotV5.asRoot g) = Work.MotV5.asRoot g + 1)
    (L : IntermediateField (RatFunc 𝕜) (Work.MotV.Kb 𝕜)) :
    asTwistFieldTrue D g τ σS ⊓ LImage D L = ⊥ := by
  refine le_antisymm ?_ bot_le
  intro x hx
  rw [IntermediateField.mem_inf] at hx
  obtain ⟨hxF, hxL⟩ := hx
  obtain ⟨c, -, hc⟩ := (mem_LImage_iff D L x).mp hxL
  subst hc
  obtain ⟨d, hd⟩ := (algebraMap_mem_asTwistFieldTrue_iff D hD.1 g τ σS σ hτ hσ c).mp hxF
  rw [IntermediateField.mem_bot]
  refine ⟨d, ?_⟩
  rw [← hd]
  exact (IsScalarTower.algebraMap_apply (RatFunc 𝕜) (Work.MotV.Kb 𝕜) (Work.MotV.Om D) d).symm

/-- **The descent, generation half.**  The twist field together with the constants `L` generates
`Ω = L(E)`. -/
theorem asTwistFieldTrue_sup_LImage (D : Work.MotV.KleinData 𝕜) (g : RatFunc 𝕜)
    (τ : Work.MotV.Om D ≃ₐ[RatFunc 𝕜] Work.MotV.Om D)
    (σS : Work.MotV.Om D ≃ₐ[Work.MotV.Kb 𝕜] Work.MotV.Om D)
    (σ : Work.MotV.Kb 𝕜 ≃ₐ[RatFunc 𝕜] Work.MotV.Kb 𝕜)
    (h : ASTwistData 𝕜 D g τ σS σ)
    (L : IntermediateField (RatFunc 𝕜) (Work.MotV.Kb 𝕜)) (hW : Work.MotV5.asRoot g ∈ L) :
    asTwistFieldTrue D g τ σS ⊔ LImage D L = Omega D L := by
  refine le_antisymm (sup_le (asTwistFieldTrue_le_Omega D g τ σS L hW) (LImage_le_Omega D L)) ?_
  have hKW : IntermediateField.adjoin (RatFunc 𝕜)
      {algebraMap (Work.MotV.Kb 𝕜) (Work.MotV.Om D) (Work.MotV5.asRoot g)} ≤ LImage D L :=
    IntermediateField.adjoin_le_iff.mpr (fun y hy => by
      rw [Set.mem_singleton_iff] at hy
      subst hy
      exact asRoot_mem_LImage D g L hW)
  have h1 := RigAS.twistFieldTrue_sup_asRoot 𝕜 D g τ σS σ h
  have hk : kleinField D ≤ asTwistFieldTrue D g τ σS ⊔ LImage D L := by
    have h3 : kleinField D ≤ asTwistFieldTrue D g τ σS ⊔ IntermediateField.adjoin (RatFunc 𝕜)
        {algebraMap (Work.MotV.Kb 𝕜) (Work.MotV.Om D) (Work.MotV5.asRoot g)} := by
      rw [h1]
      exact le_sup_left
    exact h3.trans (sup_le_sup_left hKW _)
  exact sup_le hk le_sup_right

end Work.MotV5.LamAS
