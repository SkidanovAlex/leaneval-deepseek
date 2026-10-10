import Mathlib
import Submission.Work.MotC5N3.Defs
import Submission.Work.MotC5N3.TwistField.asTwistFieldTrue_basic
import Submission.Work.MotC5N3.RigAS.twistFieldTrue_sup_asRoot
import Submission.Work.MotV.Defs
import Submission.Work.MotT.extend_algEquiv_of_linearDisjoint

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The ambient field `Ω = L(E)` of the AS link (general base field `K`)

Port of `Submission/Work/MotV5/LamAS/Setup.lean`.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Work.MotC5N3.LamAS

variable {𝕜 : Type} [Field 𝕜] {K : Type} [Field K] [Algebra 𝕜 K]

/-- The image of a subfield `L ⊆ KbA K` inside `OmA K D`. -/
noncomputable def LImage (D : Work.MotV.KleinData 𝕜)
    (L : IntermediateField K (KbA K)) :
    IntermediateField K (OmA K D) :=
  L.map (IsScalarTower.toAlgHom K (KbA K) (OmA K D))

/-- The ambient field `Ω = L(E)` of the LAM node. -/
noncomputable def Omega (D : Work.MotV.KleinData 𝕜)
    (L : IntermediateField K (KbA K)) :
    IntermediateField K (OmA K D) :=
  kleinField K D ⊔ LImage D L

theorem LImage_le_Omega (D : Work.MotV.KleinData 𝕜)
    (L : IntermediateField K (KbA K)) :
    LImage D L ≤ Omega D L := le_sup_right

theorem kleinField_le_Omega (D : Work.MotV.KleinData 𝕜)
    (L : IntermediateField K (KbA K)) :
    kleinField K D ≤ Omega D L := le_sup_left

/-- The Artin–Schreier root lies in `LImage` as soon as it lies in `L`. -/
theorem asRoot_mem_LImage (D : Work.MotV.KleinData 𝕜) (g : K)
    (L : IntermediateField K (KbA K))
    (hW : asRoot g ∈ L) :
    algebraMap (KbA K) (OmA K D) (asRoot g) ∈ LImage D L :=
  (IntermediateField.mem_map (S := L)
    (f := IsScalarTower.toAlgHom K (KbA K) (OmA K D))).mpr
    ⟨asRoot g, hW, rfl⟩

/-- The twist field is contained in `Ω` as soon as the Artin–Schreier root is in `L`. -/
theorem asTwistFieldTrue_le_Omega (D : Work.MotV.KleinData 𝕜) (g : K)
    (τ : OmA K D ≃ₐ[K] OmA K D)
    (σS : OmA K D ≃ₐ[KbA K] OmA K D)
    (L : IntermediateField K (KbA K))
    (hW : asRoot g ∈ L) :
    asTwistFieldTrue D g τ σS ≤ Omega D L := by
  have hKW : IntermediateField.adjoin K
      {algebraMap (KbA K) (OmA K D) (asRoot g)} ≤ LImage D L :=
    IntermediateField.adjoin_le_iff.mpr (fun y hy => by
      rw [Set.mem_singleton_iff] at hy
      subst hy
      exact asRoot_mem_LImage D g L hW)
  refine le_trans (asTwistFieldTrue_le_asFieldL D g τ σS) ?_
  exact sup_le le_sup_left (hKW.trans le_sup_right)

/-- Membership in `LImage`. -/
theorem mem_LImage_iff (D : Work.MotV.KleinData 𝕜)
    (L : IntermediateField K (KbA K)) (x : OmA K D) :
    x ∈ LImage D L ↔ ∃ c ∈ L, algebraMap (KbA K) (OmA K D) c = x :=
  IntermediateField.mem_map (S := L)
    (f := IsScalarTower.toAlgHom K (KbA K) (OmA K D))

/-- **The descent, intersection half.** -/
theorem asTwistFieldTrue_inf_LImage [CharP 𝕜 5] [CharP K 5]
    (D : Work.MotV.KleinData 𝕜) (hD : Work.MotV5.KleinData.ASGood D)
    (g : K) (τ : OmA K D ≃ₐ[K] OmA K D)
    (σS : OmA K D ≃ₐ[KbA K] OmA K D)
    (σ : KbA K ≃ₐ[K] KbA K)
    (hτ : ∀ c : KbA K,
      τ (algebraMap (KbA K) (OmA K D) c)
        = algebraMap (KbA K) (OmA K D) (σ c))
    (hσ : σ (asRoot g) = asRoot g + 1)
    (L : IntermediateField K (KbA K)) :
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
  exact (IsScalarTower.algebraMap_apply K (KbA K) (OmA K D) d).symm

/-- **The descent, generation half.** -/
theorem asTwistFieldTrue_sup_LImage [CharP 𝕜 5] [CharP K 5]
    (D : Work.MotV.KleinData 𝕜) (g : K)
    (τ : OmA K D ≃ₐ[K] OmA K D)
    (σS : OmA K D ≃ₐ[KbA K] OmA K D)
    (σ : KbA K ≃ₐ[K] KbA K)
    (h : ASTwistData 𝕜 D g τ σS σ)
    (L : IntermediateField K (KbA K)) (hW : asRoot g ∈ L) :
    asTwistFieldTrue D g τ σS ⊔ LImage D L = Omega D L := by
  refine le_antisymm (sup_le (asTwistFieldTrue_le_Omega D g τ σS L hW) (LImage_le_Omega D L)) ?_
  have hKW : IntermediateField.adjoin K
      {algebraMap (KbA K) (OmA K D) (asRoot g)} ≤ LImage D L :=
    IntermediateField.adjoin_le_iff.mpr (fun y hy => by
      rw [Set.mem_singleton_iff] at hy
      subst hy
      exact asRoot_mem_LImage D g L hW)
  have h1 := Work.MotC5N3.RigAS.twistFieldTrue_sup_asRoot 𝕜 D g τ σS σ h
  have hk : kleinField K D ≤ asTwistFieldTrue D g τ σS ⊔ LImage D L := by
    have h3 : kleinField K D ≤ asTwistFieldTrue D g τ σS ⊔ IntermediateField.adjoin K
        {algebraMap (KbA K) (OmA K D) (asRoot g)} := by
      rw [h1]
      exact le_sup_left
    exact h3.trans (sup_le_sup_left hKW _)
  exact sup_le hk le_sup_right

end Work.MotC5N3.LamAS
