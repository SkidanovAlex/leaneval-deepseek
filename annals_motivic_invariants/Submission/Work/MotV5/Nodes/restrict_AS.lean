import Mathlib
import Submission.Work.MotV5.ASTwistData
import Submission.Work.MotV5.Defs
import Submission.Work.MotV.Defs

set_option linter.unusedVariables false -- v435-speed

set_option maxHeartbeats 2000000

namespace Work.MotV5.Nodes

/-- **Node V1_AS (second half): the base automorphism induced by a `𝕜`-isomorphism of two twist
fields.**

Let `θ : F₁ ≃ₐ[𝕜] F₂` be a `𝕜`-algebra isomorphism of two Artin–Schreier twist fields which *maps
the base into the base* (`hθ`: for every `c : RatFunc 𝕜` there is `d` with
`θ (algebraMap c) = algebraMap d`) *and* such that the induced map on the base is onto (`hθ'`:
every `d` is hit).  Then there is `α : RatFunc 𝕜 ≃ₐ[𝕜] RatFunc 𝕜` with
`θ (algebraMap c) = algebraMap (α c)` for all `c`.

**Route.**  `hθ` makes `ψ c := (the d of hθ c)` well defined (the `algebraMap` of a field into a
field is injective), and `ψ` is a `𝕜`-algebra endomorphism of `RatFunc 𝕜`; `hθ'` says that `ψ` is
surjective, hence `α := AlgEquiv.ofBijective ψ ⟨injective, surjective⟩`.

**Why both directions.**  The one-directional input `hθ` is what the *proved*
`Work.MotV5.basePreserved_of_X` (`base_preserved_AS.lean`) delivers for `θ` and for `θ.symm` (step 5
of the design's V1); surjectivity of `ψ` does **not** follow from `hθ` alone (a `𝕜`-algebra
endomorphism of `𝕜(t)` such as `X ↦ X²` is injective but not surjective), which is why it is a
hypothesis here.  The sibling `Work.MotV.restrict_algEquiv` (proved) is the same statement for the
characteristic-`≠ 5` twist fields. -/
theorem restrict_AS (𝕜 : Type) [Field 𝕜] [CharP 𝕜 5] (D : Work.MotV.KleinData 𝕜)
    (hD : Work.MotV5.KleinData.ASGood D) (g₁ g₂ : RatFunc 𝕜)
    (τ₁ τ₂ : Work.MotV.Om D ≃ₐ[RatFunc 𝕜] Work.MotV.Om D)
    (σS : Work.MotV.Om D ≃ₐ[Work.MotV.Kb 𝕜] Work.MotV.Om D)
    (σ₁ σ₂ : Work.MotV.Kb 𝕜 ≃ₐ[RatFunc 𝕜] Work.MotV.Kb 𝕜)
    (h1 : Work.MotV5.ASTwistData 𝕜 D g₁ τ₁ σS σ₁)
    (h2 : Work.MotV5.ASTwistData 𝕜 D g₂ τ₂ σS σ₂)
    (θ : ↥(Work.MotV5.asTwistFieldTrue D g₁ τ₁ σS) ≃ₐ[𝕜]
      ↥(Work.MotV5.asTwistFieldTrue D g₂ τ₂ σS))
    (hθ : ∀ c : RatFunc 𝕜, ∃ d : RatFunc 𝕜,
      θ (algebraMap (RatFunc 𝕜) ↥(Work.MotV5.asTwistFieldTrue D g₁ τ₁ σS) c)
        = algebraMap (RatFunc 𝕜) ↥(Work.MotV5.asTwistFieldTrue D g₂ τ₂ σS) d)
    (hθ' : ∀ d : RatFunc 𝕜, ∃ c : RatFunc 𝕜,
      θ (algebraMap (RatFunc 𝕜) ↥(Work.MotV5.asTwistFieldTrue D g₁ τ₁ σS) c)
        = algebraMap (RatFunc 𝕜) ↥(Work.MotV5.asTwistFieldTrue D g₂ τ₂ σS) d) :
    ∃ α : RatFunc 𝕜 ≃ₐ[𝕜] RatFunc 𝕜, ∀ c : RatFunc 𝕜,
      θ (algebraMap (RatFunc 𝕜) ↥(Work.MotV5.asTwistFieldTrue D g₁ τ₁ σS) c)
        = algebraMap (RatFunc 𝕜) ↥(Work.MotV5.asTwistFieldTrue D g₂ τ₂ σS) (α c) := by
  classical
  -- choose the image `ψ c` of `c` on the base
  let ψ : RatFunc 𝕜 → RatFunc 𝕜 := fun c => Classical.choose (hθ c)
  have hψ : ∀ c, θ (algebraMap (RatFunc 𝕜) ↥(Work.MotV5.asTwistFieldTrue D g₁ τ₁ σS) c)
      = algebraMap (RatFunc 𝕜) ↥(Work.MotV5.asTwistFieldTrue D g₂ τ₂ σS) (ψ c) :=
    fun c => Classical.choose_spec (hθ c)
  have hinj₂ : Function.Injective
      (algebraMap (RatFunc 𝕜) ↥(Work.MotV5.asTwistFieldTrue D g₂ τ₂ σS)) := RingHom.injective _
  have hψ_one : ψ 1 = 1 := by
    refine hinj₂ ?_
    rw [← hψ 1]
    simp
  have hψ_zero : ψ 0 = 0 := by
    refine hinj₂ ?_
    rw [← hψ 0]
    simp
  have hψ_add : ∀ a b, ψ (a + b) = ψ a + ψ b := by
    intro a b
    refine hinj₂ ?_
    calc algebraMap (RatFunc 𝕜) ↥(Work.MotV5.asTwistFieldTrue D g₂ τ₂ σS) (ψ (a + b))
        = θ (algebraMap (RatFunc 𝕜) ↥(Work.MotV5.asTwistFieldTrue D g₁ τ₁ σS) (a + b)) :=
          (hψ (a + b)).symm
      _ = θ (algebraMap (RatFunc 𝕜) ↥(Work.MotV5.asTwistFieldTrue D g₁ τ₁ σS) a
              + algebraMap (RatFunc 𝕜) ↥(Work.MotV5.asTwistFieldTrue D g₁ τ₁ σS) b) := by
            rw [map_add]
      _ = θ (algebraMap (RatFunc 𝕜) ↥(Work.MotV5.asTwistFieldTrue D g₁ τ₁ σS) a)
            + θ (algebraMap (RatFunc 𝕜) ↥(Work.MotV5.asTwistFieldTrue D g₁ τ₁ σS) b) := by
            rw [map_add]
      _ = algebraMap (RatFunc 𝕜) ↥(Work.MotV5.asTwistFieldTrue D g₂ τ₂ σS) (ψ a)
            + algebraMap (RatFunc 𝕜) ↥(Work.MotV5.asTwistFieldTrue D g₂ τ₂ σS) (ψ b) := by
            rw [hψ a, hψ b]
      _ = algebraMap (RatFunc 𝕜) ↥(Work.MotV5.asTwistFieldTrue D g₂ τ₂ σS) (ψ a + ψ b) := by
            rw [map_add]
  have hψ_mul : ∀ a b, ψ (a * b) = ψ a * ψ b := by
    intro a b
    refine hinj₂ ?_
    calc algebraMap (RatFunc 𝕜) ↥(Work.MotV5.asTwistFieldTrue D g₂ τ₂ σS) (ψ (a * b))
        = θ (algebraMap (RatFunc 𝕜) ↥(Work.MotV5.asTwistFieldTrue D g₁ τ₁ σS) (a * b)) :=
          (hψ (a * b)).symm
      _ = θ (algebraMap (RatFunc 𝕜) ↥(Work.MotV5.asTwistFieldTrue D g₁ τ₁ σS) a
              * algebraMap (RatFunc 𝕜) ↥(Work.MotV5.asTwistFieldTrue D g₁ τ₁ σS) b) := by
            rw [map_mul]
      _ = θ (algebraMap (RatFunc 𝕜) ↥(Work.MotV5.asTwistFieldTrue D g₁ τ₁ σS) a)
            * θ (algebraMap (RatFunc 𝕜) ↥(Work.MotV5.asTwistFieldTrue D g₁ τ₁ σS) b) := by
            rw [map_mul]
      _ = algebraMap (RatFunc 𝕜) ↥(Work.MotV5.asTwistFieldTrue D g₂ τ₂ σS) (ψ a)
            * algebraMap (RatFunc 𝕜) ↥(Work.MotV5.asTwistFieldTrue D g₂ τ₂ σS) (ψ b) := by
            rw [hψ a, hψ b]
      _ = algebraMap (RatFunc 𝕜) ↥(Work.MotV5.asTwistFieldTrue D g₂ τ₂ σS) (ψ a * ψ b) := by
            rw [map_mul]
  have hψ_comm : ∀ r : 𝕜, ψ (algebraMap 𝕜 (RatFunc 𝕜) r) = algebraMap 𝕜 (RatFunc 𝕜) r := by
    intro r
    refine hinj₂ ?_
    calc algebraMap (RatFunc 𝕜) ↥(Work.MotV5.asTwistFieldTrue D g₂ τ₂ σS)
            (ψ (algebraMap 𝕜 (RatFunc 𝕜) r))
        = θ (algebraMap (RatFunc 𝕜) ↥(Work.MotV5.asTwistFieldTrue D g₁ τ₁ σS)
              (algebraMap 𝕜 (RatFunc 𝕜) r)) := (hψ _).symm
      _ = θ (algebraMap 𝕜 ↥(Work.MotV5.asTwistFieldTrue D g₁ τ₁ σS) r) := by
            rw [IsScalarTower.algebraMap_apply 𝕜 (RatFunc 𝕜)
              ↥(Work.MotV5.asTwistFieldTrue D g₁ τ₁ σS)]
      _ = algebraMap 𝕜 ↥(Work.MotV5.asTwistFieldTrue D g₂ τ₂ σS) r := θ.commutes r
      _ = algebraMap (RatFunc 𝕜) ↥(Work.MotV5.asTwistFieldTrue D g₂ τ₂ σS)
              (algebraMap 𝕜 (RatFunc 𝕜) r) := (IsScalarTower.algebraMap_apply 𝕜 (RatFunc 𝕜)
                ↥(Work.MotV5.asTwistFieldTrue D g₂ τ₂ σS) r).symm
  -- `ψ` is a `𝕜`-algebra endomorphism of the base, surjective by `hθ'`
  let ψ₀ : RatFunc 𝕜 →ₐ[𝕜] RatFunc 𝕜 :=
    AlgHom.mk ({ toFun := ψ, map_one' := hψ_one, map_mul' := hψ_mul, map_zero' := hψ_zero, map_add' := hψ_add } : RatFunc 𝕜 →+* RatFunc 𝕜) hψ_comm
  have hψ₀ : ∀ c, θ (algebraMap (RatFunc 𝕜) ↥(Work.MotV5.asTwistFieldTrue D g₁ τ₁ σS) c)
      = algebraMap (RatFunc 𝕜) ↥(Work.MotV5.asTwistFieldTrue D g₂ τ₂ σS) (ψ₀ c) := hψ
  have hsurj : Function.Surjective ψ₀ := by
    intro d
    obtain ⟨c, hc⟩ := hθ' d
    refine ⟨c, ?_⟩
    refine hinj₂ ?_
    rw [← hψ₀ c]
    exact hc
  have hinj₀ : Function.Injective ψ₀ := RingHom.injective _
  have hbij : Function.Bijective ψ₀ := ⟨hinj₀, hsurj⟩
  refine ⟨AlgEquiv.ofBijective ψ₀ hbij, ?_⟩
  intro c
  rw [AlgEquiv.ofBijective_apply]
  exact hψ₀ c

end Work.MotV5.Nodes
