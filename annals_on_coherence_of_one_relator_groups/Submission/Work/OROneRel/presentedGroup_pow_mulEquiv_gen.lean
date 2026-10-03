import Mathlib
import Submission.Work.OROneRel.Basic

namespace Work.OROneRel

universe u v
theorem presentedGroup_pow_mulEquiv_gen {σ : Type u} {τ : Type v} (ψ : FreeGroup σ ≃* FreeGroup τ)
    (x : FreeGroup σ) (l : ℕ) :
    ∃ e : PresentedGroup ({x ^ l} : Set (FreeGroup σ)) ≃*
        PresentedGroup ({(ψ x) ^ l} : Set (FreeGroup τ)),
      e (PresentedGroup.mk ({x ^ l} : Set (FreeGroup σ)) x) =
        PresentedGroup.mk ({(ψ x) ^ l} : Set (FreeGroup τ)) (ψ x) := by
  -- `ψ` carries the singleton relator set `{x ^ l}` onto `{(ψ x) ^ l}`.
  have hset : (↑ψ : FreeGroup σ →* FreeGroup τ) '' ({x ^ l} : Set (FreeGroup σ))
      = ({(ψ x) ^ l} : Set (FreeGroup τ)) := by
    rw [Set.image_singleton]
    congr 1
    simp only [map_pow]
    rfl
  -- hence it carries the normal closure of `{x ^ l}` onto the normal closure of `{(ψ x) ^ l}`;
  -- this is exactly the compatibility datum needed for `QuotientGroup.congr`.
  have hmap : Subgroup.map (ψ : FreeGroup σ →* FreeGroup τ)
      (Subgroup.normalClosure ({x ^ l} : Set (FreeGroup σ))) =
      Subgroup.normalClosure ({(ψ x) ^ l} : Set (FreeGroup τ)) := by
    rw [Subgroup.map_normalClosure _ _ ψ.surjective, hset]
  refine ⟨QuotientGroup.congr (Subgroup.normalClosure ({x ^ l} : Set (FreeGroup σ)))
      (Subgroup.normalClosure ({(ψ x) ^ l} : Set (FreeGroup τ))) ψ hmap, ?_⟩
  change (QuotientGroup.congr _ _ ψ hmap) (QuotientGroup.mk x) = QuotientGroup.mk (ψ x)
  rw [QuotientGroup.congr_mk]

end Work.OROneRel
