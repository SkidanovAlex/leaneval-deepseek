import Mathlib
import Submission.Work.HallHigman.GLCore.restrictRep

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.HallHigman.GLCore

/-- **A minimal nonzero invariant submodule is irreducible.**  Let `σ : E →* End K V` act on `V`
and let `W ≤ V` be a nonzero `σ`-invariant submodule of `V` containing no proper nonzero
`σ`-invariant submodule.  Then `W` is irreducible for `E`:
`Work.HallHigman.IsIrreducibleFor (Set.range (restrictRep σ W hW))`, where `restrictRep` is the
restriction of `σ` to `W`
(`Work.HallHigman.restrictRep`, defined in `Submission/Work/HallHigman/GLCore/restrictRep.lean`,
with `restrictRep σ W hW e` the restriction of `σ e` to `W`). -/
lemma isIrreducibleFor_range_restrictRep {K : Type*} [Field K] {V : Type*} [AddCommGroup V]
    [Module K V] {E : Type*} [Monoid E] (σ : E →* Module.End K V) {W : Submodule K V}
    (hW : ∀ e : E, ∀ x ∈ W, σ e x ∈ W) (hWne : W ≠ ⊥)
    (hWmin : ∀ U : Submodule K V, U ≤ W → U ≠ ⊥ → (∀ e : E, ∀ x ∈ U, σ e x ∈ U) → U = W) :
    Work.HallHigman.IsIrreducibleFor (Set.range (restrictRep σ W hW)) := by
  refine ⟨?_, ?_⟩
  · rwa [Submodule.nontrivial_iff_ne_bot]
  · intro U hU
    have hinj : Function.Injective (Submodule.map (Submodule.subtype W)) :=
      Submodule.map_injective_of_injective (Submodule.subtype_injective W)
    have hU'inv : ∀ e : E, ∀ x ∈ U.map (Submodule.subtype W),
        σ e x ∈ U.map (Submodule.subtype W) := by
      intro e x hx
      obtain ⟨y, hy, hyx⟩ := Submodule.mem_map.mp hx
      rw [← hyx]
      refine Submodule.mem_map.mpr ⟨Work.HallHigman.restrictRep σ W hW e y, ?_, ?_⟩
      · have h := (hU (Work.HallHigman.restrictRep σ W hW e) (Set.mem_range_self e)) hy
        rwa [Submodule.mem_comap] at h
      · rw [Submodule.coe_subtype, Work.HallHigman.restrictRep_apply]
    by_cases hbot : U.map (Submodule.subtype W) = ⊥
    · left
      refine hinj ?_
      rw [hbot, Submodule.map_bot]
    · right
      have htop : U.map (Submodule.subtype W) = W :=
        hWmin _ (Submodule.map_subtype_le W U) hbot hU'inv
      refine hinj ?_
      rw [htop, Submodule.map_subtype_top]

end Work.HallHigman.GLCore
