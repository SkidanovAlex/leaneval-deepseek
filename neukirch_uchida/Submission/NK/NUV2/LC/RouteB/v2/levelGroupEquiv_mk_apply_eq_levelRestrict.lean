import Mathlib
import Submission.NK.NUV2.LC.RouteB.level_kills_aux
import Submission.NK.HassePrinciple.LevelDictionary
import Submission.NK.BrauerHasse.Profinite

namespace NK.NUV2.LC.RouteB.v2

/-- **The computation rule of the level-group dictionary in the number-field form.**  Evaluating the
level-group dictionary `NK.NUV2.LC.RouteB.levelGroupEquiv V L` at an element `g` of the level
group `LevelGroup V L = ↥V ⧸ (V ⊓ Gal(K'/L))` and a point `x` of the level `L` gives the same
answer as evaluating the descended restriction map `NK.HassePrinciple.levelGroupRestrictHom V L`,
i.e. the restriction of a representative to `L`.

This is the same statement as `NK.NUV2.LC.RouteB.levelGroupEquiv_apply`, but *without* the
`NumberField K` hypothesis (the level dictionary itself needs only `[Field K] [Field K']
[Algebra K K'] [IsSepClosure K K']`).  Both sides are computed on the class of a representative
`v : ↥V`, where they are `v` acting on `x` (`NK.HassePrinciple.levelGroupRestrictHom_mk`). -/
lemma levelGroupEquiv_apply_eq_levelRestrictHom {K K' : Type} [Field K] [Field K']
    [Algebra K K'] [IsSepClosure K K'] (V : Subgroup Gal(K'/K))
    (L : FiniteGaloisIntermediateField K K') (g : NK.BrauerHasse.LevelGroup V L)
    (x : ↥(L : IntermediateField K K')) :
    (((NK.NUV2.LC.RouteB.levelGroupEquiv V L) g) x) =
      ((NK.HassePrinciple.levelGroupRestrictHom V L g :
        ↥(L : IntermediateField K K') ≃ₐ[K] ↥(L : IntermediateField K K')) x) := by
  induction g using QuotientGroup.induction_on with
  | H v => simp only [NK.NUV2.LC.RouteB.levelGroupEquiv,
      NK.HassePrinciple.levelGroupRestrictHom_mk]; rfl

/-- The level-group dictionary of the class of an element of `V` is its restriction. (Namespace `NK.NUV2.LC.RouteB.v2`.) -/
theorem levelGroupEquiv_mk_apply_eq_levelRestrict {K K' : Type} [Field K] [Field K']
    [Algebra K K'] [IsSepClosure K K'] (V : Subgroup Gal(K'/K))
    (M : FiniteGaloisIntermediateField K K') (σ : Gal(K'/K)) (hσ : σ ∈ V) :
    ∀ x : ↥(M : IntermediateField K K'),
      ((NK.NUV2.LC.RouteB.levelGroupEquiv V M) (QuotientGroup.mk (⟨σ, hσ⟩ : ↥V))) x
        = (NK.HassePrinciple.levelRestrict M σ) x := by
  intro x
  rw [levelGroupEquiv_apply_eq_levelRestrictHom V M (QuotientGroup.mk (⟨σ, hσ⟩ : ↥V)) x,
    NK.HassePrinciple.levelGroupRestrictHom_mk]

end NK.NUV2.LC.RouteB.v2
