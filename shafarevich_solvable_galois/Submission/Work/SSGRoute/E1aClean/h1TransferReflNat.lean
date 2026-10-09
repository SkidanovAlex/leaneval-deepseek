import Mathlib
import Submission.Work.SSGRoute.PT.H1Transfer
import Submission.Work.AbsoluteKummer.SES.range_mapH1_eq_ker_mapH1
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Naturality of the `H¹`-group-transfer at `Ψ = AddEquiv.refl`

`Work.SSGRoute.PT.h1Transfer Φ hΦ Ψ hΨ : H¹(G',M') ≃+ H¹(G,M)` transfers continuous cohomology
along a homeomorphic group isomorphism `Φ : G' ≃* G` and a compatible coefficient isomorphism
`Ψ`.  The local dictionary needs it at `Ψ = AddEquiv.refl`, where it is nothing but *reindexing*
the cocycles by `Φ.symm`, and — precisely because of that — it commutes with the pointwise
coefficient change `Work.AbsoluteKummer.mapH1 f`.

Both sides are computed by `h1TransferAddHom_mk` (`H¹π` then `z1Transfer`) and `mapH1_H1π`
(`H¹π` then `mapZ1`); at `Ψ = refl` the two transfers are `f ↦ f ∘ Φ.symm` on the nose, so the
comparison is `rfl` on representatives.  Coefficients therefore carry *two* actions, one for each
group, related by `hΨᵢ` (`g' • m = Φ g' • m`).
-/

namespace Work.SSGRoute.E1aClean

open Work.AbsoluteKummer

noncomputable section

/-- **Naturality of the group-transfer at `Ψ = AddEquiv.refl`** in the coefficient: for an
additive `f : M₁ →+ M₂` which is equivariant for both group actions, the transfer commutes with
the coefficient change. -/
theorem h1Transfer_refl_natural {G G' : Type*} [Group G] [TopologicalSpace G] [Group G']
    [TopologicalSpace G'] (Φ : G' ≃* G) (hΦc : Continuous (Φ.symm : G → G'))
    {M₁ M₂ : Type*} [AddCommGroup M₁] [AddCommGroup M₂]
    [DistribMulAction G' M₁] [DistribMulAction G M₁]
    [DistribMulAction G' M₂] [DistribMulAction G M₂]
    (hΨ₁ : ∀ (g' : G') (m : M₁), (AddEquiv.refl M₁) (g' • m) = Φ g' • (AddEquiv.refl M₁) m)
    (hΨ₂ : ∀ (g' : G') (m : M₂), (AddEquiv.refl M₂) (g' • m) = Φ g' • (AddEquiv.refl M₂) m)
    (f : M₁ →+ M₂) (hf : ∀ (g' : G') (m : M₁), f (g' • m) = g' • f m)
    (hfG : ∀ (g : G) (m : M₁), f (g • m) = g • f m)
    (c : ↥(Z1 G' M₁)) :
    Work.SSGRoute.PT.h1TransferAddHom Φ hΦc (AddEquiv.refl M₂) hΨ₂
        (Work.AbsoluteKummer.H1π G' M₂ (Work.AbsoluteKummer.mapZ1 f hf c))
      = Work.AbsoluteKummer.mapH1 f hfG
          (Work.SSGRoute.PT.h1TransferAddHom Φ hΦc (AddEquiv.refl M₁) hΨ₁
            (Work.AbsoluteKummer.H1π G' M₁ c)) := by
  rw [Work.SSGRoute.PT.h1TransferAddHom_mk, Work.SSGRoute.PT.h1TransferAddHom_mk]
  erw [Work.AbsoluteKummer.mapH1_H1π]
  congr 1

/-- **The `T`-half of the naturality of `h1contIsoH1loc`**: for the *inverse* transfer
`(h1Transfer Φ hΦ (AddEquiv.refl M) ·)⁻¹ : H¹(G,M) → H¹(G',M)`, naturality in the coefficient
reads `T₂⁻¹ (mapH1 f x) = mapH1 f (T₁⁻¹ x)`.

`(T)⁻¹` unfolds definitionally to `h1TransferAddHom Φ.symm … (AddEquiv.refl M) …` (the `invFun` of
`h1Transfer`), so on representatives this is `h1Transfer_refl_natural` at `Φ.symm`. -/
theorem h1Transfer_symm_refl_natural {G G' : Type*} [Group G] [TopologicalSpace G] [Group G']
    [TopologicalSpace G'] (Φ : G' ≃* G) (hΦ : IsHomeomorph (Φ : G' → G))
    {M₁ M₂ : Type*} [AddCommGroup M₁] [AddCommGroup M₂]
    [DistribMulAction G' M₁] [DistribMulAction G M₁]
    [DistribMulAction G' M₂] [DistribMulAction G M₂]
    (hΨ₁ : ∀ (g' : G') (m : M₁), (AddEquiv.refl M₁) (g' • m) = Φ g' • (AddEquiv.refl M₁) m)
    (hΨ₂ : ∀ (g' : G') (m : M₂), (AddEquiv.refl M₂) (g' • m) = Φ g' • (AddEquiv.refl M₂) m)
    (f : M₁ →+ M₂) (hf : ∀ (g : G) (m : M₁), f (g • m) = g • f m)
    (hfG : ∀ (g' : G') (m : M₁), f (g' • m) = g' • f m)
    (x : Work.AbsoluteKummer.H1 G M₁) :
    (Work.SSGRoute.PT.h1Transfer Φ hΦ (AddEquiv.refl M₂) hΨ₂).symm
        (Work.AbsoluteKummer.mapH1 f hf x)
      = Work.AbsoluteKummer.mapH1 f hfG
          ((Work.SSGRoute.PT.h1Transfer Φ hΦ (AddEquiv.refl M₁) hΨ₁).symm x) := by
  refine Work.AbsoluteKummer.SES.H1_induction_on (C := fun x =>
    (Work.SSGRoute.PT.h1Transfer Φ hΦ (AddEquiv.refl M₂) hΨ₂).symm
        (Work.AbsoluteKummer.mapH1 f hf x)
      = Work.AbsoluteKummer.mapH1 f hfG
          ((Work.SSGRoute.PT.h1Transfer Φ hΦ (AddEquiv.refl M₁) hΨ₁).symm x)) x ?_
  intro c
  erw [Work.AbsoluteKummer.mapH1_H1π]
  exact h1Transfer_refl_natural Φ.symm (by simpa using hΦ.continuous)
    (Work.SSGRoute.PT.symm_compat Φ (AddEquiv.refl M₁) hΨ₁)
    (Work.SSGRoute.PT.symm_compat Φ (AddEquiv.refl M₂) hΨ₂) f hf hfG c

end

end Work.SSGRoute.E1aClean
