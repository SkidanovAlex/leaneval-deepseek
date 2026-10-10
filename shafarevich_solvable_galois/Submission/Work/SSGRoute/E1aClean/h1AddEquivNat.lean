import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.Topology.Defs.Basic
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Algebra.GroupWithZero.Action.Defs
import Submission.Work.SSGRoute.h1_equiv_of_equiv
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Functoriality of `H¹(G,·)` in the coefficients, and naturality of `h1AddEquiv`

`Work.SSGRoute.H1Equiv.h1AddEquiv Φ` is `mapH1 Φ.toAddMonoidHom` with its two-sided inverse
`mapH1 Φ.symm.toAddMonoidHom`.  The assembly of the natural local dictionary
(`Work.SSGRoute.E1aClean.localDictFamilyNatural`) has one factor `h1AddEquiv Ψ_E`, whose
*naturality* in the coefficient module `E` is what is proved here:

* `mapH1_comp` — `mapH1` is functorial in additive maps on `H¹` (the on-`H¹π` version
  `AbsoluteKummer.mapH1_comp_H1π` is already on disk; this is the quotient version);
* `h1AddEquiv_natural` — if `Ψ₂ ∘ f = g ∘ Ψ₁` for equivariant additive maps, then
  `h1AddEquiv Ψ₂ (mapH1 f y) = mapH1 g (h1AddEquiv Ψ₁ y)`.
-/

namespace Work.SSGRoute.E1aClean

open Work.AbsoluteKummer

noncomputable section

variable {G : Type} [Group G] [TopologicalSpace G]

/-- **Functoriality of `mapH1` in the coefficients** (`H¹` version of
`AbsoluteKummer.mapH1_comp_H1π`). -/
theorem mapH1_comp {M N P : Type} [AddCommGroup M] [DistribMulAction G M]
    [AddCommGroup N] [DistribMulAction G N] [AddCommGroup P] [DistribMulAction G P]
    (φ : M →+ N) (ψ : N →+ P) (hφ : Work.GroupCohomology.IsEquivariant G φ)
    (hψ : Work.GroupCohomology.IsEquivariant G ψ) (y : H1 G M) :
    mapH1 (ψ.comp φ) (hψ.comp hφ) y = mapH1 ψ hψ (mapH1 φ hφ y) := by
  refine QuotientAddGroup.induction_on y ?_
  intro f
  change mapH1 (ψ.comp φ) (hψ.comp hφ) (H1π G M f)
    = mapH1 ψ hψ (mapH1 φ hφ (H1π G M f))
  exact mapH1_comp_H1π φ ψ hφ hψ f

/-- **Naturality of `h1AddEquiv` in the coefficient.**  If `Ψ₂ ∘ f = g ∘ Ψ₁` for equivariant
additive maps `f`, `g`, then the additive equivalence `h1AddEquiv Ψ` commutes with `mapH1 f` and
`mapH1 g`. -/
theorem h1AddEquiv_natural {M₁ M₂ N₁ N₂ : Type} [AddCommGroup M₁] [DistribMulAction G M₁]
    [AddCommGroup M₂] [DistribMulAction G M₂] [AddCommGroup N₁] [DistribMulAction G N₁]
    [AddCommGroup N₂] [DistribMulAction G N₂]
    (Ψ₁ : M₁ ≃+ N₁) (hΨ₁ : Work.GroupCohomology.IsEquivariant G Ψ₁.toAddMonoidHom)
    (hΨ₁' : Work.GroupCohomology.IsEquivariant G Ψ₁.symm.toAddMonoidHom)
    (Ψ₂ : M₂ ≃+ N₂) (hΨ₂ : Work.GroupCohomology.IsEquivariant G Ψ₂.toAddMonoidHom)
    (hΨ₂' : Work.GroupCohomology.IsEquivariant G Ψ₂.symm.toAddMonoidHom)
    (f : M₁ →+ M₂) (g : N₁ →+ N₂) (hf : Work.GroupCohomology.IsEquivariant G f)
    (hg : Work.GroupCohomology.IsEquivariant G g) (h : ∀ x, Ψ₂ (f x) = g (Ψ₁ x))
    (y : H1 G M₁) :
    H1Equiv.h1AddEquiv Ψ₂ hΨ₂ hΨ₂' (mapH1 f hf y)
      = mapH1 g hg (H1Equiv.h1AddEquiv Ψ₁ hΨ₁ hΨ₁' y) := by
  refine QuotientAddGroup.induction_on y ?_
  intro c
  change H1Equiv.h1AddEquiv Ψ₂ hΨ₂ hΨ₂' (mapH1 f hf (H1π G M₁ c))
      = mapH1 g hg (H1Equiv.h1AddEquiv Ψ₁ hΨ₁ hΨ₁' (H1π G M₁ c))
  calc H1Equiv.h1AddEquiv Ψ₂ hΨ₂ hΨ₂' (mapH1 f hf (H1π G M₁ c))
      = mapH1 (Ψ₂.toAddMonoidHom.comp f) (hΨ₂.comp hf) (H1π G M₁ c) :=
        (mapH1_comp_H1π f Ψ₂.toAddMonoidHom hf hΨ₂ c).symm
    _ = mapH1 (g.comp Ψ₁.toAddMonoidHom) (hg.comp hΨ₁) (H1π G M₁ c) := by
        rw [mapH1_H1π, mapH1_H1π]
        congr 1
        apply Subtype.ext
        funext x
        exact h (c.1 x)
    _ = mapH1 g hg (H1Equiv.h1AddEquiv Ψ₁ hΨ₁ hΨ₁' (H1π G M₁ c)) :=
        mapH1_comp_H1π Ψ₁.toAddMonoidHom g hΨ₁ hg c

end

end Work.SSGRoute.E1aClean
