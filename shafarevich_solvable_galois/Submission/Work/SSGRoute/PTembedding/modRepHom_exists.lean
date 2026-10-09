import Mathlib
import Submission.Work.SSGRoute.PTDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.PTembedding

open CategoryTheory

set_option linter.dupNamespace false

/-- Every `G`-equivariant `𝔽_p`-linear map of coefficient modules is the underlying map of a
morphism of the associated `Rep Coeff G` representations (`Coeff = ULift ℤ`).  This is the
instance/coercion bridge needed to *construct* the morphism appearing in the naturality clause of
`Work.SSGRoute.ext_sha1_bridge` (E1b) and `Work.SSGRoute.ext_sha2_bridge` (E1a); the workspace
currently only ever *consumes* such a morphism as data. -/
lemma modRepHom_exists (p : ℕ) [Fact p.Prime] (G : Type) [Group G] {M₁ M₂ : Type}
    [AddCommGroup M₁] [Module (ZMod p) M₁] [DistribMulAction G M₁]
    [SMulCommClass G (ZMod p) M₁]
    [AddCommGroup M₂] [Module (ZMod p) M₂] [DistribMulAction G M₂]
    [SMulCommClass G (ZMod p) M₂]
    (f : M₂ →ₗ[ZMod p] M₁) (hf : ∀ (g : G) (m : M₂), f (g • m) = g • f m) :
    ∃ F : SSGRoute.PTExt.modRep G M₂ ⟶ SSGRoute.PTExt.modRep G M₁, ∀ m : M₂, F.hom m = f m := by
  -- The `Coeff = ULift ℤ`-scalars of `modRep` are the canonical integer multiples
  -- (`ULift.smul_def`), and every additive map is `ℤ`-linear, so the given `𝔽_p`-linear `f` is
  -- already `Coeff`-linear.  Equivariance is exactly `hf`.
  have hfl : ∀ (c : SSGRoute.PTExt.Coeff) (m : M₂), f (c • m) = c • f m := by
    intro c m
    rw [ULift.smul_def, ULift.smul_def]
    exact map_zsmul f c.down m
  let fl : M₂ →ₗ[SSGRoute.PTExt.Coeff] M₁ :=
    { toFun := f
      map_add' := map_add f
      map_smul' := hfl }
  refine ⟨Rep.ofHom (fl.intertwiningMap_of_isIntertwiningMap _ _ ?_), ?_⟩
  · intro g m
    exact hf g m
  · intro m
    rfl

namespace Work.SSGRoute.PTembedding

/-- The same statement under the doubly nested name
`Work.SSGRoute.PTembedding.Work.SSGRoute.PTembedding.modRepHom_exists`, inherited from the doubled
`namespace` line of the original request file; the advertised name
`Work.SSGRoute.PTembedding.modRepHom_exists` is the declaration above. -/
lemma modRepHom_exists (p : ℕ) [Fact p.Prime] (G : Type) [Group G] {M₁ M₂ : Type}
    [AddCommGroup M₁] [Module (ZMod p) M₁] [DistribMulAction G M₁]
    [SMulCommClass G (ZMod p) M₁]
    [AddCommGroup M₂] [Module (ZMod p) M₂] [DistribMulAction G M₂]
    [SMulCommClass G (ZMod p) M₂]
    (f : M₂ →ₗ[ZMod p] M₁) (hf : ∀ (g : G) (m : M₂), f (g • m) = g • f m) :
    ∃ F : SSGRoute.PTExt.modRep G M₂ ⟶ SSGRoute.PTExt.modRep G M₁, ∀ m : M₂, F.hom m = f m :=
  _root_.Work.SSGRoute.PTembedding.modRepHom_exists p G f hf

end Work.SSGRoute.PTembedding

end Work.SSGRoute.PTembedding
