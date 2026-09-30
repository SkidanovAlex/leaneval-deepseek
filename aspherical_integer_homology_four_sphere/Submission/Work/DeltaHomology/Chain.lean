import Mathlib
import ChallengeDeps
import Submission.Work.DeltaHomology.Basic
import Submission.Work.DeltaHomology.ChainDefs
import Submission.Work.DeltaHomology.chainD_comp
import Submission.Work.DeltaHomology.chainMapFun_comm

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The `Δ`-chain complex of a `Δ`-complex

Assembling the chain complex `K.chain` and its functoriality from the
definitions of `Submission/Work/DeltaHomology/ChainDefs.lean` and the
chain-level lemmas of the parallel files (see `Prelims.lean` for the temporary
import).

Main contents:

* `DeltaCx.chain` : `ChainComplex (ModuleCat ℤ) ℕ` with `chain.X k = ∐_{σ} ℤ`
  and `chain.d (k+1) k = ∑_i (-1)^i d_i`;
* `DeltaCx.chain_d` : the boundary on the chain complex;
* `DeltaCx.homology` : `H_k^Δ(K; ℤ)`;
* `DeltaCx.Hom.chainMap` : functoriality in simplicial maps, with the functor
  laws `chainMap_id`, `chainMap_comp`;
* `DeltaCx.chain_hom_ext` : a chain map out of `K.chain` is determined by its
  values on basis simplices.
-/

open CategoryTheory AlgebraicTopology CategoryTheory.Limits

open Work.Homology

set_option linter.unusedVariables false

namespace Work.DeltaHomology

noncomputable section

/-- The `Δ`-chain complex of `K`: free in each degree, with boundary the
alternating sum of the face maps. -/
def DeltaCx.chain (K : DeltaCx) : ChainComplex (ModuleCat ℤ) ℕ :=
  ChainComplex.of K.chainX K.chainD (chainD_comp K)

@[simp]
theorem DeltaCx.chain_X (K : DeltaCx) (k : ℕ) : K.chain.X k = K.chainX k := rfl

@[simp]
theorem DeltaCx.chain_d (K : DeltaCx) (k : ℕ) : K.chain.d (k + 1) k = K.chainD k :=
  ChainComplex.of_d ..

/-- The boundary of the chain complex on a basis simplex. -/
theorem DeltaCx.chain_d_chainι (K : DeltaCx) (k : ℕ) (σ : Fin (K.card (k + 1))) :
    K.chainι (k + 1) σ ≫ K.chain.d (k + 1) k
      = ∑ i : Fin (k + 2), (-1 : ℤ) ^ (i : ℕ) • K.chainι k (K.face σ i) := by
  rw [DeltaCx.chain_d]
  exact K.ι_chainD k σ

/-- `H_k^Δ(K; ℤ) = H_k(C_*^Δ(K))`, the `k`-th homology of the `Δ`-chain complex. -/
abbrev DeltaCx.homology (K : DeltaCx) (k : ℕ) : ModuleCat ℤ := K.chain.homology k

namespace DeltaCx.Hom

variable {K L M : DeltaCx}

/-- The morphism of chain complexes induced by a simplicial map of
`Δ`-complexes. -/
def chainMap (f : K.Hom L) : K.chain ⟶ L.chain :=
  ChainComplex.ofHom f.chainMapFun fun k => by
    rw [DeltaCx.chain_d, DeltaCx.chain_d]
    exact chainMapFun_comm f k

theorem chainMap_f (f : K.Hom L) (k : ℕ) : (chainMap f).f k = f.chainMapFun k := rfl

attribute [simp] chainMap_f

/-- The chain map on basis elements. -/
theorem chainMap_chainι (f : K.Hom L) (k : ℕ) (σ : Fin (K.card k)) :
    K.chainι k σ ≫ (chainMap f).f k = L.chainι k (f.map σ) :=
  f.chainMapFun_chainι k σ

/-- `chainMap` of the identity is the identity. -/
@[simp]
theorem chainMap_id (K : DeltaCx) : chainMap (Hom.id K) = 𝟙 K.chain := by
  apply HomologicalComplex.Hom.ext
  funext k
  rw [chainMap_f, chainMapFun_id]
  rfl

/-- `chainMap` is compatible with composition. -/
theorem chainMap_comp (f : K.Hom L) (g : L.Hom M) :
    chainMap (f.comp g) = chainMap f ≫ chainMap g := by
  apply HomologicalComplex.Hom.ext
  funext k
  rw [chainMap_f]
  exact chainMapFun_comp f g k

end DeltaCx.Hom

/-- A chain map out of `K.chain` is determined by its values on basis elements. -/
theorem DeltaCx.chain_hom_ext {K : DeltaCx} {D : ChainComplex (ModuleCat ℤ) ℕ}
    {φ ψ : K.chain ⟶ D}
    (h : ∀ (k : ℕ) (σ : Fin (K.card k)), K.chainι k σ ≫ φ.f k = K.chainι k σ ≫ ψ.f k) :
    φ = ψ := by
  apply HomologicalComplex.Hom.ext
  funext k
  exact DeltaCx.chainX_hom_ext fun σ => h k σ

end

end Work.DeltaHomology
