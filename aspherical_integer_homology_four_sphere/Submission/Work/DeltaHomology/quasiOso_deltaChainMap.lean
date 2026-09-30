import Mathlib
import Submission.Work.DeltaHomology.quasiOso_deltaChainMapSkel
import Submission.Work.DeltaHomology.SkelProps
import Submission.Work.DeltaHomology.Skeleton
import Submission.Work.DeltaHomology.SkeletonMap
import Submission.Work.DeltaHomology.Realization
import Submission.Work.DeltaHomology.SkelChain

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.DeltaHomology

open CategoryTheory AlgebraicTopology CategoryTheory.Limits Convexity Work.Homology

namespace Work.DeltaHomology

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

/-! ## The `dim`-skeleton of a `Δ`-complex is the complex itself

`DeltaCx.skel_self_card` says that the `j`-simplices of the `dim`-skeleton of `K` are the
`j`-simplices of `K`.  The inclusion `K.skelHom K.dim : K.skel K.dim ⟶ K` is therefore a
bijection on simplices in every degree, and we record here that the induced chain map
`DeltaCx.Hom.chainMap (K.skelHom K.dim) : (K.skel K.dim).chain ⟶ K.chain` is an isomorphism of
chain complexes, hence a quasi-isomorphism.  This is the second cancellation input in
`quasiOso_deltaChainMap`.
-/

/-- The number of `j`-simplices of the `dim`-skeleton of `K` is the number of `j`-simplices of
`K`.  (Restatement of `DeltaCx.skel_self_card` with the skeleton's `card` unfolded, so that it
can be used to build the `Fin.cast` indices below.) -/
theorem skelCard_self (K : DeltaCx) (n : ℕ) : skelCard K K.dim n = K.card n :=
  DeltaCx.skel_self_card K n

/-- The inclusion of the `dim`-skeleton is a bijection on simplex indices, and this is its
inverse. -/
theorem skelMap_cast_self (K : DeltaCx) {n : ℕ} (τ : Fin (K.card n)) :
    skelMap K K.dim (Fin.cast (skelCard_self K n).symm τ) = τ := by
  by_cases h : n ≤ K.dim
  · rw [skelMap_eq K K.dim h]
    apply Fin.ext
    rw [Fin.val_cast, Fin.val_cast]
  · have h0 : K.card n = 0 := K.card_eq_zero n (by omega)
    exact Fin.elim0 (h0 ▸ τ)

/-- The inverse of the inclusion of the `dim`-skeleton on simplex indices. -/
theorem cast_skelMap_self (K : DeltaCx) {n : ℕ} (σ : Fin (skelCard K K.dim n)) :
    Fin.cast (skelCard_self K n).symm (skelMap K K.dim σ) = σ := by
  by_cases h : n ≤ K.dim
  · rw [skelMap_eq K K.dim h]
    apply Fin.ext
    rw [Fin.val_cast, Fin.val_cast]
  · have h0 : skelCard K K.dim n = 0 := skelCard_eq_zero K (by omega)
    exact Fin.elim0 (h0 ▸ σ)

/-- The inverse of the `n`-th component of the chain map `chainMap (K.skelHom K.dim)`, given on
the basis `n`-simplices of `K`. -/
noncomputable def skelSelfInvFun (K : DeltaCx) (n : ℕ) :
    K.chainX n ⟶ (K.skel K.dim).chainX n :=
  Sigma.desc (fun τ : Fin (K.card n) =>
    (K.skel K.dim).chainι n (Fin.cast (skelCard_self K n).symm τ))

/-- The defining property of `skelSelfInvFun` on a basis simplex. -/
theorem chainι_skelSelfInvFun (K : DeltaCx) (n : ℕ) (τ : Fin (K.card n)) :
    K.chainι n τ ≫ skelSelfInvFun K n
      = (K.skel K.dim).chainι n (Fin.cast (skelCard_self K n).symm τ) :=
  Limits.Sigma.ι_comp_desc _ τ

/-- `skelSelfInvFun` is a right inverse of the `n`-th component of `chainMap (K.skelHom K.dim)`. -/
theorem chainMapFun_skelHom_comp_inv (K : DeltaCx) (n : ℕ) :
    (K.skelHom K.dim).chainMapFun n ≫ skelSelfInvFun K n
      = 𝟙 ((K.skel K.dim).chainX n) := by
  apply DeltaCx.chainX_hom_ext
  intro σ
  rw [← Category.assoc, DeltaCx.Hom.chainMapFun_chainι, DeltaCx.skelHom_map,
    chainι_skelSelfInvFun, Category.comp_id]
  congr 1
  exact cast_skelMap_self K σ

/-- `skelSelfInvFun` is a left inverse of the `n`-th component of `chainMap (K.skelHom K.dim)`. -/
theorem skelSelfInvFun_comp_chainMapFun (K : DeltaCx) (n : ℕ) :
    skelSelfInvFun K n ≫ (K.skelHom K.dim).chainMapFun n = 𝟙 (K.chainX n) := by
  apply DeltaCx.chainX_hom_ext
  intro τ
  rw [← Category.assoc, chainι_skelSelfInvFun, DeltaCx.Hom.chainMapFun_chainι,
    DeltaCx.skelHom_map, Category.comp_id]
  congr 1
  exact skelMap_cast_self K τ

/-- The `n`-th component of `chainMap (K.skelHom K.dim)` is an isomorphism of `ℤ`-modules. -/
theorem isIso_chainMapFun_skelHom (K : DeltaCx) (n : ℕ) :
    IsIso ((DeltaCx.Hom.chainMap (K.skelHom K.dim)).f n) :=
  ⟨skelSelfInvFun K n, chainMapFun_skelHom_comp_inv K n,
    skelSelfInvFun_comp_chainMapFun K n⟩

/-- The inclusion of the `dim`-skeleton induces an isomorphism of `Δ`-chain complexes; hence it
is a quasi-isomorphism. -/
theorem isIso_chainMap_skelHom_self (K : DeltaCx) :
    IsIso (DeltaCx.Hom.chainMap (K.skelHom K.dim)) := by
  haveI : ∀ n : ℕ, IsIso ((DeltaCx.Hom.chainMap (K.skelHom K.dim)).f n) :=
    fun n => isIso_chainMapFun_skelHom K n
  exact HomologicalComplex.Hom.isIso_of_components _

/-- **Hatcher 2.27, the frontier statement, from the skeleton version.**  Since the comparison
chain map of the `n`-skeleton is a quasi-isomorphism for every `n`
(`Submission.Work.DeltaHomology.quasiOso_deltaChainMapSkel`), so is the comparison chain map
`deltaChainMap χ : K.chain ⟶ C_*(X)` of the whole `Δ`-complex.

Efficient route (this avoids all identifications of the complexes with `K.chain`):
`DeltaSimplexMap.deltaChainMapSkel_compat` at `k = K.dim` gives
`deltaChainMapSkel χ K.dim ≫ inclChain ZMod X (χ.skelSet K.dim) = chainMap (K.skelHom K.dim) ≫ deltaChainMap χ`.
Now `skelSet K.dim = Set.univ` (`skelSet_dim_eq_univ`), so `inclChain ZMod X (χ.skelSet K.dim)` is
an isomorphism on homology (it is `inclChain` of the homeomorphism `TopCat.of Set.univ ≃ₜ X`, and
`inclChain` of a homeomorphism is a quasi-isomorphism; more directly
`inclChain ZMod X Set.univ` is conjugate to the identity by `Homeomorph.Set.univ` and
`singChainMap`), while `chainMap (K.skelHom K.dim)` is a quasi-isomorphism as well (degreewise a
basis-to-basis isomorphism by `DeltaCx.skel_self_card`, so it is an isomorphism of chain
complexes).  Hence `QuasiIso (deltaChainMap χ)` follows from
`QuasiIso (deltaChainMapSkel χ K.dim)` (`quasiOso_deltaChainMapSkel R K.dim`) by cancelling the
isomorphisms on homology (`IsIso` of `homologyMap` composes and cancels). -/
theorem quasiOso_deltaChainMap {K : DeltaCx} {X : TopCat.{0}} (R : DeltaRealization K X) :
    QuasiIso R.toDeltaSimplexMap.deltaChainMap := by
  have hA : QuasiIso (R.toDeltaSimplexMap.deltaChainMapSkel K.dim) :=
    quasiOso_deltaChainMapSkel R K.dim
  have hB : QuasiIso (inclChain ZMod X (R.toDeltaSimplexMap.skelSet K.dim)) := by
    rw [skelSet_dim_eq_univ R]
    haveI : IsIso (incl (X := X) (Set.univ : Set X)) := by
      rw [show incl (X := X) (Set.univ : Set X)
          = homeomorphTopCatHom (Homeomorph.Set.univ X) from rfl]
      exact ⟨homeomorphTopCatInv _, homeomorphTopCatHom_comp_inv _,
        homeomorphTopCatInv_comp_hom _⟩
    infer_instance
  haveI : IsIso (DeltaCx.Hom.chainMap (K.skelHom K.dim)) :=
    isIso_chainMap_skelHom_self K
  have hAB : QuasiIso (R.toDeltaSimplexMap.deltaChainMapSkel K.dim
      ≫ inclChain ZMod X (R.toDeltaSimplexMap.skelSet K.dim)) := by
    haveI := hA
    haveI := hB
    infer_instance
  rw [DeltaSimplexMap.deltaChainMapSkel_compat R.toDeltaSimplexMap K.dim] at hAB
  haveI := hAB
  exact quasiIso_of_comp_left (DeltaCx.Hom.chainMap (K.skelHom K.dim))
    R.toDeltaSimplexMap.deltaChainMap

end Work.DeltaHomology

-- The delivered file carries two identical `namespace Work.DeltaHomology` lines (so the theorem
-- above is registered in `Work.DeltaHomology.Work.DeltaHomology`); the outer namespace is still
-- open here, so the following is the same theorem under the flat name
-- `Work.DeltaHomology.quasiOso_deltaChainMap` by which the rest of the project refers to it.
/-- **Hatcher 2.27, whole `Δ`-complex** (flat name of the declaration above). -/
theorem quasiOso_deltaChainMap {K : DeltaCx} {X : TopCat.{0}} (R : DeltaRealization K X) :
    QuasiIso R.toDeltaSimplexMap.deltaChainMap :=
  _root_.Work.DeltaHomology.Work.DeltaHomology.quasiOso_deltaChainMap R
