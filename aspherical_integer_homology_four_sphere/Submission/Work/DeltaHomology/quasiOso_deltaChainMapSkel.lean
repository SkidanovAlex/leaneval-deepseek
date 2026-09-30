import Mathlib
import Submission.Work.DeltaHomology.CellClassMap
import Submission.Work.DeltaHomology.cellClassMapCell_isIso
import Submission.Work.DeltaHomology.skelQuotient_shortExact
import Submission.Work.DeltaHomology.skelQuotient_X_isZero
import Submission.Work.DeltaHomology.skelQuotient_X_iso
import Submission.Work.DeltaHomology.relHomology_skel_succ_goodPair
import Submission.Work.DeltaHomology.relHomology_cell_splitting
import Submission.Work.DeltaHomology.cell_relHomology_iso
import Submission.Work.DeltaHomology.SkelChain
import Submission.Work.DeltaHomology.SkelInclDefs
import Submission.Work.DeltaHomology.deltaChainMapSkel_natural
import Submission.Work.DeltaHomology.relHomology_punctSkel_succ_iso
import Submission.Work.DeltaHomology.isIso_fold_cellClassMap
import Submission.Work.DeltaHomology.isIso_homologyMap_skelQuotient_desc
import Submission.Work.DeltaHomology.quasiOso_deltaChainMapSkel_zero
import Submission.Work.Subdivision.quasiIso_tau2
import Submission.Work.Subdivision.quasiIso_tau2_poly
import Submission.Work.HomologyExtra.Main

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.DeltaHomology

open CategoryTheory AlgebraicTopology CategoryTheory.Limits Convexity Work.Homology

namespace Work.DeltaHomology

/-! ## Helpers for the skeleta induction

These are the definitions and elementary lemmas used by the induction step of
`quasiOso_deltaChainMapSkel`: the inclusion of the `k`-skeleton in the punctured `(k+1)`-skeleton
(and the fact that it induces a quasi-isomorphism of singular chain complexes, by the collar of
`exists_deformationRetract_punctSkel`), and the five lemma for the morphism of short exact
sequences built from the `Δ`-side sequence and the pair sequence of `(X^{k+1}, punctSkel (k+1))`.
-/

variable {K : DeltaCx} {X : TopCat}

/-- The punctured `(k+1)`-skeleton, as a subspace of the `(k+1)`-skeleton. -/
def punctSub (R : DeltaRealization K X) (k : ℕ) :
    Set ↥(R.toDeltaSimplexMap.skelSet (k + 1)) :=
  {x | (x : X) ∈ R.toDeltaSimplexMap.punctSkel (k + 1)}

/-- The image of the `k`-skeleton inside the punctured `(k+1)`-skeleton,
viewed in the `(k+1)`-skeleton. -/
def skelPieceP (R : DeltaRealization K X) (k : ℕ) : Set ↥(punctSub R k) :=
  {x | ((x : ↥(R.toDeltaSimplexMap.skelSet (k + 1))) : X)
    ∈ R.toDeltaSimplexMap.skelSet k}

/-- The canonical homeomorphism between the `k`-skeleton and its image in the punctured
`(k+1)`-skeleton. -/
def homeoX (R : DeltaRealization K X) (k : ℕ) :
    TopCat.of (R.toDeltaSimplexMap.skelSet k) ≃ₜ TopCat.of (skelPiece R k) where
  toFun x := ⟨⟨(x : X), DeltaSimplexMap.skelSet_subset_punctSkel_succ R k x.2⟩, x.2⟩
  invFun y := ⟨((y : ↥(R.toDeltaSimplexMap.punctSkel (k + 1))) : X), y.2⟩
  left_inv x := Subtype.ext rfl
  right_inv y := Subtype.ext (Subtype.ext rfl)
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    exact continuous_subtype_val
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact continuous_subtype_val.comp continuous_subtype_val

/-- The canonical homeomorphism between the punctured `(k+1)`-skeleton as a subspace of `X`
and as a subspace of the `(k+1)`-skeleton. -/
def punctHomeo (R : DeltaRealization K X) (k : ℕ) :
    TopCat.of (R.toDeltaSimplexMap.punctSkel (k + 1)) ≃ₜ TopCat.of (punctSub R k) where
  toFun y := ⟨⟨(y : X), DeltaSimplexMap.punctSkel_subset_skelSet _ _ y.2⟩, y.2⟩
  invFun y := ⟨((y : ↥(R.toDeltaSimplexMap.skelSet (k + 1))) : X), y.2⟩
  left_inv y := Subtype.ext rfl
  right_inv y := Subtype.ext (Subtype.ext rfl)
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    exact continuous_subtype_val
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact continuous_subtype_val.comp continuous_subtype_val

/-- The inclusion of the `k`-skeleton in the punctured `(k+1)`-skeleton (as a subspace of `X`). -/
def punctSkelInclX (R : DeltaRealization K X) (k : ℕ) :
    TopCat.of (R.toDeltaSimplexMap.skelSet k) ⟶
      TopCat.of (R.toDeltaSimplexMap.punctSkel (k + 1)) :=
  TopCat.ofHom ⟨fun x => ⟨(x : X), DeltaSimplexMap.skelSet_subset_punctSkel_succ R k x.2⟩,
    Continuous.subtype_mk continuous_subtype_val
      (fun x => DeltaSimplexMap.skelSet_subset_punctSkel_succ R k x.2)⟩

/-- The inclusion of the `k`-skeleton in the punctured `(k+1)`-skeleton (as a subspace of the
`(k+1)`-skeleton). -/
def skelInPunct (R : DeltaRealization K X) (k : ℕ) :
    TopCat.of (R.toDeltaSimplexMap.skelSet k) ⟶ TopCat.of (punctSub R k) :=
  punctSkelInclX R k ≫ homeomorphTopCatHom (punctHomeo R k)

theorem punctSkelInclX_eq (R : DeltaRealization K X) (k : ℕ) :
    punctSkelInclX R k = homeomorphTopCatHom (homeoX R k) ≫ incl (X := TopCat.of (R.toDeltaSimplexMap.punctSkel (k + 1))) (skelPiece R k) := by
  apply TopCat.hom_ext; ext x; rfl

theorem skelInPunct_eq (R : DeltaRealization K X) (k : ℕ) :
    skelInPunct R k = homeomorphTopCatHom (homeoX R k)
      ≫ incl (X := TopCat.of (R.toDeltaSimplexMap.punctSkel (k + 1))) (skelPiece R k)
      ≫ homeomorphTopCatHom (punctHomeo R k) := by
  rw [skelInPunct, punctSkelInclX_eq, Category.assoc]

/-- The inclusion of the `k`-skeleton in the `(k+1)`-skeleton factors through the punctured
skeleton. -/
theorem skelIncl_eq_skelInPunct_incl (R : DeltaRealization K X) (k : ℕ) :
    (R.toDeltaSimplexMap.skelIncl k) = skelInPunct R k ≫ incl (X := TopCat.of (R.toDeltaSimplexMap.skelSet (k + 1))) (punctSub R k) := by
  apply TopCat.hom_ext; ext x; rfl

/-- Quasi-isomorphisms are closed under composition. -/
theorem quasiIso_comp {C : Type*} [Category C] [Abelian C] {ι : Type*} {c : ComplexShape ι}
    {A B D : HomologicalComplex C c} (f : A ⟶ B) (g : B ⟶ D)
    [∀ i, A.HasHomology i] [∀ i, B.HasHomology i] [∀ i, D.HasHomology i]
    (hf : QuasiIso f) (hg : QuasiIso g) : QuasiIso (f ≫ g) := by
  rw [quasiIso_iff]
  intro i
  rw [quasiIsoAt_iff_isIso_homologyMap]
  have hfi : IsIso (HomologicalComplex.homologyMap f i) :=
    (quasiIsoAt_iff_isIso_homologyMap f i).mp (hf.quasiIsoAt i)
  have hgi : IsIso (HomologicalComplex.homologyMap g i) :=
    (quasiIsoAt_iff_isIso_homologyMap g i).mp (hg.quasiIsoAt i)
  rw [HomologicalComplex.homologyMap_comp]
  haveI := hfi
  haveI := hgi
  exact inferInstance

/-- The inclusion of a deformation retract induces a quasi-isomorphism of singular chain
complexes. -/
theorem quasiIso_inclChain_of_deformationRetract {Y : TopCat} {A : Set Y}
    (h : DeformationRetract Y A) : QuasiIso (inclChain ZMod Y A) := by
  rw [quasiIso_iff]
  intro m
  rw [quasiIsoAt_iff_isIso_homologyMap]
  show IsIso (singHomologyMap ZMod m (incl A))
  refine IsIso.mk ⟨singHomologyMap ZMod m h.retract, ?_, ?_⟩
  · rw [← singHomologyMap_comp, h.retract_incl, singHomologyMap_id]
  · rw [← singHomologyMap_comp, singHomologyMap_congr ZMod m h.homotopy.some,
      singHomologyMap_id]

/-- The inclusion of the `k`-skeleton in the punctured `(k+1)`-skeleton induces a
quasi-isomorphism of singular chain complexes. -/
theorem quasiIso_singChainMap_skelInPunct (R : DeltaRealization K X) (k : ℕ) :
    QuasiIso (singChainMap ZMod (skelInPunct R k)) := by
  rw [skelInPunct_eq]
  rw [singChainMap_comp, singChainMap_comp]
  have h1 : QuasiIso (singChainMap ZMod (homeomorphTopCatHom (homeoX R k))) := by
    haveI : IsIso (homeomorphTopCatHom (homeoX R k)) :=
      ⟨homeomorphTopCatInv (homeoX R k), homeomorphTopCatHom_comp_inv (homeoX R k),
        homeomorphTopCatInv_comp_hom (homeoX R k)⟩
    exact ⟨fun i => inferInstance⟩
  have h2 : QuasiIso (singChainMap ZMod (incl (X := TopCat.of (R.toDeltaSimplexMap.punctSkel (k + 1))) (skelPiece R k))) :=
    quasiIso_inclChain_of_deformationRetract (exists_deformationRetract_punctSkel R k).some
  have h3 : QuasiIso (singChainMap ZMod (homeomorphTopCatHom (punctHomeo R k))) := by
    haveI : IsIso (homeomorphTopCatHom (punctHomeo R k)) :=
      ⟨homeomorphTopCatInv (punctHomeo R k), homeomorphTopCatHom_comp_inv (punctHomeo R k),
        homeomorphTopCatInv_comp_hom (punctHomeo R k)⟩
    exact ⟨fun i => inferInstance⟩
  exact quasiIso_comp _ _ h1 (quasiIso_comp _ _ h2 h3)

/-- **The induction step of Hatcher 2.27 on the skeleta.** -/
theorem quasiOso_deltaChainMapSkel_succ (R : DeltaRealization K X) (k : ℕ)
    (ih : QuasiIso (R.toDeltaSimplexMap.deltaChainMapSkel k)) :
    QuasiIso (R.toDeltaSimplexMap.deltaChainMapSkel (k + 1)) := by
  let W : TopCat := TopCat.of (R.toDeltaSimplexMap.skelSet (k + 1))
  let S₁ : ShortComplex (ChainComplex (ModuleCat ℤ) ℕ) :=
    ShortComplex.mk (DeltaCx.Hom.chainMap (K.skelLE (Nat.le_succ k)))
      (cokernel.π (DeltaCx.Hom.chainMap (K.skelLE (Nat.le_succ k))))
      (cokernel.condition _)
  have hS₁ : S₁.ShortExact := skelQuotient_shortExact K k
  let S₂ : ShortComplex (ChainComplex (ModuleCat ℤ) ℕ) :=
    pairSeq ZMod W (punctSub R k)
  have hS₂ : S₂.ShortExact := pairSeq_shortExact ZMod W (punctSub R k)
  let τ₁ : (K.skel k).chain ⟶ singChain ZMod (TopCat.of (punctSub R k)) :=
    R.toDeltaSimplexMap.deltaChainMapSkel k ≫ singChainMap ZMod (skelInPunct R k)
  let τ₂ : (K.skel (k + 1)).chain ⟶ singChain ZMod W :=
    R.toDeltaSimplexMap.deltaChainMapSkel (k + 1)
  have hnat : DeltaCx.Hom.chainMap (K.skelLE (Nat.le_succ k))
      ≫ R.toDeltaSimplexMap.deltaChainMapSkel (k + 1)
      = R.toDeltaSimplexMap.deltaChainMapSkel k
        ≫ singChainMap ZMod (R.toDeltaSimplexMap.skelIncl k) :=
    (deltaChainMapSkel_natural R.toDeltaSimplexMap k).symm
  have hzero : DeltaCx.Hom.chainMap (K.skelLE (Nat.le_succ k)) ≫ (τ₂ ≫ relProj ZMod W (punctSub R k)) = 0 := by
    change DeltaCx.Hom.chainMap (K.skelLE (Nat.le_succ k))
        ≫ (R.toDeltaSimplexMap.deltaChainMapSkel (k + 1) ≫ relProj ZMod W (punctSub R k)) = 0
    rw [← Category.assoc, hnat, Category.assoc, skelIncl_eq_skelInPunct_incl,
      singChainMap_comp, Category.assoc]
    rw [show relProj ZMod W (punctSub R k) = cokernel.π (inclChain ZMod W (punctSub R k)) from rfl,
      cokernel.condition, comp_zero, comp_zero]
  let τ₃ : S₁.X₃ ⟶ S₂.X₃ := cokernel.desc _ _ hzero
  have hτ₁ : QuasiIso τ₁ := by
    change QuasiIso (R.toDeltaSimplexMap.deltaChainMapSkel k ≫ singChainMap ZMod (skelInPunct R k))
    exact quasiIso_comp _ _ ih (quasiIso_singChainMap_skelInPunct R k)
  have hτ₃ : QuasiIso τ₃ := by
    rw [quasiIso_iff]
    intro m
    rw [quasiIsoAt_iff_isIso_homologyMap]
    by_cases hm : m = k + 1
    · subst hm
      exact isIso_homologyMap_skelQuotient_desc R k hzero
    · have hQ : IsZero (S₁.X₃.homology m) := by
        rw [← HomologicalComplex.exactAt_iff_isZero_homology]
        exact ShortComplex.exact_of_isZero_X₂ _ (skelQuotient_X_isZero K k hm)
      have hR : IsZero (S₂.X₃.homology m) := by
        show IsZero (relHomology ZMod m (TopCat.of (R.toDeltaSimplexMap.skelSet (k+1)))
          {x : ↥(R.toDeltaSimplexMap.skelSet (k+1)) |
            (x : X) ∈ R.toDeltaSimplexMap.punctSkel (k+1)})
        obtain ⟨e⟩ := relHomology_punctSkel_succ_iso R k m
        rw [if_neg hm] at e
        exact IsZero.of_iso (ModuleCat.isZero_of_subsingleton (ModuleCat.of ℤ PUnit)) e
      exact IsZero.isIso hQ hR _
  have h12 : τ₁ ≫ S₂.f = S₁.f ≫ τ₂ := by
    change (R.toDeltaSimplexMap.deltaChainMapSkel k ≫ singChainMap ZMod (skelInPunct R k))
        ≫ inclChain ZMod W (punctSub R k)
      = DeltaCx.Hom.chainMap (K.skelLE (Nat.le_succ k))
        ≫ R.toDeltaSimplexMap.deltaChainMapSkel (k + 1)
    rw [Category.assoc, ← singChainMap_comp, ← skelIncl_eq_skelInPunct_incl, hnat]
  have h23 : τ₂ ≫ S₂.g = S₁.g ≫ τ₃ := by
    change R.toDeltaSimplexMap.deltaChainMapSkel (k + 1) ≫ relProj ZMod W (punctSub R k)
      = cokernel.π (DeltaCx.Hom.chainMap (K.skelLE (Nat.le_succ k))) ≫ τ₃
    rw [show τ₃ = cokernel.desc _ _ hzero from rfl, cokernel.π_desc]
  let φ : S₁ ⟶ S₂ := { τ₁ := τ₁, τ₂ := τ₂, τ₃ := τ₃, comm₁₂ := h12, comm₂₃ := h23 }
  haveI : QuasiIso φ.τ₂ := Work.Subdivision.quasiIso_tau2_poly φ hS₁ hS₂ hτ₁ hτ₃
  show QuasiIso τ₂
  exact this



/-- **Hatcher 2.27 on the `n`-skeleton.**  For a realized `Δ`-complex, the comparison chain map
`deltaChainMapSkel R.toDeltaSimplexMap n : (K.skel n).chain ⟶ C_*(Xⁿ)` is a quasi-isomorphism.

This is the induction on skeleta, and every input is already proved in this directory:

* `skelQuotient_shortExact` — the short exact sequence
  `0 → (K.skel (n-1)).chain → (K.skel n).chain → Q → 0` of `Δ`-chain complexes;
* `pairSeq_shortExact` (`Work.Homology`) — the short exact pair sequence
  `0 → C_*(punctSkel n) → C_*(Xⁿ) → C_*(Xⁿ, punctSkel n) → 0`;
* `relHomology_skel_succ_goodPair` (`Hₘ(Xⁿ, punctSkel n) ≅ Hₘ(Xⁿ, X^{n-1})`, the collar),
  `relHomology_cell_splitting` and `cell_relHomology_iso` (`Hₘ(Xⁿ,X^{n-1}) = 0` for `m ≠ n`,
  `≅ ∐_σ ℤ` for `m = n`), `skelQuotient_X_isZero` and `skelQuotient_X_iso`
  (`Hₘ(Q) = 0` for `m ≠ n`, `Hₙ(Q) = ℤ^{K_n}`);
* `cellClassMapCell_isIso` — the characteristic map of a top cell has degree `±1`, i.e. the
  classes `[χ σ]` generate the relative homology of the cell pairs;
* `Work.Subdivision.quasiIso_tau2` — the middle position of the five-terms exactness result for a
  morphism of short exact sequences of chain complexes, already proved in general.

Suggested route.  Fix `n` and assume the induction hypothesis
`QuasiIso (deltaChainMapSkel χ m)` for `m < n` (so that, by the Δ-side vanishing
`chain_homology_isZero_of_dim_lt`, also `Hₘ(X^m) = 0` for `m > m₀`).  Build the morphism of short
exact sequences from the Δ-side sequence to the pair sequence of
`(Xⁿ, punctSkel n)`, with `τ₁` the comparison map of the `(n-1)`-skeleton followed by the
chain map induced by the homotopy equivalence `X^{n-1} → punctSkel n` (a quasi-isomorphism by the
induction hypothesis and the collar), `τ₂ = deltaChainMapSkel χ n` and `τ₃` induced on the
cokernels.  Then `QuasiIso τ₃` follows from: vanishing in degrees `≠ n` (items above), and in
degree `n` from the fact that the induced map `ℤ^{K_n} = Hₙ(Q) → Hₙ(Xⁿ, punctSkel n)` sends the
basis vector `e_σ` to the class of `χ σ`, which is an isomorphism because the corresponding maps
of the cell pairs are isomorphisms (`cellClassMapCell_isIso`) and the cell pairs are related to
`(Xⁿ, punctSkel n)` by the excision/splitting isomorphisms of this directory (a chain-level
tracking of the class of `χ σ`, for which the auxiliary results
`relHomology_iso_of_homeomorph`, `relHomology_iso_of_open_cover`,
`exists_homeomorph_intCell`, `punctCell_eq_sdiff` and `Work.HomologyExtra.cycleClass` are
useful; if the tracking needs a "homotopic maps of pairs induce the same map on relative
homology" input, prove it separately).  Finally `QuasiIso τ₂` follows from `QuasiIso τ₁` and
`QuasiIso τ₃` by `Work.Subdivision.quasiIso_tau2` (after converting
`∀ i, IsIso (homologyMap _ i)` to `QuasiIso` via `quasiIsoAt_iff_isIso_homologyMap`), and
`Hₘ(Xⁿ) = 0` for `m > n` follows from the pair sequence and the vanishing above.

Base case `n = 0`: `X⁰` is a disjoint union of points (a finite Hausdorff subspace of the
Hausdorff space `X`), `(K.skel 0).chain` is free on the vertices, `singChain ZMod X⁰ ≅ ℤ^{K₀}` in
degree `0` with the vertex classes as a basis, and both sides have vanishing homology in positive
degrees.

You may add further imports of this directory (`Submission.Work.DeltaHomology.*`) and of
`Work.Homology`, `Work.HomologyExtra`, `Work.Cohomology`, `Work.Subdivision` as needed. -/
theorem quasiOso_deltaChainMapSkel {K : DeltaCx} {X : TopCat} (R : DeltaRealization K X) (n : ℕ) :
    QuasiIso (R.toDeltaSimplexMap.deltaChainMapSkel n) := by
  induction n with
  | zero => exact quasiOso_deltaChainMapSkel_zero R
  | succ n ih => exact quasiOso_deltaChainMapSkel_succ R n ih

end Work.DeltaHomology

-- The delivered file carries two identical `namespace Work.DeltaHomology` lines (so the theorem
-- above is registered in `Work.DeltaHomology.Work.DeltaHomology`); the outer namespace is still
-- open here, so the following is the same theorem under the flat name
-- `Work.DeltaHomology.quasiOso_deltaChainMapSkel` by which the rest of the project refers to it.
/-- **Hatcher 2.27 on the `n`-skeleton** (flat name of the declaration above). -/
theorem quasiOso_deltaChainMapSkel {K : DeltaCx} {X : TopCat} (R : DeltaRealization K X) (n : ℕ) :
    QuasiIso (R.toDeltaSimplexMap.deltaChainMapSkel n) :=
  _root_.Work.DeltaHomology.Work.DeltaHomology.quasiOso_deltaChainMapSkel R n
