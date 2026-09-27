import Mathlib
import Submission.Work.Compact.Noncompact.Basic

/-!
# A noncompact space has a point at which every homology class is locally trivial

For a noncompact topological space `M`, every singular homology class
`α ∈ Hₙ(M; ℤ)` vanishes at some point: there is `x : M` whose localization map
`localMap x : Hₙ(M;ℤ) ⟶ Hₙ(M, M∖{x};ℤ)` kills `α`.

The point of the proof is that a singular `n`-chain is a *finite* `ℤ`-linear
combination of singular `n`-simplices, so the union of the (compact) images of
the simplices occurring in a cycle representing `α` is compact; as `M` is
noncompact, some `x` lies outside it.  Then the cycle lies in the subcomplex of
chains of `M∖{x}`, hence dies in `C_*(M)/C_*(M∖{x})`, which is exactly
`localMap x` on chains.
-/

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicTopology CategoryTheory.Limits

namespace Work.Compact.Noncompact

noncomputable section

open scoped BigOperators

/-- The inverse of the comparison isomorphism between a categorical coproduct of
`ℤ`-modules and the direct sum, evaluated on a `lof` generator. -/
lemma coprodIsoDirectSum_inv_lof {R : Type*} [Ring R] {ι : Type*} [DecidableEq ι]
    (Z : ι → ModuleCat R) [HasCoproduct Z] (i : ι) (x : Z i) :
    (ModuleCat.coprodIsoDirectSum Z).inv.hom ((DirectSum.lof R ι (fun i => Z i) i) x)
      = (Sigma.ι Z i).hom x := by
  rw [show (DirectSum.lof R ι (fun i => Z i) i) x
      = (ModuleCat.Hom.hom (ModuleCat.ofHom (DirectSum.lof R ι (fun i => Z i) i))) x by
    rw [ModuleCat.hom_ofHom]]
  rw [← ModuleCat.comp_apply]
  rw [ModuleCat.lof_coprodIsoDirectSum_inv]

/-- **A singular chain is a finite linear combination of its simplices.**

Every `n`-chain `c` of a simplicial set `X` (with `ℤ` coefficients) is a finite
`ℤ`-linear combination of the generators `ιChainComplex t` corresponding to
`n`-simplices `t`. -/
theorem chain_eq_sum_ιChainComplex (X : SSet) (n : ℕ)
    (c : (X.chainComplex (ModuleCat.of ℤ ℤ)).X n) :
    ∃ (S : Finset (X.obj (Opposite.op (SimplexCategory.mk n))))
      (a : X.obj (Opposite.op (SimplexCategory.mk n)) → ℤ),
      c = ∑ t ∈ S, (X.ιChainComplex (R := ModuleCat.of ℤ ℤ) t).hom (a t) := by
  classical
  let Z : X.obj (Opposite.op (SimplexCategory.mk n)) → ModuleCat ℤ := fun _ => ModuleCat.of ℤ ℤ
  let d : DirectSum (X.obj (Opposite.op (SimplexCategory.mk n))) (fun _ => ℤ) :=
    (ModuleCat.coprodIsoDirectSum Z).hom.hom c
  refine ⟨d.support, fun t => d t, ?_⟩
  have h1 : c = (ModuleCat.coprodIsoDirectSum Z).inv.hom d := (Iso.hom_inv_id_apply _ c).symm
  have key : (ModuleCat.coprodIsoDirectSum Z).inv.hom d
      = ∑ t ∈ d.support, (X.ιChainComplex (R := ModuleCat.of ℤ ℤ) t).hom (d t) := by
    conv_lhs => rw [← DirectSum.sum_support_of d]
    rw [map_sum]
    refine Finset.sum_congr rfl (fun i hi => ?_)
    rw [← DirectSum.lof_eq_of ℤ (X.obj (Opposite.op (SimplexCategory.mk n))) (fun _ => ℤ)]
    rw [coprodIsoDirectSum_inv_lof Z i (d i)]
    rfl
  rw [h1, key]

/-- **A noncompact space has a point avoiding finitely many compact images.**

Given a finite family of singular `n`-simplices of a noncompact space `X`, there
is a point of `X` lying in the image of none of them: the union of the (compact)
images is compact, hence cannot be all of `X`. -/
lemma exists_notMem_range_toSSet (X : TopCat) [NoncompactSpace X] {n : ℕ}
    (S : Finset ((TopCat.toSSet.obj X).obj (Opposite.op (SimplexCategory.mk n)))) :
    ∃ x : X, ∀ t ∈ S,
      x ∉ Set.range (TopCat.toSSetObjEquiv X (Opposite.op (SimplexCategory.mk n)) t) := by
  by_contra h
  push_neg at h
  have hK : (⋃ t ∈ S,
      Set.range (TopCat.toSSetObjEquiv X (Opposite.op (SimplexCategory.mk n)) t)) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    obtain ⟨t, ht, hx⟩ := h x
    simp only [Set.mem_iUnion]
    exact ⟨t, ht, hx⟩
  have hcomp : IsCompact (⋃ t ∈ S,
      Set.range (TopCat.toSSetObjEquiv X (Opposite.op (SimplexCategory.mk n)) t)) :=
    S.isCompact_biUnion (fun t _ => isCompact_range
      (TopCat.toSSetObjEquiv X (Opposite.op (SimplexCategory.mk n)) t).continuous)
  exact hcomp.ne_univ hK

/-! ## Lifting simplices landing in a subspace -/

/-- A singular `n`-simplex of `X` whose image lies in `A`, regarded as a singular
`n`-simplex of the subspace `A`. -/
def liftSimplex {X : TopCat} {A : Set X} {n : ℕ}
    (t : (TopCat.toSSet.obj X).obj (Opposite.op (SimplexCategory.mk n)))
    (h : ∀ z, TopCat.toSSetObjEquiv X (Opposite.op (SimplexCategory.mk n)) t z ∈ A) :
    (TopCat.toSSet.obj (TopCat.of A)).obj (Opposite.op (SimplexCategory.mk n)) :=
  (TopCat.toSSetObjEquiv (TopCat.of A) (Opposite.op (SimplexCategory.mk n))).symm
    ⟨fun z => ⟨TopCat.toSSetObjEquiv X (Opposite.op (SimplexCategory.mk n)) t z, h z⟩,
      Continuous.subtype_mk (TopCat.toSSetObjEquiv X (Opposite.op (SimplexCategory.mk n)) t).continuous h⟩

lemma toSSetObjEquiv_liftSimplex {X : TopCat} {A : Set X} {n : ℕ}
    (t : (TopCat.toSSet.obj X).obj (Opposite.op (SimplexCategory.mk n)))
    (h : ∀ z, TopCat.toSSetObjEquiv X (Opposite.op (SimplexCategory.mk n)) t z ∈ A) :
    TopCat.toSSetObjEquiv (TopCat.of A) (Opposite.op (SimplexCategory.mk n)) (liftSimplex t h)
      = ⟨fun z => ⟨TopCat.toSSetObjEquiv X (Opposite.op (SimplexCategory.mk n)) t z, h z⟩,
          Continuous.subtype_mk
            (TopCat.toSSetObjEquiv X (Opposite.op (SimplexCategory.mk n)) t).continuous h⟩ :=
  Equiv.apply_symm_apply _ _

/-- The simplex of `X` obtained from a lifted simplex is the original one. -/
lemma toSSet_map_subtypeIncl_liftSimplex {X : TopCat} {A : Set X} {n : ℕ}
    (t : (TopCat.toSSet.obj X).obj (Opposite.op (SimplexCategory.mk n)))
    (h : ∀ z, TopCat.toSSetObjEquiv X (Opposite.op (SimplexCategory.mk n)) t z ∈ A) :
    (TopCat.toSSet.map (Work.Cohomology.subtypeIncl X A)).app
        (Opposite.op (SimplexCategory.mk n)) (liftSimplex t h) = t := by
  apply (TopCat.toSSetObjEquiv X (Opposite.op (SimplexCategory.mk n))).injective
  rw [show TopCat.toSSetObjEquiv X (Opposite.op (SimplexCategory.mk n))
        ((TopCat.toSSet.map (Work.Cohomology.subtypeIncl X A)).app (Opposite.op (SimplexCategory.mk n))
          (liftSimplex t h))
      = (Work.Cohomology.subtypeIncl X A).hom.comp
          (TopCat.toSSetObjEquiv (TopCat.of A) (Opposite.op (SimplexCategory.mk n))
            (liftSimplex t h)) from rfl]
  rw [toSSetObjEquiv_liftSimplex]
  rfl

/-- **A chain generator whose simplex lies in `A` comes from the chains of `A`.**

If the singular `n`-simplex `t` of `X` has its image in `A ⊆ X`, then the
generator `ιChainComplex t` of the `n`-chains of `X` lies in the image of the
inclusion `C_*(A) → C_*(X)`. -/
lemma inclChains_f_ι_liftSimplex {X : TopCat} {A : Set X} {n : ℕ}
    (t : (TopCat.toSSet.obj X).obj (Opposite.op (SimplexCategory.mk n)))
    (h : ∀ z, TopCat.toSSetObjEquiv X (Opposite.op (SimplexCategory.mk n)) t z ∈ A) (a : ℤ) :
    ((Work.Cohomology.inclChains X A).f n).hom
        (((TopCat.toSSet.obj (TopCat.of A)).ιChainComplex
            (R := ModuleCat.of ℤ ℤ) (liftSimplex t h)).hom a)
      = ((TopCat.toSSet.obj X).ιChainComplex (R := ModuleCat.of ℤ ℤ) t).hom a := by
  have hkey := SSet.ι_chainComplexMap_f (TopCat.toSSet.obj (TopCat.of A)) (TopCat.toSSet.obj X)
    (TopCat.toSSet.map (Work.Cohomology.subtypeIncl X A)) (ModuleCat.of ℤ ℤ) (liftSimplex t h)
  rw [toSSet_map_subtypeIncl_liftSimplex t h] at hkey
  have h2 := congrArg (fun (g : (ModuleCat.of ℤ ℤ) ⟶
      ((TopCat.toSSet.obj X).chainComplex (ModuleCat.of ℤ ℤ)).X n) =>
        (ModuleCat.Hom.hom g) a) hkey
  rw [ModuleCat.comp_apply] at h2
  exact h2

theorem exists_localMap_eq_zero {n : ℕ} {M : Type} [TopologicalSpace M] [Nonempty M]
    [NoncompactSpace M] (α : (Work.Cohomology.singularChains ℤ (TopCat.of M)).homology n) :
    ∃ x : M, localMap (X := TopCat.of M) n x α = 0 := by
  classical
  -- a cycle representing `α`
  obtain ⟨zz, hzz⟩ := (ModuleCat.epi_iff_surjective
      ((Work.Cohomology.singularChains ℤ (TopCat.of M)).homologyπ n)).mp inferInstance α
  let c : (Work.Cohomology.singularChains ℤ (TopCat.of M)).X n :=
    (Work.Cohomology.singularChains ℤ (TopCat.of M)).iCycles n zz
  have hc_def : c = (ModuleCat.Hom.hom
      ((Work.Cohomology.singularChains ℤ (TopCat.of M)).iCycles n)) zz := rfl
  -- `c` is a finite combination of simplices, and some point is avoided by all of them
  obtain ⟨S, a, hc⟩ := chain_eq_sum_ιChainComplex (TopCat.toSSet.obj (TopCat.of M)) n c
  obtain ⟨x, hx⟩ := exists_notMem_range_toSSet (TopCat.of M) S
  refine ⟨x, ?_⟩
  let E : ChainComplex (ModuleCat ℤ) ℕ := RC (TopCat.of M) ({x}ᶜ : Set M)
  let D : Work.Cohomology.singularChains ℤ (TopCat.of M) ⟶ E :=
    cokernel.π (Work.Cohomology.inclChains (TopCat.of M) ({x}ᶜ : Set M))
  -- the localization map is the quotient by the chains of `M ∖ {x}`
  have hlocal : localMap (X := TopCat.of M) n x = HomologicalComplex.homologyMap D n := by
    show HomologicalComplex.homologyMap (cokernel.π
          (Work.Cohomology.inclChains (TopCat.of M) (∅ : Set M))) n ≫
        HomologicalComplex.homologyMap (relMap (Set.empty_subset ({x}ᶜ : Set M))) n = _
    rw [← HomologicalComplex.homologyMap_comp,
      cokernel_π_relMap (Set.empty_subset ({x}ᶜ : Set M)), Category.id_comp]
  rw [hlocal]
  -- the representing cycle dies in the quotient
  have hDc : (D.f n).hom c = 0 := by
    rw [hc]
    rw [map_sum]
    refine Finset.sum_eq_zero (fun t ht => ?_)
    have hAt : ∀ z, TopCat.toSSetObjEquiv (TopCat.of M)
        (Opposite.op (SimplexCategory.mk n)) t z ∈ ({x}ᶜ : Set M) := by
      intro z
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      exact fun hz => hx t ht (Set.mem_range.mpr ⟨z, hz⟩)
    rw [← inclChains_f_ι_liftSimplex (X := TopCat.of M) (A := ({x}ᶜ : Set M)) t hAt (a t)]
    have hcomp : (Work.Cohomology.inclChains (TopCat.of M) ({x}ᶜ : Set M)).f n ≫ D.f n = 0 := by
      rw [← HomologicalComplex.comp_f]
      rw [show (Work.Cohomology.inclChains (TopCat.of M) ({x}ᶜ : Set M)) ≫ D = 0 from by
        dsimp only [D]; rw [cokernel.condition]]
      rfl
    have h0 : (ModuleCat.Hom.hom ((Work.Cohomology.inclChains (TopCat.of M)
          ({x}ᶜ : Set M)).f n ≫ D.f n))
        (((TopCat.toSSet.obj (TopCat.of ({x}ᶜ : Set M))).ιChainComplex
          (R := ModuleCat.of ℤ ℤ) (liftSimplex t hAt)).hom (a t)) = 0 := by
      rw [hcomp]
      simp
    rwa [ModuleCat.comp_apply] at h0
  -- hence the cycle class dies
  have hcyc : HomologicalComplex.cyclesMap D n zz = 0 := by
    apply (ModuleCat.mono_iff_injective (E.iCycles n)).mp inferInstance
    have h1 : (E.iCycles n).hom ((HomologicalComplex.cyclesMap D n).hom zz) = 0 := by
      rw [← ModuleCat.comp_apply, HomologicalComplex.cyclesMap_i, ModuleCat.comp_apply]
      rw [show (ModuleCat.Hom.hom
          ((Work.Cohomology.singularChains ℤ (TopCat.of M)).iCycles n)) zz = c from hc_def.symm]
      exact hDc
    rw [h1]
    simp
  have hfinal : HomologicalComplex.homologyMap D n α = 0 := by
    rw [← hzz]
    have hnat : (ModuleCat.Hom.hom (HomologicalComplex.homologyMap D n))
        ((ModuleCat.Hom.hom ((Work.Cohomology.singularChains ℤ (TopCat.of M)).homologyπ n)) zz)
        = (ModuleCat.Hom.hom (E.homologyπ n))
            ((ModuleCat.Hom.hom (HomologicalComplex.cyclesMap D n)) zz) := by
      rw [← ModuleCat.comp_apply, HomologicalComplex.homologyπ_naturality, ModuleCat.comp_apply]
    rw [hnat, hcyc]
    simp
  exact hfinal

end

end Work.Compact.Noncompact
