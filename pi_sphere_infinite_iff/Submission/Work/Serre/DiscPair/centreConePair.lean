import Mathlib
import Submission.Work.Serre.C1Cyl
import Submission.Work.Serre.C1CylExplicit
import Submission.Work.StemsB.RelChainsR
import Submission.Work.Serre.csrDefs
import Submission.Work.RatHurewicz.AttachCells
import Submission.Work.StemsB.Fibrations
import Submission.Work.Cohomology.homologyContractible
import Submission.Work.Cohomology.HomologyPairSequence
import Submission.Work.Cohomology.pd_triple
import Submission.Work.Serre.CsrSharp.relChainsRHomeomorphCompat

/-!
# The cone pair of the fibre of a mapping-cylinder retraction

For a continuous map `q : X → Z` and a point `z : Z`, the preimage
`P := (cylRetract q) ⁻¹' {z} ⊆ cyl q` of `z` under the retraction of the mapping cylinder onto its
target is the **cone on the fibre** `F := q ⁻¹' {z}` (its apex is the point of the target copy, its
base the copy of `F` at the bottom of the cylinder).  This file proves the resulting homological
statement

`H_k(P, F) ≅ H_{k-1}(F, {b})`   (`k ≥ 1`, `b : F`),

i.e. the relative homology of the cone pair is the reduced homology of the base, shifted by one.

## Contents

* `isZero_of_epi_of_eq_zero`, `isZero_of_mono_of_eq_zero` — elementary abelian-category lemmas;
* `isZero_homology_third` — the third term of a short exact sequence of chain complexes over `ℚ`
  is acyclic, given the acyclicity of the first two terms and the connectivity of the first
  vertical map in degree `0`;
* `isIso_δ_of_isZero` — if the middle term of a short exact sequence of chain complexes is acyclic
  in degrees `k` and `k-1`, the connecting homomorphism `H_k(X₃) → H_{k-1}(X₁)` is an isomorphism;
* `isIso_toPoint_zero`, `isIso_homologyMap_zero_of_subsingleton` — the degree-`0` connectivity
  statements for contractible spaces;
* `conePairIso` — the abstract cone-pair isomorphism;

## The two geometric inputs

* `cylRetractPreimageContractible` — the preimage of a point under the retraction
  `cyl f → X` is contractible (it is the cone on the fibre `f ⁻¹' {z}`), by the explicit
  contraction `cylMove`;
* `baseHomeoFibre` — the base of that cone is homeomorphic to the fibre `f ⁻¹' {z}` (via
  `Work.Serre.cylHomeoExplicit`), and the homeomorphism carries the point of the base lying over
  `b` to `b`.

The final assembly is `centreConePair`.  The transport of relative `ℚ`-homology along a
homeomorphism of pairs is `Work.Serre.CsrSharp.relChainsRHomeomorphCompat`.
-/

open CategoryTheory CategoryTheory.Limits

namespace Work.Serre.DiscPair

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

/-! ## Elementary abelian-category lemmas -/

/-- An epimorphism which is zero has zero target. -/
theorem isZero_of_epi_of_eq_zero {C : Type*} [Category C] [HasZeroMorphisms C] {A B : C} (f : A ⟶ B)
    [Epi f] (h : f = 0) : IsZero B := by
  rw [IsZero.iff_id_eq_zero]
  exact (cancel_epi f).mp (by rw [Category.comp_id, comp_zero]; exact h)

/-- A monomorphism which is zero has zero source. -/
theorem isZero_of_mono_of_eq_zero {C : Type*} [Category C] [HasZeroMorphisms C] {A B : C} (f : A ⟶ B)
    [Mono f] (h : f = 0) : IsZero A := by
  rw [IsZero.iff_id_eq_zero]
  exact (cancel_mono f).mp (by rw [Category.id_comp, zero_comp]; exact h)

/-! ## The long exact sequence of a short exact sequence of chain complexes -/

/-- **Vanishing of the third term of a short exact sequence of chain complexes over `ℚ`.**

If `0 → X₁ → X₂ → X₃ → 0` is a short exact sequence of chain complexes of `ℚ`-modules, the first
two terms are acyclic in positive degrees and the map `H_0(X₁) → H_0(X₂)` is an isomorphism, then
`X₃` is acyclic (in every degree).  This is the long exact sequence argument
`H_k(X₂) → H_k(X₃) → H_{k-1}(X₁)` together with the degree `0` case
`H_0(X₁) → H_0(X₂) → H_0(X₃)`. -/
theorem isZero_homology_third (S : ShortComplex (ChainComplex (ModuleCat ℚ) ℕ))
    (hS : S.ShortExact)
    (h₁ : ∀ j, 1 ≤ j → IsZero (S.X₁.homology j))
    (h₂ : ∀ j, 1 ≤ j → IsZero (S.X₂.homology j))
    (h₀ : IsIso (HomologicalComplex.homologyMap S.f 0)) :
    ∀ j, IsZero (S.X₃.homology j) := by
  intro j
  rcases j with _ | j
  · -- degree `0`: `H_0(X₁) → H_0(X₂)` is onto, hence `H_0(X₂) → H_0(X₃)` is zero and onto
    have hzero : HomologicalComplex.homologyMap S.f 0 ≫ HomologicalComplex.homologyMap S.g 0 = 0 := by
      rw [← HomologicalComplex.homologyMap_comp, S.zero, HomologicalComplex.homologyMap_zero]
    have hkill : HomologicalComplex.homologyMap S.g 0 = 0 := by
      haveI := h₀
      have hsurj : Function.Surjective (HomologicalComplex.homologyMap S.f 0).hom :=
        (ModuleCat.epi_iff_surjective _).mp inferInstance
      apply ModuleCat.hom_ext
      ext x
      obtain ⟨y, hy⟩ := hsurj x
      rw [← hy]
      have h2 : (HomologicalComplex.homologyMap S.g 0).hom
            ((HomologicalComplex.homologyMap S.f 0).hom y)
          = (HomologicalComplex.homologyMap S.f 0 ≫
              HomologicalComplex.homologyMap S.g 0).hom y := rfl
      rw [h2, hzero]
      rfl
    haveI : Epi (HomologicalComplex.homologyMap S.g 0) := by
      haveI : Epi S.g := hS.epi_g
      exact HomologicalComplex.epi_homologyMap_of_epi_of_not_rel S.g 0
        (fun k hk => by simp [ComplexShape.down] at hk)
    exact isZero_of_epi_of_eq_zero _ hkill
  · rcases j with _ | j
    · -- degree `1`: `δ` is zero because it is the kernel of an injective map, and `H_1(X₂) = 0`
      have hrel : (ComplexShape.down ℕ).Rel 1 0 := by simp [ComplexShape.down]
      have hδ0 : hS.δ 1 0 hrel = 0 := by
        have hex₁ := hS.homology_exact₁ 1 0 hrel
        have hker : LinearMap.ker (HomologicalComplex.homologyMap S.f 0).hom = ⊥ := by
          haveI := h₀
          exact LinearMap.ker_eq_bot.mpr ((ModuleCat.mono_iff_injective _).mp inferInstance)
        have hrange : LinearMap.range (hS.δ 1 0 hrel).hom = ⊥ := by
          rw [ShortComplex.Exact.moduleCat_range_eq_ker hex₁, hker]
        apply ModuleCat.hom_ext
        ext x
        have hx : (hS.δ 1 0 hrel).hom x ∈ LinearMap.range (hS.δ 1 0 hrel).hom := ⟨x, rfl⟩
        rw [hrange] at hx
        simpa using hx
      have hex₃ := hS.homology_exact₃ 1 0 hrel
      haveI : Epi (HomologicalComplex.homologyMap S.g 1) :=
        (ShortComplex.exact_iff_epi _ hδ0).mp hex₃
      exact IsZero.of_epi (HomologicalComplex.homologyMap S.g 1) (h₂ 1 le_rfl)
    · -- degree `j + 2`: the two neighbours in `H_j(X₃) → H_{j+1}(X₃) → H_j(X₁)` vanish
      have hrel : (ComplexShape.down ℕ).Rel (j + 2) (j + 1) := by simp [ComplexShape.down]
      have hex₃ := hS.homology_exact₃ (j + 2) (j + 1) hrel
      have hz : hS.δ (j + 2) (j + 1) hrel = 0 :=
        IsZero.eq_zero_of_tgt (h₁ (j + 1) (by omega)) _
      haveI : Epi (HomologicalComplex.homologyMap S.g (j + 2)) :=
        (ShortComplex.exact_iff_epi _ hz).mp hex₃
      exact IsZero.of_epi (HomologicalComplex.homologyMap S.g (j + 2)) (h₂ (j + 2) (by omega))

/-- **The connecting homomorphism is an isomorphism when the middle term is acyclic.**
If the middle term of a short exact sequence of chain complexes of `ℚ`-modules is acyclic in
degrees `k` and `k - 1`, then `δ : H_k(X₃) → H_{k-1}(X₁)` is an isomorphism (`k ≥ 1`). -/
theorem isIso_δ_of_isZero (S : ShortComplex (ChainComplex (ModuleCat ℚ) ℕ)) (hS : S.ShortExact)
    (k : ℕ) (hk : 1 ≤ k) (h₁ : IsZero (S.X₂.homology k)) (h₂ : IsZero (S.X₂.homology (k - 1))) :
    IsIso (hS.δ k (k - 1) (by simp [ComplexShape.down]; omega)) := by
  have hrel : (ComplexShape.down ℕ).Rel k (k - 1) := by simp [ComplexShape.down]; omega
  have hmono : Mono (hS.δ k (k - 1) hrel) := by
    have hex₃ := hS.homology_exact₃ k (k - 1) hrel
    have hf : (ShortComplex.mk (HomologicalComplex.homologyMap S.g k) (hS.δ k (k - 1) hrel)
        (hS.comp_δ k (k - 1) hrel)).f = 0 := IsZero.eq_zero_of_src h₁ _
    exact (ShortComplex.exact_iff_mono _ hf).mp hex₃
  have hepi : Epi (hS.δ k (k - 1) hrel) := by
    have hex₁ := hS.homology_exact₁ k (k - 1) hrel
    have hg : (ShortComplex.mk (hS.δ k (k - 1) hrel) (HomologicalComplex.homologyMap S.f (k - 1))
        (hS.δ_comp k (k - 1) hrel)).g = 0 := IsZero.eq_zero_of_tgt h₂ _
    exact (ShortComplex.exact_iff_epi _ hg).mp hex₁
  exact isIso_of_mono_of_epi _

/-! ## Degree `0` connectivity of contractible spaces -/

/-- The degree-`0` map induced by the collapse of a contractible space is an isomorphism. -/
theorem isIso_toPoint_zero (X : TopCat) [ContractibleSpace ↥X] :
    IsIso (HomologicalComplex.homologyMap (Work.Cohomology.chainMap ℚ X (TopCat.of PUnit)
      (TopCat.ofHom (ContinuousMap.const ↥X PUnit.unit))) 0) := by
  obtain ⟨e⟩ := ContractibleSpace.hequiv ↥X PUnit
  let f : X ⟶ TopCat.of PUnit := TopCat.ofHom e.toFun
  let g : TopCat.of PUnit ⟶ X := TopCat.ofHom e.invFun
  have h1 : TopCat.Homotopy (f ≫ g) (𝟙 X) := e.left_inv.some
  have h2 : TopCat.Homotopy (g ≫ f) (𝟙 (TopCat.of PUnit)) := e.right_inv.some
  have h3 : IsIso (HomologicalComplex.homologyMap
      (Work.Cohomology.chainMap ℚ X (TopCat.of PUnit) f) 0) :=
    Work.Cohomology.homologyEquiv ℚ X (TopCat.of PUnit) f g h1 h2 0
  have heq : f = TopCat.ofHom (ContinuousMap.const ↥X PUnit.unit) := by
    apply TopCat.hom_ext
    exact ContinuousMap.ext (fun x => Subsingleton.elim _ _)
  rw [heq] at h3
  exact h3

/-- **Degree-`0` connectivity.**  A map `φ : S → X` from a nonempty subsingleton into a
contractible space induces an isomorphism `H_0(S;ℚ) ≅ H_0(X;ℚ)`. -/
theorem isIso_homologyMap_zero_of_subsingleton {S : Type} [TopologicalSpace S] [Subsingleton S]
    [Nonempty S] (X : TopCat) [ContractibleSpace ↥X] (φ : C(S, ↥X)) :
    IsIso (HomologicalComplex.homologyMap
      (Work.Cohomology.chainMap ℚ (TopCat.of S) X (TopCat.ofHom φ)) 0) := by
  haveI : ContractibleSpace S := inferInstance
  have hv : IsIso (HomologicalComplex.homologyMap (Work.Cohomology.chainMap ℚ X (TopCat.of PUnit)
      (TopCat.ofHom (ContinuousMap.const ↥X PUnit.unit))) 0) := isIso_toPoint_zero X
  have hw : IsIso (HomologicalComplex.homologyMap
      (Work.Cohomology.chainMap ℚ (TopCat.of S) (TopCat.of PUnit)
        (TopCat.ofHom (ContinuousMap.const S PUnit.unit))) 0) := isIso_toPoint_zero (TopCat.of S)
  have hfac : Work.Cohomology.chainMap ℚ (TopCat.of S) X (TopCat.ofHom φ) ≫
      Work.Cohomology.chainMap ℚ X (TopCat.of PUnit)
        (TopCat.ofHom (ContinuousMap.const ↥X PUnit.unit))
      = Work.Cohomology.chainMap ℚ (TopCat.of S) (TopCat.of PUnit)
        (TopCat.ofHom (ContinuousMap.const S PUnit.unit)) := by
    rw [Work.Cohomology.chainMap, Work.Cohomology.chainMap, Work.Cohomology.chainMap,
      ← Functor.map_comp]
    congr 1
  haveI := hv
  haveI : IsIso (HomologicalComplex.homologyMap
      (Work.Cohomology.chainMap ℚ (TopCat.of S) X (TopCat.ofHom φ)) 0 ≫
      HomologicalComplex.homologyMap (Work.Cohomology.chainMap ℚ X (TopCat.of PUnit)
        (TopCat.ofHom (ContinuousMap.const ↥X PUnit.unit))) 0) := by
    rw [← HomologicalComplex.homologyMap_comp, hfac]
    exact hw
  exact IsIso.of_isIso_comp_right
    (HomologicalComplex.homologyMap (Work.Cohomology.chainMap ℚ (TopCat.of S) X (TopCat.ofHom φ)) 0)
    (HomologicalComplex.homologyMap (Work.Cohomology.chainMap ℚ X (TopCat.of PUnit)
      (TopCat.ofHom (ContinuousMap.const ↥X PUnit.unit))) 0)

/-! ## The abstract cone pair -/

/-- **The homological cone pair.**  If `X` is contractible, `A ⊆ X` and `a ∈ A`, then for `k ≥ 1`

`H_k(X, A; ℚ) ≅ H_{k-1}(A, {a}; ℚ)`.

Geometrically, `A` is the base of the cone `X` and `{a}` the marked point of the base: the pair
`(X,A)` contributes the *reduced* homology of `A`, shifted by one. -/
theorem conePairIso (X : TopCat) [ContractibleSpace ↥X] (A : Set X) (a : X) (ha : a ∈ A)
    (k : ℕ) (hk : 1 ≤ k) :
    Nonempty (((Work.StemsB.relChainsR ℚ X A).homology k) ≅
      ((Work.StemsB.relChainsR ℚ (TopCat.of ↥A) {⟨a, ha⟩}).homology (k - 1))) := by
  haveI : Nonempty ↥({⟨a, ha⟩} : Set ↥A) := ⟨⟨⟨a, ha⟩, rfl⟩⟩
  -- the point of `A`, the two inclusions of the triple `{a} ⊆ A ⊆ X`
  set f := Work.StemsB.relChainsRIncl ℚ (TopCat.of ↥A) {⟨a, ha⟩} with hfdef
  set p := Work.StemsB.relChainsRIncl ℚ X A with hpdef
  haveI hf : Mono f := Work.StemsB.mono_chainMap_subtypeIncl_ring ℚ (TopCat.of ↥A) {⟨a, ha⟩}
  haveI hp : Mono p := Work.StemsB.mono_chainMap_subtypeIncl_ring ℚ X A
  set g := f ≫ p with hgdef
  haveI hg : Mono g := inferInstance
  -- the degree-`0` map of the pair `(X, {a})` is an isomorphism
  let φ : C(↥({⟨a, ha⟩} : Set ↥A), ↥X) :=
    ⟨fun y => (y.1 : ↥A).1, continuous_subtype_val.comp continuous_subtype_val⟩
  have hgφ : g = Work.Cohomology.chainMap ℚ (TopCat.of ↥({⟨a, ha⟩} : Set ↥A)) X
      (TopCat.ofHom φ) := by
    show Work.StemsB.relChainsRIncl ℚ (TopCat.of ↥A) {⟨a, ha⟩} ≫
      Work.StemsB.relChainsRIncl ℚ X A = _
    rw [Work.StemsB.relChainsRIncl, Work.StemsB.relChainsRIncl,
      Work.Cohomology.chainMap, Work.Cohomology.chainMap, ← Functor.map_comp]
    congr 1
  -- the middle term of the triple sequence is acyclic
  have hmid : ∀ j : ℕ, IsZero ((cokernel g).homology j) := by
    refine isZero_homology_third _ (ShortComplex.ShortExact.mk' (ShortComplex.exact_cokernel g)
      hg inferInstance) ?_ ?_ ?_
    · intro j hj
      exact Work.Cohomology.homologyContractible_ring ℚ j hj
    · intro j hj
      exact Work.Cohomology.homologyContractible_ring ℚ j hj
    · rw [hgφ]
      exact isIso_homologyMap_zero_of_subsingleton X φ
  -- the connecting homomorphism of the triple sequence
  have hSE : (ShortComplex.mk (cokernel.map f g (𝟙 _) p (by rw [Category.id_comp]))
      (cokernel.desc g (cokernel.π p)
        (by rw [Category.assoc, cokernel.condition, comp_zero]))
      (by
        apply (cancel_epi (cokernel.π f)).mp
        rw [← Category.assoc, cokernel.map, cokernel.π_desc, Category.assoc, cokernel.π_desc,
          cokernel.condition, comp_zero])).ShortExact :=
    Work.Cohomology.shortExact_cokernel_map f p g rfl
  have hrel : (ComplexShape.down ℕ).Rel k (k - 1) := by simp [ComplexShape.down]; omega
  have hiso : IsIso (hSE.δ k (k - 1) hrel) :=
    isIso_δ_of_isZero _ hSE k hk (hmid k) (hmid (k - 1))
  exact ⟨asIso (hSE.δ k (k - 1) hrel)⟩

/-! ## The three geometric/transport pieces (delegated elsewhere) -/

/-- The preimage of a point under the retraction of a mapping cylinder onto its target is
contractible: it is the cone on the fibre. -/
theorem cylRetractPreimageContractible {P X : Type} [TopologicalSpace P] [TopologicalSpace X]
    (f : C(P, X)) (z : X) : ContractibleSpace ↥((Work.Serre.cylRetract f) ⁻¹' {z}) := by
  have hmain : ∀ y : Work.Serre.cyl f, Work.Serre.cylRetract f y = z →
      ∀ s : unitInterval, Work.Serre.cylRetract f (Work.Serre.cylMove f (y, s)) = z := by
    intro y
    refine Quotient.inductionOn y ?_
    intro a
    rcases a with ⟨p, t⟩ | x
    · exact fun h s => h
    · exact fun h s => h
  refine (contractible_iff_id_nullhomotopic
    ↥((Work.Serre.cylRetract f) ⁻¹' {z})).mpr ?_
  refine ⟨⟨Work.Serre.cylInr f z, Set.mem_singleton_iff.mpr rfl⟩, ⟨{
    toFun := fun w => ⟨Work.Serre.cylMove f (w.2.1, w.1),
      hmain w.2.1 (Set.mem_singleton_iff.mp w.2.2) w.1⟩
    continuous_toFun := Continuous.subtype_mk
      ((Work.Serre.cylMove f).continuous.comp
        ((continuous_subtype_val.comp continuous_snd).prodMk continuous_fst)) _
    map_zero_left := fun w => by
      refine Subtype.ext ?_
      exact Work.Serre.cylMove_zero f w.1
    map_one_left := fun w => by
      refine Subtype.ext ?_
      show (Work.Serre.cylMove f (w.1, 1) : Work.Serre.cyl f) = Work.Serre.cylInr f z
      rw [Work.Serre.cylMove_one]
      exact congrArg (Work.Serre.cylInr f) (Set.mem_singleton_iff.mp w.2) }⟩⟩

/-- The base of the cone fibre of the mapping cylinder is the fibre of `q`: the point of the base
corresponding to `b` is sent to `b`. -/
theorem baseHomeoFibre (D : ℕ) (Γ : Type) [TopologicalSpace Γ] (ι : Type)
    (f : ι → C(Work.RatHurewicz.cellSphere (D - 2), Γ)) {X : Type} [TopologicalSpace X]
    (q : C(X, Work.RatHurewicz.attachCells (D - 2) Γ ι f)) (i : ι)
    (b : Work.StemsB.fibre q (Work.Serre.csrCentre (D - 2) Γ ι f i))
    (a : ↥((Work.Serre.cylRetract q) ⁻¹' {Work.Serre.csrCentre (D - 2) Γ ι f i}))
    (ha : a ∈ {x : ↥((Work.Serre.cylRetract q) ⁻¹' {Work.Serre.csrCentre (D - 2) Γ ι f i}) |
      (x : Work.Serre.cyl q) ∈ Set.range (Work.Serre.cylIncl q)})
    (h : (a : Work.Serre.cyl q) = Work.Serre.cylIncl q b.1) :
    ∃ e : ↥{x : ↥((Work.Serre.cylRetract q) ⁻¹' {Work.Serre.csrCentre (D - 2) Γ ι f i}) |
          (x : Work.Serre.cyl q) ∈ Set.range (Work.Serre.cylIncl q)} ≃ₜ
        Work.StemsB.fibre q (Work.Serre.csrCentre (D - 2) Γ ι f i),
      e ⟨a, ha⟩ = b := by
  obtain ⟨e₀, he₀⟩ := Work.Serre.cylHomeoExplicit q
  have key : ∀ (y : ↥((Work.Serre.cylRetract q) ⁻¹' {Work.Serre.csrCentre (D - 2) Γ ι f i}))
      (hy : (y : Work.Serre.cyl q) ∈ Set.range (Work.Serre.cylIncl q)),
      q (e₀.symm ⟨y.1, hy⟩) = Work.Serre.csrCentre (D - 2) Γ ι f i := by
    intro y hy
    have h1 : (e₀ (e₀.symm ⟨y.1, hy⟩) : Work.Serre.cyl q) = (y : Work.Serre.cyl q) := by
      rw [Homeomorph.apply_symm_apply]
    have h2 : q (e₀.symm ⟨y.1, hy⟩) =
        Work.Serre.cylRetract q (Work.Serre.cylIncl q (e₀.symm ⟨y.1, hy⟩)) :=
      (DFunLike.congr_fun (Work.Serre.cylRetract_cylIncl q) (e₀.symm ⟨y.1, hy⟩)).symm
    rw [h2, ← he₀ (e₀.symm ⟨y.1, hy⟩), h1]
    exact Set.mem_singleton_iff.mp y.2
  let Ψ : ↥{x : ↥((Work.Serre.cylRetract q) ⁻¹' {Work.Serre.csrCentre (D - 2) Γ ι f i}) |
        (x : Work.Serre.cyl q) ∈ Set.range (Work.Serre.cylIncl q)} →
      Work.StemsB.fibre q (Work.Serre.csrCentre (D - 2) Γ ι f i) :=
    fun y => ⟨e₀.symm ⟨y.1.1, y.2⟩, key y.1 y.2⟩
  let Φ : Work.StemsB.fibre q (Work.Serre.csrCentre (D - 2) Γ ι f i) →
      ↥{x : ↥((Work.Serre.cylRetract q) ⁻¹' {Work.Serre.csrCentre (D - 2) Γ ι f i}) |
        (x : Work.Serre.cyl q) ∈ Set.range (Work.Serre.cylIncl q)} :=
    fun x => ⟨⟨Work.Serre.cylIncl q x.1, by
        simp only [Set.mem_preimage, Set.mem_singleton_iff]
        exact (DFunLike.congr_fun (Work.Serre.cylRetract_cylIncl q) x.1).trans x.2⟩, ⟨x.1, rfl⟩⟩
  have hleft : ∀ y, Φ (Ψ y) = y := by
    intro y
    refine Subtype.ext ?_
    refine Subtype.ext ?_
    show (Work.Serre.cylIncl q (e₀.symm ⟨y.1.1, y.2⟩) : Work.Serre.cyl q) = y.1.1
    rw [← he₀ (e₀.symm ⟨y.1.1, y.2⟩), Homeomorph.apply_symm_apply]
  have hright : ∀ x, Ψ (Φ x) = x := by
    intro x
    refine Subtype.ext ?_
    show (e₀.symm (⟨(Work.Serre.cylIncl q x.1 : Work.Serre.cyl q), ⟨x.1, rfl⟩⟩ :
      ↥(Set.range (Work.Serre.cylIncl q))) : X) = x.1
    rw [show (⟨(Work.Serre.cylIncl q x.1 : Work.Serre.cyl q), ⟨x.1, rfl⟩⟩ :
          ↥(Set.range (Work.Serre.cylIncl q))) = e₀ x.1 from
        Subtype.ext (he₀ x.1).symm, Homeomorph.symm_apply_apply]
  have hcontΨ : Continuous Ψ :=
    Continuous.subtype_mk (((e₀.symm).continuous).comp
      (Continuous.subtype_mk (continuous_subtype_val.comp continuous_subtype_val) _)) _
  have hcontΦ : Continuous Φ :=
    Continuous.subtype_mk (Continuous.subtype_mk
      ((Work.Serre.cylIncl q).continuous.comp continuous_subtype_val) _) _
  let eu : ↥{x : ↥((Work.Serre.cylRetract q) ⁻¹' {Work.Serre.csrCentre (D - 2) Γ ι f i}) |
        (x : Work.Serre.cyl q) ∈ Set.range (Work.Serre.cylIncl q)} ≃
      Work.StemsB.fibre q (Work.Serre.csrCentre (D - 2) Γ ι f i) :=
    { toFun := Ψ
      invFun := Φ
      left_inv := hleft
      right_inv := hright }
  refine ⟨Homeomorph.mk eu hcontΨ ?_, ?_⟩
  · show Continuous ⇑eu.symm
    exact hcontΦ
  · refine Subtype.ext ?_
    show (e₀.symm (⟨(a : Work.Serre.cyl q), ha⟩ : ↥(Set.range (Work.Serre.cylIncl q))) : X) = b.1
    rw [show (⟨(a : Work.Serre.cyl q), ha⟩ : ↥(Set.range (Work.Serre.cylIncl q))) = e₀ b.1 from
      Subtype.ext (by rw [he₀ b.1]; exact h), Homeomorph.symm_apply_apply]

/-- **The cone pair of the fibre of a mapping-cylinder fibration.**

For a Serre fibration `q : X → attachCells (D-2) Γ ι f` and an attached cell centre `c`, the pair
`(P, A)` — where `P = (cylRetract q) ⁻¹' {c} ⊆ cyl q` is the cone on the fibre `F = q ⁻¹' {c}` and
`A` is the base of that cone — has the homology of the *reduced* homology of the fibre, shifted:

  `H_k(P, A; ℚ) ≅ H_{k-1}(F, {b}; ℚ)`   for `k ≥ 1` and any `b : F`.

This is the base case of the disc-pair tower (`Work.Serre.DiscPair.discCellStep`). -/
theorem centreConePair (D : ℕ) (Γ : Type) [TopologicalSpace Γ] (ι : Type)
    (f : ι → C(Work.RatHurewicz.cellSphere (D-2), Γ)) {X : Type} [TopologicalSpace X]
    (q : C(X, Work.RatHurewicz.attachCells (D-2) Γ ι f)) (hq : Work.StemsB.IsSerreFibration q)
    (i : ι) (b : Work.StemsB.fibre q (Work.Serre.csrCentre (D - 2) Γ ι f i)) (k : ℕ) (hk : 1 ≤ k) :
    Nonempty ((Work.StemsB.relChainsR ℚ
        (TopCat.of ↥((Work.Serre.cylRetract q) ⁻¹' {Work.Serre.csrCentre (D-2) Γ ι f i}))
        {x | (x : Work.Serre.cyl q) ∈ Set.range (Work.Serre.cylIncl q)}).homology k
      ≅ (Work.StemsB.relChainsR ℚ
          (TopCat.of (Work.StemsB.fibre q (Work.Serre.csrCentre (D-2) Γ ι f i)))
          {b}).homology (k-1)) := by
  let c := Work.Serre.csrCentre (D - 2) Γ ι f i
  let P : Set (Work.Serre.cyl q) := (Work.Serre.cylRetract q) ⁻¹' {c}
  let A : Set ↥P := {x | (x : Work.Serre.cyl q) ∈ Set.range (Work.Serre.cylIncl q)}
  let a : ↥P := ⟨Work.Serre.cylIncl q b.1, by
    show (Work.Serre.cylRetract q) (Work.Serre.cylIncl q b.1) = c
    exact (DFunLike.congr_fun (Work.Serre.cylRetract_cylIncl q) b.1).trans b.2⟩
  have ha : a ∈ A := ⟨b.1, rfl⟩
  have haeq : (a : Work.Serre.cyl q) = Work.Serre.cylIncl q b.1 := rfl
  obtain ⟨e, he⟩ := baseHomeoFibre D Γ ι f q i b a ha haeq
  haveI hcontr : ContractibleSpace ↥P := cylRetractPreimageContractible q c
  obtain ⟨iso₁⟩ := conePairIso (TopCat.of ↥P) A a ha k hk
  have he' : ∀ x : ↥A, x ∈ ({⟨a, ha⟩} : Set ↥A) ↔
      e x ∈ ({b} : Set (Work.StemsB.fibre q c)) := by
    intro x
    rw [Set.mem_singleton_iff, Set.mem_singleton_iff]
    exact ⟨fun hx => by rw [hx]; exact he, fun hx => e.injective (hx.trans he.symm)⟩
  obtain ⟨iso₂⟩ := Work.Serre.CsrSharp.relChainsRHomeomorphCompat ↥A
    (Work.StemsB.fibre q c) {⟨a, ha⟩} {b} e he' (k - 1)
  exact ⟨iso₁ ≪≫ iso₂⟩

end
end Work.Serre.DiscPair
