import Mathlib
import Submission.Work.Cohomology.pd_ab_incl_rel
import Submission.Work.Cohomology.pd_small_union_iso
import Submission.Work.Cohomology.relChainsProjective
import Submission.Work.Cohomology.relSmallCochains_iso
import Submission.Work.Cohomology.smallProj_spec

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The inclusion `C^*(X, A∪B) ⟶ C^*(X, A+B)` is a quasi-isomorphism

For open subsets `A, B ⊆ X` the inclusion of cochain complexes
`pdABInclRel X A B : C^*(X, A∪B) ⟶ C^*(X, A+B)` (from
`Submission/Work/Cohomology/pd_ab_incl_rel.lean`) induces an isomorphism on cohomology.

The proof is by duality.  The small chains of the cover `(A,B)` of the subspace `A ∪ B` corestrict to
the singular chains of `A ∪ B` by a chain map `Φ` which is a quasi-isomorphism and a degreewise split
monomorphism (`pd_small_union_iso`).  Consequently

* the dual `dualComplexMap Φ` is an epimorphism and a quasi-isomorphism, so its kernel `K` is
  acyclic;
* the restriction along `A ∪ B ↪ X` maps `C^*(X, A∪B) ⊆ C^*(X, A+B)` isomorphically onto `K`.

Hence `pdABInclRel` is a monomorphism whose cokernel is acyclic, so it is a quasi-isomorphism.

## Main result

* `Work.Cohomology.pdABCoh_quasiIso`
-/

set_option maxHeartbeats 3200000
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicTopology CategoryTheory.Limits Simplicial
open scoped Simplicial

namespace Work.Cohomology

noncomputable section

/-! ## The small chains of two subsets are the sum of the chains in the two subsets -/

/-- Every chain in `A` is a small chain for the pair `(A,B)`. -/
lemma range_inclChains_le_smallChainSubmodule {X : TopCat} (A B : Set X) (n : ℕ) :
    LinearMap.range (((inclChains X A).f n).hom) ≤ smallChainSubmodule A B n := by
  rintro x ⟨y, rfl⟩
  refine ⟨(smallOfU A B).f n y, ?_⟩
  have h := congrArg (fun (g : singularChains ℤ (TopCat.of A) ⟶ singularChains ℤ X) =>
      (ModuleCat.Hom.hom (g.f n)) y) (smallOfU_comp_smallToSing A B)
  simp only [HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply] at h
  exact h

/-- Every chain in `B` is a small chain for the pair `(A,B)`. -/
lemma range_inclChains_le_smallChainSubmoduleV {X : TopCat} (A B : Set X) (n : ℕ) :
    LinearMap.range (((inclChains X B).f n).hom) ≤ smallChainSubmodule A B n := by
  rintro x ⟨y, rfl⟩
  refine ⟨(smallOfV A B).f n y, ?_⟩
  have h := congrArg (fun (g : singularChains ℤ (TopCat.of B) ⟶ singularChains ℤ X) =>
      (ModuleCat.Hom.hom (g.f n)) y) (smallOfV_comp_smallToSing A B)
  simp only [HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply] at h
  exact h

/-- Every small chain is a sum of a chain in `A` and a chain in `B`. -/
lemma smallChainSubmodule_le_sup {X : TopCat} (A B : Set X) (n : ℕ) :
    smallChainSubmodule A B n ≤
      LinearMap.range (((inclChains X A).f n).hom)
        ⊔ LinearMap.range (((inclChains X B).f n).hom) := by
  let Q : Submodule ℤ ↥((singularChains ℤ X).X n) :=
    LinearMap.range (((inclChains X A).f n).hom) ⊔ LinearMap.range (((inclChains X B).f n).hom)
  intro c hc
  simp only [smallChainSubmodule] at hc
  obtain ⟨c', rfl⟩ := hc
  have hc' : ((ModuleCat.Hom.hom ((smallToSing A B).f n)) c') ∈ Q := by
    letI : Module ℤ (↥((singularChains ℤ X).X n) ⧸ Q) := Submodule.Quotient.module Q
    let q : (singularChains ℤ X).X n ⟶ ModuleCat.of ℤ (↥((singularChains ℤ X).X n) ⧸ Q) :=
      ModuleCat.ofHom (Submodule.mkQ Q)
    have hg : (smallToSing A B).f n ≫ q = 0 := by
      apply SSet.chainComplex_hom_ext (X := smallSSet A B) (R := ModuleCat.of ℤ ℤ)
      intro σ
      apply ModuleCat.hom_ext
      apply LinearMap.ext_ring
      simp only [ModuleCat.hom_comp, ModuleCat.hom_zero, LinearMap.comp_apply, LinearMap.zero_apply]
      show Submodule.Quotient.mk ((ModuleCat.Hom.hom ((smallToSing A B).f n))
        (genSSet (smallSSet A B) n σ)) = 0
      rw [smallToSing_gen, Submodule.Quotient.mk_eq_zero]
      change gen X n σ.1 ∈ LinearMap.range (((inclChains X A).f n).hom)
        ⊔ LinearMap.range (((inclChains X B).f n).hom)
      rcases σ.2 with h | h
      · obtain ⟨a, ha⟩ := exists_map_inclUX_of_range_subset A (Opposite.op ⦋n⦌) σ.1 h
        refine Submodule.mem_sup.mpr ⟨(inclChains X A).f n (gen (TopCat.of A) n a), ⟨_, rfl⟩,
          0, Submodule.zero_mem _, ?_⟩
        rw [add_zero]
        have h1 : (inclChains X A).f n (gen (TopCat.of A) n a)
            = gen X n ((TopCat.toSSet.map (subtypeIncl X A)).app (Opposite.op ⦋n⦌) a) :=
          chainComplexMap_ι_apply (TopCat.toSSet.map (subtypeIncl X A)) n a (1:ℤ)
        rw [h1, show (TopCat.toSSet.map (subtypeIncl X A)).app (Opposite.op ⦋n⦌) a = σ.1 from ha]
      · obtain ⟨a, ha⟩ := exists_map_inclUX_of_range_subset B (Opposite.op ⦋n⦌) σ.1 h
        refine Submodule.mem_sup.mpr ⟨0, Submodule.zero_mem _,
          (inclChains X B).f n (gen (TopCat.of B) n a), ⟨_, rfl⟩, ?_⟩
        rw [zero_add]
        have h1 : (inclChains X B).f n (gen (TopCat.of B) n a)
            = gen X n ((TopCat.toSSet.map (subtypeIncl X B)).app (Opposite.op ⦋n⦌) a) :=
          chainComplexMap_ι_apply (TopCat.toSSet.map (subtypeIncl X B)) n a (1:ℤ)
        rw [h1, show (TopCat.toSSet.map (subtypeIncl X B)).app (Opposite.op ⦋n⦌) a = σ.1 from ha]
    have h2 : (ModuleCat.Hom.hom ((smallToSing A B).f n ≫ q)) c' = 0 := by
      rw [hg, ModuleCat.hom_zero, LinearMap.zero_apply]
    rw [ModuleCat.hom_comp, LinearMap.comp_apply] at h2
    have h3 : ModuleCat.Hom.hom q = Submodule.mkQ Q := rfl
    rw [h3, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h2
    exact h2
  exact hc'

/-- **The small chains for the pair `(A,B)` are the sum of the chains in `A` and in `B`.** -/
theorem pd_smallChainSubmodule_eq_sup {X : TopCat} (A B : Set X) (n : ℕ) :
    smallChainSubmodule A B n =
      LinearMap.range (((inclChains X A).f n).hom)
        ⊔ LinearMap.range (((inclChains X B).f n).hom) :=
  le_antisymm (smallChainSubmodule_le_sup A B n) (sup_le
    (range_inclChains_le_smallChainSubmodule A B n)
    (range_inclChains_le_smallChainSubmoduleV A B n))

/-- A cochain vanishing on `A` and on `B` vanishes on every small chain. -/
lemma pdABKern_kill_smallToSing {X : TopCat} (A B : Set X) (n : ℕ)
    (φ : (pdABCoh X A B).X n) (x : (smallChains A B).X n) :
    (relDualLM X n φ.1) ((smallToSing A B).f n x) = 0 := by
  have hmem : (smallToSing A B).f n x ∈ smallChainSubmodule A B n := ⟨x, rfl⟩
  have hle := smallChainSubmodule_le_sup A B n hmem
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hle
  have hA : φ.1 ∈ relKern ℤ X A n := (pdABKern_mem_iff X A B n φ.1).mp φ.2 |>.1
  have hB : φ.1 ∈ relKern ℤ X B n := (pdABKern_mem_iff X A B n φ.1).mp φ.2 |>.2
  have hka : (relDualLM X n φ.1) a = 0 := by
    obtain ⟨y, rfl⟩ := ha
    exact (relDualKern_iff' X A n φ.1).mp hA y
  have hkb : (relDualLM X n φ.1) b = 0 := by
    obtain ⟨y, rfl⟩ := hb
    exact (relDualKern_iff' X B n φ.1).mp hB y
  rw [← hab, map_add, hka, hkb, add_zero]

/-! ## The restriction of `C^*(X,A+B)` to `C^*(X,A∪B)` -/

/-- The restriction of the `A+B`-cochains of `X` to the singular chains of the subspace `A ∪ B`. -/
def pdFB (X : TopCat) (A B : Set X) :
    pdABCoh X A B ⟶
      singularCochainComplex ℤ (TopCat.of (A ∪ B : Set X)) :=
  (pdABInclA X A B ≫ relIncl ℤ X A) ≫
    dualComplexMap ℤ (singularChains ℤ (TopCat.of (A ∪ B : Set X))) (singularChains ℤ X)
      (inclChains X (A ∪ B))

/-- The underlying linear map of the inclusion `C^*(X,A+B) ⟶ C^*(X)`. -/
@[simp] lemma pdABInclA_relIncl_apply (X : TopCat) (A B : Set X) (n : ℕ)
    (φ : (pdABCoh X A B).X n) :
    (ModuleCat.Hom.hom ((pdABInclA X A B ≫ relIncl ℤ X A).f n)) φ = relDualLM X n φ.1 := by
  rw [HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply]
  rfl

/-- The `n`-th component of `pdFB` is composition with the inclusion of the chains of `A ∪ B`. -/
@[simp] lemma pdFB_f_apply (X : TopCat) (A B : Set X) (n : ℕ)
    (φ : (pdABCoh X A B).X n) :
    (ModuleCat.Hom.hom ((pdFB X A B).f n)) φ
      = (relDualLM X n φ.1).comp (((inclChains X (A ∪ B)).f n).hom) := by
  rw [pdFB, HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply]
  erw [dualComplexMap_f, dualComplexMapComp_apply', pdABInclA_relIncl_apply]

/-- The dual of the small inclusion of the cover. -/
def pdH (X : TopCat) (A B : Set X)
    (Φ : smallChains A B ⟶ singularChains ℤ (TopCat.of (A ∪ B : Set X))) :
    singularCochainComplex ℤ (TopCat.of (A ∪ B : Set X)) ⟶
      dualComplex ℤ (smallChains A B) :=
  dualComplexMap ℤ (smallChains A B) (singularChains ℤ (TopCat.of (A ∪ B : Set X))) Φ

/-- The `n`-th component of `pdH` is composition with `Φ`. -/
@[simp] lemma pdH_f_apply (X : TopCat) (A B : Set X)
    (Φ : smallChains A B ⟶ singularChains ℤ (TopCat.of (A ∪ B : Set X))) (n : ℕ)
    (ψ : (singularCochainComplex ℤ (TopCat.of (A ∪ B : Set X))).X n) :
    (ModuleCat.Hom.hom ((pdH X A B Φ).f n)) ψ = ψ.comp ((Φ.f n).hom) := by
  rw [pdH]
  erw [dualComplexMap_f, dualComplexMapComp_apply']

/-- The restriction `pdFB` followed by `pdH` is zero. -/
theorem pdFB_comp_pdH (X : TopCat) (A B : Set X)
    (Φ : smallChains A B ⟶ singularChains ℤ (TopCat.of (A ∪ B : Set X)))
    (hΦ : Φ ≫ inclChains X (A ∪ B) = smallToSing A B) :
    pdFB X A B ≫ pdH X A B Φ = 0 := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro φ
  rw [HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply]
  erw [pdH_f_apply, pdFB_f_apply]
  rw [HomologicalComplex.zero_f, ModuleCat.hom_zero, LinearMap.zero_apply]
  apply LinearMap.ext
  intro x
  have hcomp : (((inclChains X (A ∪ B)).f n).hom).comp ((Φ.f n).hom)
      = (((smallToSing A B).f n)).hom := by
    have h := congrArg (fun (g : smallChains A B ⟶ singularChains ℤ X) =>
      (ModuleCat.Hom.hom (g.f n))) hΦ
    rw [HomologicalComplex.comp_f, ModuleCat.hom_comp] at h
    exact h
  rw [LinearMap.comp_assoc, hcomp, LinearMap.comp_apply]
  exact pdABKern_kill_smallToSing A B n φ x

/-- `pdH` is an epimorphism: the degreewise splitting of `Φ` dualises. -/
theorem pdH_epi (X : TopCat) (A B : Set X)
    (Φ : smallChains A B ⟶ singularChains ℤ (TopCat.of (A ∪ B : Set X)))
    (hΦ : Φ ≫ inclChains X (A ∪ B) = smallToSing A B) :
    Epi (pdH X A B Φ) := by
  have hretr : ∀ n, (Φ.f n) ≫ ((inclChains X (A ∪ B)).f n ≫ smallProj A B n)
      = 𝟙 ((smallChains A B).X n) := by
    intro n
    rw [← Category.assoc, ← HomologicalComplex.comp_f, hΦ]
    exact (smallProj_spec A B).1 n
  have hcomp : ∀ n, (ModuleCat.Hom.hom
        (((inclChains X (A ∪ B)).f n ≫ smallProj A B n))).comp ((Φ.f n).hom) = LinearMap.id := by
    intro n
    have h := congrArg ModuleCat.Hom.hom (hretr n)
    rw [ModuleCat.hom_comp, ModuleCat.hom_id] at h
    exact h
  apply HomologicalComplex.epi_of_epi_f
  intro n
  rw [ModuleCat.epi_iff_surjective]
  intro ψ
  refine ⟨ψ.comp (ModuleCat.Hom.hom (((inclChains X (A ∪ B)).f n ≫ smallProj A B n))), ?_⟩
  apply LinearMap.ext
  intro x
  simp only [pdH_f_apply, LinearMap.comp_apply]
  have hx : (ModuleCat.Hom.hom (((inclChains X (A ∪ B)).f n ≫ smallProj A B n)))
      ((ModuleCat.Hom.hom ((Φ.f n))) x) = x := LinearMap.congr_fun (hcomp n) x
  rw [hx]


/-! ## The comparison of the restriction `pdFB` with `pdH` -/

/-- The kernel of `pdFB` is the image of `pdABInclRel`. -/
theorem pdFB_ker_eq_range (X : TopCat) (A B : Set X) (n : ℕ) :
    LinearMap.ker ((pdFB X A B).f n).hom
      = LinearMap.range ((pdABInclRel X A B).f n).hom := by
  ext φ
  constructor
  · intro hφ
    rw [LinearMap.mem_ker, pdFB_f_apply] at hφ
    refine ⟨⟨φ.1, ?_⟩, ?_⟩
    · rw [relDualKern_iff']
      intro y
      have h := LinearMap.congr_fun hφ y
      rw [LinearMap.comp_apply, LinearMap.zero_apply] at h
      exact h
    · apply Subtype.ext
      rw [pdABInclRel_coe]
  · intro hφ
    obtain ⟨x, rfl⟩ := hφ
    rw [LinearMap.mem_ker, pdFB_f_apply]
    apply LinearMap.ext
    intro y
    simp only [LinearMap.comp_apply, LinearMap.zero_apply]
    rw [pdABInclRel_coe]
    exact (relDualKern_iff' X (A ∪ B) n x.1).mp x.2 y

/-- The image of `pdFB` is the kernel of `pdH`. -/
theorem pdFB_range_eq_ker (X : TopCat) (A B : Set X)
    (Φ : smallChains A B ⟶ singularChains ℤ (TopCat.of (A ∪ B : Set X)))
    (hΦ : Φ ≫ inclChains X (A ∪ B) = smallToSing A B) (n : ℕ) :
    LinearMap.range ((pdFB X A B).f n).hom = LinearMap.ker ((pdH X A B Φ).f n).hom := by
  have hS : ((((inclChains X (A ∪ B)).f n).hom)).comp ((Φ.f n).hom)
      = ((smallToSing A B).f n).hom := by
    have h := congrArg (fun (g : smallChains A B ⟶ singularChains ℤ X) =>
      (ModuleCat.Hom.hom (g.f n))) hΦ
    rw [HomologicalComplex.comp_f, ModuleCat.hom_comp] at h
    exact h
  have hsmallU : ((smallOfU A B).f n ≫ (smallToSing A B).f n).hom
      = ((inclChains X A).f n).hom := by
    have h := congrArg (fun (g : singularChains ℤ (TopCat.of A) ⟶ singularChains ℤ X) =>
      (ModuleCat.Hom.hom (g.f n))) (smallOfU_comp_smallToSing A B)
    exact h
  have hsmallV : ((smallOfV A B).f n ≫ (smallToSing A B).f n).hom
      = ((inclChains X B).f n).hom := by
    have h := congrArg (fun (g : singularChains ℤ (TopCat.of B) ⟶ singularChains ℤ X) =>
      (ModuleCat.Hom.hom (g.f n))) (smallOfV_comp_smallToSing A B)
    exact h
  have hS' : ∀ x : (smallChains A B).X n,
      (ModuleCat.Hom.hom ((inclChains X (A ∪ B)).f n)) ((ModuleCat.Hom.hom ((Φ.f n))) x)
        = (ModuleCat.Hom.hom ((smallToSing A B).f n)) x := by
    intro x
    have key := LinearMap.congr_fun hS x
    rwa [LinearMap.comp_apply] at key
  have hcr : ∀ z : ↥((singularChains ℤ (TopCat.of (A ∪ B : Set X))).X n),
      (ModuleCat.Hom.hom (chainRetract ℤ X (A ∪ B) n))
        ((ModuleCat.Hom.hom ((inclChains X (A ∪ B)).f n)) z) = z := by
    intro z
    have h := LinearMap.congr_fun
      (congrArg ModuleCat.Hom.hom (chainRetract_spec ℤ X (A ∪ B) n)) z
    rw [ModuleCat.hom_comp, ModuleCat.hom_id, LinearMap.comp_apply, LinearMap.id_apply] at h
    exact h
  have hkill : ∀ y : ↥((singularChains ℤ (TopCat.of A)).X n),
      (ModuleCat.Hom.hom ((inclChains X A).f n)) y
        = (ModuleCat.Hom.hom ((inclChains X (A ∪ B)).f n))
            ((ModuleCat.Hom.hom ((Φ.f n)))
              ((ModuleCat.Hom.hom ((smallOfU A B).f n)) y)) := by
    intro y
    have key := LinearMap.congr_fun hsmallU y
    rw [ModuleCat.hom_comp, LinearMap.comp_apply, ← hS'] at key
    exact key.symm
  have hkill' : ∀ y : ↥((singularChains ℤ (TopCat.of B)).X n),
      (ModuleCat.Hom.hom ((inclChains X B).f n)) y
        = (ModuleCat.Hom.hom ((inclChains X (A ∪ B)).f n))
            ((ModuleCat.Hom.hom ((Φ.f n)))
              ((ModuleCat.Hom.hom ((smallOfV A B).f n)) y)) := by
    intro y
    have key := LinearMap.congr_fun hsmallV y
    rw [ModuleCat.hom_comp, LinearMap.comp_apply, ← hS'] at key
    exact key.symm
  ext ψ
  constructor
  · rintro ⟨φ, rfl⟩
    rw [LinearMap.mem_ker, pdH_f_apply, pdFB_f_apply]
    apply LinearMap.ext
    intro x
    simp only [LinearMap.comp_apply, LinearMap.zero_apply]
    rw [hS']
    exact pdABKern_kill_smallToSing A B n φ x
  · intro hψ
    have hψ0 : ∀ z : (smallChains A B).X n,
        relDualLM (TopCat.of (A ∪ B : Set X)) n ψ ((ModuleCat.Hom.hom ((Φ.f n))) z) = 0 := by
      intro z
      have h : (relDualLM (TopCat.of (A ∪ B : Set X)) n ψ).comp
          ((Φ.f n).hom) = 0 := by
        have h2 : (ModuleCat.Hom.hom ((pdH X A B Φ).f n)) ψ = 0 := by
          rw [LinearMap.mem_ker] at hψ; exact hψ
        rwa [pdH_f_apply] at h2
      have key := LinearMap.congr_fun h z
      rw [LinearMap.comp_apply, LinearMap.zero_apply] at key
      exact key
    refine ⟨⟨(relDualLM (TopCat.of (A ∪ B : Set X)) n ψ).comp
      (chainRetract ℤ X (A ∪ B) n).hom, ?_⟩, ?_⟩
    · rw [pdABKern_mem_iff]
      constructor
      · rw [relDualKern_iff']
        intro y
        simp only [LinearMap.comp_apply]
        rw [hkill y]
        erw [hcr]
        exact hψ0 _
      · rw [relDualKern_iff']
        intro y
        simp only [LinearMap.comp_apply]
        rw [hkill' y]
        erw [hcr]
        exact hψ0 _
    · rw [pdFB_f_apply]
      apply LinearMap.ext
      intro z
      simp only [relDualLM, LinearMap.comp_apply]
      erw [hcr]

/-! ## The short exact sequence `0 → C^*(X,A∪B) → C^*(X,A+B) → K → 0` -/

/-- The corestriction of `pdFB` to the kernel of `pdH`. -/
noncomputable def pdG (X : TopCat) (A B : Set X)
    (Φ : smallChains A B ⟶ singularChains ℤ (TopCat.of (A ∪ B : Set X)))
    (hΦ : Φ ≫ inclChains X (A ∪ B) = smallToSing A B) :
    pdABCoh X A B ⟶ kernel (pdH X A B Φ) :=
  kernel.lift (pdH X A B Φ) (pdFB X A B) (pdFB_comp_pdH X A B Φ hΦ)

/-- The defining property of `pdG`. -/
theorem pdG_comp_kernel_ι (X : TopCat) (A B : Set X)
    (Φ : smallChains A B ⟶ singularChains ℤ (TopCat.of (A ∪ B : Set X)))
    (hΦ : Φ ≫ inclChains X (A ∪ B) = smallToSing A B) :
    pdG X A B Φ hΦ ≫ kernel.ι (pdH X A B Φ) = pdFB X A B :=
  kernel.lift_ι _ _ _

/-- `pdABInclRel` followed by the restriction `pdFB` is zero. -/
theorem pdABIncl_kill_pdFB (X : TopCat) (A B : Set X) :
    pdABInclRel X A B ≫ pdFB X A B = 0 := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rw [HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply]
  erw [pdFB_f_apply]
  rw [HomologicalComplex.zero_f, ModuleCat.hom_zero, LinearMap.zero_apply]
  apply LinearMap.ext
  intro y
  simp only [LinearMap.comp_apply, LinearMap.zero_apply]
  rw [pdABInclRel_coe]
  exact (relDualKern_iff' X (A ∪ B) n x.1).mp x.2 y

/-- `pdABInclRel` followed by `pdG` is zero. -/
theorem pdABIncl_pdG (X : TopCat) (A B : Set X)
    (Φ : smallChains A B ⟶ singularChains ℤ (TopCat.of (A ∪ B : Set X)))
    (hΦ : Φ ≫ inclChains X (A ∪ B) = smallToSing A B) :
    pdABInclRel X A B ≫ pdG X A B Φ hΦ = 0 := by
  rw [← cancel_mono (kernel.ι (pdH X A B Φ)), Category.assoc, pdG_comp_kernel_ι,
    pdABIncl_kill_pdFB, zero_comp]

/-- The short complex `0 ⟶ C^*(X,A∪B) ⟶ C^*(X,A+B) ⟶ ker(pdH) ⟶ 0`. -/
noncomputable def pdS (X : TopCat) (A B : Set X)
    (Φ : smallChains A B ⟶ singularChains ℤ (TopCat.of (A ∪ B : Set X)))
    (hΦ : Φ ≫ inclChains X (A ∪ B) = smallToSing A B) :
    ShortComplex (CochainComplex (ModuleCat ℤ) ℕ) :=
  ShortComplex.mk (pdABInclRel X A B) (pdG X A B Φ hΦ) (pdABIncl_pdG X A B Φ hΦ)

/-- The short complex `pdS` is short exact in every degree. -/
theorem pdS_degreewise_shortExact (X : TopCat) (A B : Set X)
    (Φ : smallChains A B ⟶ singularChains ℤ (TopCat.of (A ∪ B : Set X)))
    (hΦ : Φ ≫ inclChains X (A ∪ B) = smallToSing A B) (n : ℕ) :
    ((pdS X A B Φ hΦ).map (HomologicalComplex.eval (ModuleCat ℤ) (ComplexShape.up ℕ) n)).ShortExact := by
  have hk : ((pdFB X A B).f n) ≫ ((pdH X A B Φ).f n) = 0 := by
    have h := congrArg (fun (g : pdABCoh X A B ⟶ dualComplex ℤ (smallChains A B)) =>
      HomologicalComplex.Hom.f g n) (pdFB_comp_pdH X A B Φ hΦ)
    rw [HomologicalComplex.comp_f, HomologicalComplex.zero_f] at h
    exact h
  set e := asIso (kernelComparison (pdH X A B Φ)
    (HomologicalComplex.eval (ModuleCat ℤ) (ComplexShape.up ℕ) n)) with he
  have he_comm : e.hom ≫ kernel.ι ((pdH X A B Φ).f n) = (kernel.ι (pdH X A B Φ)).f n :=
    kernelComparison_comp_ι _ _
  have hlift : ∀ z, (ModuleCat.Hom.hom (kernel.ι ((pdH X A B Φ).f n)))
      ((ModuleCat.Hom.hom (kernel.lift ((pdH X A B Φ).f n) ((pdFB X A B).f n) hk)) z)
      = ((pdFB X A B).f n).hom z := by
    intro z
    have h := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom
      (kernel.lift_ι ((pdH X A B Φ).f n) ((pdFB X A B).f n) hk)) z
    rw [ModuleCat.hom_comp, LinearMap.comp_apply] at h
    exact h
  have hcomm : ((pdG X A B Φ hΦ).f n) ≫ e.hom
      = kernel.lift ((pdH X A B Φ).f n) ((pdFB X A B).f n) hk := by
    apply (cancel_mono (kernel.ι ((pdH X A B Φ).f n))).1
    rw [Category.assoc, he_comm, ← HomologicalComplex.comp_f, pdG_comp_kernel_ι, kernel.lift_ι]
  refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
  · rw [ShortComplex.moduleCat_exact_iff]
    intro x₂ hx₂
    have hx₂' : (ModuleCat.Hom.hom ((pdG X A B Φ hΦ).f n)) x₂ = 0 := by
      have h := hx₂
      rw [ShortComplex.map_g] at h
      exact h
    have h1 : (kernel.lift ((pdH X A B Φ).f n) ((pdFB X A B).f n) hk).hom x₂ = 0 := by
      have h : ((((pdG X A B Φ hΦ).f n) ≫ e.hom).hom) x₂ = 0 := by
        rw [ModuleCat.hom_comp, LinearMap.comp_apply, hx₂', map_zero]
      rwa [hcomm] at h
    have h2 : ((pdFB X A B).f n).hom x₂ = 0 := by
      have h := congrArg (fun w => (ModuleCat.Hom.hom (kernel.ι ((pdH X A B Φ).f n))) w) h1
      rw [LinearMap.map_zero, hlift] at h
      exact h
    rw [← LinearMap.mem_ker] at h2
    rw [pdFB_ker_eq_range X A B n] at h2
    exact h2
  · rw [ModuleCat.mono_iff_injective]
    intro a b hab
    exact Subtype.ext (congrArg (fun z : ↥(pdABKern X A B n) => z.1) hab)
  · rw [ModuleCat.epi_iff_surjective]
    intro y
    have hker : (ModuleCat.Hom.hom ((pdH X A B Φ).f n))
        ((ModuleCat.Hom.hom (kernel.ι ((pdH X A B Φ).f n))) (e.hom y)) = 0 := by
      have h := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom
        (kernel.condition ((pdH X A B Φ).f n))) (e.hom y)
      rw [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero, LinearMap.zero_apply] at h
      exact h
    have hy : (ModuleCat.Hom.hom (kernel.ι ((pdH X A B Φ).f n))) (e.hom y)
        ∈ LinearMap.range ((pdFB X A B).f n).hom := by
      rw [pdFB_range_eq_ker X A B Φ hΦ n, LinearMap.mem_ker]
      exact hker
    obtain ⟨x, hx⟩ := hy
    refine ⟨x, ?_⟩
    have key : e.hom (((pdG X A B Φ hΦ).f n).hom x) = e.hom y := by
      have h1 : (kernel.lift ((pdH X A B Φ).f n) ((pdFB X A B).f n) hk).hom x = e.hom y := by
        refine (ModuleCat.mono_iff_injective (kernel.ι ((pdH X A B Φ).f n))).mp inferInstance ?_
        rw [hlift x, ← hx]
      have h2 : ((((pdG X A B Φ hΦ).f n) ≫ e.hom).hom) x = e.hom y := by
        rw [hcomm]; exact h1
      rwa [ModuleCat.hom_comp, LinearMap.comp_apply] at h2
    exact (ModuleCat.mono_iff_injective e.hom).mp inferInstance key

/-! ## The final assembly -/

/-- A short exact sequence of cochain complexes whose third term is acyclic has its first map a
quasi-isomorphism in every degree. -/
lemma isIso_homologyMap_of_shortExact_of_acyclic_X₃
    {S : ShortComplex (CochainComplex (ModuleCat ℤ) ℕ)} (hS : S.ShortExact)
    (h3 : S.X₃.Acyclic) (n : ℕ) :
    IsIso (HomologicalComplex.homologyMap S.f n) := by
  haveI hmf : Mono S.f := hS.mono_f
  have hz : IsZero (S.X₃.homology n) :=
    (HomologicalComplex.exactAt_iff_isZero_homology S.X₃ n).mp (h3 n)
  have hg : HomologicalComplex.homologyMap S.g n = 0 := IsZero.eq_of_tgt hz _ _
  haveI hepi : Epi (HomologicalComplex.homologyMap S.f n) :=
    (ShortComplex.exact_iff_epi _ hg).mp (hS.homology_exact₂ n)
  haveI hmono : Mono (HomologicalComplex.homologyMap S.f n) := by
    rcases n with _ | m
    · exact HomologicalComplex.mono_homologyMap_of_mono_of_not_rel S.f 0
        (fun i hi => by rw [ComplexShape.up_Rel] at hi; omega)
    · haveI : IsZero (S.X₃.homology m) :=
        (HomologicalComplex.exactAt_iff_isZero_homology S.X₃ m).mp (h3 m)
      have hf : hS.δ m (m+1) (by rw [ComplexShape.up_Rel]) = 0 := IsZero.eq_of_src this _ _
      exact (ShortComplex.exact_iff_mono _ hf).mp
        (hS.homology_exact₁ m (m+1) (by rw [ComplexShape.up_Rel]))
  exact isIso_of_mono_of_epi _

theorem pdABCoh_quasiIso {X : TopCat} {A B : Set X} (hA : IsOpen A) (hB : IsOpen B) (n : ℕ) :
    CategoryTheory.IsIso (HomologicalComplex.homologyMap
      (Work.Cohomology.pdABInclRel X A B) n) := by
  obtain ⟨Φ, hΦ1, hΦ2, _, _⟩ := pd_small_union_iso A B hA hB
  have hqiso : QuasiIso (pdH X A B Φ) := by
    rw [quasiIso_iff]
    intro k
    rw [quasiIsoAt_iff_isIso_homologyMap]
    exact dualComplexMap_quasiIso Φ (fun k => projective_smallChains X A B k)
      (fun k => projective_singularChains (TopCat.of (A ∪ B : Set X)) k) hΦ2 k
  have hKac : (kernel (pdH X A B Φ)).Acyclic :=
    ShortComplex.ShortExact.acyclic_X₁
      { exact := ShortComplex.exact_kernel (pdH X A B Φ)
        mono_f := inferInstance
        epi_g := pdH_epi X A B Φ hΦ1 } hqiso
  have hS : (pdS X A B Φ hΦ1).ShortExact :=
    HomologicalComplex.shortExact_of_degreewise_shortExact (pdS X A B Φ hΦ1)
      (fun k => pdS_degreewise_shortExact X A B Φ hΦ1 k)
  exact isIso_homologyMap_of_shortExact_of_acyclic_X₃ hS hKac n

end

end Work.Cohomology
