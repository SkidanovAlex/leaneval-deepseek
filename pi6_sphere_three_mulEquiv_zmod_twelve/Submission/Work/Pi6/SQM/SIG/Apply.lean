import Mathlib
import Submission.Work.Pi6.SQM.SIG.Basic
import Submission.Work.Pi6.SQM.SIG.pbComp
import Submission.Work.Pi6.SQM.SIG.cochainDiffPb
import Submission.Work.Pi6.SQM.SIG.clsPb
import Submission.Work.Pi6.SQM.SIG.relClassOfNatural
import Submission.Work.Pi6.SQM.SIG.pairDeltaApply
import Submission.Work.Pi6.SQM.SIG.classZeroCoboundary
import Submission.Work.Cohomology.CompactSupport
import Submission.Work.Cohomology.relIncl_relCupH
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option linter.style.haveILetI false

open CategoryTheory Limits AlgebraicTopology Work.Cohomology
open scoped Simplicial

namespace Work.Pi6.SQM.SIG

noncomputable section

/-- A map of simplicial sets factoring through the inclusion of the subspace `A` kills every
relative cochain of `(X,A)`. -/
theorem pb_eq_zero_of_factors {X : TopCat} (A : Set X) {Z : SSet} (f : Z ⟶ SX X)
    (c : Z ⟶ SX ↥A) (hf : f = c ≫ TopCat.toSSet.map (subtypeIncl X A)) {n : ℕ}
    (u : relKern F2 X A n) : pb f u.1 = 0 := by
  rw [hf, pbComp, pb_subtypeIncl_relKern, pb_zero]

/-- The constant map at `k₀`, as a map of simplicial sets into `SX K` (`K = TopCat.of K`). -/
def constSSet (K : Type) [TopologicalSpace K] (k₀ : K) {Z : SSet}
    (g : Z ⟶ SX ↥({k₀} : Set K)) : Z ⟶ SX K :=
  g ≫ TopCat.toSSet.map (subtypeIncl (TopCat.of K) ({k₀} : Set K))

/-- The composite `(fibre ↪ PK) ≫ evalOne` is the constant map at `k₀`. -/
theorem comp_inclA_ev (K : Type) [TopologicalSpace K] (k₀ : K) :
    inclASSet K k₀ ≫ evSSet K k₀ =
      constSSet K k₀ (TopCat.toSSet.map (TopCat.ofHom
        (⟨fun _ : ↥(fibreSet K k₀) => (⟨k₀, rfl⟩ : ↥({k₀} : Set K)),
          continuous_const⟩ : C(↥(fibreSet K k₀), ↥({k₀} : Set K))))) := by
  rw [constSSet, inclASSet, evSSet, ← Functor.map_comp, ← Functor.map_comp]
  congr 1
  apply TopCat.ext
  intro x
  exact x.2

/-- The composite `ΩK ↪ PK ≫ evalOne` is the constant map at `k₀`. -/
theorem comp_loop_ev (K : Type) [TopologicalSpace K] (k₀ : K) :
    loopSSet K k₀ ≫ evSSet K k₀ =
      constSSet K k₀ (TopCat.toSSet.map (TopCat.ofHom
        (⟨fun _ : Path k₀ k₀ => (⟨k₀, rfl⟩ : ↥({k₀} : Set K)),
          continuous_const⟩ : C(Path k₀ k₀, ↥({k₀} : Set K))))) := by
  rw [constSSet, loopSSet, evSSet, ← Functor.map_comp, ← Functor.map_comp]
  congr 1
  apply TopCat.ext
  intro γ
  exact γ.target'

/-- The image of a relative cocycle of `(K,{k₀})` under the map of pairs `(PK, ΩK) → (K,{k₀})`. -/
def qStarRel (K : Type) [TopologicalSpace K] (k₀ : K) (m : ℕ)
    (ã : relKern F2 (TopCat.of K) ({k₀} : Set K) m) :
    relKern F2 (TopCat.of (PK K k₀)) (fibreSet K k₀) m :=
  relMapLM F2 (fibreSet K k₀) ({k₀} : Set K) (TopCat.ofHom (Work.StemsB.evalOne K k₀))
    (fun x hx => hx) m ã

/-- The image of a relative cocycle under the pair map is computed by the cochain pullback. -/
theorem pairMapK_coe (K : Type) [TopologicalSpace K] (k₀ : K) {m : ℕ}
    (ã : relKern F2 (TopCat.of K) ({k₀} : Set K) m) :
    (qStarRel K k₀ m ã).1 = pb (evSSet K k₀) ã.1 := rfl

/-- The underlying cochain of a relative cocycle is a cocycle. -/
theorem relDiffLM_zero_cochainDiff {X : TopCat} {A : Set X} {m : ℕ} (ã : relKern F2 X A m)
    (hã : relDiffLM F2 X A m ã = 0) : cochainDiff F2 (SX X) ã.1 = 0 := by
  have h := congrArg Subtype.val hã
  simpa only [relDiffLM_coe, Submodule.coe_zero, singularCochain_d_apply] using h

/-- The inverse of an isomorphism of `𝔽₂`-modules, applied to the image of an element. -/
theorem asIso_inv_apply {M N : ModuleCat F2} (f : M ⟶ N) (h : IsIso f) (y : M) :
    (@asIso _ _ _ _ f h).inv.hom (f.hom y) = y := by
  have h2 := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom (Iso.hom_inv_id (@asIso _ _ _ _ f h))) y
  simpa only [ModuleCat.hom_comp, ModuleCat.hom_id, LinearMap.comp_apply, LinearMap.id_apply,
    asIso_hom] using h2

/-- The homeomorphism `ΩK → fibre`, as a map of simplicial sets. -/
def homeoSSet (K : Type) [TopologicalSpace K] (k₀ : K) : SX (Path k₀ k₀) ⟶ SX ↥(fibreSet K k₀) :=
  TopCat.toSSet.map (TopCat.ofHom
    (⟨(fibreSetHomeo K k₀).symm.toFun, (fibreSetHomeo K k₀).symm.continuous_toFun⟩ :
      C(Path k₀ k₀, ↥(fibreSet K k₀))))

/-- The inverse of `fibreCohIso` is computed by pullback along the homeomorphism. -/
theorem fibreCohIso_inv_apply (K : Type) [TopologicalSpace K] (k₀ : K) (n : ℕ)
    (u : Cochain F2 (SX ↥(fibreSet K k₀)) n)
    (hu : cochainDiff F2 (SX ↥(fibreSet K k₀)) u = 0)
    (h : cochainDiff F2 (SX (Path k₀ k₀)) (pb (homeoSSet K k₀) u) = 0) :
    (fibreCohIso K k₀ n).inv (cls u hu) = cls (pb (homeoSSet K k₀) u) h := by
  have H : (fibreCohIso K k₀ n).inv = singularCohomologyMap F2 (TopCat.of (Path k₀ k₀))
      (TopCat.of ↥(fibreSet K k₀)) (TopCat.ofHom
        (⟨(fibreSetHomeo K k₀).symm.toFun, (fibreSetHomeo K k₀).symm.continuous_toFun⟩ :
          C(Path k₀ k₀, ↥(fibreSet K k₀)))) n := by
    simp only [fibreCohIso, homeoSSet, Iso.symm_inv, asIso_hom]
  rw [H]
  exact (clsPb (⟨(fibreSetHomeo K k₀).symm.toFun, (fibreSetHomeo K k₀).symm.continuous_toFun⟩ :
    C(Path k₀ k₀, ↥(fibreSet K k₀))) n u hu h).symm

/-- The composite `ΩK ≅ fibre ↪ PK` is the inclusion `ΩK ↪ PK`. -/
theorem homeo_incl_eq_loop (K : Type) [TopologicalSpace K] (k₀ : K) :
    homeoSSet K k₀ ≫ inclASSet K k₀ = loopSSet K k₀ := by
  have hcm : (TopCat.ofHom
      (⟨(fibreSetHomeo K k₀).symm.toFun, (fibreSetHomeo K k₀).symm.continuous_toFun⟩ :
        C(Path k₀ k₀, ↥(fibreSet K k₀)))) ≫ subtypeIncl (TopCat.of (PK K k₀))
        (fibreSet K k₀) = TopCat.ofHom (loopIncl K k₀) := by
    apply TopCat.ext
    intro γ
    rfl
  rw [homeoSSet, inclASSet, loopSSet, ← Functor.map_comp, hcm]

/-- Pulling back along the homeomorphism and then along the inclusion of the fibre is pulling back
along the inclusion of the loop space. -/
theorem pb_homeo_incl (K : Type) [TopologicalSpace K] (k₀ : K) {n : ℕ}
    (u : Cochain F2 (SX (PK K k₀)) n) :
    pb (homeoSSet K k₀) (pb (inclASSet K k₀) u) = pb (loopSSet K k₀) u := by
  rw [← pbComp (homeoSSet K k₀) (inclASSet K k₀) n u, homeo_incl_eq_loop]

/-- Every class of the relative cohomology is the class of a relative cocycle. -/
theorem existsRelCocycle (X : TopCat) (A : Set X) (n : ℕ)
    (c : relCohomology F2 X A n) :
    ∃ (a : relKern F2 X A n) (ha : relDiffLM F2 X A n a = 0),
      relClassOf F2 X A a ha = c :=
  Work.Cohomology.exists_relClassOf F2 X A n c

/-- A relative cocycle whose underlying cochain has vanishing cohomology class is a coboundary. -/
theorem existsPrimitive (X : TopCat) (A : Set X) (m : ℕ)
    (z : relKern F2 X A (m + 1))
    (hz : relDiffLM F2 X A (m + 1) z = 0)
    (h : cohomologyClassOf F2 (SX X) z.1 (relDiffLM_zero_cochainDiff z hz) = 0) :
    ∃ s : Cochain F2 (SX X) m, cochainDiff F2 (SX X) s = z.1 :=
  Work.Pi6.SQM.SIG.classZeroCoboundary (SX X) m z.1 (relDiffLM_zero_cochainDiff z hz) h

/-! ## The computation rule for `σ` -/

/-- **The computation rule for `σ`.**  If `ã` is a relative cocycle of `(K,{k₀})` representing
`ρ(c)`, and `s` is a cochain on the path space with `δs = q*ã`, then `σ c` is the class of the
restriction of `s` to the loop space. -/
theorem sigma_apply (K : Type) [TopologicalSpace K] (k₀ : K) (n : ℕ)
    (ã : relKern F2 (TopCat.of K) ({k₀} : Set K) (n + 2))
    (hã : relDiffLM F2 (TopCat.of K) ({k₀} : Set K) (n + 2) ã = 0)
    (x : Cochain F2 (SX K) (n + 2)) (hx : cochainDiff F2 (SX K) x = 0)
    (hcls : cls x hx = HomologicalComplex.homologyMap (relIncl F2 (TopCat.of K) ({k₀} : Set K))
      (n + 2) (relClassOf F2 (TopCat.of K) ({k₀} : Set K) ã hã))
    (s : Cochain F2 (SX (PK K k₀)) (n + 1))
    (hs : cochainDiff F2 (SX (PK K k₀)) s = pb (evSSet K k₀) ã.1)
    (h : cochainDiff F2 (SX (Path k₀ k₀)) (pb (loopSSet K k₀) s) = 0) :
    sigma K k₀ (n + 1) (cls x hx) = cls (pb (loopSSet K k₀) s) h := by
  have hã'coe : (qStarRel K k₀ (n + 2) ã).1 = cochainDiff F2 (SX (PK K k₀)) s := by
    rw [pairMapK_coe, hs]
  have hã'coc : relDiffLM F2 (TopCat.of (PK K k₀)) (fibreSet K k₀) (n + 2)
      (qStarRel K k₀ (n + 2) ã) = 0 := by
    apply Subtype.ext
    simp only [relDiffLM_coe, Submodule.coe_zero]
    rw [hã'coe, singularCochain_d_apply F2 (TopCat.of (PK K k₀))]
    exact cochainDiff_cochainDiff F2 (SX (PK K k₀)) s
  have hρ : (rhoLM K k₀ n).hom (cls x hx) =
      relClassOf F2 (TopCat.of K) ({k₀} : Set K) ã hã := by
    rw [hcls]
    exact rhoLM_relIncl K k₀ n _
  have hq : (qStarLM K k₀ (n + 2)).hom (relClassOf F2 (TopCat.of K) ({k₀} : Set K) ã hã) =
      relClassOf F2 (TopCat.of (PK K k₀)) (fibreSet K k₀) (qStarRel K k₀ (n + 2) ã) hã'coc := by
    have hnat := relClassOfNatural (fibreSet K k₀) ({k₀} : Set K)
      (TopCat.ofHom (Work.StemsB.evalOne K k₀)) (fun x hx => hx) (n + 2) ã hã hã'coc
    rw [qStarLM, show pairMapK K k₀ = relComplexMap F2 (fibreSet K k₀) ({k₀} : Set K)
      (TopCat.ofHom (Work.StemsB.evalOne K k₀)) (fun x hx => hx) from rfl]
    exact hnat
  have hres : cochainDiff F2 (SX ↥(fibreSet K k₀)) (pb (inclASSet K k₀) s) = 0 := by
    rw [cochainDiffPb, hs]
    exact (qStarRel K k₀ (n + 2) ã).2
  have hpair := pairDeltaApply (TopCat.of (PK K k₀)) (fibreSet K k₀) (n + 1) s
    (qStarRel K k₀ (n + 2) ã) hã'coe hã'coc hres
  have hstep : sigma K k₀ (n + 1) (cls x hx) =
      (fibreCohIso K k₀ (n + 1)).inv (cls (pb (inclASSet K k₀) s) hres) := by
    haveI := isIso_pairδ K k₀ n
    have h1 : sigma K k₀ (n + 1) (cls x hx) =
        (fibreCohIso K k₀ (n + 1)).inv
          ((asIso (pairδ F2 (TopCat.of (PK K k₀)) (fibreSet K k₀) (n + 1))).inv.hom
            ((pairδ F2 (TopCat.of (PK K k₀)) (fibreSet K k₀) (n + 1)).hom
              (cls (pb (inclASSet K k₀) s) hres))) := by
      rw [sigma_apply_def, hρ, hq, ← hpair]
      rw [deltaInv]
      simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
      rfl
    rw [h1]
    congr 1
    exact asIso_inv_apply _ _ _
  have hfin : (fibreCohIso K k₀ (n + 1)).inv (cls (pb (inclASSet K k₀) s) hres) =
      cls (pb (loopSSet K k₀) s) h := by
    have hφ : cochainDiff F2 (SX (Path k₀ k₀)) (pb (homeoSSet K k₀) (pb (inclASSet K k₀) s)) = 0 := by
      rw [cochainDiffPb, show cochainDiff F2 (SX ↥(fibreSet K k₀)) (pb (inclASSet K k₀) s) = 0
        from hres]
      exact pb_zero _
    have hcoe2 : pb (homeoSSet K k₀) (pb (inclASSet K k₀) s) = pb (loopSSet K k₀) s :=
      pb_homeo_incl K k₀ s
    rw [fibreCohIso_inv_apply K k₀ (n + 1) (pb (inclASSet K k₀) s) hres hφ]
    exact cohomologyClassOf_congr F2 (SX (Path k₀ k₀)) hcoe2 _ _
  rw [hstep, hfin]

end

end Work.Pi6.SQM.SIG
