import Mathlib
import Submission.Work.Pi6.SQM.Defs
import Submission.Work.Cohomology.PairSequence
import Submission.Work.Cohomology.pairIsoOfTrivial
import Submission.Work.Cohomology.contractible
import Submission.Work.Cohomology.homotopyEquiv
import Submission.Work.Cohomology.exists_relComplexMap
import Submission.Work.StemsB.contractible_pathSpace
import Submission.Work.StemsB.isSerreFibration_evalOne
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

/-!
# SQM / SIG — the cohomology suspension: definitions

The cohomology suspension `σ : H^{n+1}(K;𝔽₂) → H^n(ΩK;𝔽₂)` is defined through the path fibration
`evalOne : PK → K` (`PK = PathSpace K k₀`):

`σ = δ⁻¹ ∘ q* ∘ ρ`

where
* `ρ : H^{n+1}(K) → H^{n+1}(K,{k₀})` is the inverse of the isomorphism `relIncl*` (valid because a
  point has no positive-degree cohomology),
* `q* : H^{n+1}(K,{k₀}) → H^{n+1}(PK, ΩK)` is the pullback along the map of pairs
  `(PK, ΩK) → (K, {k₀})` induced by `evalOne`,
* `δ : H^n(ΩK) → H^{n+1}(PK, ΩK)` is the connecting map of the pair sequence of `(PK, ΩK)`, an
  isomorphism because `PK` is contractible.

`σ_0 := 0`.
-/

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
set_option maxHeartbeats 4000000

open CategoryTheory Limits AlgebraicTopology Work.Cohomology
open scoped Simplicial

namespace Work.Pi6.SQM.SIG

noncomputable section

abbrev F2 : Type := Work.Pi6.SQ.F2

/-- The based path space of `K` at `k₀`. -/
abbrev PK (K : Type) [TopologicalSpace K] (k₀ : K) : Type := Work.StemsB.PathSpace K k₀

/-- The fibre of `evalOne` over `k₀`, as a subset of the path space. -/
def fibreSet (K : Type) [TopologicalSpace K] (k₀ : K) : Set (PK K k₀) :=
  {γ | Work.StemsB.evalOne K k₀ γ = k₀}

/-- The inclusion of the loop space `ΩK = Path k₀ k₀` into the path space. -/
def loopIncl (K : Type) [TopologicalSpace K] (k₀ : K) : C(Path k₀ k₀, PK K k₀) where
  toFun γ := ⟨γ.toContinuousMap, γ.source'⟩
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    fun_prop

theorem loopIncl_mem (K : Type) [TopologicalSpace K] (k₀ : K) (γ : Path k₀ k₀) :
    loopIncl K k₀ γ ∈ fibreSet K k₀ := γ.target'

/-- The fibre of the path fibration is the loop space. -/
def fibreSetHomeo (K : Type) [TopologicalSpace K] (k₀ : K) :
    ↥(fibreSet K k₀) ≃ₜ Path k₀ k₀ := Work.StemsB.fibreEvalOneHomeo K k₀

/-- Homotopy equivalences induce isomorphisms on singular cohomology, over any commutative ring. -/
theorem cohomologyIso_of_homotopyEquiv' (R : Type) [CommRing R] {X Y : Type}
    [TopologicalSpace X] [TopologicalSpace Y] (e : ContinuousMap.HomotopyEquiv X Y) (n : ℕ) :
    Nonempty (singularCohomology R n (TopCat.of X) ≅ singularCohomology R n (TopCat.of Y)) := by
  let f : TopCat.of X ⟶ TopCat.of Y := TopCat.ofHom e.toFun
  let g : TopCat.of Y ⟶ TopCat.of X := TopCat.ofHom e.invFun
  have h1 : TopCat.Homotopy (f ≫ g) (𝟙 (TopCat.of X)) := e.left_inv.some
  have h2 : TopCat.Homotopy (g ≫ f) (𝟙 (TopCat.of Y)) := e.right_inv.some
  haveI := homotopyEquiv R (TopCat.of X) (TopCat.of Y) f g h1 h2 n
  exact ⟨(asIso (singularCohomologyMap R (TopCat.of X) (TopCat.of Y) f n)).symm⟩

/-- A homeomorphism induces an isomorphism on singular cohomology, realized concretely by the
pullback map. -/
theorem isIso_singularCohomologyMap_homeo (R : Type) [CommRing R] {X Y : Type}
    [TopologicalSpace X] [TopologicalSpace Y] (h : X ≃ₜ Y) (n : ℕ) :
    IsIso (singularCohomologyMap R (TopCat.of X) (TopCat.of Y)
      (TopCat.ofHom ⟨h.toFun, h.continuous_toFun⟩) n) := by
  have hf : (TopCat.ofHom ⟨h.toFun, h.continuous_toFun⟩ : TopCat.of X ⟶ TopCat.of Y) =
      TopCat.ofHom h.toHomotopyEquiv.toFun := rfl
  rw [hf]
  exact homotopyEquiv R (TopCat.of X) (TopCat.of Y) (TopCat.ofHom h.toHomotopyEquiv.toFun)
    (TopCat.ofHom h.toHomotopyEquiv.invFun) h.toHomotopyEquiv.left_inv.some
    h.toHomotopyEquiv.right_inv.some n

/-- The identification `H^n(ΩK) ≅ H^n` of the fibre of the path fibration, realized by the pullback
along the inverse of the homeomorphism `fibre ≃ ΩK`: its inverse is the concrete map induced by
`fibreSetHomeo.symm`. -/
def fibreCohIso (K : Type) [TopologicalSpace K] (k₀ : K) (n : ℕ) :
    Coh F2 (Path k₀ k₀) n ≅ Coh F2 (↥(fibreSet K k₀)) n := by
  haveI : IsIso (singularCohomologyMap F2 (TopCat.of (Path k₀ k₀))
      (TopCat.of ↥(fibreSet K k₀))
      (TopCat.ofHom ⟨(fibreSetHomeo K k₀).symm.toFun, (fibreSetHomeo K k₀).symm.continuous_toFun⟩) n) :=
    isIso_singularCohomologyMap_homeo F2 (fibreSetHomeo K k₀).symm n
  exact (asIso (singularCohomologyMap F2 (TopCat.of (Path k₀ k₀))
      (TopCat.of ↥(fibreSet K k₀))
      (TopCat.ofHom ⟨(fibreSetHomeo K k₀).symm.toFun, (fibreSetHomeo K k₀).symm.continuous_toFun⟩)
      n)).symm

/-- A point has no positive-degree cohomology. -/
theorem subsingleton_coh_point (K : Type) [TopologicalSpace K] (k₀ : K) (m : ℕ) (hm : 1 ≤ m) :
    Subsingleton (Coh F2 ({k₀} : Set K) m) := by
  have _ : ContractibleSpace (↥({k₀} : Set K)) := inferInstance
  have h := contractible F2 (TopCat.of (↥({k₀} : Set K))) (m - 1)
  rw [Nat.sub_add_cancel hm] at h
  exact ModuleCat.isZero_iff_subsingleton.mp h

/-- A contractible space has no positive-degree cohomology. -/
theorem subsingleton_coh_of_contractible (X : Type) [TopologicalSpace X] [ContractibleSpace X]
    (m : ℕ) : Subsingleton (Coh F2 X (m + 1)) :=
  ModuleCat.isZero_iff_subsingleton.mp (contractible F2 (TopCat.of X) m)

/-- `ρ`: the inverse of the isomorphism `H^{n+2}(K,{k₀}) → H^{n+2}(K)`. -/
theorem isIso_relIncl (K : Type) [TopologicalSpace K] (k₀ : K) (n : ℕ) :
    IsIso (HomologicalComplex.homologyMap (relIncl F2 (TopCat.of K) ({k₀} : Set K)) (n + 2)) :=
  pairIsoOfTrivial F2 (TopCat.of K) ({k₀} : Set K) (n + 1)
    (subsingleton_coh_point K k₀ (n + 1) (by omega))
    (subsingleton_coh_point K k₀ (n + 2) (by omega))

/-- `ρ : H^{n+2}(K) → H^{n+2}(K,{k₀})`. -/
def rhoLM (K : Type) [TopologicalSpace K] (k₀ : K) (n : ℕ) :
    Coh F2 K (n + 2) ⟶ relCohomology F2 (TopCat.of K) ({k₀} : Set K) (n + 2) := by
  haveI := isIso_relIncl K k₀ n
  exact (asIso (HomologicalComplex.homologyMap (relIncl F2 (TopCat.of K) ({k₀} : Set K))
    (n + 2))).inv

/-- The map of pairs `(PK, ΩK) → (K, {k₀})` on relative cochain complexes. -/
def pairMapK (K : Type) [TopologicalSpace K] (k₀ : K) :
    relComplex F2 (TopCat.of K) ({k₀} : Set K) ⟶
      relComplex F2 (TopCat.of (PK K k₀)) (fibreSet K k₀) :=
  relComplexMap (X₁ := TopCat.of (PK K k₀)) (X₂ := TopCat.of K) (R := F2)
    (A₁ := fibreSet K k₀) (A₂ := ({k₀} : Set K))
    (TopCat.ofHom (Work.StemsB.evalOne K k₀)) (fun x hx => hx)

/-- `q*`: pullback along the map of pairs `(PK, ΩK) → (K, {k₀})`. -/
def qStarLM (K : Type) [TopologicalSpace K] (k₀ : K) (m : ℕ) :
    relCohomology F2 (TopCat.of K) ({k₀} : Set K) m ⟶
      relCohomology F2 (TopCat.of (PK K k₀)) (fibreSet K k₀) m :=
  HomologicalComplex.homologyMap (pairMapK K k₀) m

/-- `δ` is an isomorphism because the path space is contractible. -/
theorem isIso_pairδ (K : Type) [TopologicalSpace K] (k₀ : K) (n : ℕ) :
    IsIso (pairδ F2 (TopCat.of (PK K k₀)) (fibreSet K k₀) (n + 1)) := by
  have hpk : ContractibleSpace (PK K k₀) := Work.StemsB.contractible_pathSpace K k₀
  have i1 : IsZero (singularCohomology F2 (n + 1) (TopCat.of (PK K k₀))) :=
    contractible F2 (TopCat.of (PK K k₀)) n
  have i2 : IsZero (singularCohomology F2 (n + 1 + 1) (TopCat.of (PK K k₀))) :=
    contractible F2 (TopCat.of (PK K k₀)) (n + 1)
  have hmono : Mono (pairδ F2 (TopCat.of (PK K k₀)) (fibreSet K k₀) (n + 1)) := by
    have hf : (ShortComplex.mk
        (HomologicalComplex.homologyMap (restr F2 (TopCat.of (PK K k₀)) (fibreSet K k₀)) (n + 1))
        (pairδ F2 (TopCat.of (PK K k₀)) (fibreSet K k₀) (n + 1))
        (pair_comp_δ F2 (TopCat.of (PK K k₀)) (fibreSet K k₀) (n + 1))).f = 0 :=
      i1.eq_of_src _ 0
    exact (ShortComplex.exact_iff_mono _ hf).mp
      (pair_exact₃ F2 (TopCat.of (PK K k₀)) (fibreSet K k₀) (n + 1))
  have hepi : Epi (pairδ F2 (TopCat.of (PK K k₀)) (fibreSet K k₀) (n + 1)) := by
    have hg : (ShortComplex.mk
        (pairδ F2 (TopCat.of (PK K k₀)) (fibreSet K k₀) (n + 1))
        (HomologicalComplex.homologyMap (relIncl F2 (TopCat.of (PK K k₀)) (fibreSet K k₀)) (n + 1 + 1))
        (pairδ_comp F2 (TopCat.of (PK K k₀)) (fibreSet K k₀) (n + 1))).g = 0 :=
      i2.eq_of_tgt _ 0
    exact (ShortComplex.exact_iff_epi _ hg).mp
      (pair_exact₁ F2 (TopCat.of (PK K k₀)) (fibreSet K k₀) (n + 1))
  exact isIso_of_mono_of_epi _

/-- `δ⁻¹ : H^{n+2}(PK, ΩK) → H^{n+1}(ΩK)`. -/
def deltaInv (K : Type) [TopologicalSpace K] (k₀ : K) (n : ℕ) :
    relCohomology F2 (TopCat.of (PK K k₀)) (fibreSet K k₀) (n + 2) ⟶
      Coh F2 (Path k₀ k₀) (n + 1) := by
  haveI := isIso_pairδ K k₀ n
  exact (asIso (pairδ F2 (TopCat.of (PK K k₀)) (fibreSet K k₀) (n + 1))).inv ≫
    (fibreCohIso K k₀ (n + 1)).inv

section Pullback

variable {X Y Z : SSet}

/-- Pullback of cochains along a map of simplicial sets. -/
def pb (f : X ⟶ Y) {n : ℕ} (u : Cochain F2 Y n) : Cochain F2 X n :=
  ((SSet.chainComplexMap f (ModuleCat.of F2 F2)).f n).hom.dualMap u

theorem pb_zero (f : X ⟶ Y) {n : ℕ} : pb f (0 : Cochain F2 Y n) = 0 :=
  map_zero _

/-- `pb` along a continuous map is the library's cochain pullback. -/
theorem pb_continuous {P Q : Type} [TopologicalSpace P] [TopologicalSpace Q] (φ : C(P, Q))
    {n : ℕ} (u : Cochain F2 (SX Q) n) :
    pb (TopCat.toSSet.map (TopCat.ofHom φ)) u =
      (cochainPullbackHom F2 (TopCat.of P) (TopCat.of Q) (TopCat.ofHom φ) n).hom u := rfl

/-- A relative cochain vanishes after pulling back along a map into the subspace. -/
theorem pb_subtypeIncl_relKern {X : TopCat} (A : Set X) {n : ℕ}
    (u : relKern F2 X A n) :
    pb (TopCat.toSSet.map (subtypeIncl X A)) u.1 = 0 := by
  have h : ((restr F2 X A).f n).hom u.1 = 0 := u.2
  rwa [restr, dualChainMap_f_hom, chainMap_f_eq] at h

/-- The maps of pairs used below. -/
def evSSet (K : Type) [TopologicalSpace K] (k₀ : K) : SX (PK K k₀) ⟶ SX K :=
  TopCat.toSSet.map (TopCat.ofHom (Work.StemsB.evalOne K k₀))

def loopSSet (K : Type) [TopologicalSpace K] (k₀ : K) : SX (Path k₀ k₀) ⟶ SX (PK K k₀) :=
  TopCat.toSSet.map (TopCat.ofHom (loopIncl K k₀))

def inclASSet (K : Type) [TopologicalSpace K] (k₀ : K) :
    SX (↥(fibreSet K k₀)) ⟶ SX (PK K k₀) :=
  TopCat.toSSet.map (subtypeIncl (TopCat.of (PK K k₀)) (fibreSet K k₀))

end Pullback

/-- **The cohomology suspension** `σ : H^{n+1}(K;𝔽₂) → H^n(ΩK;𝔽₂)`, with `σ_0 = 0`. -/
def sigma (K : Type) [TopologicalSpace K] (k₀ : K) (n : ℕ) :
    (Coh F2 K (n + 1) →ₗ[F2] Coh F2 (Path k₀ k₀) n) :=
  match n with
  | 0 => 0
  | (n + 1) => (rhoLM K k₀ n ≫ qStarLM K k₀ (n + 2) ≫ deltaInv K k₀ n).hom

/-- The defining formula for `σ` in positive degrees. -/
theorem sigma_apply_def (K : Type) [TopologicalSpace K] (k₀ : K) (n : ℕ)
    (c : Coh F2 K (n + 2)) :
    sigma K k₀ (n + 1) c =
      (deltaInv K k₀ n).hom ((qStarLM K k₀ (n + 2)).hom ((rhoLM K k₀ n).hom c)) := by
  simp only [sigma, deltaInv, ModuleCat.hom_comp, LinearMap.comp_apply]

/-- `ρ` is a section of the homology map of the inclusion of relative cochains. -/
theorem rhoLM_relIncl (K : Type) [TopologicalSpace K] (k₀ : K) (n : ℕ)
    (z : relCohomology F2 (TopCat.of K) ({k₀} : Set K) (n + 2)) :
    (rhoLM K k₀ n).hom ((HomologicalComplex.homologyMap (relIncl F2 (TopCat.of K)
      ({k₀} : Set K)) (n + 2)).hom z) = z := by
  haveI := isIso_relIncl K k₀ n
  have h := congrArg ModuleCat.Hom.hom (Iso.hom_inv_id
    (asIso (HomologicalComplex.homologyMap (relIncl F2 (TopCat.of K) ({k₀} : Set K)) (n + 2))))
  have h2 := LinearMap.congr_fun h z
  simp only [rhoLM, asIso_hom, ModuleCat.hom_comp, ModuleCat.hom_id, LinearMap.comp_apply,
    LinearMap.id_apply] at h2 ⊢
  exact h2

/-- The homology map of the inclusion of relative cochains is a section of `ρ`. -/
theorem relIncl_rhoLM (K : Type) [TopologicalSpace K] (k₀ : K) (n : ℕ)
    (c : Coh F2 K (n + 2)) :
    (HomologicalComplex.homologyMap (relIncl F2 (TopCat.of K) ({k₀} : Set K)) (n + 2)).hom
      ((rhoLM K k₀ n).hom c) = c := by
  haveI := isIso_relIncl K k₀ n
  have h := congrArg ModuleCat.Hom.hom (Iso.inv_hom_id
    (asIso (HomologicalComplex.homologyMap (relIncl F2 (TopCat.of K) ({k₀} : Set K)) (n + 2))))
  have h2 := LinearMap.congr_fun h c
  simp only [rhoLM, asIso_hom, ModuleCat.hom_comp, ModuleCat.hom_id, LinearMap.comp_apply,
    LinearMap.id_apply] at h2 ⊢
  exact h2

end

end Work.Pi6.SQM.SIG
