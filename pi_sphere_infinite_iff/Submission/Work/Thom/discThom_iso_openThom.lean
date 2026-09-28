import Mathlib
import Submission.Work.Thom.Pair
import Submission.Work.Thom.Basic
import Submission.Work.Thom.DiscSphereTopology
import Submission.Work.Thom.Continuous
import Submission.Work.Cohomology.exists_relComplexMap
import Submission.Work.Cohomology.relChainsMapOf_isIso
import Submission.Work.Cohomology.relChainsProjective
import Submission.Work.Cohomology.isIso_homologyMap_dualZMap
import Submission.Work.Cohomology.relComplexMapDualZ
import Submission.Work.Cohomology.homologyContractible
import Submission.Work.Cohomology.dualZ
import Submission.Work.Cohomology.dualComplexMap_quasiIso
import Submission.Work.Thom.discSub_homotopyEquiv
import Submission.Work.Thom.sphereInDisc_homotopyEquiv

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false

/-!
# The two models of the Thom pair agree

This module proves `Work.Thom.discThom_iso_openThom`: for a *Euclidean* real bundle `Z` the
relative cohomology `H^n(D(E), S(E);ℤ)` of the disc pair and the relative cohomology
`H^n(E, E∖0;ℤ)` of the pair (total space, complement of the zero section) are isomorphic in every
degree.

The argument has three parts.

* **Topology.**  The inclusion of the closed disc bundle `D(E) ↪ E` is a homotopy equivalence
  (radial deformation towards the zero section), and the inclusion of the sphere bundle
  `S(E) ↪ E∖0` is a homotopy equivalence (radial projection onto the sphere bundle).  These are
  `Work.Thom.discSub_homotopyEquiv` and `Work.Thom.sphereInDisc_homotopyEquiv`.
  Consequently the two chain maps induced on singular chains are quasi-isomorphisms
  (`Work.Cohomology.homologyEquiv`), so by the five-lemma
  `Work.Cohomology.relChainsMapOf_isIso` the map of relative *chain* complexes induced by the
  inclusion of pairs is a quasi-isomorphism.

* **Duality.**  The `ℤ`-dual of the relative chain complex is (up to the canonical isomorphism
  `Work.Cohomology.relZIsoComplex`) the relative cochain complex, and the dual of the pair map is
  the pair map on cochains (`Work.Cohomology.relComplexMapDualZ`).  A quasi-isomorphism between
  degreewise projective chain complexes dualises to a quasi-isomorphism of cochain complexes
  (`Work.Cohomology.dualComplexMap_quasiIso`); the relative chains are degreewise projective
  (`Work.Cohomology.relChainsProjective`).

* **Assembly.**  Hence `Work.Cohomology.relComplexMap` is a quasi-isomorphism, i.e. the pullback
  `H^n(E,E∖0;ℤ) ⟶ H^n(D(E),S(E);ℤ)` of the inclusion of pairs is an isomorphism; its inverse is
  the required isomorphism `DiscThom Z n ≅ OpenThom Z n`.
-/

open CategoryTheory
open Work.TangentClasses
open Work.Cohomology

namespace Work.Thom

noncomputable section

variable {B : Type} [TopologicalSpace B] {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {ι : Type}

/-- **A homotopy equivalence of spaces induces a quasi-isomorphism of singular chains.**  This is
`Work.Cohomology.homologyEquiv` specialised to the forward map of a
`ContinuousMap.HomotopyEquiv`. -/
lemma homologyMap_chainMap_isIso_of_homotopyEquiv {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (e : ContinuousMap.HomotopyEquiv X Y) (n : ℕ) :
    IsIso (HomologicalComplex.homologyMap
      (Work.Cohomology.chainMap ℤ (TopCat.of X) (TopCat.of Y) (TopCat.ofHom e.toFun)) n) :=
  Work.Cohomology.homologyEquiv ℤ (TopCat.of X) (TopCat.of Y) (TopCat.ofHom e.toFun)
    (TopCat.ofHom e.invFun) e.left_inv.some e.right_inv.some n

/-- For coefficients in `ℤ` the `ℤ`-dual `Work.Cohomology.dualZ ℤ` of a chain complex of
`ℤ`-modules agrees with `Work.Cohomology.dualComplex ℤ`, both on the complexes and on the chain
maps. -/
lemma dualComplexMap_eq_dualZMap (C D : ChainComplex (ModuleCat ℤ) ℕ) (φ : C ⟶ D) :
    dualComplexMap ℤ C D φ = dualZMap ℤ C D φ := by
  apply HomologicalComplex.hom_ext
  intro n
  rw [dualComplexMap_f, dualZMap_f]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rw [dualComplexMapComp_apply', dualZMapComp_apply']

/-- **A quasi-isomorphism between degreewise projective `ℤ`-chain complexes dualises to a
quasi-isomorphism of cochain complexes**: the `ℤ`-dual of the induced map on homology is an
isomorphism.  This is `Work.Cohomology.dualComplexMap_quasiIso` transported across
`dualComplexMap_eq_dualZMap`. -/
lemma isIso_homologyMap_dualZMap_of_quasiIso {C D : ChainComplex (ModuleCat ℤ) ℕ} (φ : C ⟶ D)
    (hC : ∀ n, Module.Projective ℤ ↥(C.X n)) (hD : ∀ n, Module.Projective ℤ ↥(D.X n))
    (h : ∀ n, IsIso (HomologicalComplex.homologyMap φ n)) (n : ℕ) :
    IsIso (HomologicalComplex.homologyMap (dualZMap ℤ C D φ) n) := by
  have hc := dualComplexMap_quasiIso φ hC hD h n
  rwa [dualComplexMap_eq_dualZMap] at hc

/-- **The map of relative cochain complexes induced by a map of pairs is a quasi-isomorphism**
whenever both components are homotopy equivalences (i.e. induce quasi-isomorphisms on singular
chains).  This is the cohomological form of
`Work.Cohomology.relChainsMapOf_isIso`, obtained by dualising: the relative cochain complex is the
`ℤ`-dual of the relative chain complex (`Work.Cohomology.relComplexMapDualZ`), and the relative
chains are degreewise projective (`Work.Cohomology.relChainsProjective`). -/
lemma relComplexMap_homologyMap_isIso {X₁ X₂ : TopCat} (A₁ : Set X₁) (A₂ : Set X₂)
    (f : X₁ ⟶ X₂) (h : ∀ x ∈ A₁, (ConcreteCategory.hom f) x ∈ A₂)
    (hf : ∀ k, IsIso (HomologicalComplex.homologyMap (Work.Cohomology.chainMap ℤ X₁ X₂ f) k))
    (hg : ∀ k, IsIso (HomologicalComplex.homologyMap
      (Work.Cohomology.chainMap ℤ (TopCat.of ↑A₁) (TopCat.of ↑A₂) (relMapSub A₁ A₂ f h)) k))
    (n : ℕ) :
    IsIso (HomologicalComplex.homologyMap (relComplexMap ℤ A₁ A₂ f h) n) := by
  have hrel : ∀ k, IsIso (HomologicalComplex.homologyMap
      (relChainsMapOf X₁ X₂ A₁ A₂ f (relMapSub A₁ A₂ f h) (relMapSub_spec A₁ A₂ f h)) k) :=
    fun k => relChainsMapOf_isIso A₁ A₂ f (relMapSub A₁ A₂ f h) (relMapSub_spec A₁ A₂ f h) k hf hg
  have hdual := isIso_homologyMap_dualZMap_of_quasiIso
    (relChainsMapOf X₁ X₂ A₁ A₂ f (relMapSub A₁ A₂ f h) (relMapSub_spec A₁ A₂ f h))
    (fun m => relChainsProjective X₁ A₁ m) (fun m => relChainsProjective X₂ A₂ m) hrel n
  have heq := relComplexMapDualZ (X₁ := X₁) (X₂ := X₂) ℤ A₁ A₂ f h
  rw [heq, HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp]
  haveI := hdual
  infer_instance

/-- **The two models of the Thom pair agree**: given the two homotopy equivalences exhibited by
`Work.Thom.discSub_homotopyEquiv` and `Work.Thom.sphereInDisc_homotopyEquiv`, the pullback along
the inclusion of pairs `(D(E),S(E)) ↪ (E,E∖0)` is an isomorphism on relative cohomology, and hence
`DiscThom Z n ≅ OpenThom Z n`. -/
theorem discThom_iso_openThom_of_homotopyEquiv (Z : RealBundle B F ι) (n : ℕ)
    (e1 : ContinuousMap.HomotopyEquiv (DiscSub Z) Z.TotalSpace)
    (he1 : ⇑e1.toFun = (Subtype.val : DiscSub Z → Z.TotalSpace))
    (e2 : ContinuousMap.HomotopyEquiv (sphereInDisc Z) (zeroComplement Z))
    (he2 : ∀ q, (e2.toFun q : Z.TotalSpace) = ((q : DiscSub Z) : Z.TotalSpace)) :
    Nonempty (DiscThom Z n ≅ OpenThom Z n) := by
  classical
  -- the map `(D(E),S(E)) → (E,E∖0)` of pairs sends the sphere to the complement of the zero
  -- section
  have hmem : ∀ x ∈ sphereInDisc Z, (TopCat.ofHom e1.toFun) x ∈ zeroComplement Z := by
    intro x hx
    have hx' : ((x : DiscSub Z) : Z.TotalSpace) ∈ sphereSet Z := hx
    rw [mem_sphereSet] at hx'
    have hfx : (TopCat.ofHom e1.toFun) x = ((x : DiscSub Z) : Z.TotalSpace) := by
      rw [TopCat.ofHom_apply]
      exact congrFun he1 (x : DiscSub Z)
    rw [mem_zeroComplement, hfx]
    intro h0
    have hz : fibreNorm Z (((x : DiscSub Z) : Z.TotalSpace)) = 0 := by
      simp [fibreNorm, h0]
    rw [hx'] at hz
    norm_num at hz
  -- the restriction of the inclusion to the sphere bundles is the inclusion `S(E) ↪ E∖0`
  have hg : relMapSub (sphereInDisc Z) (zeroComplement Z) (TopCat.ofHom e1.toFun) hmem
      = TopCat.ofHom e2.toFun := by
    apply congrArg TopCat.ofHom
    apply ContinuousMap.ext
    intro q
    apply Subtype.ext
    show (TopCat.ofHom e1.toFun) q = (e2.toFun q : Z.TotalSpace)
    rw [TopCat.ofHom_apply, he2 q]
    exact congrFun he1 (q : DiscSub Z)
  -- both components induce quasi-isomorphisms on singular chains
  have hf : ∀ k, IsIso (HomologicalComplex.homologyMap (Work.Cohomology.chainMap ℤ
      (TopCat.of (DiscSub Z)) (TopCat.of Z.TotalSpace) (TopCat.ofHom e1.toFun)) k) :=
    fun k => homologyMap_chainMap_isIso_of_homotopyEquiv e1 k
  have hg2 : ∀ k, IsIso (HomologicalComplex.homologyMap (Work.Cohomology.chainMap ℤ
      (TopCat.of ↑(sphereInDisc Z)) (TopCat.of ↑(zeroComplement Z))
      (relMapSub (sphereInDisc Z) (zeroComplement Z) (TopCat.ofHom e1.toFun) hmem)) k) := by
    intro k
    rw [hg]
    exact homologyMap_chainMap_isIso_of_homotopyEquiv e2 k
  -- hence the pair map is an isomorphism on relative cohomology
  haveI hRelCoh : IsIso (relCohMap e1.toFun (sphereInDisc Z) (zeroComplement Z) hmem ℤ n) :=
    relComplexMap_homologyMap_isIso (X₁ := TopCat.of (DiscSub Z)) (X₂ := TopCat.of Z.TotalSpace)
      (sphereInDisc Z) (zeroComplement Z) (TopCat.ofHom e1.toFun) hmem hf hg2 n
  exact ⟨(asIso (relCohMap e1.toFun (sphereInDisc Z) (zeroComplement Z) hmem ℤ n)).symm⟩

/-- **The two models of the Thom pair agree.**  For a *Euclidean* real bundle `Z` (so that the
fibrewise norm, and hence the disc and sphere bundles, are well defined) the relative cohomology of
the pair `(E, E∖0)` (total space minus the zero section) is isomorphic, in every degree, to that of
the disc pair `(D(E), S(E))`.  This is the statement that the closed disc bundle `D(E)` is a
deformation retract of `E`, with `S(E)` the corresponding deformation retract of `E∖0` (both along
the same radial deformation of the fibre), so that the inclusion of pairs `(D(E), S(E)) ↪ (E, E∖0)`
is a homotopy equivalence of pairs.

This identifies the Euler class computed on the disc pair (`Work.Thom.eulerClassDisc`, the model in
which the deliverable states the Thom class) with the one computed on `(E,E∖0)`
(`Work.Thom.eulerClass`, the model used by `Work.Thom.ThomClass` and the Gysin sequence).  Only the
*existence* of an isomorphism is claimed; a future session should exhibit the specific iso induced
by the inclusion of pairs, compatible with the zero section (`Work.Thom.zeroSection`,
`Work.Thom.zeroSectionDisc`), and transport the `isThom` condition of `Work.Thom.ThomClass` across
it.

Suggested route: `Work.Cohomology.relChainsMapOf_isIso` for the inclusion of pairs (both components
are homotopy equivalences: `E` contracts to `D(E)` and `E∖0` to `S(E)` along the radial deformation
of the fibre), followed by the duality between `relComplex` and `relChains`.  The hypothesis
`hZ : Work.Thom.IsEuclidean Z` is needed for the fibrewise norm to be well defined
(`Work.Thom.fibreNorm_localTriv`); the radial deformation is built from
`Work.Thom.continuous_smul_section` and `Work.Thom.continuous_fibreNorm`. -/
theorem discThom_iso_openThom {B : Type} [TopologicalSpace B] {F : Type} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {ι : Type} (Z : Work.TangentClasses.RealBundle B F ι)
    (hZ : Work.Thom.IsEuclidean Z) (n : ℕ) :
    Nonempty (Work.Thom.DiscThom Z n ≅ Work.Thom.OpenThom Z n) := by
  obtain ⟨e1, he1⟩ := discSub_homotopyEquiv Z hZ
  obtain ⟨e2, he2⟩ := sphereInDisc_homotopyEquiv Z hZ
  exact discThom_iso_openThom_of_homotopyEquiv Z n e1 he1 e2 he2

end

end Work.Thom
