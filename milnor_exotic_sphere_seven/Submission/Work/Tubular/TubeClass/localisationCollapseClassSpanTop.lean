import Mathlib
import Submission.Work.Tubular.TubeClass.Core
import Submission.Work.Stems.SphereMinusPoint
import Submission.Work.Cohomology.HomologyPairSequence
import Submission.Work.Cohomology.homologyContractible
import Submission.Work.ThomBordism.doubleFC.relFactor
import Submission.Work.Cohomology.relChainsMapOf_comp

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
set_option linter.style.haveILetI false
-- The module structures on the homology groups are the ones induced from the ambient modules:
attribute [local instance 5000] Submodule.module
attribute [local instance 5000] Submodule.Quotient.module

/-!
# The localisation of the Pontryagin–Thom collapse class at the zero-section point

**The statement.**  `Work.Tubular.localisationCollapseClassSpanTop` says that the localisation at
the zero-section point `x₀ = 0_{v₀} ∈ ν⁺ = OnePoint (NormalTotal E)` of the Hurewicz class of the
collapse loop `Work.Tubular.tubeGenLoopOnePoint C g hg hR hbox ∈ π_{8+k}(ν⁺)` *generates* the local
homology `H_{8+k}(ν⁺, ν⁺∖{x₀}) ≅ ℤ`.  Equivalently: the Pontryagin–Thom collapse of the tubular
neighbourhood has **local degree `±1`** at `x₀`.  This is the second of the two geometric inputs
into the degree-one property of the collapse (`Work.Tubular.tubeCollapseClass_span_top`,
`Submission/Work/Tubular/TubeClass/Reduction.lean`).

## The mathematical argument

Write `N := 8 + k`, `X := OnePoint (NormalTotal E)`, `x₀ := 0_{v₀}` and
`F := cubeLift N _ (tubeGenLoopOnePoint C g hg hR hbox) : S^N → X` — the collapse, descended from
the cube `I^N` to the sphere.  The proof has three layers.

* **The abstract local-degree lemma** (`spanLocalisationOfLocalHomeo`).  If `F` is a map with
  `F⁻¹{x₀} = {y₀}`, and if `F` restricts to a homeomorphism `U ≅ V` of an open neighbourhood `U`
  of `y₀` onto an open neighbourhood `V` of `x₀`, then the localisation of the Hurewicz class of
  `F` at `x₀` generates.  The proof factors the chain map
  `C_*(S^N) → C_*(X, X∖{x₀})` (which kills `C_*(S^N ∖ {y₀})`) through
  `C_*(S^N, S^N∖{y₀})`, uses the *factorisation criterion*
  `Work.ThomBordism.doubleFC.isIso_homologyMap_relChainsMapOf_of_factorization` (excision on both
  sides plus the middle homeomorphism) to see that the induced map on `H_N` is an isomorphism, and
  concludes with `span_singleton_map_eq_top'` from the corresponding statement
  (`localGeneratorSphere`) on the sphere.  The latter says that the localisation of the chosen
  generator `sphereGenerator N` of `H_N(S^N) ≅ ℤ` generates the local group of `S^N`: it is
  surjective because `S^N ∖ {y₀} ≅ ℝ^N` is contractible, so the connecting map of the pair
  vanishes.

* **The local model** (`continuous_normalShrink`, `g_zeta`, `zeta_inv`, `cubeEucPtInv`,
  `cubeToEuc_cubeEucPtInv`, `cubeToEuc_injective`).  On the open tube the collapse is
  `y ↦ some (normalBlowUp E ε (C.inv y))`, and this is a homeomorphism onto the finite part
  `ν = {p ≠ ∞} ⊆ ν⁺`, with inverse `p ↦ ζ(p) = tubeMap E (normalShrink E ε p)` — the radial shrink
  of the normal vector, followed by the tubular map.  The neighbourhoods used are
  `V' := range (some : ν → ν⁺)` and `U := F ⁻¹' V'`, and the homeomorphism `U ≅ V'` is
  `F|_U`, with inverse built from `ζ` and the explicit coordinate inverse `cubeEucPtInv` of the
  cube parametrisation `cubeToEuc` (which is where the cube `I^N` enters: the collapse is constant
  on the boundary of the cube, and `F⁻¹(x₀)` is the image of the single cube point over
  `E.e v₀`).

* **The fibre of the collapse** (`collapseFibre`): the only point of `S^N` mapping to `x₀` is the
  one over `E.e v₀`; a point of the boundary of the cube maps outside the tube, hence to `∞`, and
  inside the tube the collapse is injective with `normalBlowUp E ε (C.inv y) = 0_{v₀} ⟺ y = E.e v₀`.

The main theorem then assembles the three: `F` is the collapse, `localisationPunct E v₀ (8+k)` is
exactly the localisation along the pair `(X, X∖{x₀})`, and the chain-level identity relating
`localisationPunct` to the relative chain map of the pair is `cokernel_π_relChainsMapOf_aux`.
-/

open CategoryTheory Limits
open scoped Topology

open Work.ThomBordism.PontryaginThom (EmbeddingData)

namespace Work.Tubular.TubeClass

noncomputable section

/-! ## Generalities -/

/-- A surjective `ℤ`-linear map sends a generator to a generator. -/
theorem span_singleton_map_eq_top' {M N : Type*} [AddCommGroup M] [Module ℤ M]
    [AddCommGroup N] [Module ℤ N] (f : M →ₗ[ℤ] N) (hf : Function.Surjective f) (x : M)
    (hx : Submodule.span ℤ {x} = ⊤) : Submodule.span ℤ {f x} = ⊤ := by
  have h1 : Submodule.map f (Submodule.span ℤ {x}) = Submodule.span ℤ {f x} := by
    rw [Submodule.map_span]; simp
  rw [← h1, hx, Submodule.map_top]
  exact LinearMap.range_eq_top.mpr hf

/-! ## The localisation of the sphere generator at a point -/

/-- The complement of a point of `Sⁿ` is contractible. -/
theorem contractibleSpace_sphereCompl (n : ℕ) (y₀ : Work.Stems.sphere n) :
    ContractibleSpace ↥(({y₀}ᶜ : Set (Work.Stems.sphere n))) := by
  haveI h1 : ContractibleSpace ↥(Set.univ : Set
      ↥(Submodule.span ℝ ({(y₀ : EuclideanSpace ℝ (Fin (n + 1)))}))ᗮ) :=
    Convex.contractibleSpace convex_univ ⟨0, Set.mem_univ 0⟩
  haveI h2 : ContractibleSpace ↥(Submodule.span ℝ
      ({(y₀ : EuclideanSpace ℝ (Fin (n + 1)))}))ᗮ :=
    Homeomorph.contractibleSpace (Homeomorph.Set.univ _).symm
  exact Homeomorph.contractibleSpace (Work.Stems.sphereComplHomeo n y₀)

/-- `Submodule.span ℤ {1} = ⊤` in `ℤ` as a module over itself. -/
theorem span_singleton_one_int : Submodule.span ℤ ({(1 : ℤ)} : Set ℤ) = ⊤ := by
  refine Submodule.eq_top_iff'.mpr fun z => ?_
  rw [Submodule.mem_span_singleton]
  exact ⟨z, by simp⟩

/-- **The chosen generator of `Hₙ(Sⁿ;ℤ)` spans.** -/
theorem span_sphereGenerator_top (n : ℕ) (hn : 1 ≤ n) :
    Submodule.span ℤ ({Work.Stems.sphereGenerator n hn} : Set
      (↑((Work.Stems.chains (TopCat.of (Work.Stems.sphere n))).homology n))) = ⊤ := by
  let I := Classical.choice (Work.Cohomology.sphereHomologyTop n hn)
  have he : ({Work.Stems.sphereGenerator n hn} : Set
      (↑((Work.Stems.chains (TopCat.of (Work.Stems.sphere n))).homology n)))
      = (ModuleCat.Hom.hom I.inv) '' ({(1 : ℤ)} : Set ℤ) := by
    rw [Set.image_singleton]
    rfl
  rw [he, ← Submodule.map_span, span_singleton_one_int, Submodule.map_top]
  rw [LinearMap.range_eq_top]
  exact (ModuleCat.epi_iff_surjective _).mp (CategoryTheory.IsIso.epi_of_iso I.inv)

/-- **The chosen generator of `Hₙ(Sⁿ;ℤ)` still generates after localisation at a point.** -/
theorem localGeneratorSphere (n : ℕ) (hn : 2 ≤ n) (y₀ : Work.Stems.sphere n) :
    Submodule.span ℤ
      ({(HomologicalComplex.homologyMap (CategoryTheory.Limits.cokernel.π
          (Work.Cohomology.inclChains (TopCat.of (Work.Stems.sphere n))
            ({y₀}ᶜ : Set (Work.Stems.sphere n)))) n
        (Work.Stems.sphereGenerator n (by omega)))} : Set
          (↑(HomologicalComplex.homology (CategoryTheory.Limits.cokernel
            (Work.Cohomology.inclChains (TopCat.of (Work.Stems.sphere n))
              ({y₀}ᶜ : Set (Work.Stems.sphere n)))) n)))
      = ⊤ := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  have hm : 1 ≤ m := by omega
  set X : TopCat := TopCat.of (Work.Stems.sphere (m + 1)) with hX
  set A : Set X := ({y₀}ᶜ : Set (Work.Stems.sphere (m + 1))) with hA
  haveI hcontr : ContractibleSpace ↥A := contractibleSpace_sphereCompl (m + 1) y₀
  have hzero : IsZero ((Work.Cohomology.singularChains ℤ (TopCat.of A)).homology m) :=
    Work.Cohomology.homologyContractible m (by omega)
  have hδ : Work.Cohomology.hPairδ X A m = 0 := IsZero.eq_zero_of_tgt hzero _
  have hker : (ModuleCat.Hom.hom (Work.Cohomology.hPairδ X A m)).ker = ⊤ := by
    rw [hδ]; exact LinearMap.ker_zero
  have hrange : (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
      (CategoryTheory.Limits.cokernel.π (Work.Cohomology.inclChains X A)) (m + 1))).range
      = ⊤ := by
    have hex : (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
        (CategoryTheory.Limits.cokernel.π (Work.Cohomology.inclChains X A)) (m + 1))).range
        = (ModuleCat.Hom.hom (Work.Cohomology.hPairδ X A m)).ker :=
      (Work.Cohomology.hPair_exact₃ X A m).moduleCat_range_eq_ker
    rw [hex, hker]
  have hsurj : Function.Surjective (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
      (CategoryTheory.Limits.cokernel.π (Work.Cohomology.inclChains X A)) (m + 1))) :=
    LinearMap.range_eq_top.mp hrange
  exact span_singleton_map_eq_top' _ hsurj (Work.Stems.sphereGenerator (m + 1) (by omega))
    (span_sphereGenerator_top (m + 1) (by omega))

/-! ## The abstract local-degree lemma -/

/-- The compatibility of `relChainsMapOf` with the projections to the relative chain complexes. -/
theorem cokernel_π_relChainsMapOf_aux {X Y : TopCat} {A : Set X} {B : Set Y} {f : X ⟶ Y}
    {g : TopCat.of A ⟶ TopCat.of B}
    {w : Work.Cohomology.subtypeIncl X A ≫ f = g ≫ Work.Cohomology.subtypeIncl Y B} :
    CategoryTheory.Limits.cokernel.π (Work.Cohomology.inclChains X A)
        ≫ Work.Cohomology.relChainsMapOf X Y A B f g w
      = Work.Cohomology.chainMap ℤ X Y f ≫ CategoryTheory.Limits.cokernel.π
          (Work.Cohomology.inclChains Y B) := by
  rw [Work.Cohomology.relChainsMapOf]
  exact Work.Cohomology.cokernel_π_map (Work.Cohomology.inclChains X A)
    (Work.Cohomology.inclChains Y B) (Work.Cohomology.chainMap ℤ (TopCat.of A) (TopCat.of B) g)
    (Work.Cohomology.chainMap ℤ X Y f) _

/-- **A continuous map which is a homeomorphism near the (unique) preimage of `x₀` has Hurewicz
class whose localisation at that preimage generates.** -/
theorem spanLocalisationOfLocalHomeo {X : Type} [TopologicalSpace X] [T1Space X] {N : ℕ}
    (hN : 2 ≤ N) (x₀ : X) (F : C(Work.Stems.sphere N, X)) (y₀ : Work.Stems.sphere N)
    (hfib : ∀ y, F y = x₀ → y = y₀)
    (U : Set (Work.Stems.sphere N)) (hU : IsOpen U) (hy₀ : y₀ ∈ U)
    (V : Set X) (hV : IsOpen V) (hx₀ : x₀ ∈ V)
    (e : ↥U ≃ₜ ↥V) (he : e ⟨y₀, hy₀⟩ = ⟨x₀, hx₀⟩)
    (hFe : ∀ u : ↥U, (e u : X) = F u)
    (hgen : Submodule.span ℤ
      ({(HomologicalComplex.homologyMap (CategoryTheory.Limits.cokernel.π
          (Work.Cohomology.inclChains (TopCat.of (Work.Stems.sphere N))
            ({y₀}ᶜ : Set (Work.Stems.sphere N)))) N
        (Work.Stems.sphereGenerator N (by omega)))} : Set _) = ⊤) :
    Submodule.span ℤ
      ({(HomologicalComplex.homologyMap (CategoryTheory.Limits.cokernel.π
          (Work.Cohomology.inclChains (TopCat.of X) ({x₀}ᶜ : Set X))) N
        (HomologicalComplex.homologyMap
          (Work.Cohomology.chainMap ℤ (TopCat.of (Work.Stems.sphere N)) (TopCat.of X)
            (TopCat.ofHom F)) N
          (Work.Stems.sphereGenerator N (by omega))))} : Set _) = ⊤ := by
  set S : TopCat := TopCat.of (Work.Stems.sphere N) with hS
  set Y : TopCat := TopCat.of X with hY
  set A : Set S := ({y₀}ᶜ : Set (Work.Stems.sphere N)) with hA
  set B : Set Y := ({x₀}ᶜ : Set X) with hB
  have hAget : ∀ a : S, a ∈ A → a ≠ y₀ := fun a ha => by simpa [hA] using ha
  have hBget : ∀ b : Y, b ∈ B → b ≠ x₀ := fun b hb => by simpa [hB] using hb
  have hAopen : IsOpen A := by rw [hA]; exact isClosed_singleton.isOpen_compl
  have hBopen : IsOpen B := by rw [hB]; exact isClosed_singleton.isOpen_compl
  -- the restriction of `F` to the complement of `y₀`
  let g : TopCat.of A ⟶ TopCat.of B :=
    TopCat.ofHom
      { toFun := fun a => ⟨F a.1, fun hcon => hAget a.1 a.2 (hfib a.1 hcon)⟩
        continuous_toFun := Continuous.subtype_mk
          (F.continuous.comp continuous_subtype_val) _ }
  have hw : Work.Cohomology.subtypeIncl S A ≫ TopCat.ofHom F
      = g ≫ Work.Cohomology.subtypeIncl Y B := by
    ext a
    rfl
  -- the middle map on the open sets
  let hUV : TopCat.of U ⟶ TopCat.of V := TopCat.ofHom e.toHomotopyEquiv.toFun
  have hwUV : Work.Cohomology.subtypeIncl S U ≫ TopCat.ofHom F
      = hUV ≫ Work.Cohomology.subtypeIncl Y V := by
    ext u
    exact (hFe ⟨u.1, u.2⟩).symm
  -- the punctured homeomorphism
  let e' : ↥{u : ↥U | (u : Work.Stems.sphere N) ∈ A} ≃ₜ ↥{v : ↥V | (v : X) ∈ B} :=
    { toFun := fun u => ⟨e ⟨u.1.1, u.1.2⟩, fun hcon => by
        have hu : (u.1.1 : Work.Stems.sphere N) ≠ y₀ := hAget u.1.1 u.2
        have h1 : e ⟨u.1.1, u.1.2⟩ = ⟨x₀, hx₀⟩ := Subtype.ext hcon
        have h2 : (⟨u.1.1, u.1.2⟩ : ↥U) = ⟨y₀, hy₀⟩ := e.injective (h1.trans he.symm)
        exact hu (congrArg Subtype.val h2)⟩
      invFun := fun v => ⟨e.symm ⟨v.1.1, v.1.2⟩, fun hcon => by
        have h1 : e.symm ⟨v.1.1, v.1.2⟩ = ⟨y₀, hy₀⟩ := Subtype.ext hcon
        have h2 : (⟨v.1.1, v.1.2⟩ : ↥V) = ⟨x₀, hx₀⟩ := by
          calc (⟨v.1.1, v.1.2⟩ : ↥V) = e (e.symm ⟨v.1.1, v.1.2⟩) :=
                (Homeomorph.apply_symm_apply e _).symm
            _ = e ⟨y₀, hy₀⟩ := by rw [h1]
            _ = ⟨x₀, hx₀⟩ := he
        exact hBget v.1 v.2 (congrArg Subtype.val h2)⟩
      left_inv := fun u => by
        apply Subtype.ext
        exact e.left_inv ⟨u.1.1, u.1.2⟩
      right_inv := fun v => by
        apply Subtype.ext
        exact e.right_inv ⟨v.1.1, v.1.2⟩
      continuous_toFun := Continuous.subtype_mk (e.continuous.comp
        (Continuous.subtype_mk (continuous_subtype_val.comp continuous_subtype_val)
          (fun u => u.1.2))) _
      continuous_invFun := Continuous.subtype_mk (e.symm.continuous.comp
        (Continuous.subtype_mk (continuous_subtype_val.comp continuous_subtype_val)
          (fun v => v.1.2))) _ }
  let h' : TopCat.of {u : ↥U | (u : Work.Stems.sphere N) ∈ A}
      ⟶ TopCat.of {v : ↥V | (v : X) ∈ B} := TopCat.ofHom e'.toHomotopyEquiv.toFun
  have hw' : Work.Cohomology.inclInterA S U A ≫ g
      = h' ≫ Work.Cohomology.inclInterA Y V B := by
    ext u
    exact (hFe ⟨u.1.1, u.1.2⟩).symm
  have w'' : Work.Cohomology.subtypeIncl (TopCat.of U) {u : ↥U | (u : Work.Stems.sphere N) ∈ A}
        ≫ hUV
      = h' ≫ Work.Cohomology.subtypeIncl (TopCat.of V) {v : ↥V | (v : X) ∈ B} := by
    ext u
    rfl
  have hcovU : U ∪ A = Set.univ := by
    ext y
    rw [hA]
    simp only [Set.mem_union, Set.mem_compl_iff, Set.mem_singleton_iff, Set.mem_univ, iff_true]
    by_cases h : y = y₀
    · exact Or.inl (h ▸ hy₀)
    · exact Or.inr h
  have hcovV : V ∪ B = Set.univ := by
    ext y
    rw [hB]
    simp only [Set.mem_union, Set.mem_compl_iff, Set.mem_singleton_iff, Set.mem_univ, iff_true]
    by_cases h : y = x₀
    · exact Or.inl (h ▸ hx₀)
    · exact Or.inr h
  -- the factorisation criterion
  haveI hiso : IsIso (HomologicalComplex.homologyMap
      (Work.Cohomology.relChainsMapOf S Y A B (TopCat.ofHom F) g hw) N) :=
    Work.ThomBordism.doubleFC.isIso_homologyMap_relChainsMapOf_of_factorization
      (X := S) (Y := Y) (A := A) (B := B) (f := TopCat.ofHom F) (g := g) (w := hw)
      U V hU hV hAopen hBopen hcovU hcovV hUV hwUV h' hw' w'' N
      (fun j => Work.Cohomology.isIso_homologyMap_chainMap_of_homotopyEquiv
        (X := TopCat.of U) (Y := TopCat.of V) e.toHomotopyEquiv j)
      (fun j => Work.Cohomology.isIso_homologyMap_chainMap_of_homotopyEquiv
        (X := TopCat.of {u : ↥U | (u : Work.Stems.sphere N) ∈ A})
        (Y := TopCat.of {v : ↥V | (v : X) ∈ B}) e'.toHomotopyEquiv j)
  -- the chain-level identity
  have hkey : (HomologicalComplex.homologyMap
        (CategoryTheory.Limits.cokernel.π (Work.Cohomology.inclChains Y B)) N)
        ((HomologicalComplex.homologyMap
          (Work.Cohomology.chainMap ℤ S Y (TopCat.ofHom F)) N)
          (Work.Stems.sphereGenerator N (by omega)))
      = (HomologicalComplex.homologyMap
          (Work.Cohomology.relChainsMapOf S Y A B (TopCat.ofHom F) g hw) N)
        ((HomologicalComplex.homologyMap
          (CategoryTheory.Limits.cokernel.π (Work.Cohomology.inclChains S A)) N)
          (Work.Stems.sphereGenerator N (by omega))) := by
    have hcomp : (HomologicalComplex.homologyMap
          (Work.Cohomology.chainMap ℤ S Y (TopCat.ofHom F)) N
        ≫ HomologicalComplex.homologyMap
          (CategoryTheory.Limits.cokernel.π (Work.Cohomology.inclChains Y B)) N)
        = (HomologicalComplex.homologyMap
            (CategoryTheory.Limits.cokernel.π (Work.Cohomology.inclChains S A)) N
          ≫ HomologicalComplex.homologyMap
            (Work.Cohomology.relChainsMapOf S Y A B (TopCat.ofHom F) g hw) N) := by
      have hL := (HomologicalComplex.homologyMap_comp
        (Work.Cohomology.chainMap ℤ S Y (TopCat.ofHom F))
        (CategoryTheory.Limits.cokernel.π (Work.Cohomology.inclChains Y B)) N).symm
      have hR := (HomologicalComplex.homologyMap_comp
        (CategoryTheory.Limits.cokernel.π (Work.Cohomology.inclChains S A))
        (Work.Cohomology.relChainsMapOf S Y A B (TopCat.ofHom F) g hw) N).symm
      rw [hL, hR, cokernel_π_relChainsMapOf_aux]
    exact congrArg (fun (φ : _ ⟶ _) => (ModuleCat.Hom.hom φ)
      (Work.Stems.sphereGenerator N (by omega))) hcomp
  rw [hkey]
  refine span_singleton_map_eq_top'
    ((HomologicalComplex.homologyMap
      (Work.Cohomology.relChainsMapOf S Y A B (TopCat.ofHom F) g hw) N).hom)
    (CategoryTheory.ConcreteCategory.bijective_of_isIso
      (HomologicalComplex.homologyMap
        (Work.Cohomology.relChainsMapOf S Y A B (TopCat.ofHom F) g hw) N)).2
    ((HomologicalComplex.homologyMap
      (CategoryTheory.Limits.cokernel.π (Work.Cohomology.inclChains S A)) N)
      (Work.Stems.sphereGenerator N (by omega))) hgen

/-! ## The inverse of the cube parametrisation -/

/-- **The coordinate inverse of the cube parametrisation** `cubeToEuc N R : I^N → ℝ^N`: for a point
of the box `[-R,R]^N`, the (unique) cube point mapping to it. -/
noncomputable def cubeEucPtInv (N : ℕ) (R : ℝ) (hR : 0 < R) (y : Euc N)
    (hy : ∀ i : Fin N, |y i| ≤ R) : Fin N → unitInterval :=
  fun i => ⟨y i / (2 * R) + 1 / 2, by
    have h2R : (0 : ℝ) < 2 * R := by linarith
    refine ⟨?_, ?_⟩
    · have h3 : -(R) ≤ y i := neg_le_of_abs_le (hy i)
      have h4 : -(1 / 2 : ℝ) ≤ y i / (2 * R) := by
        rw [le_div_iff₀ h2R]
        nlinarith
      linarith
    · have h3 : y i ≤ R := le_of_abs_le (hy i)
      have h4 : y i / (2 * R) ≤ (1 / 2 : ℝ) := by
        rw [div_le_iff₀ h2R]
        nlinarith
      linarith⟩

theorem continuous_cubeEucPtInv (N : ℕ) (R : ℝ) (hR : 0 < R) :
    Continuous (fun y : ↥{y : Euc N | ∀ i : Fin N, |y i| ≤ R} =>
      cubeEucPtInv N R hR y.1 y.2) := by
  refine continuous_pi (fun i => Continuous.subtype_mk ?_ _)
  exact (((EuclideanSpace.proj (𝕜 := ℝ) i).continuous.comp continuous_subtype_val).div_const
    (2 * R)).add_const (1 / 2)

theorem cubeToEuc_cubeEucPtInv (N : ℕ) (R : ℝ) (hR : 0 < R) (y : Euc N)
    (hy : ∀ i : Fin N, |y i| ≤ R) :
    cubeToEuc N R (cubeEucPtInv N R hR y hy) = y := by
  ext i
  have h1 : (cubeToEuc N R (cubeEucPtInv N R hR y hy)) i
      = 2 * R * (((cubeEucPtInv N R hR y hy) i : ℝ) - 1 / 2) :=
    congrFun (funToEuc_symm_cubeToEuc N R _) i
  rw [h1]
  have h2 : ((cubeEucPtInv N R hR y hy) i : ℝ) = y i / (2 * R) + 1 / 2 := rfl
  rw [h2]
  have hR0 : (2 * R) ≠ 0 := by positivity
  field_simp
  ring

theorem cubeToEuc_injective (N : ℕ) {R : ℝ} (hR : 0 < R) : Function.Injective (cubeToEuc N R) := by
  intro t s h
  funext i
  have ht : (cubeToEuc N R t) i = 2 * R * ((t i : ℝ) - 1 / 2) :=
    congrFun (funToEuc_symm_cubeToEuc N R t) i
  have hs : (cubeToEuc N R s) i = 2 * R * ((s i : ℝ) - 1 / 2) :=
    congrFun (funToEuc_symm_cubeToEuc N R s) i
  have h' : 2 * R * ((t i : ℝ) - 1 / 2) = 2 * R * ((s i : ℝ) - 1 / 2) := by
    rw [← ht, ← hs, h]
  have hR0 : (2 * R) ≠ 0 := by positivity
  have h'' : (t i : ℝ) - 1 / 2 = (s i : ℝ) - 1 / 2 := mul_left_cancel₀ hR0 h'
  exact Subtype.ext (by linarith)

/-! ## The radial shrink and the inverse of the collapse on the open tube -/

/-- The radial shrink of the normal bundle is continuous. -/
theorem continuous_normalShrink {V : Work.ThomBordism.Man8} {N : ℕ}
    {E : EmbeddingData V N} {ε : ℝ} (hε : 0 < ε) :
    Continuous (normalShrink E ε) := by
  refine Continuous.subtype_mk (Continuous.prodMk continuous_subtype_val.fst ?_) _
  have h1 : Continuous (fun p : NormalTotal E => ε + normalNorm E p) :=
    continuous_const.add (continuous_normalNorm E)
  have h2 : Continuous (fun p : NormalTotal E => (ε + normalNorm E p)⁻¹) :=
    h1.inv₀ (fun p => by
      have hp := normalNorm_nonneg E p
      exact ne_of_gt (by linarith))
  exact (continuous_const.mul h2).smul continuous_subtype_val.snd

/-- The inverse of the tubular map on the shrunk point. -/
theorem inv_zeta {V : Work.ThomBordism.Man8} {N : ℕ} {E : EmbeddingData V N} {ε : ℝ}
    (C : TubeChart E ε) (p : NormalTotal E) :
    C.inv (tubeMap E (normalShrink E ε p)) = normalShrink E ε p :=
  C.inv_tubeMap _ (le_of_lt (normalNorm_normalShrink_lt C.eps_pos p))

/-- The collapse of the shrunk point is the point itself. -/
theorem g_zeta {V : Work.ThomBordism.Man8} {N : ℕ} {E : EmbeddingData V N} {ε : ℝ}
    (C : TubeChart E ε) (g : C(OnePoint (Euc N), OnePoint (NormalTotal E)))
    (hg2 : ∀ y, y ∈ C.openTube → g (OnePoint.some y) = OnePoint.some (normalBlowUp E ε (C.inv y)))
    (p : NormalTotal E) :
    g (OnePoint.some (tubeMap E (normalShrink E ε p))) = OnePoint.some p := by
  rw [hg2 _ (C.tubeMap_mem_openTube (normalNorm_normalShrink_lt C.eps_pos p)), inv_zeta C p,
    normalBlowUp_normalShrink C.eps_pos p]

/-- The shrink of the blow-up of a point of the open tube is that point. -/
theorem zeta_inv {V : Work.ThomBordism.Man8} {N : ℕ} {E : EmbeddingData V N} {ε : ℝ}
    (C : TubeChart E ε) {y : Euc N} (hy : y ∈ C.openTube) :
    tubeMap E (normalShrink E ε (normalBlowUp E ε (C.inv y))) = y := by
  rw [normalShrink_normalBlowUp C.eps_pos (C.normalNorm_inv_lt hy),
    C.inv_tubeMap_of_mem_openTube hy]

/-! ## The fibre of the collapse over the zero-section point -/

/-- **The only point of `S^N` that the collapse sends to the zero-section point over `v₀` is the one
over `E.e v₀`.** -/
theorem collapseFibre {V : Work.ThomBordism.Man8} {k : ℕ}
    {E : EmbeddingData V (8 + k)} {ε : ℝ}
    (C : TubeChart E ε) {R : ℝ} (hR : 0 ≤ R)
    (hbox : ∀ y ∈ C.U, ∀ i : Fin (8 + k), |y i| < R)
    (g : C(OnePoint (Euc (8 + k)), OnePoint (NormalTotal E)))
    (hg : ∀ y, y ∉ C.openTube → g (OnePoint.some y) = OnePoint.infty)
    (hg2 : ∀ y, y ∈ C.openTube → g (OnePoint.some y)
      = OnePoint.some (normalBlowUp E ε (C.inv y)))
    (v₀ : V.pt) (q₀ : Fin (8 + k) → unitInterval)
    (hq₀ : cubeToEuc (8 + k) R q₀ = E.e v₀) :
    ∀ y : Work.Stems.sphere (8 + k),
      Work.Stems.cubeLift (8 + k) (by omega)
        (Work.Tubular.tubeGenLoopOnePoint C g hg hR hbox) y = zeroSectionOnePoint E v₀ →
      y = Work.Stems.collapseMap (8 + k) (by omega) q₀ := by
  have hN : 1 ≤ 8 + k := by omega
  intro y hy
  obtain ⟨q, rfl⟩ := (Work.Stems.collapseMap_isQuotientMap (8 + k) hN).surjective y
  have hRpos : 0 < R := by
    have h1 : |E.e v₀ ⟨0, by omega⟩| < R :=
      hbox (E.e v₀) (C.zero_mem_U v₀) ⟨0, by omega⟩
    have h2 := abs_nonneg (E.e v₀ ⟨0, by omega⟩)
    linarith
  have hF : Work.Stems.cubeLift (8 + k) hN
        (Work.Tubular.tubeGenLoopOnePoint C g hg hR hbox)
        (Work.Stems.collapseMap (8 + k) hN q)
      = g (OnePoint.some (cubeToEuc (8 + k) R q)) := by
    rw [← ContinuousMap.comp_apply, Work.Stems.cubeLift_comp]
    rfl
  have hy' : g (OnePoint.some (cubeToEuc (8 + k) R q)) = zeroSectionOnePoint E v₀ := by
    rw [← hF]; exact hy
  by_cases hbd : q ∈ Cube.boundary (Fin (8 + k))
  · exfalso
    have hmem : cubeToEuc (8 + k) R q ∉ C.openTube := by
      intro hmem
      obtain ⟨i, hi⟩ := cubeToEuc_boundary (8 + k) hR hbd
      have h1 : |(cubeToEuc (8 + k) R q) i| < R := hbox _ (C.openTube_subset_U hmem) i
      rw [hi] at h1
      exact lt_irrefl R h1
    rw [hg _ hmem] at hy'
    exact (OnePoint.coe_ne_infty (⟨(v₀, (0 : Euc (8 + k))), zero_mem_normalSpace E v₀⟩ :
      NormalTotal E)) hy'.symm
  · have hmem : cubeToEuc (8 + k) R q ∈ C.openTube := by
      by_contra hnot'
      rw [hg _ hnot'] at hy'
      exact (OnePoint.coe_ne_infty (⟨(v₀, (0 : Euc (8 + k))), zero_mem_normalSpace E v₀⟩ :
        NormalTotal E)) hy'.symm
    rw [hg2 _ hmem, zeroSectionOnePoint_apply] at hy'
    have h1 : normalBlowUp E ε (C.inv (cubeToEuc (8 + k) R q))
        = ⟨(v₀, (0 : Euc (8 + k))), zero_mem_normalSpace E v₀⟩ :=
      OnePoint.coe_eq_coe.mp hy'
    have h2 : (C.inv (cubeToEuc (8 + k) R q)).1.1 = v₀ := by
      have h := congrArg (fun p : NormalTotal E => p.1.1) h1
      simpa [normalBlowUp_proj] using h
    have h3 : (C.inv (cubeToEuc (8 + k) R q)).1.2 = 0 := by
      have hb : blowCoeff E ε (C.inv (cubeToEuc (8 + k) R q))
          • (C.inv (cubeToEuc (8 + k) R q)).1.2 = 0 := by
        have h := congrArg (fun p : NormalTotal E => p.1.2) h1
        simpa [normalBlowUp] using h
      exact (smul_eq_zero.mp hb).resolve_left
        (ne_of_gt (blowCoeff_pos C.eps_pos (C.normalNorm_inv_lt hmem)))
    have h4 : C.inv (cubeToEuc (8 + k) R q)
        = ⟨(v₀, (0 : Euc (8 + k))), zero_mem_normalSpace E v₀⟩ := by
      apply Subtype.ext
      exact Prod.ext h2 h3
    have h5 : cubeToEuc (8 + k) R q = E.e v₀ := by
      rw [← C.inv_tubeMap_of_mem_openTube hmem, h4, tubeMap_mk]
      simp
    have h6 : q = q₀ := cubeToEuc_injective (8 + k) hRpos (by rw [h5, hq₀])
    rw [h6]

/-! ## The collapse on a collapsed cube point -/

theorem cubeLift_collapseMap {V : Work.ThomBordism.Man8} {k : ℕ}
    {E : EmbeddingData V (8 + k)} {ε : ℝ}
    (C : TubeChart E ε) {R : ℝ} (hR : 0 ≤ R)
    (hbox : ∀ y ∈ C.U, ∀ i : Fin (8 + k), |y i| < R)
    (g : C(OnePoint (Euc (8 + k)), OnePoint (NormalTotal E)))
    (hg : ∀ y, y ∉ C.openTube → g (OnePoint.some y) = OnePoint.infty)
    (hN : 1 ≤ 8 + k) (q : Fin (8 + k) → unitInterval) :
    Work.Stems.cubeLift (8 + k) hN (Work.Tubular.tubeGenLoopOnePoint C g hg hR hbox)
        (Work.Stems.collapseMap (8 + k) hN q)
      = g (OnePoint.some (cubeToEuc (8 + k) R q)) := by
  rw [← ContinuousMap.comp_apply, Work.Stems.cubeLift_comp]
  rfl

/-! ## The main theorem -/

theorem localisationCollapseClassSpanTop {V : Work.ThomBordism.Man8} {k : ℕ}
    {E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)} {ε : ℝ}
    (C : Work.Tubular.TubeChart E ε) (hU : IsCompact C.U) {R : ℝ} (hR : 0 ≤ R)
    (hbox : ∀ y ∈ C.U, ∀ i : Fin (8 + k), |y i| < R)
    (g : C(OnePoint (Work.Tubular.Euc (8 + k)), OnePoint (Work.Tubular.NormalTotal E)))
    (hg : ∀ y, y ∉ C.openTube → g (OnePoint.some y) = OnePoint.infty)
    (hg2 : ∀ y, y ∈ C.openTube → g (OnePoint.some y)
      = OnePoint.some (Work.Tubular.normalBlowUp E ε (C.inv y)))
    (v₀ : V.pt) :
    Submodule.span ℤ
      {(Work.Tubular.localisationPunct E v₀ (8 + k)
        (Work.Stems.hurewiczChain (8 + k) (by omega) OnePoint.infty
          (Work.Tubular.tubeGenLoopOnePoint C g hg hR hbox)))} = ⊤ := by
  have hN : 1 ≤ 8 + k := by omega
  have hRpos : 0 < R := by
    have h1 : |E.e v₀ ⟨0, by omega⟩| < R := hbox (E.e v₀) (C.zero_mem_U v₀) ⟨0, by omega⟩
    have h2 := abs_nonneg (E.e v₀ ⟨0, by omega⟩)
    linarith
  set q₀ : Fin (8 + k) → unitInterval :=
    cubeEucPtInv (8 + k) R hRpos (E.e v₀)
      (fun i => le_of_lt (hbox (E.e v₀) (C.zero_mem_U v₀) i)) with hq₀def
  have hq₀ : cubeToEuc (8 + k) R q₀ = E.e v₀ :=
    cubeToEuc_cubeEucPtInv (8 + k) R hRpos (E.e v₀) _
  set y₀ : Work.Stems.sphere (8 + k) := Work.Stems.collapseMap (8 + k) hN q₀ with hy₀def
  set F : C(Work.Stems.sphere (8 + k), OnePoint (NormalTotal E)) :=
    Work.Stems.cubeLift (8 + k) hN (Work.Tubular.tubeGenLoopOnePoint C g hg hR hbox) with hFdef
  set x₀ : OnePoint (NormalTotal E) := zeroSectionOnePoint E v₀ with hx₀def
  have hFy₀ : F y₀ = x₀ := by
    rw [hFdef, hy₀def, hx₀def, cubeLift_collapseMap C hR hbox g hg hN q₀, hq₀,
      hg2 (E.e v₀) (C.mem_openTube v₀)]
    congr 1
    have hinv : C.inv (E.e v₀) = ⟨(v₀, (0 : Euc (8 + k))), zero_mem_normalSpace E v₀⟩ := by
      have h := C.inv_tubeMap
        (⟨(v₀, (0 : Euc (8 + k))), zero_mem_normalSpace E v₀⟩ : NormalTotal E)
        (by simp [C.eps_pos.le])
      simpa using h
    rw [hinv]
    simp [normalBlowUp]
  have hfib : ∀ y, F y = x₀ → y = y₀ := collapseFibre C hR hbox g hg hg2 v₀ q₀ hq₀
  -- the open neighbourhoods and the local homeomorphism
  set V' : Set (OnePoint (NormalTotal E)) :=
    Set.range (OnePoint.some : NormalTotal E → OnePoint (NormalTotal E)) with hV'def
  have hV'open : IsOpen V' := by
    rw [hV'def]
    rw [show Set.range (OnePoint.some : NormalTotal E → OnePoint (NormalTotal E))
        = OnePoint.some '' (Set.univ : Set (NormalTotal E)) from Set.image_univ.symm]
    exact OnePoint.isOpen_image_coe.mpr isOpen_univ
  set U : Set (Work.Stems.sphere (8 + k)) := F ⁻¹' V' with hUdef
  have hUopen : IsOpen U := by rw [hUdef]; exact hV'open.preimage F.continuous
  have hx₀V : x₀ ∈ V' := by
    rw [hV'def, hx₀def]
    exact ⟨⟨(v₀, (0 : Euc (8 + k))), zero_mem_normalSpace E v₀⟩, rfl⟩
  have hy₀U : y₀ ∈ U := by
    rw [hUdef, Set.mem_preimage, hFy₀]; exact hx₀V
  let σ : NormalTotal E ≃ₜ ↥V' := (OnePoint.isOpenEmbedding_coe.toIsEmbedding).toHomeomorph
  let zeta : ↥V' → Euc (8 + k) := fun p => tubeMap E (normalShrink E ε (σ.symm p))
  have hzeta_cont : Continuous zeta :=
    (continuous_tubeMap E).comp ((continuous_normalShrink C.eps_pos).comp σ.symm.continuous)
  have hzeta_mem : ∀ p : ↥V', zeta p ∈ C.openTube := fun p =>
    C.tubeMap_mem_openTube (normalNorm_normalShrink_lt C.eps_pos (σ.symm p))
  have hzeta_le : ∀ p : ↥V', ∀ i : Fin (8 + k), |zeta p i| ≤ R := fun p i =>
    le_of_lt (hbox _ (C.openTube_subset_U (hzeta_mem p)) i)
  let psi : ↥V' → (Fin (8 + k) → unitInterval) := fun p =>
    cubeEucPtInv (8 + k) R hRpos (zeta p) (hzeta_le p)
  have hpsi_cont : Continuous psi :=
    Continuous.comp (continuous_cubeEucPtInv (8 + k) R hRpos)
      (Continuous.subtype_mk hzeta_cont (fun p => hzeta_le p))
  have hpsi_cube : ∀ p : ↥V', cubeToEuc (8 + k) R (psi p) = zeta p := fun p =>
    cubeToEuc_cubeEucPtInv (8 + k) R hRpos (zeta p) (hzeta_le p)
  have hg_zeta : ∀ p : ↥V', g (OnePoint.some (zeta p)) = OnePoint.some (σ.symm p) := fun p =>
    g_zeta C g hg2 (σ.symm p)
  let iota : ↥V' → ↥U := fun p => ⟨Work.Stems.collapseMap (8 + k) hN (psi p), by
    rw [hUdef, Set.mem_preimage, hFdef,
      cubeLift_collapseMap C hR hbox g hg hN (psi p), hpsi_cube]
    exact ⟨σ.symm p, (hg_zeta p).symm⟩⟩
  have hiota_cont : Continuous iota :=
    Continuous.subtype_mk ((Work.Stems.collapseMap (8 + k) hN).continuous.comp hpsi_cont) _
  have hσcoe : ∀ q : NormalTotal E, ((σ q : ↥V') : OnePoint (NormalTotal E)) = OnePoint.some q :=
    fun q => rfl
  have hsome_symm : ∀ p : ↥V', OnePoint.some (σ.symm p) = (p : OnePoint (NormalTotal E)) := by
    intro p
    rw [← hσcoe (σ.symm p), σ.apply_symm_apply p]
  let e : ↥U ≃ₜ ↥V' :=
    { toFun := fun u => ⟨F u.1, u.2⟩
      invFun := iota
      left_inv := by
        intro u
        apply Subtype.ext
        obtain ⟨q, hq⟩ := (Work.Stems.collapseMap_isQuotientMap (8 + k) hN).surjective u.1
        have hFu : F u.1 = OnePoint.some (σ.symm (⟨F u.1, u.2⟩ : ↥V')) := by
          rw [← hσcoe (σ.symm (⟨F u.1, u.2⟩ : ↥V')), σ.apply_symm_apply]
        have h1 : F u.1 = g (OnePoint.some (cubeToEuc (8 + k) R q)) := by
          rw [← hq, hFdef]
          exact cubeLift_collapseMap C hR hbox g hg hN q
        have hmem : cubeToEuc (8 + k) R q ∈ C.openTube := by
          by_contra hnot
          have h1' : F u.1 = OnePoint.infty := by rw [h1, hg _ hnot]
          exact (OnePoint.coe_ne_infty (σ.symm (⟨F u.1, u.2⟩ : ↥V'))) (hFu.symm.trans h1')
        have h2 : σ.symm (⟨F u.1, u.2⟩ : ↥V')
            = normalBlowUp E ε (C.inv (cubeToEuc (8 + k) R q)) :=
          OnePoint.coe_eq_coe.mp (hFu.symm.trans (h1.trans (hg2 _ hmem)))
        have h3 : zeta (⟨F u.1, u.2⟩ : ↥V') = cubeToEuc (8 + k) R q := by
          show tubeMap E (normalShrink E ε (σ.symm (⟨F u.1, u.2⟩ : ↥V')))
            = cubeToEuc (8 + k) R q
          rw [h2, zeta_inv C hmem]
        have h4 : psi (⟨F u.1, u.2⟩ : ↥V') = q :=
          cubeToEuc_injective (8 + k) hRpos (by rw [hpsi_cube, h3])
        show Work.Stems.collapseMap (8 + k) hN (psi ⟨F u.1, u.2⟩) = u.1
        rw [h4, hq]
      right_inv := by
        intro p
        apply Subtype.ext
        show F (Work.Stems.collapseMap (8 + k) hN (psi p)) = (p : OnePoint (NormalTotal E))
        rw [hFdef, cubeLift_collapseMap C hR hbox g hg hN (psi p), hpsi_cube, hg_zeta p]
        exact hsome_symm p
      continuous_toFun := Continuous.subtype_mk (F.continuous.comp continuous_subtype_val) _
      continuous_invFun := hiota_cont }
  have hgen : Submodule.span ℤ
      ({(HomologicalComplex.homologyMap (CategoryTheory.Limits.cokernel.π
          (Work.Cohomology.inclChains (TopCat.of (Work.Stems.sphere (8 + k)))
            ({y₀}ᶜ : Set (Work.Stems.sphere (8 + k))))) (8 + k)
        (Work.Stems.sphereGenerator (8 + k) hN))} : Set _) = ⊤ :=
    localGeneratorSphere (8 + k) (by omega) y₀
  exact spanLocalisationOfLocalHomeo (X := OnePoint (NormalTotal E)) (N := 8 + k)
    (by omega) x₀ F y₀ hfib U hUopen hy₀U V' hV'open hx₀V e
    (Subtype.ext hFy₀) (fun u => rfl) hgen

end

end Work.Tubular.TubeClass
