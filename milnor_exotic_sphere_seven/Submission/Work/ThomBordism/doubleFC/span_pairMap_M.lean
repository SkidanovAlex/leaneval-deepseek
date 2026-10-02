import Mathlib
import Submission.Work.ThomBordism.doubleFC.defs
import Submission.Work.ThomBordism.doubleFC.interiorData
import Submission.Work.ThomBordism.doubleFC.relFactor
import Submission.Work.ThomBordism.doubleChartedT2
import Submission.Work.ThomBordism.doubleCharted
import Submission.Work.Cohomology.localHomology
import Submission.Work.Cohomology.relChainsMapOf_comp
import Submission.Work.Cohomology.pd_plumbing
import Submission.Work.Orient.Boundary.localHomology_corner

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open CategoryTheory AlgebraicTopology CategoryTheory.Limits
open scoped Manifold

namespace Work.ThomBordism.doubleFC

/-- **An isomorphism of `ℤ`-modules sends a generator to a generator.** -/
private lemma span_singleton_of_isIso {A B : ModuleCat ℤ} (φ : A ⟶ B) [IsIso φ] (a : A)
    (h : Submodule.span ℤ {a} = ⊤) :
    Submodule.span ℤ {(ModuleCat.Hom.hom φ) a} = ⊤ := by
  have hmap : Submodule.map (ModuleCat.Hom.hom φ) (Submodule.span ℤ {a}) =
      Submodule.span ℤ {(ModuleCat.Hom.hom φ) a} := by
    rw [Submodule.map_span]
    simp
  have htop : Submodule.map (ModuleCat.Hom.hom φ) (⊤ : Submodule ℤ A) = ⊤ := by
    rw [Submodule.map_top, LinearMap.range_eq_top.mpr]
    exact (ModuleCat.epi_iff_surjective _).mp (IsIso.epi_of_iso φ)
  rw [← hmap, h, htop]

/-- **The first copy of `M` in its double preserves local generators at an interior point.**

Route (do NOT try to apply `relChainsMapOf_homologyMap_isIso` to the pair map itself: `M∖{y} → D∖{ιM y}`
is not a quasi-isomorphism).  Instead factor `pairMapιM` through the *open* sets `int M ⊆ M` and
`V := doubleιM '' (interior M) ⊆ Double n M`: the excision isomorphisms
`Work.Cohomology.excision_relChainsMap_isIso` for `H(int M, int M∖{y}) ≅ H(M, M∖{y})` and for
`H(V, V∖{ιM y}) ≅ H(D, D∖{ιM y})` (the covers are `U ∪ {y}ᶜ = M`, `V ∪ {ιM y}ᶜ = D`), together with
`Work.Orient.homeoRelChainsIso` for the homeomorphism `int M ≅ V` induced by the open embedding
`Work.ThomBordism.isOpenEmbedding_interiorEmb`.  The composite
`(excision) ∘ (homeo) ∘ (excision)⁻¹` is an isomorphism and equals `pairMapιM` by
`Work.ThomBordism.DoubleFC.relChainsMapOf_comp`-style functoriality of `relChainsMapOf`; an
isomorphism sends generators to generators (`Submodule.map_span`). -/
theorem span_pairMap_M (n : ℕ) (M : Type) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) M]
    [IsManifold (modelWithCornersEuclideanHalfSpace (n + 1)) 1 M]
    (y : M) (hy : y ∉ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary M)
    (v : (Work.Cohomology.relChains (TopCat.of M) ({y} : Set M)ᶜ).homology (n + 1))
    (hv : Submodule.span ℤ {v} = ⊤) :
    Submodule.span ℤ {((HomologicalComplex.homologyMap
      (Work.ThomBordism.DoubleFC.pairMapιM n M y) (n + 1)) v)} = ⊤ := by
  -- the double of a `T2` manifold with boundary is `T2`
  haveI hT2 : T2Space (Double n M) := Work.ThomBordism.DblT2.t2Space_double (n := n) (M := M)
  -- the two open sets and the two covers
  have hU : IsOpen (Work.ThomBordism.DoubleFC.intSet n M) :=
    (Work.ThomBordism.isClosed_boundary_one (n := n) (M := M)).isOpen_compl
  have hV : IsOpen (Work.ThomBordism.DoubleFC.intImg n M) :=
    (Work.ThomBordism.isOpenEmbedding_interiorEmb (n := n) (M := M)).isOpen_range
  have hA : IsOpen (({y} : Set M)ᶜ) := isClosed_singleton.isOpen_compl
  have hB : IsOpen (({doubleιM (n := n) (M := M) y} : Set (Double n M))ᶜ) :=
    isClosed_singleton.isOpen_compl
  have hcovU : Work.ThomBordism.DoubleFC.intSet n M ∪ ({y} : Set M)ᶜ = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    by_cases h : x = y
    · subst h; left; exact hy
    · right; exact h
  have hcovV : Work.ThomBordism.DoubleFC.intImg n M ∪
      ({doubleιM (n := n) (M := M) y} : Set (Double n M))ᶜ = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    by_cases h : x = doubleιM (n := n) (M := M) y
    · subst h; left; exact ⟨⟨y, hy⟩, rfl⟩
    · right; exact h
  -- the four compatibility equations of the factorisation criterion
  have hw : Work.Cohomology.subtypeIncl (TopCat.of M) (Work.ThomBordism.DoubleFC.intSet n M)
        ≫ Work.ThomBordism.DoubleFC.fPair n M =
      Work.ThomBordism.DoubleFC.hInt n M ≫
        Work.Cohomology.subtypeIncl (TopCat.of (Double n M))
          (Work.ThomBordism.DoubleFC.intImg n M) := by
    apply TopCat.ext; intro u; rfl
  have hw' : Work.Cohomology.inclInterA (TopCat.of M) (Work.ThomBordism.DoubleFC.intSet n M)
        ({y} : Set M)ᶜ ≫ Work.ThomBordism.DoubleFC.gPair n M y =
      Work.ThomBordism.DoubleFC.hIntPunct n M y hy ≫
        Work.Cohomology.inclInterA (TopCat.of (Double n M))
          (Work.ThomBordism.DoubleFC.intImg n M)
          ({doubleιM (n := n) (M := M) y} : Set (Double n M))ᶜ := by
    apply TopCat.ext; intro u; rfl
  have w'' : Work.Cohomology.subtypeIncl (TopCat.of (Work.ThomBordism.DoubleFC.intSet n M))
        (Work.ThomBordism.DoubleFC.punctSet n M y) ≫ Work.ThomBordism.DoubleFC.hInt n M =
      Work.ThomBordism.DoubleFC.hIntPunct n M y hy ≫
        Work.Cohomology.subtypeIncl (TopCat.of (Work.ThomBordism.DoubleFC.intImg n M))
          (Work.ThomBordism.DoubleFC.punctImg n M y) := by
    apply TopCat.ext; intro u; rfl
  -- the abstract factorisation criterion
  haveI hiso : CategoryTheory.IsIso (HomologicalComplex.homologyMap
      (Work.Cohomology.relChainsMapOf (TopCat.of M) (TopCat.of (Double n M))
        ({y} : Set M)ᶜ ({doubleιM (n := n) (M := M) y} : Set (Double n M))ᶜ
        (Work.ThomBordism.DoubleFC.fPair n M) (Work.ThomBordism.DoubleFC.gPair n M y)
        (by ext m; rfl)) (n + 1)) :=
    isIso_homologyMap_relChainsMapOf_of_factorization
      (X := TopCat.of M) (Y := TopCat.of (Double n M))
      (A := ({y} : Set M)ᶜ) (B := ({doubleιM (n := n) (M := M) y} : Set (Double n M))ᶜ)
      (f := Work.ThomBordism.DoubleFC.fPair n M)
      (g := Work.ThomBordism.DoubleFC.gPair n M y) (w := by ext m; rfl)
      (U := Work.ThomBordism.DoubleFC.intSet n M) (V := Work.ThomBordism.DoubleFC.intImg n M)
      hU hV hA hB hcovU hcovV
      (h := Work.ThomBordism.DoubleFC.hInt n M) hw
      (h' := Work.ThomBordism.DoubleFC.hIntPunct n M y hy) hw' w'' (n + 1)
      (fun j => Work.ThomBordism.DoubleFC.isIso_homologyMap_chainMap_hInt n M j)
      (fun j => Work.ThomBordism.DoubleFC.isIso_homologyMap_chainMap_hIntPunct n M y hy j)
  -- `pairMapιM` is definitionally the `relChainsMapOf` built from `fPair`/`gPair`
  haveI hpair : CategoryTheory.IsIso (HomologicalComplex.homologyMap
      (Work.ThomBordism.DoubleFC.pairMapιM n M y) (n + 1)) := hiso
  exact span_singleton_of_isIso
    (HomologicalComplex.homologyMap (Work.ThomBordism.DoubleFC.pairMapιM n M y) (n + 1)) v hv

end Work.ThomBordism.doubleFC
