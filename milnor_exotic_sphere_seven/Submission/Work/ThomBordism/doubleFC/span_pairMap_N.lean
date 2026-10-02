import Mathlib
import Submission.Work.ThomBordism.doubleFC.defs
import Submission.Work.ThomBordism.doubleChartedT2
import Submission.Work.ThomBordism.doubleCharted
import Submission.Work.Cohomology.localHomology
import Submission.Work.Cohomology.pd_plumbing
import Submission.Work.Orient.Boundary.localHomology_corner
import Submission.Work.Cohomology.relChainsMapOf_comp

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The second copy of `M` in its double preserves local generators at an interior point

The proof factors the pair map `pairMapιN` through the interior of `M` (an open set `U ⊆ M` on which
the second inclusion is an open embedding, hence a homeomorphism onto its image `V ⊆ D = Double n M`):

`H(U, U∖{y}) --exc--> H(M, M∖{y}) --pairMapιN--> H(D, D∖{ιN y})`

is, on the chain level, the composite

`(excision) ≫ (homeomorphism U ≅ V) ≫ (excision for V ⊆ D)`,

each of whose factors induces an isomorphism on homology.  The chain-level identification of the two
composites is `comp_identity` below (`relChainsMapOf_comp`-style functoriality), and the conclusion
follows because a bijective map sends generators of `ℤ`-modules to generators.
-/

set_option linter.style.haveILetI false
set_option maxHeartbeats 1600000

open CategoryTheory AlgebraicTopology CategoryTheory.Limits
open scoped Manifold

namespace Work.ThomBordism.doubleFC

/-! Auxiliary data: the interior of `M`, its image in the double, and the induced homeomorphism. -/
namespace SpanNData

noncomputable section

abbrev Uu (n : ℕ) (M : Type) [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) M] : Set M :=
  ((modelWithCornersEuclideanHalfSpace (n + 1)).boundary M)ᶜ

abbrev Vv (n : ℕ) (M : Type) [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) M] : Set (Work.ThomBordism.Double n M) :=
  Set.range (Work.ThomBordism.interiorEmbN (n := n) (M := M))

abbrev CY (n : ℕ) (M : Type) [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) M] (y : M) : Set (Work.ThomBordism.Double n M) :=
  ({Work.ThomBordism.doubleιN (n := n) (M := M) y} : Set (Work.ThomBordism.Double n M))ᶜ

abbrev eN (n : ℕ) (M : Type) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) M]
    [IsManifold (modelWithCornersEuclideanHalfSpace (n + 1)) 1 M] :
    ↥(Uu n M) ≃ₜ ↥(Vv n M) :=
  (Work.ThomBordism.isOpenEmbedding_interiorEmbN (n := n) (M := M)).toIsEmbedding.toHomeomorph

abbrev hN (n : ℕ) (M : Type) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) M]
    [IsManifold (modelWithCornersEuclideanHalfSpace (n + 1)) 1 M] :
    TopCat.of (Uu n M) ⟶ TopCat.of (Vv n M) :=
  (TopCat.isoOfHomeo (eN n M)).hom

theorem isIso_hN (n : ℕ) (M : Type) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) M]
    [IsManifold (modelWithCornersEuclideanHalfSpace (n + 1)) 1 M] :
    IsIso (hN n M) :=
  (TopCat.isoOfHomeo (X := TopCat.of (Uu n M)) (Y := TopCat.of (Vv n M)) (eN n M)).isIso_hom

abbrev AY (n : ℕ) (M : Type) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) M]
    [IsManifold (modelWithCornersEuclideanHalfSpace (n + 1)) 1 M] (y : M) : Set ↥(Uu n M) :=
  {z | (z : M) ∈ ({y} : Set M)ᶜ}

abbrev BY (n : ℕ) (M : Type) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) M]
    [IsManifold (modelWithCornersEuclideanHalfSpace (n + 1)) 1 M] (y : M) :
    Set ↥(Vv n M) :=
  {z | (z : Work.ThomBordism.Double n M) ∈ CY n M y}

theorem hAB (n : ℕ) (M : Type) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) M]
    [IsManifold (modelWithCornersEuclideanHalfSpace (n + 1)) 1 M] (y : M) :
    ∀ u : ↥(Uu n M), u ∈ AY n M y ↔ (eN n M) u ∈ BY n M y := by
  intro u
  have hcoe : ((eN n M) u : Work.ThomBordism.Double n M) =
      Work.ThomBordism.doubleιN (n := n) (M := M) (u : M) := rfl
  simp only [AY, BY, CY, Set.mem_compl_iff, Set.mem_singleton_iff]
  constructor
  · intro h hc
    exact h (Work.ThomBordism.doubleιN_injective (n := n) (M := M) (hcoe.symm.trans hc))
  · intro h hc
    exact h (hcoe.trans (congrArg (Work.ThomBordism.doubleιN (n := n) (M := M)) hc))

abbrev psT (n : ℕ) (M : Type) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) M]
    [IsManifold (modelWithCornersEuclideanHalfSpace (n + 1)) 1 M] (y : M) :
    ↥(AY n M y) ≃ₜ ↥(BY n M y) :=
  Work.Orient.Boundary.homeomorphRestrict (eN n M) _ _ (hAB n M y)

abbrev g2 (n : ℕ) (M : Type) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) M]
    [IsManifold (modelWithCornersEuclideanHalfSpace (n + 1)) 1 M] (y : M) :
    TopCat.of (AY n M y) ⟶ TopCat.of (BY n M y) :=
  (TopCat.isoOfHomeo (psT n M y)).hom

theorem isIso_g2 (n : ℕ) (M : Type) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) M]
    [IsManifold (modelWithCornersEuclideanHalfSpace (n + 1)) 1 M] (y : M) :
    IsIso (g2 n M y) :=
  (TopCat.isoOfHomeo (X := TopCat.of (AY n M y)) (Y := TopCat.of (BY n M y)) (psT n M y)).isIso_hom

theorem w2 (n : ℕ) (M : Type) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) M]
    [IsManifold (modelWithCornersEuclideanHalfSpace (n + 1)) 1 M] (y : M) :
    Work.Cohomology.subtypeIncl (TopCat.of (Uu n M)) (AY n M y) ≫ hN n M
      = g2 n M y ≫ Work.Cohomology.subtypeIncl (TopCat.of (Vv n M)) (BY n M y) := by
  ext a
  rfl

abbrev fp (n : ℕ) (M : Type) [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) M] :
    TopCat.of M ⟶ TopCat.of (Work.ThomBordism.Double n M) :=
  TopCat.ofHom ⟨Work.ThomBordism.doubleιN (n := n) (M := M),
    Work.ThomBordism.continuous_doubleιN (n := n) (M := M)⟩

abbrev gp (n : ℕ) (M : Type) [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) M] (y : M) :
    TopCat.of ↥(({y} : Set M)ᶜ) ⟶ TopCat.of (CY n M y) :=
  TopCat.ofHom
    ⟨fun m => ⟨Work.ThomBordism.doubleιN (n := n) (M := M) m.1,
        by
          intro h
          exact m.2 (Work.ThomBordism.doubleιN_injective (n := n) (M := M) h)⟩,
      Continuous.subtype_mk
        ((Work.ThomBordism.continuous_doubleιN (n := n) (M := M)).comp continuous_subtype_val) _⟩

theorem relChainsMapOf_congr_fg {X Y : TopCat} (A : Set X) (B : Set Y)
    {f f' : X ⟶ Y} (hf : f = f')
    {g g' : TopCat.of A ⟶ TopCat.of B} (hg : g = g')
    (w : Work.Cohomology.subtypeIncl X A ≫ f = g ≫ Work.Cohomology.subtypeIncl Y B)
    (w' : Work.Cohomology.subtypeIncl X A ≫ f' = g' ≫ Work.Cohomology.subtypeIncl Y B) :
    Work.Cohomology.relChainsMapOf X Y A B f g w
      = Work.Cohomology.relChainsMapOf X Y A B f' g' w' := by
  rcases hf with rfl
  rcases hg with rfl
  exact congrArg (fun v => Work.Cohomology.relChainsMapOf X Y A B f g v) (Subsingleton.elim w w')

abbrev FP (n : ℕ) (M : Type) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) M]
    [IsManifold (modelWithCornersEuclideanHalfSpace (n + 1)) 1 M] :
    TopCat.of (Uu n M) ⟶ TopCat.of (Work.ThomBordism.Double n M) :=
  Work.Cohomology.subtypeIncl (TopCat.of M) (Uu n M) ≫ fp n M

abbrev GP (n : ℕ) (M : Type) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) M]
    [IsManifold (modelWithCornersEuclideanHalfSpace (n + 1)) 1 M] (y : M) :
    TopCat.of (AY n M y) ⟶ TopCat.of (CY n M y) :=
  Work.Cohomology.inclInterA (TopCat.of M) (Uu n M) (({y} : Set M)ᶜ) ≫ gp n M y

theorem WP (n : ℕ) (M : Type) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) M]
    [IsManifold (modelWithCornersEuclideanHalfSpace (n + 1)) 1 M] (y : M) :
    Work.Cohomology.subtypeIncl (TopCat.of (Uu n M)) (AY n M y) ≫ FP n M
      = GP n M y ≫ Work.Cohomology.subtypeIncl (TopCat.of (Work.ThomBordism.Double n M)) (CY n M y) := by
  ext a
  rfl

abbrev FQ (n : ℕ) (M : Type) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) M]
    [IsManifold (modelWithCornersEuclideanHalfSpace (n + 1)) 1 M] :
    TopCat.of (Uu n M) ⟶ TopCat.of (Work.ThomBordism.Double n M) :=
  hN n M ≫ Work.Cohomology.subtypeIncl (TopCat.of (Work.ThomBordism.Double n M)) (Vv n M)

abbrev GQ (n : ℕ) (M : Type) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) M]
    [IsManifold (modelWithCornersEuclideanHalfSpace (n + 1)) 1 M] (y : M) :
    TopCat.of (AY n M y) ⟶ TopCat.of (CY n M y) :=
  g2 n M y ≫ Work.Cohomology.inclInterA (TopCat.of (Work.ThomBordism.Double n M)) (Vv n M) (CY n M y)

theorem WQ (n : ℕ) (M : Type) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) M]
    [IsManifold (modelWithCornersEuclideanHalfSpace (n + 1)) 1 M] (y : M) :
    Work.Cohomology.subtypeIncl (TopCat.of (Uu n M)) (AY n M y) ≫ FQ n M
      = GQ n M y ≫ Work.Cohomology.subtypeIncl (TopCat.of (Work.ThomBordism.Double n M)) (CY n M y) := by
  ext a
  rfl

theorem hPQ (n : ℕ) (M : Type) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) M]
    [IsManifold (modelWithCornersEuclideanHalfSpace (n + 1)) 1 M] :
    FP n M = FQ n M := by
  ext u
  rfl

theorem hPQg (n : ℕ) (M : Type) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) M]
    [IsManifold (modelWithCornersEuclideanHalfSpace (n + 1)) 1 M] (y : M) :
    GP n M y = GQ n M y := by
  ext a
  rfl

theorem comp_identity (n : ℕ) (M : Type) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) M]
    [IsManifold (modelWithCornersEuclideanHalfSpace (n + 1)) 1 M] (y : M) :
    (Work.Cohomology.relChainsMap (TopCat.of M) (Uu n M) ({y} : Set M)ᶜ)
      ≫ (Work.ThomBordism.DoubleFC.pairMapιN n M y)
    = (Work.Cohomology.relChainsMapOf (TopCat.of (Uu n M)) (TopCat.of (Vv n M))
        (AY n M y) (BY n M y) (hN n M) (g2 n M y) (w2 n M y))
      ≫ (Work.Cohomology.relChainsMap (TopCat.of (Work.ThomBordism.Double n M)) (Vv n M) (CY n M y)) := by
  calc
    _ = Work.Cohomology.relChainsMapOf (TopCat.of (Uu n M)) (TopCat.of (Work.ThomBordism.Double n M))
          (AY n M y) (CY n M y) (FP n M) (GP n M y) (WP n M y) := by
        exact Work.Cohomology.relChainsMapOf_comp _ _ _ _ _ _ _ _ _ _
    _ = Work.Cohomology.relChainsMapOf (TopCat.of (Uu n M)) (TopCat.of (Work.ThomBordism.Double n M))
          (AY n M y) (CY n M y) (FQ n M) (GQ n M y) (WQ n M y) := by
        exact relChainsMapOf_congr_fg _ _ (hPQ n M) (hPQg n M y) _ _
    _ = _ := by
        exact (Work.Cohomology.relChainsMapOf_comp _ _ _ _ _ _ _ _ _ _).symm

abbrev W1c (n : ℕ) (M : Type) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) M]
    [IsManifold (modelWithCornersEuclideanHalfSpace (n + 1)) 1 M] (y : M) :=
  Work.Cohomology.relChainsMap (TopCat.of M) (Uu n M) ({y} : Set M)ᶜ

abbrev W2c (n : ℕ) (M : Type) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) M]
    [IsManifold (modelWithCornersEuclideanHalfSpace (n + 1)) 1 M] (y : M) :=
  Work.Cohomology.relChainsMapOf (TopCat.of (Uu n M)) (TopCat.of (Vv n M))
    (AY n M y) (BY n M y) (hN n M) (g2 n M y) (w2 n M y)

abbrev W3c (n : ℕ) (M : Type) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) M]
    [IsManifold (modelWithCornersEuclideanHalfSpace (n + 1)) 1 M] (y : M) :=
  Work.Cohomology.relChainsMap (TopCat.of (Work.ThomBordism.Double n M)) (Vv n M) (CY n M y)

end

end SpanNData

open SpanNData

/-- **The second copy of `M` in its double preserves local generators at an interior point.**

Route: exactly as for `span_pairMap_M`, with `Work.ThomBordism.isOpenEmbedding_interiorEmbN` and
`pairMapιN`. -/
theorem span_pairMap_N (n : ℕ) (M : Type) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) M]
    [IsManifold (modelWithCornersEuclideanHalfSpace (n + 1)) 1 M]
    (y : M) (hy : y ∉ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary M)
    (v : (Work.Cohomology.relChains (TopCat.of M) ({y} : Set M)ᶜ).homology (n + 1))
    (hv : Submodule.span ℤ {v} = ⊤) :
    Submodule.span ℤ {((HomologicalComplex.homologyMap
      (Work.ThomBordism.DoubleFC.pairMapιN n M y) (n + 1)) v)} = ⊤ := by
  haveI hT2D : T2Space (Work.ThomBordism.Double n M) :=
    Work.ThomBordism.DblT2.t2Space_double (n := n) (M := M)
  have hUopen : IsOpen (Uu n M) := by
    show IsOpen (((modelWithCornersEuclideanHalfSpace (n + 1)).boundary M)ᶜ)
    exact (Work.ThomBordism.isClosed_boundary_one (n := n) (M := M)).isOpen_compl
  have hAopen : IsOpen (({y} : Set M)ᶜ) := isClosed_singleton.isOpen_compl
  have hcovM : Uu n M ∪ ({y} : Set M)ᶜ = Set.univ := by
    apply Set.eq_univ_of_forall
    intro z
    by_cases hzy : z = y
    · exact Or.inl (by
        rw [hzy]
        show y ∈ (((modelWithCornersEuclideanHalfSpace (n + 1)).boundary M)ᶜ)
        simpa using hy)
    · exact Or.inr hzy
  have hVopen : IsOpen (Vv n M) := by
    show IsOpen (Set.range (Work.ThomBordism.interiorEmbN (n := n) (M := M)))
    rw [← Set.image_univ]
    exact (Work.ThomBordism.isOpenMap_interior_doubleιN (n := n) (M := M)) Set.univ isOpen_univ
  have hCopen : IsOpen (CY n M y) := isClosed_singleton.isOpen_compl
  have hcovD : Vv n M ∪ CY n M y = Set.univ := by
    apply Set.eq_univ_of_forall
    intro z
    by_cases hz : z = Work.ThomBordism.doubleιN (n := n) (M := M) y
    · exact Or.inl (by
        rw [hz]
        show Work.ThomBordism.doubleιN (n := n) (M := M) y ∈
          Set.range (Work.ThomBordism.interiorEmbN (n := n) (M := M))
        refine ⟨⟨y, ?_⟩, rfl⟩
        show y ∈ (((modelWithCornersEuclideanHalfSpace (n + 1)).boundary M)ᶜ)
        simpa using hy)
    · exact Or.inr (by
        show z ∈ ({Work.ThomBordism.doubleιN (n := n) (M := M) y} : Set (Work.ThomBordism.Double n M))ᶜ
        simpa using hz)
  haveI hW1 : IsIso (HomologicalComplex.homologyMap (W1c n M y) (n+1)) :=
    Work.Cohomology.excision_relChainsMap_isIso (X := TopCat.of M) (U := Uu n M)
      (A := ({y} : Set M)ᶜ) hUopen hAopen hcovM (n+1)
  haveI hW2 : IsIso (HomologicalComplex.homologyMap (W2c n M y) (n+1)) :=
    Work.Cohomology.relChainsMapOf_homologyMap_isIso (AY n M y) (BY n M y) (hN n M) (g2 n M y)
      (w2 n M y) (n+1) (hf := fun k => by haveI : IsIso (hN n M) := isIso_hN n M; infer_instance)
      (hg := fun k => by haveI : IsIso (g2 n M y) := isIso_g2 n M y; infer_instance)
  haveI hW3 : IsIso (HomologicalComplex.homologyMap (W3c n M y) (n+1)) :=
    Work.Cohomology.excision_relChainsMap_isIso (X := TopCat.of (Work.ThomBordism.Double n M))
      (U := Vv n M) (A := CY n M y) hVopen hCopen hcovD (n+1)
  have hcomp' : W1c n M y ≫ (Work.ThomBordism.DoubleFC.pairMapιN n M y) = W2c n M y ≫ W3c n M y :=
    comp_identity n M y
  haveI hT : IsIso (HomologicalComplex.homologyMap (W2c n M y) (n+1)
      ≫ HomologicalComplex.homologyMap (W3c n M y) (n+1)) :=
    (((asIso (HomologicalComplex.homologyMap (W2c n M y) (n+1))).trans
      (asIso (HomologicalComplex.homologyMap (W3c n M y) (n+1))))).isIso_hom
  haveI hW23 : IsIso (HomologicalComplex.homologyMap (W2c n M y ≫ W3c n M y) (n+1)) :=
    (HomologicalComplex.homologyMap_comp (W2c n M y) (W3c n M y) (n+1)).symm ▸ hT
  haveI hBA : IsIso (HomologicalComplex.homologyMap
      (W1c n M y ≫ (Work.ThomBordism.DoubleFC.pairMapιN n M y)) (n+1)) :=
    (congrArg (fun z => HomologicalComplex.homologyMap z (n+1)) hcomp').symm ▸ hW23
  haveI hAB : IsIso (HomologicalComplex.homologyMap (W1c n M y) (n+1)
      ≫ HomologicalComplex.homologyMap (Work.ThomBordism.DoubleFC.pairMapιN n M y) (n+1)) :=
    (HomologicalComplex.homologyMap_comp (W1c n M y)
      (Work.ThomBordism.DoubleFC.pairMapιN n M y) (n+1)) ▸ hBA
  haveI hB : IsIso (HomologicalComplex.homologyMap
      (Work.ThomBordism.DoubleFC.pairMapιN n M y) (n+1)) :=
    CategoryTheory.IsIso.of_isIso_comp_left (HomologicalComplex.homologyMap (W1c n M y) (n+1))
      (HomologicalComplex.homologyMap (Work.ThomBordism.DoubleFC.pairMapιN n M y) (n+1))
  have hsurj : Function.Surjective (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
      (Work.ThomBordism.DoubleFC.pairMapιN n M y) (n+1))) :=
    (ModuleCat.epi_iff_surjective _).mp inferInstance
  have hmap : Submodule.map (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
        (Work.ThomBordism.DoubleFC.pairMapιN n M y) (n+1)))
        (Submodule.span ℤ {v})
      = Submodule.span ℤ {((ModuleCat.Hom.hom (HomologicalComplex.homologyMap
        (Work.ThomBordism.DoubleFC.pairMapιN n M y) (n+1))) v)} := by
    rw [Submodule.map_span, Set.image_singleton]
  calc Submodule.span ℤ {((HomologicalComplex.homologyMap
          (Work.ThomBordism.DoubleFC.pairMapιN n M y) (n+1)) v)}
      = Submodule.map (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
          (Work.ThomBordism.DoubleFC.pairMapιN n M y) (n+1))) (Submodule.span ℤ {v}) := hmap.symm
    _ = Submodule.map (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
          (Work.ThomBordism.DoubleFC.pairMapιN n M y) (n+1))) ⊤ := by rw [hv]
    _ = ⊤ := by rw [Submodule.map_top, LinearMap.range_eq_top.mpr hsurj]

end Work.ThomBordism.doubleFC
