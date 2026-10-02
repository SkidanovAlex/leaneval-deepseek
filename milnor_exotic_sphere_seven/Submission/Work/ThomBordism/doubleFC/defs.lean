import Mathlib
import Submission.Work.ThomBordism.doubleDefs
import Submission.Work.ThomBordism.doubleCharted
import Submission.Work.ThomBordism.doubleChartedT2
import Submission.Work.ThomBordism.localClassAt
import Submission.Work.ThomBordism.Interface
import Submission.Work.Cohomology.pd_plumbing
import Submission.Work.Cohomology.capRelAux

import Submission.Work.Orient.Defs
import Submission.Work.Orient.Boundary.localHomology_corner

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option backward.isDefEq.respectTransparency false

/-!
# The double of a manifold with boundary: the pair maps at an interior point

For a `C¹` manifold `M` with boundary modelled on the half-space `EuclideanHalfSpace (n+1)`, an
interior point `y : M` and the corresponding point `doubleιM y` of the double `D = Double n M`,
this file defines the two maps of pairs

* `pairMapιM n M y : C_*(M, M∖{y}) ⟶ C_*(D, D∖{ιM y})` — induced by the first inclusion `ιM`,
* `pairMapιN n M y : C_*(M, M∖{y}) ⟶ C_*(D, D∖{ιN y})` — induced by the second inclusion `ιN`,

i.e. the maps on the *local* groups of an interior point induced by the two copies.  These are the
maps through which the local class of the fundamental class of the double is computed
(`Work.ThomBordism.doubleFundamentalClass`).

The point of the definitions is that at an interior point of `M` the inclusion of either copy is an
*open embedding*, so that the induced map on local homology is an isomorphism: this is
`Work.ThomBordism.DoubleFC.pairMapιM_isIso` (and its `ιN`-analogue) in
`Submission/Work/ThomBordism/doubleFC/pairMapIso.lean`.
-/


open CategoryTheory AlgebraicTopology CategoryTheory.Limits

namespace Work.ThomBordism.DoubleFC

noncomputable section

variable {n : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (n + 1)) M]

/-- **The pair map `(M, M∖{y}) → (D, D∖{ιM y})` of the first copy.** -/
noncomputable def pairMapιM (n : ℕ) (M : Type) [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) M] (y : M) :=
  Work.Cohomology.relChainsMapOf (TopCat.of M) (TopCat.of (Double n M))
    ({y} : Set M)ᶜ ({doubleιM (n := n) (M := M) y} : Set (Double n M))ᶜ
    (TopCat.ofHom ⟨doubleιM (n := n) (M := M), continuous_doubleιM (n := n) (M := M)⟩)
    (TopCat.ofHom
      ⟨fun m => ⟨doubleιM (n := n) (M := M) m.1,
          by
            intro h
            exact m.2 (doubleιM_injective (n := n) (M := M) h)⟩,
        Continuous.subtype_mk
          ((continuous_doubleιM (n := n) (M := M)).comp continuous_subtype_val) _⟩)
    (by ext m; rfl)

/-- **The pair map `(M, M∖{y}) → (D, D∖{ιN y})` of the second copy.** -/
noncomputable def pairMapιN (n : ℕ) (M : Type) [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) M] (y : M) :=
  Work.Cohomology.relChainsMapOf (TopCat.of M) (TopCat.of (Double n M))
    ({y} : Set M)ᶜ ({doubleιN (n := n) (M := M) y} : Set (Double n M))ᶜ
    (TopCat.ofHom ⟨doubleιN (n := n) (M := M), continuous_doubleιN (n := n) (M := M)⟩)
    (TopCat.ofHom
      ⟨fun m => ⟨doubleιN (n := n) (M := M) m.1,
          by
            intro h
            exact m.2 (doubleιN_injective (n := n) (M := M) h)⟩,
        Continuous.subtype_mk
          ((continuous_doubleιN (n := n) (M := M)).comp continuous_subtype_val) _⟩)
    (by ext m; rfl)


/-- The first inclusion `M → Double n M`, as a morphism of `TopCat`. -/
noncomputable def iMHom (n : ℕ) (M : Type) [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) M] : TopCat.of M ⟶ TopCat.of (Double n M) :=
  TopCat.ofHom ⟨doubleιM (n := n) (M := M), continuous_doubleιM (n := n) (M := M)⟩

/-- The second inclusion `M → Double n M`, as a morphism of `TopCat`. -/
noncomputable def iNHom (n : ℕ) (M : Type) [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) M] : TopCat.of M ⟶ TopCat.of (Double n M) :=
  TopCat.ofHom ⟨doubleιN (n := n) (M := M), continuous_doubleιN (n := n) (M := M)⟩

end

/-- The defining property of `pairMapιM`. -/
theorem pairMapιM_π (n : ℕ) (M : Type) [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) M] (y : M) :
    CategoryTheory.Limits.cokernel.π (Work.Cohomology.inclChains (TopCat.of M) ({y} : Set M)ᶜ)
        ≫ pairMapιM n M y
      = Work.Cohomology.chainMap ℤ (TopCat.of M) (TopCat.of (Double n M)) (iMHom n M)
        ≫ CategoryTheory.Limits.cokernel.π (Work.Cohomology.inclChains (TopCat.of (Double n M))
            ({doubleιM (n := n) (M := M) y} : Set (Double n M))ᶜ) := by
  rw [pairMapιM]
  exact Work.Cohomology.capRel_cokernel_π_relChainsMapOf _ _ _ _ _

/-- The defining property of `pairMapιN`. -/
theorem pairMapιN_π (n : ℕ) (M : Type) [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) M] (y : M) :
    CategoryTheory.Limits.cokernel.π (Work.Cohomology.inclChains (TopCat.of M) ({y} : Set M)ᶜ)
        ≫ pairMapιN n M y
      = Work.Cohomology.chainMap ℤ (TopCat.of M) (TopCat.of (Double n M)) (iNHom n M)
        ≫ CategoryTheory.Limits.cokernel.π (Work.Cohomology.inclChains (TopCat.of (Double n M))
            ({doubleιN (n := n) (M := M) y} : Set (Double n M))ᶜ) := by
  rw [pairMapιN]
  exact Work.Cohomology.capRel_cokernel_π_relChainsMapOf _ _ _ _ _


/-- The defining property of `pairMapιM`, at the element level. -/
theorem pairMapιM_apply (n : ℕ) (M : Type) [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) M] (y : M) (k : ℕ)
    (v : (Work.Cohomology.singularChains ℤ (TopCat.of M)).X k) :
    (((CategoryTheory.Limits.cokernel.π (Work.Cohomology.inclChains (TopCat.of M)
        (({y} : Set M)ᶜ))).f k ≫ (pairMapιM n M y).f k) v)
      = ((((Work.Cohomology.chainMap ℤ (TopCat.of M) (TopCat.of (Double n M)) (iMHom n M)).f k ≫
          (CategoryTheory.Limits.cokernel.π (Work.Cohomology.inclChains
            (TopCat.of (Double n M))
            (({doubleιM (n := n) (M := M) y} : Set (Double n M))ᶜ))).f k) v)) := by
  rw [← HomologicalComplex.comp_f, ← HomologicalComplex.comp_f, pairMapιM_π]
  rfl

/-- The defining property of `pairMapιN`, at the element level. -/
theorem pairMapιN_apply (n : ℕ) (M : Type) [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) M] (y : M) (k : ℕ)
    (v : (Work.Cohomology.singularChains ℤ (TopCat.of M)).X k) :
    (((CategoryTheory.Limits.cokernel.π (Work.Cohomology.inclChains (TopCat.of M)
        (({y} : Set M)ᶜ))).f k ≫ (pairMapιN n M y).f k) v)
      = ((((Work.Cohomology.chainMap ℤ (TopCat.of M) (TopCat.of (Double n M)) (iNHom n M)).f k ≫
          (CategoryTheory.Limits.cokernel.π (Work.Cohomology.inclChains
            (TopCat.of (Double n M))
            (({doubleιN (n := n) (M := M) y} : Set (Double n M))ᶜ))).f k) v)) := by
  rw [← HomologicalComplex.comp_f, ← HomologicalComplex.comp_f, pairMapιN_π]
  rfl

end Work.ThomBordism.DoubleFC
