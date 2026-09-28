import Mathlib
import Submission.Work.Serre.C1Cyl
import Submission.Work.StemsB.RelChainsR
import Submission.Work.Serre.csrDefs
import Submission.Work.RatHurewicz.AttachCells
import Submission.Work.StemsB.Fibrations
import Submission.Work.Cohomology.pd_triple
import Submission.Work.Serre.DiscPair.lesSplitPair
import Submission.Work.Serre.DiscPair.cylPairDefs
import Submission.Work.Serre.DiscPair.relPairFiveRat
import Submission.Work.Serre.DiscPair.subPairMapQuasiIso

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The homology of the cofibre of a map of pairs, for the mapping cylinder of `q`

The target statement `Work.Serre.DiscPair.cylPairCofibre`.
-/

set_option linter.style.haveILetI false
set_option maxHeartbeats 1600000

open CategoryTheory CategoryTheory.Limits
open scoped Topology unitInterval

namespace Work.Serre.DiscPair

noncomputable section

variable {D : ℕ} {Γ : Type} [TopologicalSpace Γ] {ι : Type}
  {f : ι → C(Work.RatHurewicz.cellSphere (D-2), Γ)} {X : Type} [TopologicalSpace X]

/-- The composite `C_*(U) → C_*(A₂) → C_*(C)` is `C_*(U) → C_*(C)`. -/
theorem cylPairChainInclU_comp (q : C(X, Work.RatHurewicz.attachCells (D-2) Γ ι f)) :
    cylPairChainInclU (D := D) (Γ := Γ) (ι := ι) (f := f) q ≫
        Work.StemsB.relChainsRIncl ℚ (TopCat.of (cyl q))
          (cylPairA₂ (D := D) (Γ := Γ) (ι := ι) (f := f) q)
      = Work.StemsB.relChainsRIncl ℚ (TopCat.of (cyl q))
          (cylPairU (D := D) (Γ := Γ) (ι := ι) (f := f) q) := by
  simp only [cylPairChainInclU, Work.StemsB.relChainsRIncl, Work.Cohomology.chainMap,
    ← Functor.map_comp]
  have h : TopCat.ofHom (cylPairUincl (D := D) (Γ := Γ) (ι := ι) (f := f) q) ≫
        Work.Cohomology.subtypeIncl (TopCat.of (cyl q))
          (cylPairA₂ (D := D) (Γ := Γ) (ι := ι) (f := f) q)
      = Work.Cohomology.subtypeIncl (TopCat.of (cyl q))
          (cylPairU (D := D) (Γ := Γ) (ι := ι) (f := f) q) := by
    simp only [Work.Cohomology.subtypeIncl, ← TopCat.ofHom_comp]
    exact congrArg TopCat.ofHom (ContinuousMap.ext (fun x => rfl))
  rw [h]

/-- The first map of the cofibre short complex: `C_*(A₂,U) ⟶ C_*(C,U)`. -/
abbrev cylPairFirst (q : C(X, Work.RatHurewicz.attachCells (D-2) Γ ι f)) :
    cokernel (cylPairChainInclU (D := D) (Γ := Γ) (ι := ι) (f := f) q) ⟶
      Work.StemsB.relChainsR ℚ (TopCat.of (cyl q))
        (cylPairU (D := D) (Γ := Γ) (ι := ι) (f := f) q) :=
  cokernel.map (cylPairChainInclU (D := D) (Γ := Γ) (ι := ι) (f := f) q)
    (Work.StemsB.relChainsRIncl ℚ (TopCat.of (cyl q))
      (cylPairU (D := D) (Γ := Γ) (ι := ι) (f := f) q))
    (𝟙 _)
    (Work.StemsB.relChainsRIncl ℚ (TopCat.of (cyl q))
      (cylPairA₂ (D := D) (Γ := Γ) (ι := ι) (f := f) q))
    (by rw [Category.id_comp]; exact cylPairChainInclU_comp (D := D) (Γ := Γ) (ι := ι) (f := f) q)

/-- The second map of the cofibre short complex: `C_*(C,U) ⟶ C_*(C,A₂)`. -/
abbrev cylPairSecond (q : C(X, Work.RatHurewicz.attachCells (D-2) Γ ι f)) :
    Work.StemsB.relChainsR ℚ (TopCat.of (cyl q))
        (cylPairU (D := D) (Γ := Γ) (ι := ι) (f := f) q) ⟶
      Work.StemsB.relChainsR ℚ (TopCat.of (cyl q))
        (cylPairA₂ (D := D) (Γ := Γ) (ι := ι) (f := f) q) :=
  cokernel.desc (Work.StemsB.relChainsRIncl ℚ (TopCat.of (cyl q))
      (cylPairU (D := D) (Γ := Γ) (ι := ι) (f := f) q))
    (cokernel.π (Work.StemsB.relChainsRIncl ℚ (TopCat.of (cyl q))
      (cylPairA₂ (D := D) (Γ := Γ) (ι := ι) (f := f) q)))
    (by
      rw [← cylPairChainInclU_comp (D := D) (Γ := Γ) (ι := ι) (f := f) q, Category.assoc,
        cokernel.condition, comp_zero])

/-- **The cofibre short complex of the triple `U ⊆ A₂ ⊆ C`**:
`0 → C_*(A₂,U;ℚ) → C_*(C,U;ℚ) → C_*(C,A₂;ℚ) → 0`. -/
def cylPairShort (q : C(X, Work.RatHurewicz.attachCells (D-2) Γ ι f)) :
    ShortComplex (ChainComplex (ModuleCat ℚ) ℕ) :=
  ShortComplex.mk (cylPairFirst (D := D) (Γ := Γ) (ι := ι) (f := f) q)
    (cylPairSecond (D := D) (Γ := Γ) (ι := ι) (f := f) q)
    (by
      simp only [cylPairFirst, cylPairSecond]
      apply (cancel_epi (cokernel.π (cylPairChainInclU (D := D) (Γ := Γ) (ι := ι) (f := f) q))).mp
      rw [← Category.assoc, cokernel.map, cokernel.π_desc, Category.assoc, cokernel.π_desc,
        cokernel.condition, comp_zero])

/-- The cofibre short complex is short exact. -/
theorem cylPairShort_shortExact (q : C(X, Work.RatHurewicz.attachCells (D-2) Γ ι f)) :
    (cylPairShort (D := D) (Γ := Γ) (ι := ι) (f := f) q).ShortExact := by
  haveI : Mono (Work.StemsB.relChainsRIncl ℚ (TopCat.of (cyl q))
      (cylPairA₂ (D := D) (Γ := Γ) (ι := ι) (f := f) q)) :=
    Work.StemsB.mono_chainMap_subtypeIncl_ring ℚ (TopCat.of (cyl q))
      (cylPairA₂ (D := D) (Γ := Γ) (ι := ι) (f := f) q)
  exact Work.Cohomology.shortExact_cokernel_map
    (cylPairChainInclU (D := D) (Γ := Γ) (ι := ι) (f := f) q)
    (Work.StemsB.relChainsRIncl ℚ (TopCat.of (cyl q))
      (cylPairA₂ (D := D) (Γ := Γ) (ι := ι) (f := f) q))
    (Work.StemsB.relChainsRIncl ℚ (TopCat.of (cyl q))
      (cylPairU (D := D) (Γ := Γ) (ι := ι) (f := f) q))
    (cylPairChainInclU_comp (D := D) (Γ := Γ) (ι := ι) (f := f) q)

/-- The connecting map `H_{n+1}(C,A₂;ℚ) ⟶ H_n(A₂,U;ℚ)` of the cofibre sequence. -/
def cylPairδ (q : C(X, Work.RatHurewicz.attachCells (D-2) Γ ι f)) (n : ℕ) :
    (Work.StemsB.relChainsR ℚ (TopCat.of (cyl q))
      (cylPairA₂ (D := D) (Γ := Γ) (ι := ι) (f := f) q)).homology (n + 1) ⟶
      (cokernel (cylPairChainInclU (D := D) (Γ := Γ) (ι := ι) (f := f) q)).homology n :=
  (cylPairShort_shortExact (D := D) (Γ := Γ) (ι := ι) (f := f) q).δ (n + 1) n
    (by simp [ComplexShape.down])

/-- Exactness of the cofibre sequence at the middle terms. -/
theorem cylPairShort_exact_data (q : C(X, Work.RatHurewicz.attachCells (D-2) Γ ι f)) (k : ℕ) :
    LinearMap.range (HomologicalComplex.homologyMap
        (cylPairShort (D := D) (Γ := Γ) (ι := ι) (f := f) q).f (k + 1)).hom
      = LinearMap.ker (HomologicalComplex.homologyMap
        (cylPairShort (D := D) (Γ := Γ) (ι := ι) (f := f) q).g (k + 1)).hom ∧
    LinearMap.range (HomologicalComplex.homologyMap
        (cylPairShort (D := D) (Γ := Γ) (ι := ι) (f := f) q).g (k + 1)).hom
      = LinearMap.ker (cylPairδ (D := D) (Γ := Γ) (ι := ι) (f := f) q k).hom ∧
    LinearMap.range (cylPairδ (D := D) (Γ := Γ) (ι := ι) (f := f) q k).hom
      = LinearMap.ker (HomologicalComplex.homologyMap
        (cylPairShort (D := D) (Γ := Γ) (ι := ι) (f := f) q).f k).hom := by
  have hS := cylPairShort_shortExact (D := D) (Γ := Γ) (ι := ι) (f := f) q
  refine ⟨?_, ?_, ?_⟩
  · exact (hS.homology_exact₂ (k + 1)).moduleCat_range_eq_ker
  · exact (hS.homology_exact₃ (k + 1) k (by simp [ComplexShape.down])).moduleCat_range_eq_ker
  · exact (hS.homology_exact₁ (k + 1) k (by simp [ComplexShape.down])).moduleCat_range_eq_ker

/-- The pushforward of a relative chain map to the cokernels is determined by the map itself. -/
theorem relChainsRPairMap_eq_of_comp_π {X' Y' : Type} [TopologicalSpace X'] [TopologicalSpace Y']
    {A : Set X'} {B : Set Y'}
    {f f' : Work.StemsB.relChainsR ℚ (TopCat.of X') A ⟶
      Work.StemsB.relChainsR ℚ (TopCat.of Y') B}
    (h : cokernel.π (Work.StemsB.relChainsRIncl ℚ (TopCat.of X') A) ≫ f
      = cokernel.π (Work.StemsB.relChainsRIncl ℚ (TopCat.of X') A) ≫ f') : f = f' :=
  (cancel_epi (cokernel.π (Work.StemsB.relChainsRIncl ℚ (TopCat.of X') A))).mp h

/-- **The chain level commuting square of the assembly.**  The composite
`C_*(X,A) → coker(C_*(U) → C_*(A₂)) → C_*(C,U) → C_*(Z,Y')` is the map induced by `q`. -/
theorem subPairMap_comp_short_comp (q : C(X, Work.RatHurewicz.attachCells (D-2) Γ ι f)) :
    subPairMap (D := D) (Γ := Γ) (ι := ι) (f := f) q ≫
        (cylPairShort (D := D) (Γ := Γ) (ι := ι) (f := f) q).f ≫
        (Work.Serre.relChainsRPairMap
          (cylPairU (D := D) (Γ := Γ) (ι := ι) (f := f) q)
          (cylPairS (D := D) (Γ := Γ) (ι := ι) (f := f))
          (cylRetract q) (mapsTo_cylRetract_cylPairU (D := D) (Γ := Γ) (ι := ι) (f := f) q))
      = Work.Serre.relChainsRPairMap
          (cylPairA (D := D) (Γ := Γ) (ι := ι) (f := f) (X := X) q)
          (cylPairS (D := D) (Γ := Γ) (ι := ι) (f := f))
          q (mapsTo_q_cylPairA (D := D) (Γ := Γ) (ι := ι) (f := f) (X := X) q) := by
  apply relChainsRPairMap_eq_of_comp_π
  have h1 : cokernel.π (Work.StemsB.relChainsRIncl ℚ (TopCat.of X)
        (cylPairA (D := D) (Γ := Γ) (ι := ι) (f := f) (X := X) q)) ≫
        subPairMap (D := D) (Γ := Γ) (ι := ι) (f := f) q
      = Work.Cohomology.chainMap ℚ (TopCat.of X)
          (TopCat.of ↥(cylPairA₂ (D := D) (Γ := Γ) (ι := ι) (f := f) q))
          (TopCat.ofHom (cylInclA₂ (D := D) (Γ := Γ) (ι := ι) (f := f) q)) ≫
        cokernel.π (cylPairChainInclU (D := D) (Γ := Γ) (ι := ι) (f := f) q) := by
    rw [subPairMap]
    exact Work.Cohomology.cokernel_π_map _ _ _ _ _
  have h2 : cokernel.π (cylPairChainInclU (D := D) (Γ := Γ) (ι := ι) (f := f) q) ≫
        (cylPairShort (D := D) (Γ := Γ) (ι := ι) (f := f) q).f
      = Work.StemsB.relChainsRIncl ℚ (TopCat.of (cyl q))
          (cylPairA₂ (D := D) (Γ := Γ) (ι := ι) (f := f) q) ≫
        cokernel.π (Work.StemsB.relChainsRIncl ℚ (TopCat.of (cyl q))
          (cylPairU (D := D) (Γ := Γ) (ι := ι) (f := f) q)) := by
    show cokernel.π (cylPairChainInclU (D := D) (Γ := Γ) (ι := ι) (f := f) q) ≫
        cylPairFirst (D := D) (Γ := Γ) (ι := ι) (f := f) q = _
    exact Work.Cohomology.cokernel_π_map _ _ _ _ _
  have h3m : TopCat.ofHom (cylInclA₂ (D := D) (Γ := Γ) (ι := ι) (f := f) q) ≫
        Work.Cohomology.subtypeIncl (TopCat.of (cyl q))
          (cylPairA₂ (D := D) (Γ := Γ) (ι := ι) (f := f) q)
      = TopCat.ofHom (cylIncl q) := by
    show TopCat.ofHom ((⟨Subtype.val, continuous_subtype_val⟩ :
      C(↥(cylPairA₂ (D := D) (Γ := Γ) (ι := ι) (f := f) q), cyl q)).comp
        (cylInclA₂ (D := D) (Γ := Γ) (ι := ι) (f := f) q)) = TopCat.ofHom (cylIncl q)
    rfl
  have h3 : Work.Cohomology.chainMap ℚ (TopCat.of X)
        (TopCat.of ↥(cylPairA₂ (D := D) (Γ := Γ) (ι := ι) (f := f) q))
        (TopCat.ofHom (cylInclA₂ (D := D) (Γ := Γ) (ι := ι) (f := f) q)) ≫
        Work.StemsB.relChainsRIncl ℚ (TopCat.of (cyl q))
          (cylPairA₂ (D := D) (Γ := Γ) (ι := ι) (f := f) q)
      = Work.Cohomology.chainMap ℚ (TopCat.of X) (TopCat.of (cyl q))
          (TopCat.ofHom (cylIncl q)) := by
    simp only [Work.StemsB.relChainsRIncl, Work.Cohomology.chainMap]
    rw [← Functor.map_comp]
    exact congrArg _ h3m
  have h4 : cokernel.π (Work.StemsB.relChainsRIncl ℚ (TopCat.of (cyl q))
        (cylPairU (D := D) (Γ := Γ) (ι := ι) (f := f) q)) ≫
        (Work.Serre.relChainsRPairMap
          (cylPairU (D := D) (Γ := Γ) (ι := ι) (f := f) q)
          (cylPairS (D := D) (Γ := Γ) (ι := ι) (f := f))
          (cylRetract q) (mapsTo_cylRetract_cylPairU (D := D) (Γ := Γ) (ι := ι) (f := f) q))
      = Work.Cohomology.chainMap ℚ (TopCat.of (cyl q))
          (TopCat.of (Work.RatHurewicz.attachCells (D-2) Γ ι f))
          (TopCat.ofHom (cylRetract q)) ≫
        cokernel.π (Work.StemsB.relChainsRIncl ℚ
          (TopCat.of (Work.RatHurewicz.attachCells (D-2) Γ ι f))
          (cylPairS (D := D) (Γ := Γ) (ι := ι) (f := f))) := by
    rw [Work.Serre.relChainsRPairMap, Work.Serre.csrRelMapOf]
    exact Work.Cohomology.cokernel_π_map _ _ _ _ _
  have h5 : cokernel.π (Work.StemsB.relChainsRIncl ℚ (TopCat.of X)
        (cylPairA (D := D) (Γ := Γ) (ι := ι) (f := f) (X := X) q)) ≫
        (Work.Serre.relChainsRPairMap
          (cylPairA (D := D) (Γ := Γ) (ι := ι) (f := f) (X := X) q)
          (cylPairS (D := D) (Γ := Γ) (ι := ι) (f := f))
          q (mapsTo_q_cylPairA (D := D) (Γ := Γ) (ι := ι) (f := f) (X := X) q))
      = Work.Cohomology.chainMap ℚ (TopCat.of X)
          (TopCat.of (Work.RatHurewicz.attachCells (D-2) Γ ι f))
          (TopCat.ofHom q) ≫
        cokernel.π (Work.StemsB.relChainsRIncl ℚ
          (TopCat.of (Work.RatHurewicz.attachCells (D-2) Γ ι f))
          (cylPairS (D := D) (Γ := Γ) (ι := ι) (f := f))) := by
    rw [Work.Serre.relChainsRPairMap, Work.Serre.csrRelMapOf]
    exact Work.Cohomology.cokernel_π_map _ _ _ _ _
  have h7 : Work.Cohomology.chainMap ℚ (TopCat.of X) (TopCat.of (cyl q))
        (TopCat.ofHom (cylIncl q)) ≫
        Work.Cohomology.chainMap ℚ (TopCat.of (cyl q))
          (TopCat.of (Work.RatHurewicz.attachCells (D-2) Γ ι f))
          (TopCat.ofHom (cylRetract q))
      = Work.Cohomology.chainMap ℚ (TopCat.of X)
          (TopCat.of (Work.RatHurewicz.attachCells (D-2) Γ ι f))
          (TopCat.ofHom q) := by
    simp only [Work.Cohomology.chainMap, ← Functor.map_comp, ← TopCat.ofHom_comp,
      Work.Serre.cylRetract_cylIncl q]
  calc (cokernel.π (Work.StemsB.relChainsRIncl ℚ (TopCat.of X) (cylPairA (D := D) (Γ := Γ) (ι := ι) (f := f) (X := X) q))) ≫ ((subPairMap (D := D) (Γ := Γ) (ι := ι) (f := f) q) ≫ (((cylPairShort (D := D) (Γ := Γ) (ι := ι) (f := f) q).f) ≫ (Work.Serre.relChainsRPairMap (cylPairU (D := D) (Γ := Γ) (ι := ι) (f := f) q) (cylPairS (D := D) (Γ := Γ) (ι := ι) (f := f)) (cylRetract q) (mapsTo_cylRetract_cylPairU (D := D) (Γ := Γ) (ι := ι) (f := f) q))))
      = ((cokernel.π (Work.StemsB.relChainsRIncl ℚ (TopCat.of X) (cylPairA (D := D) (Γ := Γ) (ι := ι) (f := f) (X := X) q))) ≫ (subPairMap (D := D) (Γ := Γ) (ι := ι) (f := f) q)) ≫ (((cylPairShort (D := D) (Γ := Γ) (ι := ι) (f := f) q).f) ≫ (Work.Serre.relChainsRPairMap (cylPairU (D := D) (Γ := Γ) (ι := ι) (f := f) q) (cylPairS (D := D) (Γ := Γ) (ι := ι) (f := f)) (cylRetract q) (mapsTo_cylRetract_cylPairU (D := D) (Γ := Γ) (ι := ι) (f := f) q))) := (Category.assoc _ _ _).symm
    _ = ((Work.Cohomology.chainMap ℚ (TopCat.of X) (TopCat.of ↥(cylPairA₂ (D := D) (Γ := Γ) (ι := ι) (f := f) q)) (TopCat.ofHom (cylInclA₂ (D := D) (Γ := Γ) (ι := ι) (f := f) q))) ≫ (cokernel.π (cylPairChainInclU (D := D) (Γ := Γ) (ι := ι) (f := f) q))) ≫ (((cylPairShort (D := D) (Γ := Γ) (ι := ι) (f := f) q).f) ≫ (Work.Serre.relChainsRPairMap (cylPairU (D := D) (Γ := Γ) (ι := ι) (f := f) q) (cylPairS (D := D) (Γ := Γ) (ι := ι) (f := f)) (cylRetract q) (mapsTo_cylRetract_cylPairU (D := D) (Γ := Γ) (ι := ι) (f := f) q))) := congrArg (fun z => z ≫ (((cylPairShort (D := D) (Γ := Γ) (ι := ι) (f := f) q).f) ≫ (Work.Serre.relChainsRPairMap (cylPairU (D := D) (Γ := Γ) (ι := ι) (f := f) q) (cylPairS (D := D) (Γ := Γ) (ι := ι) (f := f)) (cylRetract q) (mapsTo_cylRetract_cylPairU (D := D) (Γ := Γ) (ι := ι) (f := f) q)))) h1
    _ = (Work.Cohomology.chainMap ℚ (TopCat.of X) (TopCat.of ↥(cylPairA₂ (D := D) (Γ := Γ) (ι := ι) (f := f) q)) (TopCat.ofHom (cylInclA₂ (D := D) (Γ := Γ) (ι := ι) (f := f) q))) ≫ ((cokernel.π (cylPairChainInclU (D := D) (Γ := Γ) (ι := ι) (f := f) q)) ≫ (((cylPairShort (D := D) (Γ := Γ) (ι := ι) (f := f) q).f) ≫ (Work.Serre.relChainsRPairMap (cylPairU (D := D) (Γ := Γ) (ι := ι) (f := f) q) (cylPairS (D := D) (Γ := Γ) (ι := ι) (f := f)) (cylRetract q) (mapsTo_cylRetract_cylPairU (D := D) (Γ := Γ) (ι := ι) (f := f) q)))) := Category.assoc _ _ _
    _ = (Work.Cohomology.chainMap ℚ (TopCat.of X) (TopCat.of ↥(cylPairA₂ (D := D) (Γ := Γ) (ι := ι) (f := f) q)) (TopCat.ofHom (cylInclA₂ (D := D) (Γ := Γ) (ι := ι) (f := f) q))) ≫ (((cokernel.π (cylPairChainInclU (D := D) (Γ := Γ) (ι := ι) (f := f) q)) ≫ ((cylPairShort (D := D) (Γ := Γ) (ι := ι) (f := f) q).f)) ≫ (Work.Serre.relChainsRPairMap (cylPairU (D := D) (Γ := Γ) (ι := ι) (f := f) q) (cylPairS (D := D) (Γ := Γ) (ι := ι) (f := f)) (cylRetract q) (mapsTo_cylRetract_cylPairU (D := D) (Γ := Γ) (ι := ι) (f := f) q))) :=
        congrArg (fun z => (Work.Cohomology.chainMap ℚ (TopCat.of X) (TopCat.of ↥(cylPairA₂ (D := D) (Γ := Γ) (ι := ι) (f := f) q)) (TopCat.ofHom (cylInclA₂ (D := D) (Γ := Γ) (ι := ι) (f := f) q))) ≫ z) (Category.assoc _ _ _).symm
    _ = (Work.Cohomology.chainMap ℚ (TopCat.of X) (TopCat.of ↥(cylPairA₂ (D := D) (Γ := Γ) (ι := ι) (f := f) q)) (TopCat.ofHom (cylInclA₂ (D := D) (Γ := Γ) (ι := ι) (f := f) q))) ≫ (((Work.StemsB.relChainsRIncl ℚ (TopCat.of (cyl q)) (cylPairA₂ (D := D) (Γ := Γ) (ι := ι) (f := f) q)) ≫ (cokernel.π (Work.StemsB.relChainsRIncl ℚ (TopCat.of (cyl q)) (cylPairU (D := D) (Γ := Γ) (ι := ι) (f := f) q)))) ≫ (Work.Serre.relChainsRPairMap (cylPairU (D := D) (Γ := Γ) (ι := ι) (f := f) q) (cylPairS (D := D) (Γ := Γ) (ι := ι) (f := f)) (cylRetract q) (mapsTo_cylRetract_cylPairU (D := D) (Γ := Γ) (ι := ι) (f := f) q))) := congrArg (fun z => (Work.Cohomology.chainMap ℚ (TopCat.of X) (TopCat.of ↥(cylPairA₂ (D := D) (Γ := Γ) (ι := ι) (f := f) q)) (TopCat.ofHom (cylInclA₂ (D := D) (Γ := Γ) (ι := ι) (f := f) q))) ≫ (z ≫ (Work.Serre.relChainsRPairMap (cylPairU (D := D) (Γ := Γ) (ι := ι) (f := f) q) (cylPairS (D := D) (Γ := Γ) (ι := ι) (f := f)) (cylRetract q) (mapsTo_cylRetract_cylPairU (D := D) (Γ := Γ) (ι := ι) (f := f) q)))) h2
    _ = ((Work.Cohomology.chainMap ℚ (TopCat.of X) (TopCat.of ↥(cylPairA₂ (D := D) (Γ := Γ) (ι := ι) (f := f) q)) (TopCat.ofHom (cylInclA₂ (D := D) (Γ := Γ) (ι := ι) (f := f) q))) ≫ (Work.StemsB.relChainsRIncl ℚ (TopCat.of (cyl q)) (cylPairA₂ (D := D) (Γ := Γ) (ι := ι) (f := f) q))) ≫ ((cokernel.π (Work.StemsB.relChainsRIncl ℚ (TopCat.of (cyl q)) (cylPairU (D := D) (Γ := Γ) (ι := ι) (f := f) q))) ≫ (Work.Serre.relChainsRPairMap (cylPairU (D := D) (Γ := Γ) (ι := ι) (f := f) q) (cylPairS (D := D) (Γ := Γ) (ι := ι) (f := f)) (cylRetract q) (mapsTo_cylRetract_cylPairU (D := D) (Γ := Γ) (ι := ι) (f := f) q))) :=
        (congrArg (fun z => (Work.Cohomology.chainMap ℚ (TopCat.of X) (TopCat.of ↥(cylPairA₂ (D := D) (Γ := Γ) (ι := ι) (f := f) q)) (TopCat.ofHom (cylInclA₂ (D := D) (Γ := Γ) (ι := ι) (f := f) q))) ≫ z) (Category.assoc _ _ _)).trans
          (Category.assoc _ _ _).symm
    _ = (Work.Cohomology.chainMap ℚ (TopCat.of X) (TopCat.of (cyl q)) (TopCat.ofHom (cylIncl q))) ≫ ((cokernel.π (Work.StemsB.relChainsRIncl ℚ (TopCat.of (cyl q)) (cylPairU (D := D) (Γ := Γ) (ι := ι) (f := f) q))) ≫ (Work.Serre.relChainsRPairMap (cylPairU (D := D) (Γ := Γ) (ι := ι) (f := f) q) (cylPairS (D := D) (Γ := Γ) (ι := ι) (f := f)) (cylRetract q) (mapsTo_cylRetract_cylPairU (D := D) (Γ := Γ) (ι := ι) (f := f) q))) := congrArg (fun z => z ≫ ((cokernel.π (Work.StemsB.relChainsRIncl ℚ (TopCat.of (cyl q)) (cylPairU (D := D) (Γ := Γ) (ι := ι) (f := f) q))) ≫ (Work.Serre.relChainsRPairMap (cylPairU (D := D) (Γ := Γ) (ι := ι) (f := f) q) (cylPairS (D := D) (Γ := Γ) (ι := ι) (f := f)) (cylRetract q) (mapsTo_cylRetract_cylPairU (D := D) (Γ := Γ) (ι := ι) (f := f) q)))) h3
    _ = (Work.Cohomology.chainMap ℚ (TopCat.of X) (TopCat.of (cyl q)) (TopCat.ofHom (cylIncl q))) ≫ ((Work.Cohomology.chainMap ℚ (TopCat.of (cyl q)) (TopCat.of (Work.RatHurewicz.attachCells (D-2) Γ ι f)) (TopCat.ofHom (cylRetract q))) ≫ (cokernel.π (Work.StemsB.relChainsRIncl ℚ (TopCat.of (Work.RatHurewicz.attachCells (D-2) Γ ι f)) (cylPairS (D := D) (Γ := Γ) (ι := ι) (f := f))))) := congrArg (fun z => (Work.Cohomology.chainMap ℚ (TopCat.of X) (TopCat.of (cyl q)) (TopCat.ofHom (cylIncl q))) ≫ z) h4
    _ = ((Work.Cohomology.chainMap ℚ (TopCat.of X) (TopCat.of (cyl q)) (TopCat.ofHom (cylIncl q))) ≫ (Work.Cohomology.chainMap ℚ (TopCat.of (cyl q)) (TopCat.of (Work.RatHurewicz.attachCells (D-2) Γ ι f)) (TopCat.ofHom (cylRetract q)))) ≫ (cokernel.π (Work.StemsB.relChainsRIncl ℚ (TopCat.of (Work.RatHurewicz.attachCells (D-2) Γ ι f)) (cylPairS (D := D) (Γ := Γ) (ι := ι) (f := f)))) := (Category.assoc _ _ _).symm
    _ = (Work.Cohomology.chainMap ℚ (TopCat.of X) (TopCat.of (Work.RatHurewicz.attachCells (D-2) Γ ι f)) (TopCat.ofHom q)) ≫ (cokernel.π (Work.StemsB.relChainsRIncl ℚ (TopCat.of (Work.RatHurewicz.attachCells (D-2) Γ ι f)) (cylPairS (D := D) (Γ := Γ) (ι := ι) (f := f)))) := congrArg (fun z => z ≫ (cokernel.π (Work.StemsB.relChainsRIncl ℚ (TopCat.of (Work.RatHurewicz.attachCells (D-2) Γ ι f)) (cylPairS (D := D) (Γ := Γ) (ι := ι) (f := f))))) h7
    _ = (cokernel.π (Work.StemsB.relChainsRIncl ℚ (TopCat.of X) (cylPairA (D := D) (Γ := Γ) (ι := ι) (f := f) (X := X) q))) ≫ (Work.Serre.relChainsRPairMap (cylPairA (D := D) (Γ := Γ) (ι := ι) (f := f) (X := X) q) (cylPairS (D := D) (Γ := Γ) (ι := ι) (f := f)) q (mapsTo_q_cylPairA (D := D) (Γ := Γ) (ι := ι) (f := f) (X := X) q)) := h5.symm

/-! ## The comparison `H_*(C,U) ≅ H_*(Z,Y')` (the retraction `cylRetract`)

This is the second input of the cofibre sequence; it is a direct application of the five term
argument `relChainsRPairMap_homologyMap_isIso` to the map of pairs `(cyl q, U) → (Z, Y')`, whose
two components are homotopy equivalences.  (It is proved here rather than imported so that this
file does not depend on a module also declaring the auxiliary name `cylRetract_cylMove`.) -/

/-- `cylInr q` maps `Y'` into `U`. -/
theorem axMapsTo_cylInr (q : C(X, Work.RatHurewicz.attachCells (D-2) Γ ι f)) :
    Set.MapsTo (cylInr q)
      (cylPairS (D := D) (Γ := Γ) (ι := ι) (f := f))
      (cylPairU (D := D) (Γ := Γ) (ι := ι) (f := f) q) := by
  intro z hz
  show cylRetract q (cylInr q z) ∈ cylPairS (D := D) (Γ := Γ) (ι := ι) (f := f)
  rwa [show cylRetract q (cylInr q z) = z from rfl]

/-- The restricted retraction `U → Y'`. -/
def axRestrRetr (q : C(X, Work.RatHurewicz.attachCells (D-2) Γ ι f)) :
    C(↥(cylPairU (D := D) (Γ := Γ) (ι := ι) (f := f) q),
      ↥(cylPairS (D := D) (Γ := Γ) (ι := ι) (f := f))) :=
  restrictPair _ _ (cylRetract q)
    (mapsTo_cylRetract_cylPairU (D := D) (Γ := Γ) (ι := ι) (f := f) q)

/-- The restricted target inclusion `Y' → U`. -/
def axRestrInr (q : C(X, Work.RatHurewicz.attachCells (D-2) Γ ι f)) :
    C(↥(cylPairS (D := D) (Γ := Γ) (ι := ι) (f := f)),
      ↥(cylPairU (D := D) (Γ := Γ) (ι := ι) (f := f) q)) :=
  restrictPair _ _ (cylInr q) (axMapsTo_cylInr (D := D) (Γ := Γ) (ι := ι) (f := f) q)

/-- The push-up homotopy, restricted to `U` (which it preserves). -/
def axRestrHomotopyMap (q : C(X, Work.RatHurewicz.attachCells (D-2) Γ ι f)) :
    C(unitInterval × ↥(cylPairU (D := D) (Γ := Γ) (ι := ι) (f := f) q),
      ↥(cylPairU (D := D) (Γ := Γ) (ι := ι) (f := f) q)) where
  toFun p := ⟨cylMove q (p.2.1, p.1),
    cylMove_mem_cylPairU (D := D) (Γ := Γ) (ι := ι) (f := f) q p.2.2 p.1⟩
  continuous_toFun := Continuous.subtype_mk
    ((cylMove q).continuous.comp
      ((continuous_subtype_val.comp continuous_snd).prodMk continuous_fst))
    (fun p => cylMove_mem_cylPairU (D := D) (Γ := Γ) (ι := ι) (f := f) q p.2.2 p.1)

/-- The homotopy equivalence `U ≃ Y'` given by the retraction. -/
def axHE (q : C(X, Work.RatHurewicz.attachCells (D-2) Γ ι f)) :
    ContinuousMap.HomotopyEquiv
      ↥(cylPairU (D := D) (Γ := Γ) (ι := ι) (f := f) q)
      ↥(cylPairS (D := D) (Γ := Γ) (ι := ι) (f := f)) :=
  ContinuousMap.HomotopyEquiv.mk (axRestrRetr (D := D) (Γ := Γ) (ι := ι) (f := f) q)
    (axRestrInr (D := D) (Γ := Γ) (ι := ι) (f := f) q)
    ⟨(ContinuousMap.Homotopy.symm
      { toContinuousMap := axRestrHomotopyMap (D := D) (Γ := Γ) (ι := ι) (f := f) q
        map_zero_left := fun y => Subtype.ext (by
          show (cylMove q (y.1, 0) : cyl q) = y.1
          rw [Work.Serre.cylMove_zero])
        map_one_left := fun y => Subtype.ext (by
          show (cylMove q (y.1, 1) : cyl q) = cylInr q (cylRetract q y.1)
          rw [Work.Serre.cylMove_one]
          rfl) })⟩
    (by
      have hcomp : ((axRestrRetr (D := D) (Γ := Γ) (ι := ι) (f := f) q).comp
          (axRestrInr (D := D) (Γ := Γ) (ι := ι) (f := f) q))
          = ContinuousMap.id ↥(cylPairS (D := D) (Γ := Γ) (ι := ι) (f := f)) := by
        apply ContinuousMap.ext
        intro y
        exact Subtype.ext rfl
      simpa only [hcomp] using
        (show ((ContinuousMap.id
            ↥(cylPairS (D := D) (Γ := Γ) (ι := ι) (f := f))).Homotopic
            (ContinuousMap.id ↥(cylPairS (D := D) (Γ := Γ) (ι := ι) (f := f)))) from
          ⟨ContinuousMap.Homotopy.refl _⟩))

/-- The push-up homotopy, run backwards, as a map `I × cyl q → cyl q`. -/
def axCylMoveRev (q : C(X, Work.RatHurewicz.attachCells (D-2) Γ ι f)) :
    C(unitInterval × cyl q, cyl q) where
  toFun p := cylMove q (p.2, Work.Serre.unitIntervalOneSub p.1)
  continuous_toFun := (cylMove q).continuous.comp
    (continuous_snd.prodMk (Work.Serre.continuous_unitIntervalOneSub.comp continuous_fst))

/-- The full retraction `cyl q → Z` is a homotopy equivalence (this explicit form is used so
that its underlying map is definitionally `cylRetract q`). -/
abbrev axHEfull (q : C(X, Work.RatHurewicz.attachCells (D-2) Γ ι f)) :
    ContinuousMap.HomotopyEquiv (cyl q) (Work.RatHurewicz.attachCells (D-2) Γ ι f) :=
  ContinuousMap.HomotopyEquiv.mk (cylRetract q) (cylInr q)
    ⟨{ toContinuousMap := axCylMoveRev (D := D) (Γ := Γ) (ι := ι) (f := f) q
       map_zero_left := fun y => by
         show (cylMove q (y, Work.Serre.unitIntervalOneSub 0) : cyl q)
           = ((cylInr q).comp (cylRetract q)) y
         rw [Work.Serre.unitIntervalOneSub_zero, Work.Serre.cylMove_one]
       map_one_left := fun y => by
         show (cylMove q (y, Work.Serre.unitIntervalOneSub 1) : cyl q)
           = (ContinuousMap.id (cyl q)) y
         rw [Work.Serre.unitIntervalOneSub_one, Work.Serre.cylMove_zero]
         rfl }⟩
    (by
      have hcomp : (cylRetract q).comp (cylInr q) = ContinuousMap.id
          (Work.RatHurewicz.attachCells (D-2) Γ ι f) := ContinuousMap.ext (fun z => rfl)
      simpa only [hcomp] using
        (show ((ContinuousMap.id (Work.RatHurewicz.attachCells (D-2) Γ ι f)).Homotopic
            (ContinuousMap.id (Work.RatHurewicz.attachCells (D-2) Γ ι f))) from
          ⟨ContinuousMap.Homotopy.refl _⟩))

/-- `cylRetract q` is a rational homology isomorphism. -/
theorem axIsRatHomologyIso_retract (q : C(X, Work.RatHurewicz.attachCells (D-2) Γ ι f)) :
    Work.Serre.IsRatHomologyIso (cylRetract q) :=
  Work.Serre.IsRatHomologyIso.of_homotopyEquiv (axHEfull (D := D) (Γ := Γ) (ι := ι) (f := f) q)

/-- The restricted retraction is a rational homology isomorphism. -/
theorem axIsRatHomologyIso_restr (q : C(X, Work.RatHurewicz.attachCells (D-2) Γ ι f)) :
    Work.Serre.IsRatHomologyIso (axRestrRetr (D := D) (Γ := Γ) (ι := ι) (f := f) q) :=
  Work.Serre.IsRatHomologyIso.of_homotopyEquiv (axHE (D := D) (Γ := Γ) (ι := ι) (f := f) q)

/-- **The retraction of the mapping cylinder is an isomorphism on the relative rational homology
of the pair `(cyl q, U) → (Z, Y')`.** -/
theorem axCylRetractPairIso (q : C(X, Work.RatHurewicz.attachCells (D-2) Γ ι f)) (m : ℕ) :
    CategoryTheory.IsIso (HomologicalComplex.homologyMap
      (Work.Serre.relChainsRPairMap (cylPairU (D := D) (Γ := Γ) (ι := ι) (f := f) q)
        (cylPairS (D := D) (Γ := Γ) (ι := ι) (f := f)) (cylRetract q)
        (mapsTo_cylRetract_cylPairU (D := D) (Γ := Γ) (ι := ι) (f := f) q)) m) :=
  relChainsRPairMap_homologyMap_isIso
    (cylPairU (D := D) (Γ := Γ) (ι := ι) (f := f) q)
    (cylPairS (D := D) (Γ := Γ) (ι := ι) (f := f)) (cylRetract q)
    (mapsTo_cylRetract_cylPairU (D := D) (Γ := Γ) (ι := ι) (f := f) q) m
    (fun k => axIsRatHomologyIso_retract (D := D) (Γ := Γ) (ι := ι) (f := f) q k)
    (fun k => axIsRatHomologyIso_restr (D := D) (Γ := Γ) (ι := ι) (f := f) q k)

/-- **The cofibre of the map of pairs `q : (X,A) → (Z,Y')`.**  The rational homology of the pair
`(cyl q, A₂)` of the mapping cylinder is the homology of the cofibre of the induced map of relative
chain complexes: over `ℚ` it splits as the product of the cokernel and the kernel. -/
theorem cylPairCofibre (D : ℕ) (Γ : Type) [TopologicalSpace Γ] (ι : Type)
    (f : ι → C(Work.RatHurewicz.cellSphere (D-2), Γ)) {X : Type} [TopologicalSpace X]
    (q : C(X, Work.RatHurewicz.attachCells (D-2) Γ ι f)) (hq : Work.StemsB.IsSerreFibration q)
    (m : ℕ) (hm : 1 ≤ m) :
    Nonempty (((Work.StemsB.relChainsR ℚ (TopCat.of (Work.Serre.cyl q))
        ((Work.Serre.cylRetract q) ⁻¹' Set.range (Work.RatHurewicz.attachIncl (D-2) Γ ι f) ∪
          Set.range (Work.Serre.cylIncl q))).homology m) ≅
      ModuleCat.of ℚ (↥(CategoryTheory.Limits.cokernel (HomologicalComplex.homologyMap
          (Work.Serre.relChainsRPairMap (q ⁻¹' Set.range (Work.RatHurewicz.attachIncl (D-2) Γ ι f))
            (Set.range (Work.RatHurewicz.attachIncl (D-2) Γ ι f)) q (fun _ hx => hx)) m))
        × ↥(CategoryTheory.Limits.kernel (HomologicalComplex.homologyMap
          (Work.Serre.relChainsRPairMap (q ⁻¹' Set.range (Work.RatHurewicz.attachIncl (D-2) Γ ι f))
            (Set.range (Work.RatHurewicz.attachIncl (D-2) Γ ι f)) q (fun _ hx => hx)) (m-1))))) := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, (Nat.sub_add_cancel hm).symm⟩
  -- the comparison isomorphisms
  haveI hP : CategoryTheory.IsIso (HomologicalComplex.homologyMap
      (subPairMap (D := D) (Γ := Γ) (ι := ι) (f := f) q) (k + 1)) :=
    subPairMapQuasiIso (D := D) (Γ := Γ) (ι := ι) (f := f) q (k + 1)
  haveI hQ : CategoryTheory.IsIso (HomologicalComplex.homologyMap
      (Work.Serre.relChainsRPairMap (cylPairU (D := D) (Γ := Γ) (ι := ι) (f := f) q)
        (cylPairS (D := D) (Γ := Γ) (ι := ι) (f := f)) (cylRetract q)
        (mapsTo_cylRetract_cylPairU (D := D) (Γ := Γ) (ι := ι) (f := f) q)) (k + 1)) :=
    axCylRetractPairIso (D := D) (Γ := Γ) (ι := ι) (f := f) q (k + 1)
  haveI hP' : CategoryTheory.IsIso (HomologicalComplex.homologyMap
      (subPairMap (D := D) (Γ := Γ) (ι := ι) (f := f) q) k) :=
    subPairMapQuasiIso (D := D) (Γ := Γ) (ι := ι) (f := f) q k
  haveI hQ' : CategoryTheory.IsIso (HomologicalComplex.homologyMap
      (Work.Serre.relChainsRPairMap (cylPairU (D := D) (Γ := Γ) (ι := ι) (f := f) q)
        (cylPairS (D := D) (Γ := Γ) (ι := ι) (f := f)) (cylRetract q)
        (mapsTo_cylRetract_cylPairU (D := D) (Γ := Γ) (ι := ι) (f := f) q)) k) :=
    axCylRetractPairIso (D := D) (Γ := Γ) (ι := ι) (f := f) q k
  -- the maps of the cofibre sequence and the comparison maps.  The type ascriptions below
  -- (`α`, `β`, `γ`) spell out `(cylPairShort q).X₁`, `(cylPairShort q).X₂` so that the
  -- submodule manipulations at the end of the proof are carried out in a single syntactic form.
  let α : (cokernel (cylPairChainInclU (D := D) (Γ := Γ) (ι := ι) (f := f) q)).homology (k+1) ⟶
      (Work.StemsB.relChainsR ℚ (TopCat.of (cyl q))
        (cylPairU (D := D) (Γ := Γ) (ι := ι) (f := f) q)).homology (k+1) :=
    HomologicalComplex.homologyMap (cylPairShort (D := D) (Γ := Γ) (ι := ι) (f := f) q).f (k+1)
  let β : (Work.StemsB.relChainsR ℚ (TopCat.of (cyl q))
        (cylPairU (D := D) (Γ := Γ) (ι := ι) (f := f) q)).homology (k+1) ⟶
      (Work.StemsB.relChainsR ℚ (TopCat.of (cyl q))
        (cylPairA₂ (D := D) (Γ := Γ) (ι := ι) (f := f) q)).homology (k+1) :=
    HomologicalComplex.homologyMap (cylPairShort (D := D) (Γ := Γ) (ι := ι) (f := f) q).g (k+1)
  let δ := cylPairδ (D := D) (Γ := Γ) (ι := ι) (f := f) q k
  let γ : (cokernel (cylPairChainInclU (D := D) (Γ := Γ) (ι := ι) (f := f) q)).homology k ⟶
      (Work.StemsB.relChainsR ℚ (TopCat.of (cyl q))
        (cylPairU (D := D) (Γ := Γ) (ι := ι) (f := f) q)).homology k :=
    HomologicalComplex.homologyMap (cylPairShort (D := D) (Γ := Γ) (ι := ι) (f := f) q).f k
  let ψP := asIso (HomologicalComplex.homologyMap
      (subPairMap (D := D) (Γ := Γ) (ι := ι) (f := f) q) (k+1))
  let ψQ := asIso (HomologicalComplex.homologyMap
      (Work.Serre.relChainsRPairMap (cylPairU (D := D) (Γ := Γ) (ι := ι) (f := f) q)
        (cylPairS (D := D) (Γ := Γ) (ι := ι) (f := f)) (cylRetract q)
        (mapsTo_cylRetract_cylPairU (D := D) (Γ := Γ) (ι := ι) (f := f) q)) (k+1))
  let ψP' := asIso (HomologicalComplex.homologyMap
      (subPairMap (D := D) (Γ := Γ) (ι := ι) (f := f) q) k)
  let ψQ' := asIso (HomologicalComplex.homologyMap
      (Work.Serre.relChainsRPairMap (cylPairU (D := D) (Γ := Γ) (ι := ι) (f := f) q)
        (cylPairS (D := D) (Γ := Γ) (ι := ι) (f := f)) (cylRetract q)
        (mapsTo_cylRetract_cylPairU (D := D) (Γ := Γ) (ι := ι) (f := f) q)) k)
  let f₁ := HomologicalComplex.homologyMap (Work.Serre.relChainsRPairMap
      (cylPairA (D := D) (Γ := Γ) (ι := ι) (f := f) (X := X) q)
      (cylPairS (D := D) (Γ := Γ) (ι := ι) (f := f))
      q (mapsTo_q_cylPairA (D := D) (Γ := Γ) (ι := ι) (f := f) (X := X) q)) (k+1)
  let f₂ := HomologicalComplex.homologyMap (Work.Serre.relChainsRPairMap
      (cylPairA (D := D) (Γ := Γ) (ι := ι) (f := f) (X := X) q)
      (cylPairS (D := D) (Γ := Γ) (ι := ι) (f := f))
      q (mapsTo_q_cylPairA (D := D) (Γ := Γ) (ι := ι) (f := f) (X := X) q)) k
  -- the commuting squares, from the chain level identity
  have hsq : ψP.hom ≫ α ≫ ψQ.hom = f₁ := by
    show HomologicalComplex.homologyMap (subPairMap (D := D) (Γ := Γ) (ι := ι) (f := f) q) (k + 1) ≫
        HomologicalComplex.homologyMap (cylPairShort (D := D) (Γ := Γ) (ι := ι) (f := f) q).f (k + 1) ≫
        HomologicalComplex.homologyMap (Work.Serre.relChainsRPairMap (cylPairU (D := D) (Γ := Γ) (ι := ι) (f := f) q) (cylPairS (D := D) (Γ := Γ) (ι := ι) (f := f)) (cylRetract q) (mapsTo_cylRetract_cylPairU (D := D) (Γ := Γ) (ι := ι) (f := f) q)) (k + 1) = _
    erw [← HomologicalComplex.homologyMap_comp (φ := (cylPairShort (D := D) (Γ := Γ) (ι := ι) (f := f) q).f)
      (ψ := (Work.Serre.relChainsRPairMap (cylPairU (D := D) (Γ := Γ) (ι := ι) (f := f) q) (cylPairS (D := D) (Γ := Γ) (ι := ι) (f := f)) (cylRetract q) (mapsTo_cylRetract_cylPairU (D := D) (Γ := Γ) (ι := ι) (f := f) q))) (i := k + 1)]
    erw [← HomologicalComplex.homologyMap_comp (φ := (subPairMap (D := D) (Γ := Γ) (ι := ι) (f := f) q))
      (ψ := ((cylPairShort (D := D) (Γ := Γ) (ι := ι) (f := f) q).f ≫ (Work.Serre.relChainsRPairMap (cylPairU (D := D) (Γ := Γ) (ι := ι) (f := f) q) (cylPairS (D := D) (Γ := Γ) (ι := ι) (f := f)) (cylRetract q) (mapsTo_cylRetract_cylPairU (D := D) (Γ := Γ) (ι := ι) (f := f) q)))) (i := k + 1)]
    rw [subPairMap_comp_short_comp (D := D) (Γ := Γ) (ι := ι) (f := f) q]
  have hsq' : ψP'.hom ≫ γ ≫ ψQ'.hom = f₂ := by
    show HomologicalComplex.homologyMap (subPairMap (D := D) (Γ := Γ) (ι := ι) (f := f) q) k ≫
        HomologicalComplex.homologyMap (cylPairShort (D := D) (Γ := Γ) (ι := ι) (f := f) q).f k ≫
        HomologicalComplex.homologyMap (Work.Serre.relChainsRPairMap (cylPairU (D := D) (Γ := Γ) (ι := ι) (f := f) q) (cylPairS (D := D) (Γ := Γ) (ι := ι) (f := f)) (cylRetract q) (mapsTo_cylRetract_cylPairU (D := D) (Γ := Γ) (ι := ι) (f := f) q)) k = _
    erw [← HomologicalComplex.homologyMap_comp (φ := (cylPairShort (D := D) (Γ := Γ) (ι := ι) (f := f) q).f)
      (ψ := (Work.Serre.relChainsRPairMap (cylPairU (D := D) (Γ := Γ) (ι := ι) (f := f) q) (cylPairS (D := D) (Γ := Γ) (ι := ι) (f := f)) (cylRetract q) (mapsTo_cylRetract_cylPairU (D := D) (Γ := Γ) (ι := ι) (f := f) q))) (i := k)]
    erw [← HomologicalComplex.homologyMap_comp (φ := (subPairMap (D := D) (Γ := Γ) (ι := ι) (f := f) q))
      (ψ := ((cylPairShort (D := D) (Γ := Γ) (ι := ι) (f := f) q).f ≫ (Work.Serre.relChainsRPairMap (cylPairU (D := D) (Γ := Γ) (ι := ι) (f := f) q) (cylPairS (D := D) (Γ := Γ) (ι := ι) (f := f)) (cylRetract q) (mapsTo_cylRetract_cylPairU (D := D) (Γ := Γ) (ι := ι) (f := f) q)))) (i := k)]
    rw [subPairMap_comp_short_comp (D := D) (Γ := Γ) (ι := ι) (f := f) q]
  -- the two submodule identifications
  have hrange : (LinearMap.range α.hom).map ψQ.hom.hom = LinearMap.range f₁.hom := by
    have hrange_ψP : (ψP.hom.hom).range = ⊤ := by
      rw [LinearMap.range_eq_top]
      intro y
      exact ⟨ψP.inv.hom y, Iso.inv_hom_id_apply ψP y⟩
    have hLM : ModuleCat.Hom.hom f₁ = (ModuleCat.Hom.hom ψQ.hom).comp
        ((ModuleCat.Hom.hom α).comp (ModuleCat.Hom.hom ψP.hom)) := by
      rw [← hsq, ModuleCat.hom_comp, ModuleCat.hom_comp, LinearMap.comp_assoc]
    rw [hLM, LinearMap.range_comp, LinearMap.range_comp, hrange_ψP, Submodule.map_top]
  have hker : (LinearMap.ker γ.hom).map ψP'.inv.hom = LinearMap.ker f₂.hom := by
    have hLM : ModuleCat.Hom.hom f₂ = (ModuleCat.Hom.hom ψQ'.hom).comp
        ((ModuleCat.Hom.hom γ).comp (ModuleCat.Hom.hom ψP'.hom)) := by
      rw [← hsq', ModuleCat.hom_comp, ModuleCat.hom_comp, LinearMap.comp_assoc]
    rw [hLM]
    ext x
    simp only [Submodule.mem_map, LinearMap.mem_ker, LinearMap.comp_apply]
    constructor
    · rintro ⟨y, hy, rfl⟩
      rw [Iso.inv_hom_id_apply ψP' y, hy, LinearMap.map_zero]
    · intro hy
      refine ⟨ψP'.hom.hom x, ?_, Iso.hom_inv_id_apply ψP' x⟩
      have h := congrArg (ModuleCat.Hom.hom ψQ'.inv) hy
      rw [Iso.hom_inv_id_apply ψQ' (γ.hom (ψP'.hom.hom x)), LinearMap.map_zero] at h
      exact h
  -- the splitting
  obtain ⟨e₀⟩ := linearEquiv_prod_of_exact α.hom β.hom δ.hom γ.hom
    (cylPairShort_exact_data (D := D) (Γ := Γ) (ι := ι) (f := f) q k).1
    (cylPairShort_exact_data (D := D) (Γ := Γ) (ι := ι) (f := f) q k).2.1
    (cylPairShort_exact_data (D := D) (Γ := Γ) (ι := ι) (f := f) q k).2.2
  have eC : (↥((Work.StemsB.relChainsR ℚ (TopCat.of (cyl q))
        (cylPairU (D := D) (Γ := Γ) (ι := ι) (f := f) q)).homology (k+1)) ⧸
      LinearMap.range α.hom) ≃ₗ[ℚ]
      (↥((Work.StemsB.relChainsR ℚ
          (TopCat.of (Work.RatHurewicz.attachCells (D-2) Γ ι f))
          (cylPairS (D := D) (Γ := Γ) (ι := ι) (f := f))).homology (k+1)) ⧸
        LinearMap.range f₁.hom) :=
    Submodule.Quotient.equiv (LinearMap.range α.hom) (LinearMap.range f₁.hom)
      ψQ.toLinearEquiv hrange
  have eK : ↥(LinearMap.ker γ.hom) ≃ₗ[ℚ] ↥(LinearMap.ker f₂.hom) :=
    LinearEquiv.ofSubmodules ψP'.toLinearEquiv.symm (LinearMap.ker γ.hom)
      (LinearMap.ker f₂.hom) hker
  exact ⟨((e₀.trans (eC.prodCongr eK)).trans
    (((ModuleCat.cokernelIsoRangeQuotient f₁).toLinearEquiv.prodCongr
      (ModuleCat.kernelIsoKer f₂).toLinearEquiv).symm)).toModuleIso⟩

end

end Work.Serre.DiscPair
