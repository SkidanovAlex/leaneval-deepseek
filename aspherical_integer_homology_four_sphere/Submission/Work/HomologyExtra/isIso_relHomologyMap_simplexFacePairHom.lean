import Mathlib
import Submission.Work.HomologyExtra.SimplexFaceSetup
import Submission.Work.HomologyExtra.RelChainMapFunctor
import Submission.Work.HomologyExtra.ExcisionInterior
import Submission.Work.HomologyExtra.isIso_relHomologyMap_pairHomOfHomeomorph
import Submission.Work.HomologyExtra.simplexSouthCap_contractible
import Submission.Work.HomologyExtra.simplexNorthCap_contractible
import Submission.Work.HomologyExtra.simplexBoundary_homologyOne
import Submission.Work.HomologyExtra.simplexLastFace_contractible
import Submission.Work.HomologyExtra.simplexFaceHomeo_exists
import Submission.Work.HomologyExtra.equatorInCollar_isHomotopyEquivalence
import Submission.Work.HomologyExtra.closure_lastVertex_subset_interior_star

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The face map `(Δⁿ, ∂Δⁿ) → (∂Δⁿ⁺¹, B)` is an isomorphism on relative homology

`Work.HomologyExtra.simplexFacePairHom n` is the map of pairs induced by the last face of
`∂Δⁿ⁺¹`, where `B = simplexStar n` is the closed star of the last vertex.  This file proves that
it induces an isomorphism on relative homology in degree `n` (`n ≥ 1`), by factoring it as

  `(Δⁿ, ∂Δⁿ) --face map--> (A, E) --inclusion--> (S, T) --inclusion--> (X, B)`,

with `A = simplexLastFace n` the last face, `E = simplexEquator n = ∂A` its equator,
`S = simplexSouthCap n = X ∖ {last vertex}` and `T = simplexCollar n = B ∩ S`:

* the first map is a homeomorphism of pairs (`Work.HomologyExtra.simplexFaceHomeo_exists`);
* the second is an isomorphism by the five lemma, because `A` and `S` are contractible
  (`Work.HomologyExtra.simplexLastFace_contractible`, `Work.HomologyExtra.simplexSouthCap_contractible`)
  and `E → T` is a homotopy equivalence (`Work.HomologyExtra.equatorInCollar_isHomotopyEquivalence`);
* the third is excision, since `B` and `S` cover `X` by interiors
  (`Work.HomologyExtra.closure_lastVertex_subset_interior_star`).

Functoriality of the relative chain map is `Work.HomologyExtra.relChainMap_comp`, the five lemma
for a map of pairs is `Work.HomologyExtra.isIso_relHomologyMap_of_pairMap`, and the excision step is
`Work.HomologyExtra.isIso_relChainMap_homologyMap_of_interior`.
-/

open CategoryTheory AlgebraicTopology CategoryTheory.Limits

namespace Work.HomologyExtra

noncomputable section

set_option backward.isDefEq.respectTransparency false








/-! ## Congruence for the explicit comparison map of relative chains -/

/-- `Work.Cohomology.relChainsMapOf` only depends on its arguments up to propositional equality. -/
theorem relChainsMapOf_congr {X Y : TopCat} {A : Set X} {B : Set Y} {f f' : X ⟶ Y}
    {g g' : TopCat.of A ⟶ TopCat.of B} (hf : f = f') (hg : g = g')
    (w : Work.Cohomology.subtypeIncl X A ≫ f = g ≫ Work.Cohomology.subtypeIncl Y B)
    (w' : Work.Cohomology.subtypeIncl X A ≫ f' = g' ≫ Work.Cohomology.subtypeIncl Y B) :
    Work.Cohomology.relChainsMapOf X Y A B f g w =
      Work.Cohomology.relChainsMapOf X Y A B f' g' w' := by
  cases hf
  cases hg
  exact congrArg (fun w => Work.Cohomology.relChainsMapOf X Y A B f g w)
    (Subsingleton.elim w w')

/-- `Work.Cohomology.relChainsMap` is the explicit comparison map of the pair `(U, A ∩ U)`. -/
theorem relChainsMap_eq_relChainsMapOf_gen (X : TopCat) (U A : Set X)
    (w : Work.Cohomology.subtypeIncl (TopCat.of U) {y : ↥U | (y : X) ∈ A} ≫
          Work.Cohomology.subtypeIncl X U =
        Work.Cohomology.inclInterA X U A ≫ Work.Cohomology.subtypeIncl X A) :
    Work.Cohomology.relChainsMap X U A =
      Work.Cohomology.relChainsMapOf (TopCat.of U) X {y : ↥U | (y : X) ∈ A} A
        (Work.Cohomology.subtypeIncl X U) (Work.Cohomology.inclInterA X U A) w :=
  relChainsMapOf_congr rfl rfl _ w

/-! ## Small genericity lemmas -/

/-- A morphism between two zero objects is an isomorphism. -/
theorem isIso_of_isZero_of_isZero {C : Type*} [Category C] [HasZeroMorphisms C] {X Y : C}
    (hX : IsZero X) (hY : IsZero Y) (f : X ⟶ Y) : IsIso f := by
  have h1 : f = 0 := hX.eq_of_src f 0
  have h2 : 𝟙 X = 0 := hX.eq_of_src (𝟙 X) 0
  have h3 : 𝟙 Y = 0 := hY.eq_of_tgt (𝟙 Y) 0
  refine ⟨0, ?_, ?_⟩
  · rw [h2]; exact comp_zero
  · rw [h1, zero_comp, h3]

/-- For path-connected spaces, the map induced by a continuous map on `H₀` is a monomorphism
(its composition with the augmentations is the augmentation, an isomorphism). -/
theorem mono_singHomologyMap_zero {X Y : TopCat} (f : X ⟶ Y) [PathConnectedSpace X]
    [PathConnectedSpace Y] :
    Mono (Work.Homology.singHomologyMap Work.Homology.ZMod 0 f) := by
  have hcomp := Work.Cohomology.epsilonNaturality X Y f
  haveI hX : IsIso (X.singularHomology₀ε (ModuleCat.of ℤ ℤ)) := inferInstance
  haveI hY : IsIso (Y.singularHomology₀ε (ModuleCat.of ℤ ℤ)) := inferInstance
  have hf : Work.Homology.singHomologyMap Work.Homology.ZMod 0 f =
      X.singularHomology₀ε (ModuleCat.of ℤ ℤ) ≫ inv (Y.singularHomology₀ε (ModuleCat.of ℤ ℤ)) := by
    rw [← hcomp, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  rw [hf]
  infer_instance

/-! ## The three maps of pairs -/

/-- The inclusion of the last face `A` into the south cap `S`. -/
def lastFaceInSouthCap (n : ℕ) :
    TopCat.of (simplexLastFace n) ⟶ TopCat.of (simplexSouthCap n) :=
  TopCat.ofHom ⟨fun x => ⟨(x : ↥(boundarySpace (n + 1))), mem_southCap_of_mem_lastFace x.2⟩,
    by fun_prop⟩

/-- **The face map as a map of pairs** `(Δⁿ, ∂Δⁿ) → (A, E)`. -/
def lastFacePairHom (n : ℕ) : Work.Homology.PairHom (simplex n)
    (TopCat.of (simplexLastFace n)) (simplexBoundary n) (equatorInLastFace n) where
  hom := TopCat.ofHom ⟨faceToLastFaceFun n, continuous_faceToLastFaceFun n⟩
  mapsTo := by
    intro w hw
    rw [mem_equatorInLastFace, mem_simplexEquator]
    constructor
    · change (((faceToLastFaceFun n w : ↥(simplexLastFace n)) : ↥(boundarySpace (n + 1))) :
        simplex (n + 1)).weights (Fin.last (n + 1)) = 0
      rw [faceToLastFaceFun_weights_last]
    · obtain ⟨i, hi⟩ := hw
      refine ⟨i, ?_⟩
      change (((faceToLastFaceFun n w : ↥(simplexLastFace n)) : ↥(boundarySpace (n + 1))) :
        simplex (n + 1)).weights (Fin.castSucc i) = 0
      rw [faceToLastFaceFun_weights_castSucc]
      exact hi

/-- **The inclusion of pairs** `(A, E) → (S, T)`. -/
def lastFaceToCollarPairHom (n : ℕ) : Work.Homology.PairHom (TopCat.of (simplexLastFace n))
    (TopCat.of (simplexSouthCap n)) (equatorInLastFace n) (simplexCollar n) where
  hom := lastFaceInSouthCap n
  mapsTo := by
    intro x hx
    rw [mem_simplexCollar]
    exact mem_star_of_mem_equator hx

/-- **The inclusion of pairs** `(S, T) → (X, B)`. -/
def collarPairHom (n : ℕ) : Work.Homology.PairHom (TopCat.of (simplexSouthCap n))
    (boundarySpace (n + 1)) (simplexCollar n) (simplexStar n) where
  hom := Work.Homology.incl (simplexSouthCap n)
  mapsTo := fun _ hx => hx

/-- The composite pair map `(Δⁿ, ∂Δⁿ) → (X, B)`. -/
def facePairHomTotal (n : ℕ) : Work.Homology.PairHom (simplex n) (boundarySpace (n + 1))
    (simplexBoundary n) (simplexStar n) :=
  (collarPairHom n).comp ((lastFaceToCollarPairHom n).comp (lastFacePairHom n))

theorem lastFaceInSouthCap_apply (n : ℕ) (x : ↥(simplexLastFace n)) :
    ((lastFaceInSouthCap n x : ↥(simplexSouthCap n)) : ↥(boundarySpace (n + 1))) = x := rfl

theorem lastFaceToCollarPairHom_hom (n : ℕ) :
    (lastFaceToCollarPairHom n).hom = lastFaceInSouthCap n := rfl

theorem lastFaceToCollarPairHom_sub (n : ℕ) :
    (lastFaceToCollarPairHom n).sub = equatorInCollar n := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro x
  rfl

theorem collarPairHom_hom (n : ℕ) :
    (collarPairHom n).hom = Work.Cohomology.subtypeIncl (boundarySpace (n + 1))
      (simplexSouthCap n) := rfl

theorem collarPairHom_sub (n : ℕ) :
    (collarPairHom n).sub = Work.Cohomology.inclInterA (boundarySpace (n + 1))
      (simplexSouthCap n) (simplexStar n) := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro x
  rfl

/-- The composite pair map has the same underlying map as the face pair map of the closed star. -/
theorem facePairHomTotal_hom_eq (n : ℕ) :
    (facePairHomTotal n).hom = (simplexFacePairHom n).hom := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro w
  apply Subtype.ext
  rfl

/-- The composite pair map induces the same map on relative chains as the face pair map. -/
theorem relChainMap_facePairHomTotal_eq (n : ℕ) :
    Work.Homology.relChainMap Work.Homology.ZMod (facePairHomTotal n) =
      Work.Homology.relChainMap Work.Homology.ZMod (simplexFacePairHom n) := by
  apply (cancel_epi (Work.Homology.relProj Work.Homology.ZMod (simplex n)
    (simplexBoundary n))).1
  rw [← Work.Homology.relChainMap_comp_relProj, ← Work.Homology.relChainMap_comp_relProj,
    facePairHomTotal_hom_eq n]

/-- The composite pair map induces the same map on relative homology as the face pair map. -/
theorem relHomologyMap_facePairHomTotal_eq (n : ℕ) :
    Work.Homology.relHomologyMap Work.Homology.ZMod n (facePairHomTotal n) =
      Work.Homology.relHomologyMap Work.Homology.ZMod n (simplexFacePairHom n) := by
  simp only [Work.Homology.relHomologyMap, relChainMap_facePairHomTotal_eq]

/-! ## The three steps -/

/-- **Step 1**: the face map `(Δⁿ, ∂Δⁿ) → (A, E)` is an isomorphism on relative homology. -/
theorem isIso_relHomologyMap_lastFacePairHom (n : ℕ)
    (hface : ∃ e : simplex n ≃ₜ TopCat.of (simplexLastFace n),
      ∀ w : simplex n, e w = faceToLastFaceFun n w) :
    IsIso (Work.Homology.relHomologyMap Work.Homology.ZMod n (lastFacePairHom n)) := by
  obtain ⟨e, he⟩ := hface
  have he_mem : ∀ w : simplex n, w ∈ simplexBoundary n ↔ e w ∈ equatorInLastFace n := by
    intro w
    rw [mem_equatorInLastFace, mem_simplexEquator, he w]
    constructor
    · intro hw
      refine ⟨faceToLastFaceFun_weights_last n w, ?_⟩
      obtain ⟨i, hi⟩ := hw
      exact ⟨i, by rw [faceToLastFaceFun_weights_castSucc]; exact hi⟩
    · intro hw
      obtain ⟨-, i, hi⟩ := hw
      exact ⟨i, by rw [faceToLastFaceFun_weights_castSucc] at hi; exact hi⟩
  have hhom : (pairHomOfHomeomorph e he_mem).hom = (lastFacePairHom n).hom := by
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro w
    show e w = faceToLastFaceFun n w
    exact he w
  have hchain : Work.Homology.relChainMap Work.Homology.ZMod (pairHomOfHomeomorph e he_mem) =
      Work.Homology.relChainMap Work.Homology.ZMod (lastFacePairHom n) := by
    apply (cancel_epi (Work.Homology.relProj Work.Homology.ZMod (simplex n)
      (simplexBoundary n))).1
    rw [← Work.Homology.relChainMap_comp_relProj, ← Work.Homology.relChainMap_comp_relProj, hhom]
  have hhomology : Work.Homology.relHomologyMap Work.Homology.ZMod n
      (pairHomOfHomeomorph e he_mem) =
      Work.Homology.relHomologyMap Work.Homology.ZMod n (lastFacePairHom n) := by
    simp only [Work.Homology.relHomologyMap, hchain]
  rw [← hhomology]
  exact isIso_relHomologyMap_pairHomOfHomeomorph e he_mem n

/-- **Step 2**: the inclusion `(A, E) → (S, T)` is an isomorphism on relative homology. -/
theorem isIso_relHomologyMap_lastFaceToCollarPairHom (n : ℕ) (hn : 1 ≤ n)
    (hcontr : ContractibleSpace (TopCat.of (simplexLastFace n)))
    (hcollar : Work.Homology.IsHomotopyEquivalence (equatorInCollar n)) :
    IsIso (Work.Homology.relHomologyMap Work.Homology.ZMod n (lastFaceToCollarPairHom n)) := by
  haveI hA : ContractibleSpace (TopCat.of (simplexLastFace n)) := hcontr
  haveI hS : ContractibleSpace (TopCat.of (simplexSouthCap n)) := simplexSouthCap_contractible n
  have hsub : IsIso (HomologicalComplex.homologyMap
      (Work.Homology.singChainMap Work.Homology.ZMod (lastFaceToCollarPairHom n).sub) n) := by
    rw [lastFaceToCollarPairHom_sub]
    exact isIso_singHomologyMap_of_isHomotopyEquivalence (equatorInCollar n) hcollar n
  have hsub' : IsIso (HomologicalComplex.homologyMap
      (Work.Homology.singChainMap Work.Homology.ZMod (lastFaceToCollarPairHom n).sub) (n - 1)) := by
    rw [lastFaceToCollarPairHom_sub]
    exact isIso_singHomologyMap_of_isHomotopyEquivalence (equatorInCollar n) hcollar (n - 1)
  have hhom : IsIso (HomologicalComplex.homologyMap
      (Work.Homology.singChainMap Work.Homology.ZMod (lastFaceToCollarPairHom n).hom) n) := by
    rw [lastFaceToCollarPairHom_hom]
    refine isIso_of_isZero_of_isZero ?_ ?_ _
    · have h := Work.Homology.ContractibleHomology Work.Homology.ZMod
        (TopCat.of (simplexLastFace n)) (n - 1)
      simpa [Nat.sub_add_cancel hn] using h
    · have h := Work.Homology.ContractibleHomology Work.Homology.ZMod
        (TopCat.of (simplexSouthCap n)) (n - 1)
      simpa [Nat.sub_add_cancel hn] using h
  have hhom' : Mono (HomologicalComplex.homologyMap
      (Work.Homology.singChainMap Work.Homology.ZMod (lastFaceToCollarPairHom n).hom) (n - 1)) := by
    rw [lastFaceToCollarPairHom_hom]
    rcases Nat.lt_or_ge n 2 with h | h
    · interval_cases n
      exact mono_singHomologyMap_zero (lastFaceInSouthCap 1)
    · haveI : IsZero (Work.Homology.singHomology Work.Homology.ZMod (n - 1)
          (TopCat.of (simplexLastFace n))) := by
        have hc := Work.Homology.ContractibleHomology Work.Homology.ZMod
          (TopCat.of (simplexLastFace n)) (n - 2)
        simpa [show n - 1 = (n - 2) + 1 from by omega] using hc
      exact IsZero.mono ‹_› _
  exact isIso_relHomologyMap_of_pairMap (lastFaceToCollarPairHom n) n
    (IsIso.epi_of_iso _) hhom hsub' hhom'

/-- **Step 3**: the inclusion `(S, T) → (X, B)` is an isomorphism on relative homology. -/
theorem isIso_relHomologyMap_collarPairHom (n : ℕ)
    (hclosure : closure ({simplexLastVertex n} : Set ↥(boundarySpace (n + 1)))
      ⊆ interior (simplexStar n)) :
    IsIso (Work.Homology.relHomologyMap Work.Homology.ZMod n (collarPairHom n)) := by
  have hX : interior (simplexStar n) ∪ interior (simplexSouthCap n) = Set.univ := by
    rw [(isOpen_simplexSouthCap n).interior_eq]
    apply Set.eq_univ_of_forall
    intro x
    by_cases hx : x ∈ simplexSouthCap n
    · exact Or.inr hx
    · refine Or.inl (hclosure ?_)
      have hw : ((x : ↥(boundarySpace (n + 1))) : simplex (n + 1)).weights
          (Fin.last (n + 1)) = 1 := by
        have hle : ((x : ↥(boundarySpace (n + 1))) : simplex (n + 1)).weights
            (Fin.last (n + 1)) ≤ 1 := by
          have htot := Convexity.StdSimplex.total_of_fintype
            ((x : ↥(boundarySpace (n + 1))) : simplex (n + 1))
          calc ((x : ↥(boundarySpace (n + 1))) : simplex (n + 1)).weights (Fin.last (n + 1))
              ≤ ∑ i, ((x : ↥(boundarySpace (n + 1))) : simplex (n + 1)).weights i :=
                Finset.single_le_sum
                  (fun i _ => Convexity.StdSimplex.weights_nonneg
                    (w := ((x : ↥(boundarySpace (n + 1))) : simplex (n + 1))) i)
                  (Finset.mem_univ _)
            _ = 1 := htot
        exact le_antisymm hle (le_of_not_gt (fun hlt => hx hlt))
      rw [(eq_simplexLastVertex_iff n x).mpr hw]
      exact subset_closure (Set.mem_singleton (simplexLastVertex n))
  exact isIso_relChainMap_homologyMap_of_interior (boundarySpace (n + 1)) (simplexSouthCap n)
    (simplexStar n) hX (collarPairHom n) (collarPairHom_hom n) n

/-- **The face pair map is an isomorphism on relative homology**, given the four geometric
inputs. -/
theorem isIso_relHomologyMap_simplexFacePairHom_of_geometry (n : ℕ) (hn : 1 ≤ n)
    (hface : ∃ e : simplex n ≃ₜ TopCat.of (simplexLastFace n),
      ∀ w : simplex n, e w = faceToLastFaceFun n w)
    (hcontr : ContractibleSpace (TopCat.of (simplexLastFace n)))
    (hcollar : Work.Homology.IsHomotopyEquivalence (equatorInCollar n))
    (hclosure : closure ({simplexLastVertex n} : Set ↥(boundarySpace (n + 1)))
      ⊆ interior (simplexStar n)) :
    IsIso (Work.Homology.relHomologyMap Work.Homology.ZMod n (simplexFacePairHom n)) := by
  have h1 := isIso_relHomologyMap_lastFacePairHom n hface
  have h2 := isIso_relHomologyMap_lastFaceToCollarPairHom n hn hcontr hcollar
  have h3 := isIso_relHomologyMap_collarPairHom n hclosure
  have h12 : IsIso (Work.Homology.relHomologyMap Work.Homology.ZMod n
      ((lastFaceToCollarPairHom n).comp (lastFacePairHom n))) :=
    isIso_relHomologyMap_comp (lastFacePairHom n) (lastFaceToCollarPairHom n) h1 h2
  have h123 : IsIso (Work.Homology.relHomologyMap Work.Homology.ZMod n (facePairHomTotal n)) :=
    isIso_relHomologyMap_comp ((lastFaceToCollarPairHom n).comp (lastFacePairHom n))
      (collarPairHom n) h12 h3
  rwa [relHomologyMap_facePairHomTotal_eq] at h123

/-! ## The main theorem -/

/-- **The face pair map induces an isomorphism on relative homology.** -/
theorem isIso_relHomologyMap_simplexFacePairHom (n : ℕ) (hn : 1 ≤ n) :
    CategoryTheory.IsIso (Work.Homology.relHomologyMap Work.Homology.ZMod n
      (Work.HomologyExtra.simplexFacePairHom n)) :=
  isIso_relHomologyMap_simplexFacePairHom_of_geometry n hn
    (simplexFaceHomeo_exists n)
    (simplexLastFace_contractible n)
    (equatorInCollar_isHomotopyEquivalence n)
    (closure_lastVertex_subset_interior_star n)

end

end Work.HomologyExtra
