import Mathlib
import Submission.Work.Whitney.RelABComplex
import Submission.Work.Whitney.relABZ
import Submission.Work.Thom.Cohomology
import Submission.Work.Thom.naturalModelClass_punct
import Submission.Work.Whitney.Cup

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

/-!
# The canonical relative–relative cup product, for the top-class multiplicativity

This module fixes the *canonical* relative–relative cup product
`H^m(X,A) ⊗ H^n(X,B) → H^{m+n}(X, A∪B)` (the Alexander–Whitney product on the `A+B` complex
transported along the inverse of the quasi-isomorphism `C^*(X,A∪B) → C^*(X,A+B)`), together with
its computation rule.  It is the vocabulary in which the multiplicativity of the top Chern class
(`Work.Whitney.TopClassMul`, i.e. `c_{m+n}(E⊕F) = c_m(E) ⌣ c_n(F)`) is stated: the Thom class of a
direct sum is the relative–relative cup of the two Thom classes.

The construction is the one of `Work.Whitney.relRelCupG`
(`Submission/Work/Whitney/chernClass_whitneySum_top.lean`), isolated here under fresh names so that
the top-class development does not depend on that module (whose proof of the top-class formula is in
flight).
-/

namespace Work.Whitney

open Work.Thom
open Work.Cohomology
open CategoryTheory AlgebraicTopology CategoryTheory.Limits

noncomputable section

variable {R : Type} [CommRing R]

/-! ## The relative–relative cup with an explicit transport -/

/-- **The relative–relative cup product with the transport made explicit**: for classes
`a ∈ H^m(X,A)`, `b ∈ H^n(X,B)` and a linear `g` from the cohomology of the `A+B` complex to
`H^{m+n}(X,A∪B)`, this is `g (a ⋆ b)`, where `⋆` is the Alexander–Whitney product
`Work.Whitney.relRelCupHMap` on `C^*(X,A) ∩ C^*(X,B)`. -/
noncomputable def tcmRelCupG {X : Type} [TopologicalSpace X] (A B : Set X) (m n : ℕ)
    (g : (pdABCohR (R := R) (TopCat.of X) A B).homology (m + n) →ₗ[R]
      Work.Thom.RelCoh R (m + n) X (A ∪ B)) :
    Work.Thom.RelCoh R m X A →ₗ[R] Work.Thom.RelCoh R n X B →ₗ[R]
      Work.Thom.RelCoh R (m + n) X (A ∪ B) :=
  LinearMap.mk₂ R
    (fun a b => g ((relRelCupHMap (R := R) (TopCat.of X) A B m n) a b))
    (fun a a' b => by simp only [map_add, LinearMap.add_apply])
    (fun c a b => by simp only [map_smul, LinearMap.smul_apply])
    (fun a b b' => by simp only [map_add, LinearMap.add_apply])
    (fun c a b => by simp only [map_smul, LinearMap.smul_apply])

/-- The defining equation of `Work.Whitney.tcmRelCupG`. -/
theorem tcmRelCupG_apply {X : Type} [TopologicalSpace X] (A B : Set X) (m n : ℕ)
    (g : (pdABCohR (R := R) (TopCat.of X) A B).homology (m + n) →ₗ[R]
      Work.Thom.RelCoh R (m + n) X (A ∪ B))
    (a : Work.Thom.RelCoh R m X A) (b : Work.Thom.RelCoh R n X B) :
    tcmRelCupG A B m n g a b
      = g ((relRelCupHMap (R := R) (TopCat.of X) A B m n) a b) :=
  rfl

/-- **The computation rule of the relative–relative cup**: forgetting the relative data recovers
the absolute Alexander–Whitney product of the two classes.  Only the gauge-fixing equation `hg`
for the transport is used (which holds for the canonical choice `g = φ⁻¹`). -/
theorem tcmRelCupG_relToAbs {X : Type} [TopologicalSpace X] (A B : Set X) (m n : ℕ)
    (g : (pdABCohR (R := R) (TopCat.of X) A B).homology (m + n) →ₗ[R]
      Work.Thom.RelCoh R (m + n) X (A ∪ B))
    (hg : ∀ y, (HomologicalComplex.homologyMap (pdABInclRelR (R := R) (TopCat.of X) A B) (m + n)).hom
      (g y) = y)
    (a : Work.Thom.RelCoh R m X A) (b : Work.Thom.RelCoh R n X B) :
    (Work.Thom.relToAbs R (A ∪ B) (m + n)).hom (tcmRelCupG A B m n g a b)
      = Work.Cohomology.cupH' R (ssB X) m n
          ((Work.Thom.relToAbs R A m).hom a) ((Work.Thom.relToAbs R B n).hom b) := by
  change (HomologicalComplex.homologyMap (relIncl R (TopCat.of X) (A ∪ B)) (m + n)).hom
      (g ((relRelCupHMap (R := R) (TopCat.of X) A B m n) a b))
      = cupH' R (ssB X) m n
          ((HomologicalComplex.homologyMap (relIncl R (TopCat.of X) A) m).hom a)
          ((HomologicalComplex.homologyMap (relIncl R (TopCat.of X) B) n).hom b)
  have hrel : (HomologicalComplex.homologyMap (relIncl R (TopCat.of X) (A ∪ B)) (m + n))
      = HomologicalComplex.homologyMap (pdABInclRelR (R := R) (TopCat.of X) A B) (m + n)
        ≫ HomologicalComplex.homologyMap (pdABInclL (R := R) (TopCat.of X) A B) (m + n) := by
    rw [← HomologicalComplex.homologyMap_comp, relIncl_eq_pdABInclRelR_comp]
  obtain ⟨α, hα, rfl⟩ := exists_relClassOf R (TopCat.of X) A m a
  obtain ⟨β, hβ, rfl⟩ := exists_relClassOf R (TopCat.of X) B n b
  have hα' : ((relComplex R (TopCat.of X) A).d m (m + 1)).hom α = 0 := by
    rw [relComplex_d_apply]; exact hα
  have hβ' : ((relComplex R (TopCat.of X) B).d n (n + 1)).hom β = 0 := by
    rw [relComplex_d_apply]; exact hβ
  have hstar : ((pdABCohR (R := R) (TopCat.of X) A B).d (m + n) (m + n + 1))
      (starAB (R := R) (TopCat.of X) A B m n α β) = 0 :=
    ThreeCup.star3_cocycle_cochain (Leibniz3_starAB (TopCat.of X) A B) m n α β hα' hβ'
  rw [relIncl_homologyMap_relClassOf R (TopCat.of X) A α hα,
      relIncl_homologyMap_relClassOf R (TopCat.of X) B β hβ]
  rw [cupH'_apply' R (ssB X) α.1 β.1 _ _]
  rw [relClassOf_eq_homologyπ_cocycleOfK R (TopCat.of X) A α hα hα',
      relClassOf_eq_homologyπ_cocycleOfK R (TopCat.of X) B β hβ hβ']
  rw [relRelCupHMap_apply (R := R) (TopCat.of X) A B m n α β hα' hβ' hstar]
  rw [show (HomologicalComplex.homologyMap (relIncl R (TopCat.of X) (A ∪ B)) (m + n)).hom
        (g (((pdABCohR (R := R) (TopCat.of X) A B).homologyπ (m + n)).hom
          (cocycleOfK (pdABCohR (R := R) (TopCat.of X) A B)
            (starAB (R := R) (TopCat.of X) A B m n α β) hstar)))
      = (HomologicalComplex.homologyMap (pdABInclL (R := R) (TopCat.of X) A B) (m + n)).hom
          (((pdABCohR (R := R) (TopCat.of X) A B).homologyπ (m + n)).hom
            (cocycleOfK (pdABCohR (R := R) (TopCat.of X) A B)
              (starAB (R := R) (TopCat.of X) A B m n α β) hstar)) from by
    rw [hrel]
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
    rw [hg]]
  rw [pdABInclL_homologyMap_cocycleOfK (TopCat.of X) A B
    (starAB (R := R) (TopCat.of X) A B m n α β) hstar]
  exact cohomologyClassOf_congr R (ssB X)
    (starAB_coe (R := R) (TopCat.of X) A B m n α β) _ _

/-! ## The canonical transport and the canonical cup -/

/-- **The canonical transport**: the inverse of the quasi-isomorphism
`H^{m+n}(X,A∪B) → H^{m+n}(X,A+B)`.  Its defining (gauge-fixing) equation is
`Work.Whitney.tcmRelCupInv_spec`. -/
noncomputable def tcmRelCupInv {X : Type} [TopologicalSpace X] (A B : Set X)
    (hA : IsOpen A) (hB : IsOpen B) (k : ℕ) :
    (pdABCohR (R := R) (TopCat.of X) A B).homology k →ₗ[R]
      Work.Thom.RelCoh R k X (A ∪ B) :=
  letI : IsIso (HomologicalComplex.homologyMap (pdABInclRelR (R := R) (TopCat.of X) A B) k) :=
    pdABInclRelR_quasiIso (R := R) (M := TopCat.of X) A B hA hB k
  (CategoryTheory.inv (HomologicalComplex.homologyMap
    (pdABInclRelR (R := R) (TopCat.of X) A B) k)).hom

/-- **The gauge-fixing equation of the canonical transport**: it is a section of the
quasi-isomorphism. -/
theorem tcmRelCupInv_spec {X : Type} [TopologicalSpace X] (A B : Set X)
    (hA : IsOpen A) (hB : IsOpen B) (k : ℕ)
    (y : (pdABCohR (R := R) (TopCat.of X) A B).homology k) :
    (HomologicalComplex.homologyMap (pdABInclRelR (R := R) (TopCat.of X) A B) k).hom
      (tcmRelCupInv (R := R) A B hA hB k y) = y := by
  letI : IsIso (HomologicalComplex.homologyMap (pdABInclRelR (R := R) (TopCat.of X) A B) k) :=
    pdABInclRelR_quasiIso (R := R) (M := TopCat.of X) A B hA hB k
  unfold tcmRelCupInv
  exact IsIso.inv_hom_id_apply (HomologicalComplex.homologyMap
    (pdABInclRelR (R := R) (TopCat.of X) A B) k) y

/-- **The canonical relative–relative cup product** `H^m(X,A) ⊗ H^n(X,B) → H^{m+n}(X,A∪B)` for
open `A, B ⊆ X`: the Alexander–Whitney product on `C^*(X,A) ∩ C^*(X,B)` transported along the
inverse of the quasi-isomorphism `C^*(X,A∪B) → C^*(X,A+B)`.  This is *canonical* (a function of the
data, no `Classical.choice` beyond the construction of the complexes), so its values are computable
and it is natural under maps of pairs
(`Work.Whitney.chernClass_whitneySum_top`'s `relRelCupG` with the canonical transport). -/
noncomputable def tcmRelCup {X : Type} [TopologicalSpace X] (A B : Set X)
    (hA : IsOpen A) (hB : IsOpen B) (m n : ℕ) :
    Work.Thom.RelCoh R m X A →ₗ[R] Work.Thom.RelCoh R n X B →ₗ[R]
      Work.Thom.RelCoh R (m + n) X (A ∪ B) :=
  tcmRelCupG A B m n (tcmRelCupInv (R := R) A B hA hB (m + n))

/-- **The computation rule of the canonical relative–relative cup product**:
`relToAbs (a ⋆ b) = relToAbs a ⌣ relToAbs b`. -/
theorem tcmRelCup_relToAbs {X : Type} [TopologicalSpace X] (A B : Set X)
    (hA : IsOpen A) (hB : IsOpen B) (m n : ℕ)
    (a : Work.Thom.RelCoh R m X A) (b : Work.Thom.RelCoh R n X B) :
    (Work.Thom.relToAbs R (A ∪ B) (m + n)).hom (tcmRelCup A B hA hB m n a b)
      = Work.Cohomology.cupH' R (ssB X) m n
          ((Work.Thom.relToAbs R A m).hom a) ((Work.Thom.relToAbs R B n).hom b) :=
  tcmRelCupG_relToAbs A B m n _ (fun y => tcmRelCupInv_spec (R := R) A B hA hB (m + n) y) a b


/-! ## The vocabulary of the model product formula

The model product formula compares the relative–relative cup of the two pulled-back model Thom
classes `Work.Thom.Mpun p B`, `Work.Thom.Mpun q B` (of the trivial bundles of ranks `p` and `q`
over a base `B`) with the model class `Work.Thom.Mpun (p+q) B` of the sum, along the linear
(orientation-preserving) identification `ℝ^p × ℝ^q ≅ ℝ^{p+q}`.  This section fixes the space, the
two closed sets, the two projections and the identification. -/

/-- The linear equivalence `ℝ^p × ℝ^q ≅ ℝ^{p+q}` (coordinates kept in order; its determinant is
`+1` for the standard bases). -/
abbrev tcmSumLin (p q : ℕ) :
    (EuclideanSpace ℝ (Fin p) × EuclideanSpace ℝ (Fin q)) ≃L[ℝ]
      EuclideanSpace ℝ (Fin (p + q)) :=
  (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := p) (m := q)).symm

/-- The space `B × (ℝ^p × ℝ^q)` in which the model product formula lives. -/
abbrev tcmX (B : Type) (p q : ℕ) :=
  B × (EuclideanSpace ℝ (Fin p) × EuclideanSpace ℝ (Fin q))

/-- The first closed set: the points whose first fibre coordinate is nonzero. -/
def tcmA (B : Type) (p q : ℕ) : Set (tcmX B p q) := {x | x.2.1 ≠ 0}

/-- The second closed set: the points whose second fibre coordinate is nonzero. -/
def tcmC (B : Type) (p q : ℕ) : Set (tcmX B p q) := {x | x.2.2 ≠ 0}

theorem isOpen_tcmA (B : Type) [TopologicalSpace B] (p q : ℕ) : IsOpen (tcmA B p q) := by
  have h : tcmA B p q
      = (fun x : tcmX B p q => x.2.1) ⁻¹' {v : EuclideanSpace ℝ (Fin p) | v ≠ 0} := by
    ext x; rfl
  rw [h]
  exact isOpen_compl_singleton.preimage (continuous_fst.comp continuous_snd)

theorem isOpen_tcmC (B : Type) [TopologicalSpace B] (p q : ℕ) : IsOpen (tcmC B p q) := by
  have h : tcmC B p q
      = (fun x : tcmX B p q => x.2.2) ⁻¹' {v : EuclideanSpace ℝ (Fin q) | v ≠ 0} := by
    ext x; rfl
  rw [h]
  exact isOpen_compl_singleton.preimage (continuous_snd.comp continuous_snd)

/-- The projection `B × (ℝ^p × ℝ^q) → B × ℝ^p` onto the first summand. -/
def tcmPr1 (B : Type) [TopologicalSpace B] (p q : ℕ) :
    C(tcmX B p q, B × EuclideanSpace ℝ (Fin p)) :=
  ⟨fun x => (x.1, x.2.1), continuous_fst.prodMk (continuous_fst.comp continuous_snd)⟩

/-- The projection `B × (ℝ^p × ℝ^q) → B × ℝ^q` onto the second summand. -/
def tcmPr2 (B : Type) [TopologicalSpace B] (p q : ℕ) :
    C(tcmX B p q, B × EuclideanSpace ℝ (Fin q)) :=
  ⟨fun x => (x.1, x.2.2), continuous_fst.prodMk (continuous_snd.comp continuous_snd)⟩

/-- The homeomorphism `B × (ℝ^p × ℝ^q) → B × ℝ^{p+q}` given by the coordinate identification. -/
def tcmF (B : Type) [TopologicalSpace B] (p q : ℕ) :
    C(tcmX B p q, B × EuclideanSpace ℝ (Fin (p + q))) :=
  ⟨fun x => (x.1, tcmSumLin p q x.2),
    continuous_fst.prodMk ((tcmSumLin p q).continuous.comp continuous_snd)⟩

/-- The pair condition of `Work.Whitney.tcmF`: outside the zero section the identification preserves
the punctured set. -/
theorem tcmF_mem (B : Type) [TopologicalSpace B] (p q : ℕ) :
    ∀ x ∈ tcmA B p q ∪ tcmC B p q, tcmF B p q x ∈ Punct B (p + q) := by
  intro x hx
  rcases hx with hx | hx
  · show tcmSumLin p q x.2 ≠ 0
    intro h
    exact hx (congrArg Prod.fst ((tcmSumLin p q).injective (h.trans (map_zero (tcmSumLin p q)).symm)))
  · show tcmSumLin p q x.2 ≠ 0
    intro h
    exact hx (congrArg Prod.snd ((tcmSumLin p q).injective (h.trans (map_zero (tcmSumLin p q)).symm)))

end

end Work.Whitney
