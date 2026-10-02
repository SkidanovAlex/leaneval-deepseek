import Submission.Work.Serre.ThmCylSigma.Rel
import Submission.Work.StemsB.AToolsR
import Submission.Work.StemsB.MixedCupR

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# Additivity of the Thom cup map over a `σ`-type

For a family of maps `π i : Y i → B i` and relative classes `U i ∈ H^n(Y i, A i)` whose cup maps
`x ↦ π i^*(x) ⌣ U i` are bijective in degrees up to `N`, the assembled class
`Uσ ∈ H^n(Σ i, Y i, Σ i, A i)` has the same property for the `σ`-type map `Σ i, π i`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

open CategoryTheory AlgebraicTopology Simplicial Limits
open scoped Simplicial Topology

namespace Work.Serre.Sigma

noncomputable section

variable {ι : Type} {B Y : ι → Type} [∀ i, TopologicalSpace (B i)] [∀ i, TopologicalSpace (Y i)]

/-! ## The restriction of the assembled class -/

/-- **The restriction of the assembled class is the class of the piece.** -/
theorem relClassOf_assembleRel_restr (A : ∀ i, Set (Y i)) (n : ℕ)
    (w : ∀ i, Work.Cohomology.relKern ℚ (TopCat.of (Y i)) (A i) n)
    (hw : ∀ i, Work.Cohomology.relDiffLM ℚ (TopCat.of (Y i)) (A i) n (w i) = 0)
    (hcoc : Work.Cohomology.relDiffLM ℚ (TopCat.of (Σ i, Y i)) (sigmaSet A) n
      (assembleRel ℚ A n w) = 0) (i : ι) :
    (Work.Thom.relCohMap (pieceIncl (Y := Y) i).hom (A i) (sigmaSet A)
        (fun x hx => pieceIncl_mem_sigmaSet A i x hx) ℚ n).hom
      (Work.Cohomology.relClassOf ℚ (TopCat.of (Σ i, Y i)) (sigmaSet A)
        (assembleRel ℚ A n w) hcoc)
      = Work.Cohomology.relClassOf ℚ (TopCat.of (Y i)) (A i) (w i) (hw i) := by
  change (HomologicalComplex.homologyMap (Work.Cohomology.relComplexMap ℚ (A i) (sigmaSet A)
      (pieceIncl (Y := Y) i) (fun x hx => pieceIncl_mem_sigmaSet A i x hx)) n).hom
      (Work.Cohomology.relClassOf ℚ (TopCat.of (Σ i, Y i)) (sigmaSet A)
        (assembleRel ℚ A n w) hcoc)
    = Work.Cohomology.relClassOf ℚ (TopCat.of (Y i)) (A i) (w i) (hw i)
  refine (@Work.Cohomology.homologyMap_relComplexMap_relClassOf ℚ _ (TopCat.of (Y i))
    (TopCat.of (Σ i, Y i)) (A i) (sigmaSet A) (pieceIncl (Y := Y) i)
    (fun x hx => pieceIncl_mem_sigmaSet A i x hx) n (assembleRel ℚ A n w) hcoc).trans ?_
  exact Work.Cohomology.relClassOf_congr ℚ (TopCat.of (Y i)) (A i) _ (hw i)
    (restrRel_assembleRel ℚ A n w i)


/-! ## The differential of the relative assembly -/

/-- **The relative differential of an assembled family, assembled.** -/
theorem relDiffLM_assembleRel (A : ∀ i, Set (Y i)) (n : ℕ)
    (w : ∀ i, Work.Cohomology.relKern ℚ (TopCat.of (Y i)) (A i) n) :
    Work.Cohomology.relDiffLM ℚ (TopCat.of (Σ i, Y i)) (sigmaSet A) n (assembleRel ℚ A n w) =
      assembleRel ℚ A (n + 1)
        (fun i => Work.Cohomology.relDiffLM ℚ (TopCat.of (Y i)) (A i) n (w i)) := by
  refine Subtype.ext ?_
  rw [relDiffLM_assembleRel_coe ℚ A n w, assembleRel_coe]

/-! ## A relative class with vanishing restrictions vanishes -/

/-- **A relative class of the `σ`-pair whose restrictions to all pieces vanish is zero** (in
positive degrees). -/
theorem relZero_of_restr_zero (A : ∀ i, Set (Y i)) (m : ℕ)
    (y : Work.Thom.RelCoh ℚ (m + 1) (Σ i, Y i) (sigmaSet A))
    (h : ∀ i, (Work.Thom.relCohMap (pieceIncl (Y := Y) i).hom (A i) (sigmaSet A)
      (fun x hx => pieceIncl_mem_sigmaSet A i x hx) ℚ (m + 1)).hom y = 0) : y = 0 := by
  obtain ⟨v, hv, rfl⟩ :=
    Work.Cohomology.exists_relClassOf ℚ (TopCat.of (Σ i, Y i)) (sigmaSet A) (m + 1) y
  have hcob : ∀ i, ∃ wi : Work.Cohomology.relKern ℚ (TopCat.of (Y i)) (A i) m,
      Work.Cohomology.relDiffLM ℚ (TopCat.of (Y i)) (A i) m wi = restrRel ℚ A i (m + 1) v := by
    intro i
    have hnat := @Work.Cohomology.homologyMap_relComplexMap_relClassOf ℚ _ (TopCat.of (Y i))
      (TopCat.of (Σ i, Y i)) (A i) (sigmaSet A) (pieceIncl (Y := Y) i)
      (fun x hx => pieceIncl_mem_sigmaSet A i x hx) (m + 1) v hv
    have hmono : (HomologicalComplex.homologyMap (Work.Cohomology.relComplexMap ℚ (A i)
        (sigmaSet A) (pieceIncl (Y := Y) i) (fun x hx => pieceIncl_mem_sigmaSet A i x hx))
        (m + 1)).hom
        (Work.Cohomology.relClassOf ℚ (TopCat.of (Σ i, Y i)) (sigmaSet A) v hv) = 0 := h i
    have hzero : Work.Cohomology.relClassOf ℚ (TopCat.of (Y i)) (A i)
        (restrRel ℚ A i (m + 1) v) _ = 0 := hnat.symm.trans hmono
    exact Work.Serre.Sigma.exists_relDiff_of_relClassOf_eq_zero (TopCat.of (Y i)) (A i)
      (restrRel ℚ A i (m + 1) v) _ hzero
  choose w hw using hcob
  have hmaps : (fun i => restrRel ℚ A i (m + 1) v)
      = (fun i => Work.Cohomology.relDiffLM ℚ (TopCat.of (Y i)) (A i) m (w i)) := by
    funext i
    exact (hw i).symm
  have hveq : v = Work.Cohomology.relDiffLM ℚ (TopCat.of (Σ i, Y i)) (sigmaSet A) m
      (assembleRel ℚ A m w) := by
    rw [← assembleRel_restrRel ℚ A (m + 1) v, hmaps, relDiffLM_assembleRel (A := A) (n := m) (w := w)]
  exact (Work.Cohomology.relClassOf_congr ℚ (TopCat.of (Σ i, Y i)) (sigmaSet A) hv _ hveq).trans
    (relClassOf_relDiffLM_eq_zero (TopCat.of (Σ i, Y i)) (sigmaSet A) (assembleRel ℚ A m w))


/-! ## The naturality of the `σ`-type cup map -/

/-- **The `σ`-type cup map is compatible with the restrictions to the pieces.** -/
theorem relCohMap_mixedCup_sigmaMap (A : ∀ i, Set (Y i)) (π : ∀ i, C(Y i, B i)) (n k : ℕ)
    (Uσ : Work.Thom.RelCoh ℚ n (Σ i, Y i) (sigmaSet A))
    (x : Work.Thom.Coh ℚ k (Σ i, B i)) (i : ι) :
    (Work.Thom.relCohMap (pieceIncl (Y := Y) i).hom (A i) (sigmaSet A)
        (fun x hx => pieceIncl_mem_sigmaSet A i x hx) ℚ (k + n)).hom
      ((Work.Thom.mixedCupC ℚ (sigmaSet A) k n)
        ((Work.Thom.CohMap (sigmaMap π) ℚ k).hom x) Uσ)
    = (Work.Thom.mixedCupC ℚ (A i) k n)
        ((Work.Thom.CohMap (π i) ℚ k).hom
          ((Work.Thom.CohMap (pieceIncl (Y := B) i).hom ℚ k).hom x))
        ((Work.Thom.relCohMap (pieceIncl (Y := Y) i).hom (A i) (sigmaSet A)
          (fun x hx => pieceIncl_mem_sigmaSet A i x hx) ℚ n).hom Uσ) := by
  have hcomp : (sigmaMap π).comp ((pieceIncl (Y := Y) i).hom)
      = (pieceIncl (Y := B) i).hom.comp (π i) := by
    simpa using congrArg TopCat.Hom.hom (sigmaMap_pieceIncl (X := Y) π i)
  have hca : (Work.Thom.CohMap (pieceIncl (Y := Y) i).hom ℚ k).hom
        ((Work.Thom.CohMap (sigmaMap π) ℚ k).hom x)
      = (Work.Thom.CohMap (π i) ℚ k).hom
        ((Work.Thom.CohMap (pieceIncl (Y := B) i).hom ℚ k).hom x) := by
    have h1 : (Work.Thom.CohMap (pieceIncl (Y := Y) i).hom ℚ k).hom
        ((Work.Thom.CohMap (sigmaMap π) ℚ k).hom x)
        = (Work.Thom.CohMap ((sigmaMap π).comp (pieceIncl (Y := Y) i).hom) ℚ k).hom x := by
      have h := LinearMap.congr_fun (Work.Thom.CohMap_linear_comp (pieceIncl (Y := Y) i).hom
        (sigmaMap π) ℚ k) x
      simpa only [LinearMap.comp_apply] using h
    have h2 : (Work.Thom.CohMap (π i) ℚ k).hom
        ((Work.Thom.CohMap (pieceIncl (Y := B) i).hom ℚ k).hom x)
        = (Work.Thom.CohMap ((pieceIncl (Y := B) i).hom.comp (π i)) ℚ k).hom x := by
      have h := LinearMap.congr_fun (Work.Thom.CohMap_linear_comp (π i)
        (pieceIncl (Y := B) i).hom ℚ k) x
      simpa only [LinearMap.comp_apply] using h
    rw [h1, h2, hcomp]
  exact (Work.StemsB.mixedCupC_pairNaturalR ℚ (pieceIncl (Y := Y) i).hom (A i) (sigmaSet A)
    (fun x hx => pieceIncl_mem_sigmaSet A i x hx) k n
    ((Work.Thom.CohMap (sigmaMap π) ℚ k).hom x) Uσ).trans (by rw [hca])

end

end Work.Serre.Sigma
