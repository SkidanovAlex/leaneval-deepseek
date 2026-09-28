import Mathlib
import Submission.Work.SSS.serreE1CoefExplicit
import Submission.Work.SSS.faceDiff

namespace Work.SSS

open CategoryTheory CategoryTheory.Limits Simplicial HomologicalComplex

noncomputable section

set_option maxHeartbeats 800000

/-! ## Auxiliary computations

The proof of `Work.SSS.tensorComplex_d_coef` conjugates the differential of the tensor complex
`N_*(X) ⊗ M` by the explicit coefficient isomorphism `Work.SSS.serreE1CoefIsoIso`.  The
isomorphism is a composite of four isomorphisms; we compute the conjugate of the differential
along each of them.

* `tensorComplexIsoExpTens_conj_d`: conjugating the differential of `tensorComplex K M` by the
  explicit isomorphism `tensorComplexIsoExpTensIso K M` gives the differential of the naive
  coefficient extension `expTens K M`.
* `normalizedCoeffIso_conj_d`: conjugating the differential of `expTens (N_*(X)) M` by the
  explicit isomorphism `normalizedCoeffIsoIso X M` gives the differential of the normalized chain
  complex `N_*(X; M)` with coefficients in `M`.
* `coprodIso_conj_d`: conjugating the differential of `N_*(X; M)` by the degreewise coefficient
  isomorphism `normalizedChainComplexCoprodIso` gives the alternating face differential
  `faceD` on the coproduct of copies of `M` indexed by the nondegenerate simplices.

The last one uses Mathlib's `SSet.ιNormalizedChainComplex_d` (the differential on a generator)
and `SSet.ιNormalizedChainComplex_eq_zero` (a degenerate generator vanishes). -/

/-- Conjugating the differential of `tensorComplex K M` by the explicit isomorphism
`tensorComplexIsoExpTensIso K M` (whose components are isomorphisms) gives the differential of
the naive coefficient extension `expTens K M`. -/
lemma tensorComplexIsoExpTens_conj_d (X : SSet.{0}) (M : ModuleCat ℤ) (j : ℕ) :
    (asIso ((Work.SSS.tensorComplexIsoExpTensIso (X.normalizedChainComplex (ModuleCat.of ℤ ℤ)) M).hom.f (j+1))).inv ≫
      (Work.SSS.tensorComplex (X.normalizedChainComplex (ModuleCat.of ℤ ℤ)) M).d (j+1) j ≫
      (asIso ((Work.SSS.tensorComplexIsoExpTensIso (X.normalizedChainComplex (ModuleCat.of ℤ ℤ)) M).hom.f j)).hom
    = (Work.SSS.expTens (X.normalizedChainComplex (ModuleCat.of ℤ ℤ)) M).d (j+1) j := by
  have h := ((Work.SSS.tensorComplexIsoExpTensIso (X.normalizedChainComplex (ModuleCat.of ℤ ℤ)) M).hom).comm (j+1) j
  rw [show (asIso ((Work.SSS.tensorComplexIsoExpTensIso (X.normalizedChainComplex (ModuleCat.of ℤ ℤ)) M).hom.f (j+1))).inv
        = inv ((Work.SSS.tensorComplexIsoExpTensIso (X.normalizedChainComplex (ModuleCat.of ℤ ℤ)) M).hom.f (j+1)) from rfl,
      show (asIso ((Work.SSS.tensorComplexIsoExpTensIso (X.normalizedChainComplex (ModuleCat.of ℤ ℤ)) M).hom.f j)).hom
        = ((Work.SSS.tensorComplexIsoExpTensIso (X.normalizedChainComplex (ModuleCat.of ℤ ℤ)) M).hom.f j) from rfl,
      ← h, ← Category.assoc, IsIso.inv_hom_id, Category.id_comp]

/-- Conjugating the differential of `expTens (N_*(X)) M` by the explicit isomorphism
`normalizedCoeffIsoIso X M` gives the differential of the normalized chain complex `N_*(X; M)`
with coefficients in `M`. -/
lemma normalizedCoeffIso_conj_d (X : SSet.{0}) (M : ModuleCat ℤ) (j : ℕ) :
    (asIso ((Work.SSS.normalizedCoeffIsoIso X M).hom.f (j+1))).hom ≫
      (Work.SSS.expTens (X.normalizedChainComplex (ModuleCat.of ℤ ℤ)) M).d (j+1) j ≫
      (asIso ((Work.SSS.normalizedCoeffIsoIso X M).hom.f j)).inv
    = (X.normalizedChainComplex M).d (j+1) j := by
  have h := ((Work.SSS.normalizedCoeffIsoIso X M).hom).comm (j+1) j
  rw [show (asIso ((Work.SSS.normalizedCoeffIsoIso X M).hom.f (j+1))).hom
        = ((Work.SSS.normalizedCoeffIsoIso X M).hom.f (j+1)) from rfl,
      show (asIso ((Work.SSS.normalizedCoeffIsoIso X M).hom.f j)).inv
        = inv ((Work.SSS.normalizedCoeffIsoIso X M).hom.f j) from rfl,
      ← Category.assoc, h, Category.assoc, IsIso.hom_inv_id, Category.comp_id]

/-- **The differential of the normalized chain complex `N_*(X; M)` in the coordinates
`∐_{σ ∈ ND_n} M`.**  Through the degreewise coefficient isomorphism
`Work.SSS.normalizedChainComplexCoprodIso` (the coproduct, over the nondegenerate `n`-simplices,
of copies of `M`, with the `n`-th term of `N_*(X; M)`), the differential of `N_*(X; M)` is the
alternating face differential `Work.SSS.faceD`: a nondegenerate `(j+1)`-simplex `σ` is sent to
`∑_i (-1)^i [d_iσ]`, a degenerate face contributing `0`. -/
lemma coprodIso_conj_d (X : SSet.{0}) (M : ModuleCat ℤ) (j : ℕ) :
    (Work.SSS.normalizedChainComplexCoprodIso X M (j+1)).hom ≫
      (X.normalizedChainComplex M).d (j+1) j ≫
      (Work.SSS.normalizedChainComplexCoprodIso X M j).inv
    = Work.SSS.faceD X M j := by
  have hcomp : ∀ (d : ℕ) (σ : X.nonDegenerate d),
      Sigma.ι (fun _ : X.nonDegenerate d => M) σ ≫
        (Work.SSS.normalizedChainComplexCoprodIso X M d).hom
      = X.ιNormalizedChainComplex σ.val := by
    intro d σ
    unfold Work.SSS.normalizedChainComplexCoprodIso
    simp only
    exact IsColimit.comp_coconePointUniqueUpToIso_hom
      (P := coproductIsCoproduct (fun _ : X.nonDegenerate d => M))
      (Q := X.isColimitCofanNormalizedChainComplex M d) (Discrete.mk σ)
  have hcomp' : ∀ (d : ℕ) (σ : X.nonDegenerate d),
      X.ιNormalizedChainComplex σ.val ≫
        (Work.SSS.normalizedChainComplexCoprodIso X M d).inv
      = Sigma.ι (fun _ : X.nonDegenerate d => M) σ := by
    intro d σ
    unfold Work.SSS.normalizedChainComplexCoprodIso
    simp only
    exact IsColimit.comp_coconePointUniqueUpToIso_inv
      (P := coproductIsCoproduct (fun _ : X.nonDegenerate d => M))
      (Q := X.isColimitCofanNormalizedChainComplex M d) (Discrete.mk σ)
  apply Sigma.hom_ext
  intro σ
  rw [Work.SSS.faceD_ι]
  rw [← Category.assoc, hcomp (j+1) σ, ← Category.assoc, SSet.ιNormalizedChainComplex_d,
    Preadditive.sum_comp]
  apply Finset.sum_congr rfl
  intro i _
  rw [Preadditive.zsmul_comp]
  congr 1
  by_cases h : X.δ i σ.val ∈ X.nonDegenerate j
  · rw [dif_pos h, hcomp' j ⟨X.δ i σ.val, h⟩]
  · rw [dif_neg h]
    have hdeg : X.δ i σ.val ∈ X.degenerate j := by
      rwa [SSet.mem_degenerate_iff_notMem_nonDegenerate]
    rw [SSet.ιNormalizedChainComplex_eq_zero X _ hdeg, zero_comp]

/-- **The differential of `N_*(X) ⊗ M` in the coordinates `∐_{σ ∈ nIndex X n} M`.**

Through the explicit coefficient isomorphism `Work.SSS.serreE1CoefIsoIso` (whose source is the
coproduct, over the nondegenerate `n`-simplices of `X`, of copies of `M`, and whose target is the
`n`-th term of the tensor complex `N_*(X) ⊗ M`), the differential of the tensor complex is the
alternating face differential `Work.SSS.faceD'`: a nondegenerate `(j+1)`-simplex `σ` is sent to
`∑_i (-1)^i [d_iσ]`, a degenerate face contributing `0`.

This is the standard description of the normalized Moore complex of a simplicial set (free on the
nondegenerate simplices, with the alternating face differential), together with the fact that
tensoring with `M` acts on the second factor.

Mathlib's `SSet.ιNormalizedChainComplex_d` (the differential of the normalized chain complex on a
generator) and `SSet.ιNormalizedChainComplex_eq_zero` (a generator attached to a degenerate simplex
vanishes) are the key inputs. -/
theorem tensorComplex_d_coef (X : SSet.{0}) (M : ModuleCat ℤ) (j : ℕ) :
    (Work.SSS.serreE1CoefIsoIso X M (j+1)).hom ≫
        (Work.SSS.tensorComplex (X.normalizedChainComplex (ModuleCat.of ℤ ℤ)) M).d (j+1) j ≫
        (Work.SSS.serreE1CoefIsoIso X M j).inv
      = Work.SSS.faceD' X M j := by
  have hF := tensorComplexIsoExpTens_conj_d X M j
  have hE := normalizedCoeffIso_conj_d X M j
  have hC := coprodIso_conj_d X M j
  have h1 : (Work.SSS.serreE1CoefIsoIso X M (j+1)).hom =
      (Work.SSS.coprodReindexIso X (j+1) M).inv ≫
      (Work.SSS.normalizedChainComplexCoprodIso X M (j+1)).hom ≫
      (asIso ((Work.SSS.normalizedCoeffIsoIso X M).hom.f (j+1))).hom ≫
      (asIso ((Work.SSS.tensorComplexIsoExpTensIso (X.normalizedChainComplex (ModuleCat.of ℤ ℤ)) M).hom.f (j+1))).inv := by
    rw [Work.SSS.serreE1CoefIsoIso]; simp only [Iso.trans_hom, Iso.symm_hom]
  have h2 : (Work.SSS.serreE1CoefIsoIso X M j).inv =
      (asIso ((Work.SSS.tensorComplexIsoExpTensIso (X.normalizedChainComplex (ModuleCat.of ℤ ℤ)) M).hom.f j)).hom ≫
      (asIso ((Work.SSS.normalizedCoeffIsoIso X M).hom.f j)).inv ≫
      (Work.SSS.normalizedChainComplexCoprodIso X M j).inv ≫
      (Work.SSS.coprodReindexIso X j M).hom := by
    rw [Work.SSS.serreE1CoefIsoIso]; simp only [Iso.trans_inv, Iso.symm_inv, Category.assoc]
  rw [h1, h2, Work.SSS.faceD']
  simp only [Category.assoc]
  have hmid : (Work.SSS.normalizedChainComplexCoprodIso X M (j+1)).hom ≫
      (asIso ((Work.SSS.normalizedCoeffIsoIso X M).hom.f (j+1))).hom ≫
      (asIso ((Work.SSS.tensorComplexIsoExpTensIso (X.normalizedChainComplex (ModuleCat.of ℤ ℤ)) M).hom.f (j+1))).inv ≫
      (Work.SSS.tensorComplex (X.normalizedChainComplex (ModuleCat.of ℤ ℤ)) M).d (j+1) j ≫
      (asIso ((Work.SSS.tensorComplexIsoExpTensIso (X.normalizedChainComplex (ModuleCat.of ℤ ℤ)) M).hom.f j)).hom ≫
      (asIso ((Work.SSS.normalizedCoeffIsoIso X M).hom.f j)).inv ≫
      (Work.SSS.normalizedChainComplexCoprodIso X M j).inv = Work.SSS.faceD X M j := by
    calc (Work.SSS.normalizedChainComplexCoprodIso X M (j+1)).hom ≫
        (asIso ((Work.SSS.normalizedCoeffIsoIso X M).hom.f (j+1))).hom ≫
        (asIso ((Work.SSS.tensorComplexIsoExpTensIso (X.normalizedChainComplex (ModuleCat.of ℤ ℤ)) M).hom.f (j+1))).inv ≫
        (Work.SSS.tensorComplex (X.normalizedChainComplex (ModuleCat.of ℤ ℤ)) M).d (j+1) j ≫
        (asIso ((Work.SSS.tensorComplexIsoExpTensIso (X.normalizedChainComplex (ModuleCat.of ℤ ℤ)) M).hom.f j)).hom ≫
        (asIso ((Work.SSS.normalizedCoeffIsoIso X M).hom.f j)).inv ≫
        (Work.SSS.normalizedChainComplexCoprodIso X M j).inv
      = (Work.SSS.normalizedChainComplexCoprodIso X M (j+1)).hom ≫
        (asIso ((Work.SSS.normalizedCoeffIsoIso X M).hom.f (j+1))).hom ≫
        ((asIso ((Work.SSS.tensorComplexIsoExpTensIso (X.normalizedChainComplex (ModuleCat.of ℤ ℤ)) M).hom.f (j+1))).inv ≫
        (Work.SSS.tensorComplex (X.normalizedChainComplex (ModuleCat.of ℤ ℤ)) M).d (j+1) j ≫
        (asIso ((Work.SSS.tensorComplexIsoExpTensIso (X.normalizedChainComplex (ModuleCat.of ℤ ℤ)) M).hom.f j)).hom) ≫
        (asIso ((Work.SSS.normalizedCoeffIsoIso X M).hom.f j)).inv ≫
        (Work.SSS.normalizedChainComplexCoprodIso X M j).inv := by simp only [Category.assoc]
    _ = (Work.SSS.normalizedChainComplexCoprodIso X M (j+1)).hom ≫
        (asIso ((Work.SSS.normalizedCoeffIsoIso X M).hom.f (j+1))).hom ≫
        (Work.SSS.expTens (X.normalizedChainComplex (ModuleCat.of ℤ ℤ)) M).d (j+1) j ≫
        (asIso ((Work.SSS.normalizedCoeffIsoIso X M).hom.f j)).inv ≫
        (Work.SSS.normalizedChainComplexCoprodIso X M j).inv := by rw [hF]
    _ = (Work.SSS.normalizedChainComplexCoprodIso X M (j+1)).hom ≫
        ((asIso ((Work.SSS.normalizedCoeffIsoIso X M).hom.f (j+1))).hom ≫
        (Work.SSS.expTens (X.normalizedChainComplex (ModuleCat.of ℤ ℤ)) M).d (j+1) j ≫
        (asIso ((Work.SSS.normalizedCoeffIsoIso X M).hom.f j)).inv) ≫
        (Work.SSS.normalizedChainComplexCoprodIso X M j).inv := by simp only [Category.assoc]
    _ = (Work.SSS.normalizedChainComplexCoprodIso X M (j+1)).hom ≫
        (X.normalizedChainComplex M).d (j+1) j ≫
        (Work.SSS.normalizedChainComplexCoprodIso X M j).inv := by rw [hE]
    _ = Work.SSS.faceD X M j := hC
  calc (Work.SSS.coprodReindexIso X (j+1) M).inv ≫
      (Work.SSS.normalizedChainComplexCoprodIso X M (j+1)).hom ≫
      (asIso ((Work.SSS.normalizedCoeffIsoIso X M).hom.f (j+1))).hom ≫
      (asIso ((Work.SSS.tensorComplexIsoExpTensIso (X.normalizedChainComplex (ModuleCat.of ℤ ℤ)) M).hom.f (j+1))).inv ≫
      (Work.SSS.tensorComplex (X.normalizedChainComplex (ModuleCat.of ℤ ℤ)) M).d (j+1) j ≫
      (asIso ((Work.SSS.tensorComplexIsoExpTensIso (X.normalizedChainComplex (ModuleCat.of ℤ ℤ)) M).hom.f j)).hom ≫
      (asIso ((Work.SSS.normalizedCoeffIsoIso X M).hom.f j)).inv ≫
      (Work.SSS.normalizedChainComplexCoprodIso X M j).inv ≫
      (Work.SSS.coprodReindexIso X j M).hom
    = ((Work.SSS.coprodReindexIso X (j+1) M).inv ≫
        ((Work.SSS.normalizedChainComplexCoprodIso X M (j+1)).hom ≫
        (asIso ((Work.SSS.normalizedCoeffIsoIso X M).hom.f (j+1))).hom ≫
        (asIso ((Work.SSS.tensorComplexIsoExpTensIso (X.normalizedChainComplex (ModuleCat.of ℤ ℤ)) M).hom.f (j+1))).inv ≫
        (Work.SSS.tensorComplex (X.normalizedChainComplex (ModuleCat.of ℤ ℤ)) M).d (j+1) j ≫
        (asIso ((Work.SSS.tensorComplexIsoExpTensIso (X.normalizedChainComplex (ModuleCat.of ℤ ℤ)) M).hom.f j)).hom ≫
        (asIso ((Work.SSS.normalizedCoeffIsoIso X M).hom.f j)).inv ≫
        (Work.SSS.normalizedChainComplexCoprodIso X M j).inv)) ≫
      (Work.SSS.coprodReindexIso X j M).hom := by simp only [Category.assoc]
  _ = ((Work.SSS.coprodReindexIso X (j+1) M).inv ≫ Work.SSS.faceD X M j) ≫
      (Work.SSS.coprodReindexIso X j M).hom := by rw [hmid]
  _ = (Work.SSS.coprodReindexIso X (j+1) M).inv ≫ Work.SSS.faceD X M j ≫
      (Work.SSS.coprodReindexIso X j M).hom := by simp only [Category.assoc]

end

end Work.SSS
