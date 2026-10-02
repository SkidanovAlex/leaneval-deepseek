import Mathlib
import Submission.Work.ThomBordism.LeadChapter.TubeDetDefs
import Submission.Work.ThomBordism.LeadChapter.det_dthetaEndo_pos
import Submission.Work.PTGeometric.exists_model_submersion_at_mem_core
import Submission.Work.ThomBordism.KeyLocal.gmTubeProductAux
import Submission.Work.ThomBordism.KeyLocal.pairSignGauss
import Submission.Work.ThomBordism.LeadChapter.thetaInvAux
import Submission.Work.ThomBordism.padGaussFunM_eq_of_normalData
import Submission.Work.ThomBordism.gaussBranchUniformOfUniversal
import Submission.Work.ThomBordism.OrthFrame.sign_det_combMat
import Submission.Work.ThomBordism.KeyLocal.gmSign
import Submission.Work.ThomBordism.LeadChapter.tubeDetKernel
import Submission.Work.ThomBordism.LeadChapter.TubeDetCore
import Submission.Work.ThomBordism.KeyLocal.tubeCoordsFDeriv
import Submission.Work.ThomBordism.tubePairSignGauss
import Submission.Work.ThomBordism.tubePairSignGaussFlip

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# `Work.ThomBordism.LeadChapter.tubeDetDetSign`

The determinant sign of the tube at the collar, with the *explicit* candidates: the derivative
`B = collarB k (spatialDeriv G m a i y)` of the collar chart and the canonical normal frame
`N = frameN G m hpow h a i y z hne` of the Gauss plane.  The block determinant `blockDet k B N`
has the constant sign `ε · frameSign (Fam a.2) i y` with `ε = ±1` independent of the piece, the
chart, the point and the collar height.

The proof has three layers.

* **Linear algebra.**  The `e₀`-splitting `(w, c) ↦ srcOfSpatial w + c • e₀` of the ambient model
  space `ModN k` turns the block frame `[collarB k A | srcOfSpatial ∘ W]` into the plain frame
  `[A | W]`; its determinant (read through the fixed splitting `CofAtlas.sigma k`) is a *fixed*
  constant times `det (reEK ∘ (A.coprod W) ∘ tcmSumLin.symm)`, and the latter is `Sig T G`, whose
  determinant is `pairMat T G` (`Work.ThomBordism.KeyLocal.det_Sig`).
* **The reindexing.**  `dthetaInv` contributes `reEK ∘ dthetaInv`, whose determinant sign is `+1`
  (`Work.ThomBordism.LeadChapter.thetaInvAux`).
* **The Gauss orientation.**  `G.gauss` at the tube point is the tied `padGaussFunM`, whose
  `ogFrameCLM`-frame is the Gauss frame `gframe` up to `SO(k)`; the telescoping chapter gives
  `pairSign (chart frame) (gframe) = frameSign`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

open scoped Manifold ContDiff Topology
open CategoryTheory

namespace Work.ThomBordism.LeadChapter

open Work.PTGeometric

noncomputable section

variable {k : ℕ} {D : Work.ThomBordism.PontryaginThom.ThomTarget k} {ι : Type} [Fintype ι]
  {Fam : ι → Work.ThomBordism.Man8}

/-! ## Elementary algebraic lemmas -/

/-- The standard basis expansion of a Euclidean vector. -/
theorem sum_single_euc (n : ℕ) (u : EuclideanSpace ℝ (Fin n)) :
    (∑ a : Fin n, u.ofLp a • (EuclideanSpace.single a (1 : ℝ))) = u := by
  simpa [EuclideanSpace.basisFun_apply, EuclideanSpace.basisFun_repr] using
    (EuclideanSpace.basisFun (Fin n) ℝ).sum_repr u

/-- A linear map applied to the standard basis expansion. -/
theorem sum_smul_single {n : ℕ} {M : Type*} [AddCommMonoid M] [Module ℝ M]
    (u : EuclideanSpace ℝ (Fin n)) (g : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] M) :
    (∑ a : Fin n, u.ofLp a • g (EuclideanSpace.single a (1 : ℝ))) = g u := by
  rw [show (∑ a : Fin n, u.ofLp a • g (EuclideanSpace.single a (1 : ℝ)))
      = ∑ a : Fin n, g (u.ofLp a • EuclideanSpace.single a (1 : ℝ)) from
    Finset.sum_congr rfl (fun a _ => (map_smul g _ _).symm)]
  rw [← map_sum g (fun a => u.ofLp a • EuclideanSpace.single a (1 : ℝ)) Finset.univ]
  congr 1
  exact sum_single_euc n u

/-- The `ℝ`-valued `Real.sign` is multiplicative (unconditionally). -/
theorem real_sign_mul (a b : ℝ) : Real.sign (a * b) = Real.sign a * Real.sign b := by
  rcases lt_trichotomy a 0 with ha | ha | ha
  · rcases lt_trichotomy b 0 with hb | hb | hb
    · rw [Real.sign_of_neg ha, Real.sign_of_neg hb, Real.sign_of_pos (mul_pos_of_neg_of_neg ha hb)]
      norm_num
    · subst hb; simp [Real.sign_zero]
    · rw [Real.sign_of_neg ha, Real.sign_of_pos hb, Real.sign_of_neg (mul_neg_of_neg_of_pos ha hb)]
      norm_num
  · subst ha
    rcases lt_trichotomy b 0 with hb | hb | hb
    · simp [Real.sign_zero, hb]
    · subst hb; simp [Real.sign_zero]
    · simp [Real.sign_zero, hb]
  · rcases lt_trichotomy b 0 with hb | hb | hb
    · rw [Real.sign_of_pos ha, Real.sign_of_neg hb, Real.sign_of_neg (mul_neg_of_pos_of_neg ha hb)]
      norm_num
    · subst hb; simp [Real.sign_zero]
    · rw [Real.sign_of_pos ha, Real.sign_of_pos hb, Real.sign_of_pos (mul_pos ha hb)]
      norm_num

/-- **The reindexed block frame is `Sig`**: the endomorphism
`reEK ∘ (A.coprod W) ∘ tcmSumLin.symm` of `ℝ^{8+k}` is the coordinate reading in the pair frame
whose columns are the frames `A` and `W` (reindexed by the value-preserving `reEK`). -/
theorem coprod_reEK_eq_Sig (k : ℕ)
    (A : EuclideanSpace ℝ (Fin 8) →L[ℝ] EuclideanSpace ℝ (Fin (k + 8)))
    (W : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin (k + 8))) :
    (reEK k).comp ((A.coprod W).comp
        ((Work.Whitney.tcmSumLin 8 k).symm).toContinuousLinearMap)
      = (Work.ThomBordism.KeyLocal.Sig
          (fun a : Fin 8 => reEK k (A (EuclideanSpace.single a 1)))
          (fun b : Fin k => reEK k (W (EuclideanSpace.single b 1)))).toContinuousLinearMap := by
  apply ContinuousLinearMap.ext
  intro z
  show (reEK k) ((A.coprod W) ((Work.Whitney.tcmSumLin 8 k).symm z))
    = Work.ThomBordism.KeyLocal.Sig
        (fun a : Fin 8 => reEK k (A (EuclideanSpace.single a 1)))
        (fun b : Fin k => reEK k (W (EuclideanSpace.single b 1))) z
  rw [Work.ThomBordism.KeyLocal.Sig_apply, ContinuousLinearMap.coprod_apply,
    Work.ThomBordism.KeyLocal.combFrame_apply, Work.ThomBordism.KeyLocal.combFrame_apply,
    Work.ThomBordism.PontryaginThom.eucToFun_apply,
    Work.ThomBordism.PontryaginThom.eucToFun_apply]
  have hA := sum_smul_single ((Work.Whitney.tcmSumLin 8 k).symm z).1
    ((reEK k).toLinearMap.comp A.toLinearMap)
  have hB := sum_smul_single ((Work.Whitney.tcmSumLin 8 k).symm z).2
    ((reEK k).toLinearMap.comp W.toLinearMap)
  simp only [LinearMap.comp_apply, ContinuousLinearMap.coe_coe] at hA hB
  rw [hA, hB, ← map_add]

/-! ## The elementary linear equivalences -/

/-- `reEK` is a left inverse of `reEKInv`. -/
theorem reEK_reEKInv (k : ℕ) (x : EuclideanSpace ℝ (Fin (8 + k))) :
    reEK k (reEKInv k x) = x := by
  rw [reEK, reEKInv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe]
  apply (euclToPi (8 + k)).injective
  rw [euclToPi_piToEucl]
  funext i
  simp only [ContinuousLinearMap.pi_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.proj_apply, euclToPi_piToEucl, finKR_finKRInv]
  rfl

/-- `consCLM` of `(1, 0)` is the first standard basis vector. -/
theorem consCLM_one_zero_apply (n : ℕ) (j : Fin (n + 1)) :
    ((consCLM n) ((1 : ℝ), (0 : EuclideanSpace ℝ (Fin n)))).ofLp j
      = if j = 0 then 1 else 0 := by
  rcases eq_or_ne j 0 with h | h
  · subst h
    rw [if_pos rfl, consCLM_apply_zero]
  · rw [if_neg h]
    obtain ⟨m, rfl⟩ := Fin.eq_succ_of_ne_zero h
    rw [consCLM_apply_succ]
    rfl

/-- `Fin.cons` as a linear equivalence `ℝ × ℝ^{n} ≅ ℝ^{n+1}` (explicit inverse). -/
def consEquiv (n : ℕ) : (ℝ × EuclideanSpace ℝ (Fin n)) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin (n + 1)) :=
  LinearEquiv.mk (consCLM n).toLinearMap (fun x => (x.ofLp 0, tailCLM n x))
    (fun p => by
      obtain ⟨a, u⟩ := p
      show (((consCLM n) (a, u)).ofLp 0, tailCLM n ((consCLM n) (a, u))) = (a, u)
      rw [consCLM_apply_zero, tailCLM_consCLM])
    (fun x => consCLM_tail n x)

theorem consEquiv_apply (n : ℕ) (a : ℝ) (u : EuclideanSpace ℝ (Fin n)) :
    consEquiv n (a, u) = consCLM n (a, u) := rfl

/-- The coordinate reindexing `ℝ^{(k+8)+1} ≅ ℝ^{(8+k)+1}` as a linear equivalence. -/
def srcCastInvEquiv (k : ℕ) :
    EuclideanSpace ℝ (Fin ((k + 8) + 1)) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin ((8 + k) + 1)) :=
  LinearEquiv.mk (srcCastInv k).toLinearMap (fun x => srcCast k x)
    (fun x => srcCast_srcCastInv k x) (fun x => srcCastInv_srcCast k x)

theorem srcCastInvEquiv_apply (k : ℕ) (x : EuclideanSpace ℝ (Fin ((k + 8) + 1))) :
    srcCastInvEquiv k x = srcCastInv k x := rfl

/-- **The `e₀`-splitting of the ambient model space** of the source, in coordinates:
`(w, c) ↦ srcCastInv (consCLM (c, w)) = srcOfSpatial w + c • e₀`. -/
def tubeSplit (k : ℕ) : (EuclideanSpace ℝ (Fin (k + 8)) × ℝ) ≃ₗ[ℝ] CofAtlas.ModN k :=
  (LinearEquiv.prodComm ℝ (EuclideanSpace ℝ (Fin (k + 8))) ℝ).trans
    ((consEquiv (k + 8)).trans (srcCastInvEquiv k))

theorem tubeSplit_apply (k : ℕ) (w : EuclideanSpace ℝ (Fin (k + 8))) (c : ℝ) :
    tubeSplit k (w, c) = srcCastInv k (consCLM (k + 8) (c, w)) := rfl

/-- The first standard basis vector of the ambient model space, in the `srcCastInv ∘ consCLM`
spelling. -/
theorem srcCastInv_consCLM_one_zero (k : ℕ) :
    srcCastInv k (consCLM (k + 8) (1, 0)) = (eZero : CofAtlas.ModN k) := by
  ext i
  rw [srcCastInv_apply, consCLM_one_zero_apply]
  rcases eq_or_ne i 0 with h | h
  · subst h
    rw [Fin.cast_zero, if_pos rfl, eZero_apply]
  · rw [eZero_apply_ne h, if_neg]
    intro hh
    exact h (Fin.ext (by simpa using congrArg Fin.val hh))

/-- `srcCastInv ∘ consCLM` in the `srcOfSpatial + c • e₀` form. -/
theorem tubeSplit_eq (k : ℕ) (w : EuclideanSpace ℝ (Fin (k + 8))) (c : ℝ) :
    tubeSplit k (w, c) = srcOfSpatialCLM k w + c • (eZero : CofAtlas.ModN k) := by
  have h1 : (c, w) = c • ((1 : ℝ), (0 : EuclideanSpace ℝ (Fin (k + 8))))
      + (0, w) := by
    ext <;> simp
  rw [tubeSplit_apply, h1, map_add, map_smul, map_add, map_smul,
    srcCastInv_consCLM_one_zero, srcOfSpatialCLM_apply]
  exact add_comm _ _

/-- `collarB` is `tubeSplit` of the block coordinates. -/
theorem collarB_eq_tubeSplit (k : ℕ)
    (A : EuclideanSpace ℝ (Fin 8) →L[ℝ] EuclideanSpace ℝ (Fin (k + 8)))
    (z : CofAtlas.E9) :
    collarB k A z = tubeSplit k (A (tailCLM 8 z), z 0) := by
  rw [collarB, add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    tubeSplit_eq, collarCLM_apply]

/-- `reEK` as a linear equivalence. -/
def reEKEquiv (k : ℕ) :
    EuclideanSpace ℝ (Fin (k + 8)) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin (8 + k)) :=
  LinearEquiv.mk (reEK k).toLinearMap (fun x => reEKInv k x)
    (fun x => reEKInv_reEK k x) (fun x => reEK_reEKInv k x)

theorem reEKEquiv_apply (k : ℕ) (x : EuclideanSpace ℝ (Fin (k + 8))) :
    reEKEquiv k x = reEK k x := rfl

/-- `reEKInv` as a linear equivalence. -/
def reEKInvEquiv (k : ℕ) :
    EuclideanSpace ℝ (Fin (8 + k)) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin (k + 8)) :=
  (reEKEquiv k).symm

theorem reEKInvEquiv_apply (k : ℕ) (x : EuclideanSpace ℝ (Fin (8 + k))) :
    reEKInvEquiv k x = reEKInv k x := rfl

theorem reEKEquiv_symm_apply (k : ℕ) (x : EuclideanSpace ℝ (Fin (8 + k))) :
    (reEKEquiv k).symm x = reEKInv k x := rfl

theorem reEKInvEquiv_symm_apply (k : ℕ) (x : EuclideanSpace ℝ (Fin (k + 8))) :
    (reEKInvEquiv k).symm x = reEK k x := rfl

/-! ## The block-determinant factorisation -/

/-- **The plain block coordinates** of the collar chart: the level directions `A` and the normal
directions `W`, together with the collar coordinate `z 0`. -/
def blockPhi (k : ℕ)
    (A : EuclideanSpace ℝ (Fin 8) →L[ℝ] EuclideanSpace ℝ (Fin (k + 8)))
    (W : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin (k + 8))) :
    CofAtlas.E9 × EuclideanSpace ℝ (Fin k) →L[ℝ]
      (EuclideanSpace ℝ (Fin (k + 8)) × ℝ) :=
  ((A.comp (tailCLM 8)).coprod W).prod
    (((EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 9) : CofAtlas.E9 →L[ℝ] ℝ)).comp
      (ContinuousLinearMap.fst ℝ CofAtlas.E9 (EuclideanSpace ℝ (Fin k))))

theorem blockPhi_apply (k : ℕ)
    (A : EuclideanSpace ℝ (Fin 8) →L[ℝ] EuclideanSpace ℝ (Fin (k + 8)))
    (W : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin (k + 8)))
    (z : CofAtlas.E9) (v : EuclideanSpace ℝ (Fin k)) :
    blockPhi k A W (z, v) = (A (tailCLM 8 z) + W v, z 0) := rfl

/-- **The reindexed pair frame**: the endomorphism `reEK ∘ (A.coprod W) ∘ tcmSumLin.symm` of
`ℝ^{8+k}`. -/
def blockM (k : ℕ)
    (A : EuclideanSpace ℝ (Fin 8) →L[ℝ] EuclideanSpace ℝ (Fin (k + 8)))
    (W : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin (k + 8))) :
    EuclideanSpace ℝ (Fin (8 + k)) →L[ℝ] EuclideanSpace ℝ (Fin (8 + k)) :=
  (reEK k).comp ((A.coprod W).comp
    ((Work.Whitney.tcmSumLin 8 k).symm).toContinuousLinearMap)

theorem blockM_apply (k : ℕ)
    (A : EuclideanSpace ℝ (Fin 8) →L[ℝ] EuclideanSpace ℝ (Fin (k + 8)))
    (W : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin (k + 8)))
    (z : EuclideanSpace ℝ (Fin (8 + k))) :
    blockM k A W z = reEK k ((A.coprod W) ((Work.Whitney.tcmSumLin 8 k).symm z)) := rfl

theorem blockM_tcmSumLin (k : ℕ)
    (A : EuclideanSpace ℝ (Fin 8) →L[ℝ] EuclideanSpace ℝ (Fin (k + 8)))
    (W : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin (k + 8)))
    (x : EuclideanSpace ℝ (Fin 8) × EuclideanSpace ℝ (Fin k)) :
    blockM k A W (Work.Whitney.tcmSumLin 8 k x) = reEK k ((A.coprod W) x) := by
  rw [blockM_apply]
  exact congrArg (fun y => reEK k ((A.coprod W) y)) ((Work.Whitney.tcmSumLin 8 k).symm_apply_apply x)

theorem reEKInv_blockM_tcmSumLin (k : ℕ)
    (A : EuclideanSpace ℝ (Fin 8) →L[ℝ] EuclideanSpace ℝ (Fin (k + 8)))
    (W : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin (k + 8)))
    (x : EuclideanSpace ℝ (Fin 8) × EuclideanSpace ℝ (Fin k)) :
    reEKInv k (blockM k A W (Work.Whitney.tcmSumLin 8 k x)) = (A.coprod W) x := by
  rw [blockM_tcmSumLin, reEKInv_reEK]

/-- The splitting `ℝ⁹ ≅ ℝ⁸ × ℝ` (tail and first coordinate). -/
def rhoT : CofAtlas.E9 ≃ₗ[ℝ] (EuclideanSpace ℝ (Fin 8) × ℝ) :=
  LinearEquiv.mk
    (LinearMap.prod (tailCLM 8).toLinearMap
      ((EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 9) : CofAtlas.E9 →L[ℝ] ℝ)).toLinearMap)
    (fun p => consCLM 8 (p.2, p.1))
    (fun z => by
      show consCLM 8 (((EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 9)) z),
        (tailCLM 8) z) = z
      rw [show (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 9)) z = z.ofLp 0 from rfl]
      exact consCLM_tail 8 z)
    (fun p => by
      obtain ⟨w, c⟩ := p
      show ((tailCLM 8) (consCLM 8 (c, w)), (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 9))
        (consCLM 8 (c, w))) = (w, c)
      rw [tailCLM_consCLM]
      exact congrArg (fun t => (w, t)) (by simpa using consCLM_apply_zero 8 c w))

theorem rhoT_apply (z : CofAtlas.E9) : rhoT z = (tailCLM 8 z, z 0) := rfl

/-- The reassociation `ℝ⁹ × ℝ^k ≅ (ℝ⁸ × ℝ^k) × ℝ` (dropping the collar coordinate). -/
def psiEquiv (k : ℕ) :
    (CofAtlas.E9 × EuclideanSpace ℝ (Fin k)) ≃ₗ[ℝ]
      ((EuclideanSpace ℝ (Fin 8) × EuclideanSpace ℝ (Fin k)) × ℝ) :=
  LinearEquiv.mk
    (LinearMap.prod
      (LinearMap.prod ((tailCLM 8).toLinearMap.comp (LinearMap.fst ℝ CofAtlas.E9
          (EuclideanSpace ℝ (Fin k))))
        (LinearMap.snd ℝ CofAtlas.E9 (EuclideanSpace ℝ (Fin k))))
      (((EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 9) : CofAtlas.E9 →L[ℝ] ℝ)).toLinearMap.comp
        (LinearMap.fst ℝ CofAtlas.E9 (EuclideanSpace ℝ (Fin k)))))
    (fun p => (consCLM 8 (p.2, p.1.1), p.1.2))
    (fun z => by
      obtain ⟨z₁, z₂⟩ := z
      show (consCLM 8 ((EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 9)) z₁, (tailCLM 8) z₁), z₂)
        = (z₁, z₂)
      rw [show (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 9)) z₁ = z₁.ofLp 0 from rfl, consCLM_tail])
    (fun p => by
      obtain ⟨⟨w, v⟩, c⟩ := p
      show (((tailCLM 8) (consCLM 8 (c, w)), v),
        (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 9)) (consCLM 8 (c, w))) = ((w, v), c)
      rw [tailCLM_consCLM]
      exact congrArg (fun t => ((w, v), t)) (by simpa using consCLM_apply_zero 8 c w))

theorem psiEquiv_apply (k : ℕ) (z : CofAtlas.E9) (v : EuclideanSpace ℝ (Fin k)) :
    psiEquiv k (z, v) = ((tailCLM 8 z, v), z 0) := rfl

/-- The identification `(ℝ⁸ × ℝ^k) × ℝ ≅ ℝ^{8+k} × ℝ` (`tcmSumLin` on the first factor). -/
def sumIdEquiv (k : ℕ) :
    ((EuclideanSpace ℝ (Fin 8) × EuclideanSpace ℝ (Fin k)) × ℝ) ≃ₗ[ℝ]
      (EuclideanSpace ℝ (Fin (8 + k)) × ℝ) :=
  (Work.Whitney.tcmSumLin 8 k).toLinearEquiv.prodCongr (LinearEquiv.refl ℝ ℝ)

theorem sumIdEquiv_apply (k : ℕ)
    (p : (EuclideanSpace ℝ (Fin 8) × EuclideanSpace ℝ (Fin k)) × ℝ) :
    sumIdEquiv k p = (Work.Whitney.tcmSumLin 8 k p.1, p.2) := rfl

/-- The fixed reassociation `ℝ⁹ × ℝ^k ≅ ℝ^{8+k} × ℝ`. -/
def blockZE (k : ℕ) :
    (CofAtlas.E9 × EuclideanSpace ℝ (Fin k)) ≃ₗ[ℝ]
      (EuclideanSpace ℝ (Fin (8 + k)) × ℝ) :=
  (psiEquiv k).trans (sumIdEquiv k)

theorem blockZE_apply (k : ℕ) (z : CofAtlas.E9) (v : EuclideanSpace ℝ (Fin k)) :
    blockZE k (z, v) = (Work.Whitney.tcmSumLin 8 k (tailCLM 8 z, v), z 0) := by
  show sumIdEquiv k (psiEquiv k (z, v)) = _
  rw [psiEquiv_apply]
  rfl

/-- The fixed equivalence `ℝ^{8+k} × ℝ ≅ ℝ⁹ × ℝ^k` through the `e₀`-splitting. -/
def blockLam (k : ℕ) :
    (EuclideanSpace ℝ (Fin (8 + k)) × ℝ) ≃ₗ[ℝ]
      (CofAtlas.E9 × EuclideanSpace ℝ (Fin k)) :=
  ((reEKInvEquiv k).prodCongr (LinearEquiv.refl ℝ ℝ)).trans
    ((tubeSplit k).trans (CofAtlas.sigma k).symm)

theorem blockLam_apply (k : ℕ) (w : EuclideanSpace ℝ (Fin (8 + k))) (c : ℝ) :
    blockLam k (w, c)
      = (CofAtlas.sigma k).symm (srcCastInv k (consCLM (k + 8) (c, reEKInv k w))) := by
  show (CofAtlas.sigma k).symm (tubeSplit k (reEKInvEquiv k w, c)) = _
  rw [reEKInvEquiv_apply, tubeSplit_apply]

/-- **The fixed constant** of the factorisation of the block determinant:
`blockP = blockLam ≫ blockZE` (an endomorphism of `ℝ^{8+k} × ℝ`). -/
def blockP (k : ℕ) :
    (EuclideanSpace ℝ (Fin (8 + k)) × ℝ) ≃ₗ[ℝ]
      (EuclideanSpace ℝ (Fin (8 + k)) × ℝ) :=
  (blockLam k).trans (blockZE k)

/-! ## The two identities of the factorisation -/

theorem coprod_eq_tubeSplit_comp_blockPhi (k : ℕ)
    (A : EuclideanSpace ℝ (Fin 8) →L[ℝ] EuclideanSpace ℝ (Fin (k + 8)))
    (W : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin (k + 8))) :
    ((collarB k A).coprod (srcOfSpatialCLM k ∘L W)).toLinearMap
      = (tubeSplit k).toLinearMap.comp (blockPhi k A W).toLinearMap := by
  apply LinearMap.ext
  intro p
  obtain ⟨z, v⟩ := p
  show (collarB k A z + (srcOfSpatialCLM k) (W v)) = (tubeSplit k) (blockPhi k A W (z, v))
  calc (collarB k A z + (srcOfSpatialCLM k) (W v))
      = tubeSplit k (A (tailCLM 8 z), z 0) + (srcOfSpatialCLM k) (W v) := by
        rw [collarB_eq_tubeSplit]
    _ = ((srcOfSpatialCLM k) (A (tailCLM 8 z)) + z 0 • (eZero : CofAtlas.ModN k))
          + (srcOfSpatialCLM k) (W v) := by rw [tubeSplit_eq]
    _ = ((srcOfSpatialCLM k) (A (tailCLM 8 z)) + (srcOfSpatialCLM k) (W v))
          + z 0 • (eZero : CofAtlas.ModN k) := by abel
    _ = (srcOfSpatialCLM k) (A (tailCLM 8 z) + W v)
          + z 0 • (eZero : CofAtlas.ModN k) := by rw [map_add]
    _ = tubeSplit k (A (tailCLM 8 z) + W v, z 0) := by rw [tubeSplit_eq]
    _ = tubeSplit k (blockPhi k A W (z, v)) := by rw [blockPhi_apply]

theorem blockPhi_eq (k : ℕ)
    (A : EuclideanSpace ℝ (Fin 8) →L[ℝ] EuclideanSpace ℝ (Fin (k + 8)))
    (W : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin (k + 8))) :
    (blockPhi k A W).toLinearMap
      = (LinearMap.prodMap
          ((reEKInv k).toLinearMap.comp ((blockM k A W).toLinearMap.comp
            (Work.Whitney.tcmSumLin 8 k).toLinearMap))
          (LinearMap.id : ℝ →ₗ[ℝ] ℝ)).comp (psiEquiv k).toLinearMap := by
  apply LinearMap.ext
  intro p
  obtain ⟨z, v⟩ := p
  show blockPhi k A W (z, v)
    = ((reEKInv k) (blockM k A W
        ((Work.Whitney.tcmSumLin 8 k) ((psiEquiv k) (z, v)).1)), ((psiEquiv k) (z, v)).2)
  rw [psiEquiv_apply, blockPhi_apply, blockM]
  show (A (tailCLM 8 z) + W v, z 0) = ((reEKInv k) ((reEK k) ((A.coprod W)
    ((Work.Whitney.tcmSumLin 8 k).symm (Work.Whitney.tcmSumLin 8 k (tailCLM 8 z, v))))), z 0)
  rw [show ((Work.Whitney.tcmSumLin 8 k).symm
      ((Work.Whitney.tcmSumLin 8 k) (tailCLM 8 z, v))) = (tailCLM 8 z, v) from
    (Work.Whitney.tcmSumLin 8 k).symm_apply_apply (tailCLM 8 z, v),
    ContinuousLinearMap.coprod_apply, reEKInv_reEK]


/-! ## The pair frame of a frame in the ambient model space -/

/-- The block frame of a pair `(A₀, W₀)` of frames in `ℝ^{8+k}` is the coordinate reading in the
pair frame (`Sig`). -/
theorem eq_Sig_of_coprod (k : ℕ)
    (A₀ : EuclideanSpace ℝ (Fin 8) →L[ℝ] EuclideanSpace ℝ (Fin (8 + k)))
    (W₀ : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin (8 + k))) :
    (A₀.coprod W₀).comp ((Work.Whitney.tcmSumLin 8 k).symm).toContinuousLinearMap
      = (Work.ThomBordism.KeyLocal.Sig
          (fun a : Fin 8 => A₀ (EuclideanSpace.single a (1 : ℝ)))
          (fun b : Fin k => W₀ (EuclideanSpace.single b (1 : ℝ)))).toContinuousLinearMap := by
  apply ContinuousLinearMap.ext
  intro z
  show (A₀.coprod W₀) ((Work.Whitney.tcmSumLin 8 k).symm z)
    = Work.ThomBordism.KeyLocal.Sig
        (fun a : Fin 8 => A₀ (EuclideanSpace.single a (1 : ℝ)))
        (fun b : Fin k => W₀ (EuclideanSpace.single b (1 : ℝ))) z
  rw [Work.ThomBordism.KeyLocal.Sig_apply, ContinuousLinearMap.coprod_apply,
    Work.ThomBordism.KeyLocal.combFrame_apply, Work.ThomBordism.KeyLocal.combFrame_apply,
    Work.ThomBordism.PontryaginThom.eucToFun_apply,
    Work.ThomBordism.PontryaginThom.eucToFun_apply]
  have hA := sum_smul_single ((Work.Whitney.tcmSumLin 8 k).symm z).1 A₀.toLinearMap
  have hB := sum_smul_single ((Work.Whitney.tcmSumLin 8 k).symm z).2 W₀.toLinearMap
  simp only [ContinuousLinearMap.coe_coe] at hA hB
  rw [← hA, ← hB]

/-- The endomorphism of `ℝ^{8+k}` of a pair of frames in `ℝ^{8+k}`. -/
def pairEnd (k : ℕ)
    (A₀ : EuclideanSpace ℝ (Fin 8) →L[ℝ] EuclideanSpace ℝ (Fin (8 + k)))
    (W₀ : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin (8 + k))) :
    EuclideanSpace ℝ (Fin (8 + k)) →L[ℝ] EuclideanSpace ℝ (Fin (8 + k)) :=
  (A₀.coprod W₀).comp ((Work.Whitney.tcmSumLin 8 k).symm).toContinuousLinearMap

theorem pairEnd_eq_Sig (k : ℕ)
    (A₀ : EuclideanSpace ℝ (Fin 8) →L[ℝ] EuclideanSpace ℝ (Fin (8 + k)))
    (W₀ : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin (8 + k))) :
    (pairEnd k A₀ W₀).toLinearMap
      = Work.ThomBordism.KeyLocal.Sig
          (fun a : Fin 8 => A₀ (EuclideanSpace.single a (1 : ℝ)))
          (fun b : Fin k => W₀ (EuclideanSpace.single b (1 : ℝ))) :=
  congrArg ContinuousLinearMap.toLinearMap (eq_Sig_of_coprod k A₀ W₀)

theorem det_pairEnd (k : ℕ)
    (A₀ : EuclideanSpace ℝ (Fin 8) →L[ℝ] EuclideanSpace ℝ (Fin (8 + k)))
    (W₀ : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin (8 + k))) :
    LinearMap.det (pairEnd k A₀ W₀).toLinearMap
      = (OrthFrame.pairMat (fun a : Fin 8 => A₀ (EuclideanSpace.single a (1 : ℝ)))
          (fun b : Fin k => W₀ (EuclideanSpace.single b (1 : ℝ)))).det := by
  rw [pairEnd_eq_Sig]
  exact Work.ThomBordism.KeyLocal.det_Sig _ _

/-- The block frame of the collapsed pair is the reindexing of the plain pair frame. -/
theorem blockM_eq_reEK_comp (k : ℕ)
    (δ : EuclideanSpace ℝ (Fin (8 + k)) →L[ℝ] EuclideanSpace ℝ (Fin (k + 8)))
    (A₀ : EuclideanSpace ℝ (Fin 8) →L[ℝ] EuclideanSpace ℝ (Fin (8 + k)))
    (W₀ : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin (8 + k))) :
    blockM k (δ.comp A₀) (δ.comp W₀)
      = ((reEK k).comp δ).comp (pairEnd k A₀ W₀) := by
  apply ContinuousLinearMap.ext
  intro z
  show (reEK k) (((δ.comp A₀).coprod (δ.comp W₀)) ((Work.Whitney.tcmSumLin 8 k).symm z))
    = (reEK k) (δ ((A₀.coprod W₀) ((Work.Whitney.tcmSumLin 8 k).symm z)))
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.coprod_apply, map_add]

/-! ## The determinant sign of `reEK ∘ dthetaInv` -/

/-- **The determinant sign of `reEK ∘ dthetaInv`** at a point of the image of the block model is
`+1`: `dthetaInv` is the inverse of the block model `theta`, whose `reEKInv`-reindexed derivative is
positive (`Work.ThomBordism.LeadChapter.thetaAux_det_dthetaEndo_pos`). -/
theorem det_reEK_comp_dthetaInv_pos (G : GenuineTubeGeometry k D ι Fam) (m k₀ j₀ : ℕ)
    (v : EuclideanSpace ℝ (Fin (k + 8))) (hR : 0 < G.R) :
    0 < LinearMap.det ((reEK k).comp (dthetaInv G m k₀ j₀ (theta G m k₀ j₀ v))).toLinearMap := by
  set δ : EuclideanSpace ℝ (Fin (8 + k)) →L[ℝ] EuclideanSpace ℝ (Fin (k + 8)) :=
    dthetaInv G m k₀ j₀ (theta G m k₀ j₀ v) with hδ
  have hconj : LinearMap.det ((reEK k).comp δ).toLinearMap
      = LinearMap.det ((δ.comp (reEK k)).toLinearMap) := by
    have h := LinearMap.det_conj ((reEK k).comp δ).toLinearMap (reEKInvEquiv k)
    rw [show ((reEKInvEquiv k) : EuclideanSpace ℝ (Fin (8 + k)) →ₗ[ℝ]
          EuclideanSpace ℝ (Fin (k + 8)))
        ∘ₗ ((reEK k).comp δ).toLinearMap ∘ₗ ((reEKInvEquiv k).symm :
          EuclideanSpace ℝ (Fin (k + 8)) →ₗ[ℝ] EuclideanSpace ℝ (Fin (8 + k)))
        = (δ.comp (reEK k)).toLinearMap from ?_] at h
    exact h.symm
    apply LinearMap.ext
    intro x
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, ContinuousLinearMap.coe_coe,
      ContinuousLinearMap.toLinearMap_comp, reEKInvEquiv_apply, reEKInvEquiv_symm_apply,
      reEKInv_reEK]
  rw [hconj]
  have h4 : δ.comp (dtheta G m k₀ j₀ v) = 1 := by
    rw [hδ]; exact (thetaInvAux G m k₀ j₀ hR).2.2.2.1 v
  have hsplit : ((δ.comp (reEK k)).comp (dthetaEndo G m k₀ j₀ v))
      = δ.comp (dtheta G m k₀ j₀ v) := by
    apply ContinuousLinearMap.ext
    intro x
    show δ ((reEK k) ((reEKInv k) ((dtheta G m k₀ j₀ v) x))) = δ ((dtheta G m k₀ j₀ v) x)
    rw [reEK_reEKInv]
  have hcomp : ((δ.comp (reEK k)).comp (dthetaEndo G m k₀ j₀ v)) = 1 := by
    rw [hsplit]; exact h4
  have hfg : LinearMap.det (((δ.comp (reEK k)).comp (dthetaEndo G m k₀ j₀ v)).toLinearMap)
      = 1 := by
    rw [hcomp]
    exact LinearMap.det_id
  rw [ContinuousLinearMap.toLinearMap_comp] at hfg
  rw [LinearMap.det_comp] at hfg
  have hb : 0 < LinearMap.det (dthetaEndo G m k₀ j₀ v).toLinearMap :=
    (thetaInvAux G m k₀ j₀ hR).2.2.2.2 v
  by_contra hle
  rw [not_lt] at hle
  have hprod : LinearMap.det ((δ.comp (reEK k)).toLinearMap)
      * LinearMap.det (dthetaEndo G m k₀ j₀ v).toLinearMap ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg hle (le_of_lt hb)
  linarith

/-! ## Determinant helpers -/

/-- `det (f ∘ e⁻¹) = det (e⁻¹ ∘ f)` for a linear map `f : V → W` and a linear equivalence
`e : V ≃ W`. -/
theorem det_comp_symm {V W : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
    (f : V →ₗ[ℝ] W) (e : V ≃ₗ[ℝ] W) :
    LinearMap.det (f ∘ₗ (e.symm : W →ₗ[ℝ] V))
      = LinearMap.det ((e.symm : W →ₗ[ℝ] V) ∘ₗ f) := by
  have hX : ((e : V →ₗ[ℝ] W) ∘ₗ ((e.symm : W →ₗ[ℝ] V) ∘ₗ f) ∘ₗ (e.symm : W →ₗ[ℝ] V))
      = f ∘ₗ (e.symm : W →ₗ[ℝ] V) := by
    apply LinearMap.ext
    intro x
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
  have h := LinearMap.det_conj ((e.symm : W →ₗ[ℝ] V) ∘ₗ f) e
  rw [hX] at h
  exact h

/-! ## The factorisation of the block determinant -/

set_option maxHeartbeats 6400000 in
theorem blockDet_collarB_factor (k : ℕ)
    (A : EuclideanSpace ℝ (Fin 8) →L[ℝ] EuclideanSpace ℝ (Fin (k + 8)))
    (W : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin (k + 8))) :
    blockDet k (collarB k A) (srcOfSpatialCLM k ∘L W)
      = LinearMap.det (blockP k).toLinearMap * LinearMap.det (blockM k A W).toLinearMap := by
  have h1 := coprod_eq_tubeSplit_comp_blockPhi k A W
  have h2 := blockPhi_eq k A W
  have hconj : ↑(CofAtlas.sigma k).symm ∘ₗ
        ((tubeSplit k).toLinearMap ∘ₗ ((LinearMap.prodMap
          ((reEKInv k).toLinearMap.comp ((blockM k A W).toLinearMap.comp
            (Work.Whitney.tcmSumLin 8 k).toLinearMap))
          (LinearMap.id : ℝ →ₗ[ℝ] ℝ)).comp (psiEquiv k).toLinearMap))
      = (blockLam k).toLinearMap ∘ₗ
        ((LinearMap.prodMap (blockM k A W).toLinearMap (LinearMap.id : ℝ →ₗ[ℝ] ℝ)).comp
          (blockZE k).toLinearMap) := by
    apply LinearMap.ext
    intro p
    obtain ⟨z, v⟩ := p
    simp only [LinearMap.comp_apply, LinearMap.prodMap_apply, LinearMap.id_apply,
      LinearEquiv.coe_coe, blockZE_apply, blockLam_apply, psiEquiv_apply, tubeSplit_apply,
      blockM_tcmSumLin, reEKInv_reEK, LinearEquiv.symm_apply_apply]
    rfl
  rw [blockDet, h1, h2, det_comp_symm _ (CofAtlas.sigma k)]
  rw [hconj]
  rw [← LinearMap.det_conj ((blockLam k).toLinearMap ∘ₗ
      ((LinearMap.prodMap (blockM k A W).toLinearMap (LinearMap.id : ℝ →ₗ[ℝ] ℝ)).comp
        (blockZE k).toLinearMap)) (blockZE k)]
  rw [show (↑(blockZE k) ∘ₗ ((blockLam k).toLinearMap ∘ₗ
        ((LinearMap.prodMap (blockM k A W).toLinearMap (LinearMap.id : ℝ →ₗ[ℝ] ℝ)).comp
          (blockZE k).toLinearMap)) ∘ₗ ↑(blockZE k).symm)
      = (blockP k).toLinearMap ∘ₗ
        (LinearMap.prodMap (blockM k A W).toLinearMap (LinearMap.id : ℝ →ₗ[ℝ] ℝ)) from by
    apply LinearMap.ext
    intro p
    simp only [LinearMap.comp_apply, LinearMap.prodMap_apply, LinearMap.id_apply,
      LinearEquiv.coe_coe, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply, blockP]]
  rw [LinearMap.det_comp, LinearMap.det_prodMap, LinearMap.det_id, mul_one]

/-! ## The sign of the block determinant in terms of `pairSign` -/

theorem sign_blockDet_collarB (k : ℕ)
    (δ : EuclideanSpace ℝ (Fin (8 + k)) →L[ℝ] EuclideanSpace ℝ (Fin (k + 8)))
    (A₀ : EuclideanSpace ℝ (Fin 8) →L[ℝ] EuclideanSpace ℝ (Fin (8 + k)))
    (W₀ : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin (8 + k)))
    (hΔ : Real.sign (LinearMap.det ((reEK k).comp δ).toLinearMap) = 1) :
    Real.sign (blockDet k (collarB k (δ.comp A₀)) (srcOfSpatialCLM k ∘L (δ.comp W₀)))
      = Real.sign (LinearMap.det (blockP k).toLinearMap)
        * OrthFrame.pairSign (fun a : Fin 8 => A₀ (EuclideanSpace.single a (1 : ℝ)))
            (fun b : Fin k => W₀ (EuclideanSpace.single b (1 : ℝ))) := by
  rw [blockDet_collarB_factor k (δ.comp A₀) (δ.comp W₀), blockM_eq_reEK_comp]
  rw [ContinuousLinearMap.toLinearMap_comp, LinearMap.det_comp, det_pairEnd]
  rw [real_sign_mul, real_sign_mul, hΔ, one_mul]
  rfl


/-! ## The assembly of the target theorem -/

set_option maxHeartbeats 6400000 in
theorem tubeDetDetSign {k : ℕ} (hk : 1 ≤ k)
    {D : Work.ThomBordism.PontryaginThom.ThomTarget k} {ι : Type} [Fintype ι]
    {Fam : ι → Work.ThomBordism.Man8}
    (G : Work.PTGeometric.GenuineTubeGeometry k D ι Fam) (m : ℕ)
    (hpow : (∏ i, Work.PTGeometric.tubeAlpha (G.rep i)) ^ m = 1)
    (h : Work.ThomBordism.LeadChapter.BdryId G m hpow)
    (hspec : Work.ThomBordism.LeadChapter.BdryIdSpec G m hpow h) :
    ∃ ε : ℝ, (ε = 1 ∨ ε = -1) ∧
      ∀ (a : Fin m × ι) (i : Work.ThomBordism.FrameSigns.ChartIdx (Fam a.2))
        (y : (Fam a.2).pt) (hy : y ∈ Work.ThomBordism.FrameSigns.src (Fam a.2) i)
        (z : Work.ThomBordism.CofAtlas.E9)
        (hz : Work.PTGeometric.tail 8 z =
          (Work.ThomBordism.FrameSigns.chartOf (Fam a.2) i).1 y)
        (hz0 : 0 < z 0) (hz12 : z 0 ≤ 1 / 2)
        (hne : Work.ThomBordism.LeadChapter.srcHf G m hpow
          (Work.ThomBordism.LeadChapter.collarPiece G m hpow h a i z) ≠ D.t₀),
        0 < ε * Work.ThomBordism.FrameSigns.frameSign (Fam a.2) i y *
          Work.ThomBordism.LeadChapter.blockDet k
            (Work.ThomBordism.LeadChapter.collarB k
              (Work.ThomBordism.LeadChapter.spatialDeriv G m a i y))
            (Work.ThomBordism.LeadChapter.frameN G m hpow h a i y z hne) := by
  by_cases hneN : Nonempty (Fin m × ι)
  swap
  · refine ⟨1, Or.inl rfl, ?_⟩
    intro a
    exact absurd ⟨a⟩ hneN
  obtain ⟨a₀⟩ := hneN
  haveI : Nonempty ι := ⟨a₀.2⟩
  obtain ⟨s, hs, hunif⟩ := Work.ThomBordism.gaussBranch_uniform_of_universal (k := k) hk G
  choose ND Gc hgm hpt hproj hvec hgauss using hunif
  have hdPne : LinearMap.det (blockP k).toLinearMap ≠ 0 := by
    intro h0
    have hker := (LinearMap.det_eq_zero_iff_ker_ne_bot (f := (blockP k).toLinearMap)).mp h0
    exact hker (by rw [LinearMap.ker_eq_bot]; exact (blockP k).injective)
  have hdetP : Real.sign (LinearMap.det (blockP k).toLinearMap) = 1
      ∨ Real.sign (LinearMap.det (blockP k).toLinearMap) = -1 := by
    rcases lt_trichotomy (LinearMap.det (blockP k).toLinearMap) 0 with h | h | h
    · exact Or.inr (Real.sign_of_neg h)
    · exact absurd h hdPne
    · exact Or.inl (Real.sign_of_pos h)
  refine ⟨Real.sign (LinearMap.det (blockP k).toLinearMap) * (if s = 1 then (1 : ℝ) else -1),
    ?_, ?_⟩
  · rcases hdetP with h | h <;> rcases hs with hs | hs
    · left; rw [h, if_pos hs, mul_one]
    · right; rw [h, if_neg (by omega), mul_neg_one]
    · right; rw [h, if_pos hs]; ring
    · left; rw [h, if_neg (by omega)]; ring
  · intro a i y hy z hz hz0 hz12 hne
    set δ : EuclideanSpace ℝ (Fin (8 + k)) →L[ℝ] EuclideanSpace ℝ (Fin (k + 8)) :=
      dthetaInv G m (a.1 : ℕ) ((Fintype.equivFin ι a.2 : ℕ)) ((G.emb a.2).e y) with hδ
    set A₀ : EuclideanSpace ℝ (Fin 8) →L[ℝ] EuclideanSpace ℝ (Fin (8 + k)) :=
      fderiv ℝ (Work.ThomBordism.PontryaginThom.chartRep (G.emb a.2).e
        (Work.ThomBordism.FrameSigns.chartOf (Fam a.2) i))
        ((Work.ThomBordism.FrameSigns.chartOf (Fam a.2) i).1 y) with hA₀
    set W₀ : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin (8 + k)) :=
      (Work.PTGeometric.projEuc k G.mU G.hmU).comp
        (ogFrameCLM (G.gauss ⟨srcHf G m hpow (collarPiece G m hpow h a i z), hne⟩)) with hW₀
    set t : Fin (8 + k) → Set.Icc (0 : ℝ) 1 :=
      reIdx k (clipPt k (cZero k) (cOne k) (a.1 : ℕ) ((Fintype.equivFin ι a.2 : ℕ))
        (srcOfSpatial k (xiCoord G m hpow h a y))) with ht
    have hval := srcHf_collarPiece_eq_alphaV G m hpow h hspec a i y hy z hz hz12
    have htube := cubeToEuc_clipPt_collarPiece G m hpow h hspec a i y
    rw [← ht] at hval htube
    have hopen : Work.Tubular.cubeToEuc (8 + k) G.R t ∈ (G.chart a.2).openTube := by
      rw [htube]; exact (G.chart a.2).mem_openTube y
    obtain ⟨hne'', hgauss''⟩ := hgauss a.2 t hopen
    have hfoot : ((G.chart a.2).inv ((G.emb a.2).e y)).1.1 = y :=
      Work.ThomBordism.KeyLocal.proj_inv_embed_tcfd (G.emb a.2) (G.chart a.2) y
    -- the oriented Gauss plane of the collar point is the tied padded Gauss plane
    have hsub : (⟨srcHf G m hpow (collarPiece G m hpow h a i z), hne⟩ : {x : D.T // x ≠ D.t₀})
        = ⟨Work.Tubular.alphaV (G.chart a.2) G.hR (G.hbox a.2) D.t₀ (G.J a.2) (G.hJ a.2)
            (G.g a.2) (G.hg a.2) t, hne''⟩ := Subtype.ext hval
    have hGauss : G.gauss ⟨srcHf G m hpow (collarPiece G m hpow h a i z), hne⟩
        = (if s = 1 then id else Work.ThomBordism.Grassmann.ogFlip k G.mU)
            (Work.ThomBordism.padGaussFunM (G.emb a.2) (ND a.2) G.mU G.hmU y) := by
      rw [hsub, hgauss'', htube, hfoot]
    -- the positivity of the reindexed `dthetaInv`
    have hΔ : Real.sign (LinearMap.det ((reEK k).comp δ).toLinearMap) = 1 := by
      rw [Real.sign_of_pos]
      rw [hδ]
      have hθ := Work.ThomBordism.LeadChapter.theta_xiCoord_eq_emb G m hpow h hspec a y
      have hpos := det_reEK_comp_dthetaInv_pos G m (a.1 : ℕ) ((Fintype.equivFin ι a.2 : ℕ))
        (xiCoord G m hpow h a y) (Work.PTGeometric.tube_radius_pos (G := G) a.2)
      rwa [hθ] at hpos
    -- the sign of the block determinant
    have hsign := sign_blockDet_collarB k δ A₀ W₀ hΔ
    -- the pair sign of the chart frame and the Gauss frame
    have hW₀apply : (fun b : Fin k => W₀ (EuclideanSpace.single b 1))
        = (fun b : Fin k => Work.PTGeometric.projEuc k G.mU G.hmU
            (ogFrameCLM (G.gauss ⟨srcHf G m hpow (collarPiece G m hpow h a i z), hne⟩)
              (EuclideanSpace.single b 1))) := rfl
    have hframe1 : (fun a' : Fin 8 => A₀ (EuclideanSpace.single a' 1))
        = Work.ThomBordism.PontryaginThom.frame (G.emb a.2).e
            (Work.ThomBordism.FrameSigns.chartOf (Fam a.2) i) y := rfl
    have hpS : OrthFrame.pairSign (fun a' : Fin 8 => A₀ (EuclideanSpace.single a' 1))
        (fun b : Fin k => W₀ (EuclideanSpace.single b 1))
        = (if s = 1 then (1 : ℝ) else -1) * Work.ThomBordism.FrameSigns.frameSign (Fam a.2) i y := by
      show Real.sign (OrthFrame.pairMat (fun a' : Fin 8 => A₀ (EuclideanSpace.single a' 1))
        (fun b : Fin k => W₀ (EuclideanSpace.single b 1))).det = _
      by_cases hs1 : s = 1
      · have hGauss1 : G.gauss ⟨srcHf G m hpow (collarPiece G m hpow h a i z), hne⟩
            = Work.ThomBordism.padGaussFunM (G.emb a.2) (ND a.2) G.mU G.hmU y := by
          rw [hGauss, if_pos hs1]; rfl
        have hW'' : (fun b : Fin k => W₀ (EuclideanSpace.single b 1))
            = (fun b : Fin k => Work.PTGeometric.projEuc k G.mU G.hmU
                (ogFrameCLM (Work.ThomBordism.padGaussFunM (G.emb a.2) (ND a.2) G.mU G.hmU y)
                  (EuclideanSpace.single b 1))) := by
          rw [hW₀apply, hGauss1]
        rw [hframe1, hW'', Work.ThomBordism.tubePairSignGauss (V := Fam a.2) (k := k) hk
          (G.emb a.2) (ND a.2) G.mU G.hmU i y hy, if_pos hs1, one_mul]
      · have hGauss2 : G.gauss ⟨srcHf G m hpow (collarPiece G m hpow h a i z), hne⟩
            = Work.ThomBordism.Grassmann.ogFlip k G.mU
                (Work.ThomBordism.padGaussFunM (G.emb a.2) (ND a.2) G.mU G.hmU y) := by
          rw [hGauss, if_neg hs1]
        have hW'' : (fun b : Fin k => W₀ (EuclideanSpace.single b 1))
            = (fun b : Fin k => Work.PTGeometric.projEuc k G.mU G.hmU
                (ogFrameCLM (Work.ThomBordism.Grassmann.ogFlip k G.mU
                    (Work.ThomBordism.padGaussFunM (G.emb a.2) (ND a.2) G.mU G.hmU y))
                  (EuclideanSpace.single b 1))) := by
          rw [hW₀apply, hGauss2]
        rw [hframe1, hW'', Work.ThomBordism.tubePairSignGaussFlip (V := Fam a.2) (k := k) hk
          (G.emb a.2) (ND a.2) G.mU G.hmU i y hy, if_neg hs1]
        ring
    -- the final sign identity
    have hfin : Real.sign (blockDet k (collarB k (spatialDeriv G m a i y))
          (frameN G m hpow h a i y z hne))
        = (Real.sign (LinearMap.det (blockP k).toLinearMap) * (if s = 1 then (1 : ℝ) else -1))
          * Work.ThomBordism.FrameSigns.frameSign (Fam a.2) i y := by
      rw [show spatialDeriv G m a i y = δ.comp A₀ from rfl,
        show frameN G m hpow h a i y z hne = (srcOfSpatialCLM k).comp (δ.comp W₀) from rfl,
        hsign, hpS]
      ring
    -- positivity
    have hfs : Work.ThomBordism.FrameSigns.frameSign (Fam a.2) i y = 1
        ∨ Work.ThomBordism.FrameSigns.frameSign (Fam a.2) i y = -1 :=
      Work.ThomBordism.FrameSigns.frameSign_eq_one_or_neg_one (Fam a.2) i y
    have hεne : Real.sign (LinearMap.det (blockP k).toLinearMap) * (if s = 1 then (1 : ℝ) else -1)
        ≠ 0 := by
      have h1 : Real.sign (LinearMap.det (blockP k).toLinearMap) = 1
          ∨ Real.sign (LinearMap.det (blockP k).toLinearMap) = -1 := hdetP
      rcases h1 with h1 | h1 <;> rcases hs with hs | hs
      · rw [h1, if_pos hs]; norm_num
      · rw [h1, if_neg (by omega)]; norm_num
      · rw [h1, if_pos hs]; norm_num
      · rw [h1, if_neg (by omega)]; norm_num
    have hbne : blockDet k (collarB k (spatialDeriv G m a i y))
        (frameN G m hpow h a i y z hne) ≠ 0 := by
      intro h0
      have h1 : Real.sign (blockDet k (collarB k (spatialDeriv G m a i y))
          (frameN G m hpow h a i y z hne)) = 0 := by rw [h0, Real.sign_zero]
      rw [hfin] at h1
      rcases hfs with hfs | hfs
      · rw [hfs, mul_one] at h1
        exact hεne h1
      · rw [hfs, mul_neg, mul_one] at h1
        exact hεne (neg_eq_zero.mp h1)
    have hpos := Real.sign_mul_pos_of_ne_zero
      (blockDet k (collarB k (spatialDeriv G m a i y)) (frameN G m hpow h a i y z hne)) hbne
    rw [hfin] at hpos
    linarith [hpos]

end

end Work.ThomBordism.LeadChapter
