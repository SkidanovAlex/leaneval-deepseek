import Mathlib
import Submission.Work.ThomBordism.LeadChapter.TubeDetDefs
import Submission.Work.ThomBordism.LeadChapter.ogFrameSO
import Submission.Work.ThomBordism.padGaussFunM_eq_of_normalData

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option linter.unusedVariables false

/-!
# The pair sign of the tangent frame against the *orientation reversed* Gauss normal frame

`Work.ThomBordism.sigmaTelescope_gauss` and `Work.ThomBordism.padGaussND_pairSign_tanFrame_gframe`
identify the pair sign of the chart tangent frame of an embedded `8`-manifold against the
`σ`-corrected Gauss normal frame `Work.ThomBordism.Gauss.gframe` with the tangent frame sign
`Work.ThomBordism.FrameSigns.frameSign`.

Here we compute the same pair sign for the **orientation reversed** Gauss frame, i.e. for the frame
read off the point `ogFlip (padGaussFunM …)` of the oriented Grassmannian.  Reversing the
orientation of the plane multiplies the frame by a matrix of determinant `-1`
(`Work.ThomBordism.LeadChapter.ogFrameSO`, second half), so the pair sign is exactly the negative of
the frame sign.

The mathematical content is the second half of `LeadChapter.ogFrameSO` (the orientation reversing
change of frame of `ogFrameCLM`) combined with the block determinant rule
`Work.ThomBordism.OrthFrame.sign_det_pairMat`.
-/

namespace Work.ThomBordism

open Work.ThomBordism.PontryaginThom Work.ThomBordism.Grassmann

noncomputable section

open scoped BigOperators

variable {k m : ℕ}

/-- Evaluating the frame map `∑ b, proj_b ⊗ F b` of `ogFrameCLM` on a vector. -/
theorem frameSum_apply (F : Fin k → EuclideanSpace ℝ (Fin (k + m)))
    (u : EuclideanSpace ℝ (Fin k)) :
    (∑ b : Fin k, (EuclideanSpace.proj b : EuclideanSpace ℝ (Fin k) →L[ℝ] ℝ).smulRight (F b)) u
      = ∑ b : Fin k, u b • F b := by
  rw [sum_apply]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [ContinuousLinearMap.smulRight_apply]
  rfl

/-- The standard basis vector of `ℝ^k` in the form used by `ogFrameCLM`. -/
theorem basisK_apply (k : ℕ) (i : Fin k) :
    ((EuclideanSpace.basisFun (Fin k) ℝ).toBasis) i = EuclideanSpace.single i 1 := by
  simp only [OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply]

/-- **The frame of `ogFlip Γ` is the frame of `Γ` acted on by a matrix of determinant `-1`.**
This is the `ogFrameCLM` form of the second half of `Work.ThomBordism.LeadChapter.ogFrameSO`. -/
theorem exists_frameAct_ogFlip (hk : 0 < k)
    (F : Fin k → EuclideanSpace ℝ (Fin (k + m))) (hF : Orthonormal ℝ F)
    (π : EuclideanSpace ℝ (Fin (k + m)) →L[ℝ] EuclideanSpace ℝ (Fin (8 + k))) :
    ∃ M : Matrix (Fin k) (Fin k) ℝ, M.det = -1 ∧
      (fun b => π (LeadChapter.ogFrameCLM (ogFlip k m (ogMk k m ⟨F, hF⟩))
          (EuclideanSpace.single b 1)))
        = Gauss.frameAct M (fun b => π (F b)) := by
  obtain ⟨⟨e, he1, -, he3⟩, ⟨e', he'1, he'2⟩⟩ := LeadChapter.ogFrameSO hk F hF
  set L : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin k) := e.comp e' with hL
  refine ⟨LinearMap.toMatrix ((EuclideanSpace.basisFun (Fin k) ℝ).toBasis)
      ((EuclideanSpace.basisFun (Fin k) ℝ).toBasis) L.toLinearMap, ?_, ?_⟩
  · have hLto : L.toLinearMap = e.toLinearMap.comp e'.toLinearMap := by
      rw [hL, ContinuousLinearMap.toLinearMap_comp]
    rw [LinearMap.det_toMatrix, hLto, LinearMap.det_comp, he1, he'1, one_mul]
  · funext b
    rw [he'2, he3, ContinuousLinearMap.comp_assoc, ← hL]
    simp only [ContinuousLinearMap.comp_apply]
    rw [show (∑ b : Fin k, (EuclideanSpace.proj b : EuclideanSpace ℝ (Fin k) →L[ℝ] ℝ).smulRight
          (F b)) (L (EuclideanSpace.single b 1))
        = ∑ b' : Fin k, (L (EuclideanSpace.single b 1)) b' • F b' from by
      rw [sum_apply]
      exact Finset.sum_congr rfl fun b' _ => by rw [ContinuousLinearMap.smulRight_apply]; rfl]
    show π (∑ b', (L (EuclideanSpace.single b 1)) b' • F b') = ∑ b', _ • π (F b')
    rw [map_sum]
    refine Finset.sum_congr rfl fun b' _ => ?_
    rw [map_smul]
    rw [show (L (EuclideanSpace.single b 1)) b'
        = (LinearMap.toMatrix ((EuclideanSpace.basisFun (Fin k) ℝ).toBasis)
            ((EuclideanSpace.basisFun (Fin k) ℝ).toBasis) L.toLinearMap) b' b from by
      rw [LinearMap.toMatrix_apply, basisK_apply]
      rfl]

/-- **The pair sign against the orientation reversed Gauss frame is the negative frame sign.**
The frame of `ogFlip (ogMk ⟨F, hF⟩)` is `π F` acted on by a matrix of determinant `-1`
(`exists_frameAct_ogFlip`), so the block determinant rule
`Work.ThomBordism.OrthFrame.sign_det_pairMat` flips the sign. -/
theorem pairSign_ogFlip_projEuc (hk : 0 < k)
    (P : Fin 8 → EuclideanSpace ℝ (Fin (8 + k)))
    (F : Fin k → EuclideanSpace ℝ (Fin (k + m))) (hF : Orthonormal ℝ F)
    (π : EuclideanSpace ℝ (Fin (k + m)) →L[ℝ] EuclideanSpace ℝ (Fin (8 + k)))
    (hdet : (OrthFrame.pairMat P (fun b => π (F b))).det ≠ 0) :
    OrthFrame.pairSign P (fun b => π (LeadChapter.ogFrameCLM
        (ogFlip k m (ogMk k m ⟨F, hF⟩)) (EuclideanSpace.single b 1)))
      = - OrthFrame.pairSign P (fun b => π (F b)) := by
  obtain ⟨M, hMdet, hMframe⟩ := exists_frameAct_ogFlip hk F hF π
  have hMdet_ne : M.det ≠ 0 := by rw [hMdet]; norm_num
  have hC : ∀ a : Fin 8, P a = ∑ a', (1 : Matrix (Fin 8) (Fin 8) ℝ) a' a • P a' :=
    fun a => (congrFun (Gauss.frameAct_one P) a).symm
  have hMrel : ∀ b : Fin k,
      (fun b => π (LeadChapter.ogFrameCLM (ogFlip k m (ogMk k m ⟨F, hF⟩))
        (EuclideanSpace.single b 1))) b
        = ∑ b', M b' b • (fun b => π (F b)) b' :=
    fun b => by
      rw [hMframe]
      rfl
  have hmain := OrthFrame.sign_det_pairMat hC hMrel hdet (by rw [Matrix.det_one]; norm_num)
    hMdet_ne
  have hbb : Real.sign (OrthFrame.pairMat P (fun b => π (F b))).det
      * Real.sign (OrthFrame.pairMat P (fun b => π (F b))).det = 1 :=
    OrthFrame.sign_mul_self_of_ne_zero hdet
  have hmain' : Real.sign (OrthFrame.pairMat P
        (fun b => π (LeadChapter.ogFrameCLM (ogFlip k m (ogMk k m ⟨F, hF⟩))
          (EuclideanSpace.single b 1)))).det
        * Real.sign (OrthFrame.pairMat P (fun b => π (F b))).det = -1 := by
    rw [hmain, Matrix.det_one, Real.sign_one, hMdet,
      Real.sign_of_neg (show (-1 : ℝ) < 0 by norm_num), one_mul]
  show Real.sign (OrthFrame.pairMat P
      (fun b => π (LeadChapter.ogFrameCLM (ogFlip k m (ogMk k m ⟨F, hF⟩))
        (EuclideanSpace.single b 1)))).det
      = - Real.sign (OrthFrame.pairMat P (fun b => π (F b))).det
  calc Real.sign (OrthFrame.pairMat P
        (fun b => π (LeadChapter.ogFrameCLM (ogFlip k m (ogMk k m ⟨F, hF⟩))
          (EuclideanSpace.single b 1)))).det
      = Real.sign (OrthFrame.pairMat P
          (fun b => π (LeadChapter.ogFrameCLM (ogFlip k m (ogMk k m ⟨F, hF⟩))
            (EuclideanSpace.single b 1)))).det
          * (Real.sign (OrthFrame.pairMat P (fun b => π (F b))).det
            * Real.sign (OrthFrame.pairMat P (fun b => π (F b))).det) := by
        rw [hbb, mul_one]
    _ = (Real.sign (OrthFrame.pairMat P
          (fun b => π (LeadChapter.ogFrameCLM (ogFlip k m (ogMk k m ⟨F, hF⟩))
            (EuclideanSpace.single b 1)))).det
          * Real.sign (OrthFrame.pairMat P (fun b => π (F b))).det)
          * Real.sign (OrthFrame.pairMat P (fun b => π (F b))).det := by ring
    _ = -1 * Real.sign (OrthFrame.pairMat P (fun b => π (F b))).det := by rw [hmain']
    _ = - Real.sign (OrthFrame.pairMat P (fun b => π (F b))).det := by ring

theorem tubePairSignGaussFlip {k : ℕ} (hk : 1 ≤ k) {V : Work.ThomBordism.Man8}
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k))
    (ND : Work.ThomBordism.PontryaginThom.NormalData V k E.e)
    (mU : ℕ) (hmU : 8 ≤ mU)
    (i : Work.ThomBordism.FrameSigns.ChartIdx V) (x : V.pt)
    (hx : x ∈ Work.ThomBordism.FrameSigns.src V i) :
    Real.sign (Work.ThomBordism.OrthFrame.pairMat
      (Work.ThomBordism.PontryaginThom.frame E.e (Work.ThomBordism.FrameSigns.chartOf V i) x)
      (fun b : Fin k => Work.PTGeometric.projEuc k mU hmU
        (Work.ThomBordism.LeadChapter.ogFrameCLM
          (Work.ThomBordism.Grassmann.ogFlip k mU
            (Work.ThomBordism.padGaussFunM E ND mU hmU x))
          (EuclideanSpace.single b 1)))).det
      = - Work.ThomBordism.FrameSigns.frameSign V i x := by
  classical
  have hk0 : 0 < k := by omega
  have hx₀ : x ∈ ND.D.baseSet (ND.D.indexAt x) := ND.D.mem_baseSet_at x
  have hi₀src : x ∈ (coverChart (ND.D.indexAt x)).1.source :=
    ND.baseSet_sub (ND.D.indexAt x).1 (ND.D.indexAt x).2 x hx₀
  have hForth : Orthonormal ℝ (padGFrameM E ND mU hmU (ND.D.indexAt x) x) :=
    padGFrameM_orthonormal E ND mU hmU (ND.D.indexAt x) hx₀
  -- the normal frame of the statement
  set Nm : Fin k → EuclideanSpace ℝ (Fin (8 + k)) := fun b =>
    Work.PTGeometric.projEuc k mU hmU
      (Work.ThomBordism.LeadChapter.ogFrameCLM
        (Work.ThomBordism.Grassmann.ogFlip k mU
          (Work.ThomBordism.padGaussFunM E ND mU hmU x))
        (EuclideanSpace.single b 1)) with hNm
  -- the projected padded Gauss frame is the corrected normal frame
  have hfun : (fun b : Fin k =>
        Work.PTGeometric.projEuc k mU hmU (padGFrameM E ND mU hmU (ND.D.indexAt x) x b))
      = Gauss.gframe E ND (ND.D.indexAt x) x := by
    funext b
    show Work.PTGeometric.projEuc k mU hmU
      (Work.ThomBordism.padIsomM k mU hmU (Gauss.gframe E ND (ND.D.indexAt x) x b)) = _
    rw [Work.ThomBordism.padIsomM_apply, Work.PTGeometric.projEuc_padEuc]
  have hdet : (OrthFrame.pairMat (tanFrame E (ND.D.indexAt x) x)
      (fun b : Fin k =>
        Work.PTGeometric.projEuc k mU hmU (padGFrameM E ND mU hmU (ND.D.indexAt x) x b))).det
      ≠ 0 := by
    rw [hfun]
    exact padGaussND_pairMat_gframe_det_ne_zero hk E ND (ND.D.indexAt x) hx₀
  -- Step A: the orientation reversal flips the pair sign
  have hA : OrthFrame.pairSign (tanFrame E (ND.D.indexAt x) x) Nm
      = - OrthFrame.pairSign (tanFrame E (ND.D.indexAt x) x)
          (fun b : Fin k =>
            Work.PTGeometric.projEuc k mU hmU (padGFrameM E ND mU hmU (ND.D.indexAt x) x b)) :=
    pairSign_ogFlip_projEuc (k := k) (m := mU) hk0
      (tanFrame E (ND.D.indexAt x) x) (padGFrameM E ND mU hmU (ND.D.indexAt x) x) hForth
      (Work.PTGeometric.projEuc k mU hmU) hdet
  have hB : OrthFrame.pairSign (tanFrame E (ND.D.indexAt x) x)
      (fun b : Fin k =>
        Work.PTGeometric.projEuc k mU hmU (padGFrameM E ND mU hmU (ND.D.indexAt x) x b))
      = FrameSigns.frameSign V (ND.D.indexAt x).1 x := by
    rw [hfun]
    exact padGaussND_pairSign_tanFrame_gframe E ND hk (ND.D.indexAt x) hx₀
  have hCp : OrthFrame.pairSign (tanFrame E (ND.D.indexAt x) x) Nm
      = - FrameSigns.frameSign V (ND.D.indexAt x).1 x := by
    rw [hA, hB]
  -- Step B: the change of chart
  have hi₁src : x ∈ (coverChart (i, (ND.D.indexAt x).2)).1.source := hx
  have hi₀src' : x ∈ FrameSigns.src V (ND.D.indexAt x).1 := hi₀src
  obtain ⟨C, hCrel, hCdet, hCeq⟩ :=
    padGaussND_tanFrame_change_source E (ND.D.indexAt x) (i, (ND.D.indexAt x).2) hi₀src hi₁src
  have hδ := FrameSigns.frameSign_mul V (ND.D.indexAt x).1 i hi₀src' hx
  have hCsign : Real.sign C.det
      = FrameSigns.frameSign V (ND.D.indexAt x).1 x * FrameSigns.frameSign V i x := by
    rw [hCeq]
    exact hδ.symm
  have hMrel1 : ∀ b : Fin k, Nm b = ∑ b', (1 : Matrix (Fin k) (Fin k) ℝ) b' b • Nm b' :=
    fun b => (congrFun (Gauss.frameAct_one Nm) b).symm
  have hblock := OrthFrame.pairMat_mul_fromBlocks (F := tanFrame E (ND.D.indexAt x) x)
    (F' := tanFrame E (i, (ND.D.indexAt x).2) x) (G := Nm) (G' := Nm) (C := C) (M := 1)
    hCrel hMrel1
  have hdet₀ : (OrthFrame.pairMat (tanFrame E (ND.D.indexAt x) x) Nm).det ≠ 0 := by
    intro hzero
    have hsign : OrthFrame.pairSign (tanFrame E (ND.D.indexAt x) x) Nm = 0 := by
      rw [OrthFrame.pairSign, hzero, Real.sign_zero]
    rw [hCp] at hsign
    rcases FrameSigns.frameSign_eq_one_or_neg_one V (ND.D.indexAt x).1 x with h1 | h1 <;>
      rw [h1] at hsign <;> norm_num at hsign
  have hdet₁ : (OrthFrame.pairMat (tanFrame E (i, (ND.D.indexAt x).2) x) Nm).det ≠ 0 := by
    intro hzero
    have h := congrArg Matrix.det hblock
    have h2 : (OrthFrame.pairMat (tanFrame E (ND.D.indexAt x) x) Nm).det = 0 := by
      rw [h, Matrix.det_mul, Matrix.det_fromBlocks_zero₁₂, hzero, zero_mul]
    exact hdet₀ h2
  have hmain2 := OrthFrame.sign_det_pairMat hCrel hMrel1 hdet₁ hCdet
    (by rw [Matrix.det_one]; norm_num)
  have hsignB : OrthFrame.pairSign (tanFrame E (i, (ND.D.indexAt x).2) x) Nm
      = - FrameSigns.frameSign V i x := by
    have h1 : OrthFrame.pairSign (tanFrame E (ND.D.indexAt x) x) Nm
        * OrthFrame.pairSign (tanFrame E (i, (ND.D.indexAt x).2) x) Nm
        = Real.sign C.det := by
      rw [OrthFrame.pairSign, OrthFrame.pairSign, hmain2, Matrix.det_one, Real.sign_one,
        mul_one]
    rw [hCp, hCsign] at h1
    rcases FrameSigns.frameSign_eq_one_or_neg_one V (ND.D.indexAt x).1 x with hu | hu <;>
      rcases FrameSigns.frameSign_eq_one_or_neg_one V i x with hv | hv <;>
      (rw [hu, hv] at h1; rw [hv]; linarith)
  exact hsignB

end

end Work.ThomBordism
