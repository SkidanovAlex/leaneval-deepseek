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
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

open scoped Matrix

namespace Work.ThomBordism

/-!
# The pair sign of the chart tangent frame and the Gauss frame of the tube

`Work.ThomBordism.LeadChapter.ogFrameCLM Γ` is the orthonormal frame of the oriented `k`-plane `Γ`,
read from the `Classical.choice` representative of the `SO(k)`-orbit.  The present file compares the
*projected* Gauss frame
`b ↦ projEuc k mU hmU (ogFrameCLM (padGaussFunM E ND mU hmU x) (single b 1))` — the frame of the
tautological normal plane of the classifying map, read back in the ambient space `ℝ^{8+k}` — with
the `σ`-corrected Gauss frame `Work.ThomBordism.Gauss.gframe`, for an **arbitrary** chart index `i`
of the base manifold (not only the chart index carried by the normal datum at `x`).

The two steps are:

* `Work.ThomBordism.LeadChapter.exists_so_matrix` produces `M ∈ SO(k)` with
  `ogFrameCLM (padGaussFunM …) = ∑ a, proj_a ⊗ (soActFun M (padGFrameM …)_a)`, so that the projected
  Gauss frame is `Gauss.frameAct M (gframe …)` — an `SO(k)`-change of frame, invisible to
  `Real.sign ∘ det`;
* the change of the *chart* from `i` to the chart of `ND.D.indexAt x` is the `8 × 8` transition
  matrix `C` of `Work.ThomBordism.padGaussND_tanFrame_change_source`, whose determinant sign is
  `frameSign V i x · frameSign V i'.1 x` by `Work.ThomBordism.FrameSigns.frameSign_mul`.

The additivity `Work.ThomBordism.OrthFrame.sign_det_pairMat` then turns these two factors into the
desired identity, the base case being
`Work.ThomBordism.padGaussND_pairSign_tanFrame_gframe`.
-/

/-- The padding `padIsomM` is a section of the projection `projEuc`. -/
private theorem projEuc_padIsomM (k m : ℕ) (hm : 8 ≤ m) (v : Work.Tubular.Euc (8 + k)) :
    Work.PTGeometric.projEuc k m hm (padIsomM k m hm v) = v := by
  rw [padIsomM_apply, Work.PTGeometric.projEuc_padEuc]

/-- The coordinate projection of a standard basis vector. -/
private theorem proj_single (k : ℕ) (a b : Fin k) :
    (EuclideanSpace.proj a : EuclideanSpace ℝ (Fin k) →L[ℝ] ℝ)
        (EuclideanSpace.single b (1 : ℝ)) = if a = b then (1 : ℝ) else 0 := by
  rw [show (EuclideanSpace.proj a : EuclideanSpace ℝ (Fin k) →L[ℝ] ℝ)
      (EuclideanSpace.single b (1 : ℝ)) = (EuclideanSpace.single b (1 : ℝ)).ofLp a from rfl]
  rw [PiLp.single_apply]

/-- Evaluation of a sum of rank-one maps at a basis vector. -/
private theorem sum_smulRight_single {k n : ℕ} (Y : Fin k → EuclideanSpace ℝ (Fin n))
    (b : Fin k) :
    (∑ a : Fin k,
      (EuclideanSpace.proj a : EuclideanSpace ℝ (Fin k) →L[ℝ] ℝ).smulRight (Y a))
        (EuclideanSpace.single b (1 : ℝ)) = Y b := by
  rw [sum_apply]
  simp only [ContinuousLinearMap.smulRight_apply]
  rw [Finset.sum_eq_single b]
  · rw [proj_single, if_pos rfl, one_smul]
  · intro a _ ha
    rw [proj_single, if_neg ha, zero_smul]
  · intro hb
    exact absurd (Finset.mem_univ b) hb

theorem tubePairSignGauss {k : ℕ} (hk : 1 ≤ k) {V : Work.ThomBordism.Man8}
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k))
    (ND : Work.ThomBordism.PontryaginThom.NormalData V k E.e)
    (mU : ℕ) (hmU : 8 ≤ mU)
    (i : Work.ThomBordism.FrameSigns.ChartIdx V) (x : V.pt)
    (hx : x ∈ Work.ThomBordism.FrameSigns.src V i) :
    Real.sign (Work.ThomBordism.OrthFrame.pairMat
      (Work.ThomBordism.PontryaginThom.frame E.e (Work.ThomBordism.FrameSigns.chartOf V i) x)
      (fun b : Fin k => Work.PTGeometric.projEuc k mU hmU
        (Work.ThomBordism.LeadChapter.ogFrameCLM
          (Work.ThomBordism.padGaussFunM E ND mU hmU x)
          (EuclideanSpace.single b 1)))).det
      = Work.ThomBordism.FrameSigns.frameSign V i x := by
  classical
  set i' : PontryaginThom.CoverIdx V k := ND.D.indexAt x with hi'def
  have hx' : x ∈ ND.D.baseSet i' := ND.D.mem_baseSet_at x
  have hx'src : x ∈ (PontryaginThom.coverChart i').1.source :=
    ND.baseSet_sub i'.1 i'.2 x hx'
  set iS : PontryaginThom.CoverIdx V k := (i, i'.2) with hiSdef
  have hxSsrc : x ∈ (PontryaginThom.coverChart iS).1.source := hx
  -- the reference frame of the Gauss plane
  have hF0 : Orthonormal ℝ (padGFrameM E ND mU hmU i' x) :=
    padGFrameM_orthonormal E ND mU hmU i' hx'
  obtain ⟨M, hM, hMout⟩ := LeadChapter.exists_so_matrix
    (⟨padGFrameM E ND mU hmU i' x, hF0⟩ : Grassmann.Stiefel k mU)
  have hMdet : M.det = 1 := hM.2
  -- the chosen frame of the Gauss plane is `padGFrameM` acted on by `M`
  have hGauss : (fun b : Fin k => Work.PTGeometric.projEuc k mU hmU
        (LeadChapter.ogFrameCLM (padGaussFunM E ND mU hmU x) (EuclideanSpace.single b 1)))
      = Gauss.frameAct M (Gauss.gframe E ND i' x) := by
    have hout : (Quotient.out (padGaussFunM E ND mU hmU x)).1
        = Grassmann.soActFun M (padGFrameM E ND mU hmU i' x) := by
      have h1 : padGaussFunM E ND mU hmU x
          = Quotient.mk'' (s₁ := Grassmann.grassmannSetoid k mU)
              (⟨padGFrameM E ND mU hmU i' x, hF0⟩ : Grassmann.Stiefel k mU) := rfl
      rw [h1]
      exact hMout
    funext b
    have h1 : LeadChapter.ogFrameCLM (padGaussFunM E ND mU hmU x)
          (EuclideanSpace.single b 1)
        = ∑ t : Fin k, M t b • padGFrameM E ND mU hmU i' x t := by
      rw [show LeadChapter.ogFrameCLM (padGaussFunM E ND mU hmU x)
          = ∑ a : Fin k, (EuclideanSpace.proj a : EuclideanSpace ℝ (Fin k) →L[ℝ] ℝ).smulRight
              ((Quotient.out (padGaussFunM E ND mU hmU x)).1 a) from rfl]
      rw [hout]
      exact sum_smulRight_single (fun t : Fin k => Grassmann.soActFun M
        (padGFrameM E ND mU hmU i' x) t) b
    have h2 : Work.PTGeometric.projEuc k mU hmU
          (∑ t : Fin k, M t b • padGFrameM E ND mU hmU i' x t)
        = ∑ t : Fin k, M t b • Gauss.gframe E ND i' x t := by
      rw [map_sum]
      refine Finset.sum_congr rfl fun t _ => ?_
      rw [map_smul]
      exact congrArg (fun z => M t b • z)
        (projEuc_padIsomM k mU hmU (Gauss.gframe E ND i' x t))
    rw [h1, h2]
    rfl
  -- the transition matrix between the chart `i` and the chart of the index at `x`
  obtain ⟨C, hCrel, hCdet, hCeq⟩ :=
    padGaussND_tanFrame_change_source E iS i' hxSsrc hx'src
  have hdet : (OrthFrame.pairMat (tanFrame E i' x) (Gauss.gframe E ND i' x)).det ≠ 0 :=
    padGaussND_pairMat_gframe_det_ne_zero hk E ND i' hx'
  have hMdetne : M.det ≠ 0 := by rw [hMdet]; norm_num
  have hMrel : ∀ b : Fin k, Work.PTGeometric.projEuc k mU hmU
        (LeadChapter.ogFrameCLM (padGaussFunM E ND mU hmU x) (EuclideanSpace.single b 1))
      = ∑ b' : Fin k, M b' b • Gauss.gframe E ND i' x b' :=
    fun b => congrFun hGauss b
  have hmain := OrthFrame.sign_det_pairMat
    (F := PontryaginThom.frame E.e (FrameSigns.chartOf V i) x)
    (F' := tanFrame E i' x)
    (G := fun b : Fin k => Work.PTGeometric.projEuc k mU hmU
        (LeadChapter.ogFrameCLM (padGaussFunM E ND mU hmU x) (EuclideanSpace.single b 1)))
    (G' := Gauss.gframe E ND i' x) (C := C) (M := M)
    (fun a => hCrel a) hMrel hdet hCdet hMdetne
  have hbase : Real.sign (OrthFrame.pairMat (tanFrame E i' x) (Gauss.gframe E ND i' x)).det
      = FrameSigns.frameSign V i'.1 x :=
    padGaussND_pairSign_tanFrame_gframe E ND hk i' hx'
  have hδc : FrameSigns.frameSign V i x * FrameSigns.frameSign V i'.1 x
      = Real.sign (LinearMap.det (ContinuousLinearMap.toLinearMap (fderiv ℝ
          (fun y => (PontryaginThom.coverChart i').1 ((PontryaginThom.coverChart iS).1.symm y))
          ((PontryaginThom.coverChart iS).1 x))))
    := FrameSigns.frameSign_mul V i i'.1 hx hx'src
  have hsc : Real.sign C.det = FrameSigns.frameSign V i x * FrameSigns.frameSign V i'.1 x := by
    rw [hCeq, ← hδc]
  have hsm : Real.sign M.det = 1 := by rw [hMdet, Real.sign_one]
  have hprod : Real.sign (OrthFrame.pairMat
        (PontryaginThom.frame E.e (FrameSigns.chartOf V i) x)
        (fun b : Fin k => Work.PTGeometric.projEuc k mU hmU
          (LeadChapter.ogFrameCLM (padGaussFunM E ND mU hmU x) (EuclideanSpace.single b 1)))).det
      * FrameSigns.frameSign V i'.1 x
      = FrameSigns.frameSign V i x * FrameSigns.frameSign V i'.1 x := by
    have h1 := hmain
    rw [hbase] at h1
    rw [hsc] at h1
    rw [hsm, mul_one] at h1
    exact h1
  have hbne : FrameSigns.frameSign V i'.1 x ≠ 0 := by
    rcases FrameSigns.frameSign_eq_one_or_neg_one V i'.1 x with h | h <;> rw [h] <;> norm_num
  exact mul_right_cancel₀ hbne hprod

end Work.ThomBordism
