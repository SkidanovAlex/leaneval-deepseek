import Mathlib
import Submission.Work.ThomBordism.padGaussFunM
import Submission.Work.ThomBordism.sigmaGaussTelescope
import Submission.Work.ThomBordism.sigmaTelescope_frameSign
import Submission.Work.ThomBordism.FrameSigns.Assembly
import Submission.Work.ThomBordism.OrthFrame.FrameAlgebra
import Submission.Work.ThomBordism.Grassmann.projOfPlaneEqIff
import Submission.Work.ThomBordism.OrLift.existsCorrectedFrame
import Submission.Work.ThomBordism._gtd.P2
import Submission.Work.ThomBordism.frameSign_fps_cocycle

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option linter.unusedVariables false

/-!
# The padded `σ`-corrected Gauss map does not depend on the normal datum

`Work.ThomBordism.padGaussFunM E ND m hm` is the oriented Gauss map `V → G̃r_k(ℝ^{k+m})` of the
normal data `ND` of an embedding `E : V ↪ ℝ^{8+k}`, built on the `σ`-corrected normal frame
`Work.ThomBordism.Gauss.gframe`.  The point of the correction is that `gframe` represents the
**canonical** coorientation of the normal bundle of `V`: by
`Work.ThomBordism.sigmaTelescope_gauss`, the closing-up of `gframe` with the `V.c`-oriented chart
tangent frame is the standard orientation of the ambient space.  Hence the *oriented* `k`-plane it
defines is completely determined by the embedding, the orientation `V.c` of `V` and the standard
orientation of `ℝ^{8+k}` — in particular it does not depend on which normal datum `ND` is used.

This file proves that the padded Gauss map is invariant under the choice of the normal datum
(`Work.ThomBordism.padGaussFunM_eq_of_normalData`), i.e. that two normal data of the same embedding
give the same classifying map `V → G̃r_k(ℝ^{k+m})`.

The proof is a *linear-algebraic* comparison of the two Gauss frames, not a homotopy argument:

* both frames `gframe E ND i x` and `gframe E ND' i' x` are orthonormal and span the *same* plane
  (`Work.ThomBordism.Grassmann.span_gframe`), so they differ by an orthogonal matrix `A`
  (`Work.ThomBordism.OrLift.frameProj_eq_of_span_eq` + `...frameProj_eq_iff_soActFun`);
* the *orientation* half is the block-determinant rule
  `Work.ThomBordism.OrthFrame.sign_det_pairMat` applied twice.  Once to the two tangent frames
  (with the tangent sign cocycle `Work.ThomBordism.FrameSigns.frameSign_mul` and
  `Work.ThomBordism.OrthFrame.tanFrame_change`), which identifies the product of the two pair signs
  with the sign of the tangent transition; once to `gframe` against the tangent frame, which turns
  the telescoping `pairSign (flipTan δ) (gframe) = 1` into `pairSign (tanFrame) (gframe) = δ`;
* cancelling the tangent transition sign leaves `Real.sign A.det = 1`, i.e. `A ∈ SO(k)`, so the two
  frames (and their paddings `padIsomM`) define the same point of `G̃r_k(ℝ^{k+m})`.
-/

open scoped Matrix

namespace Work.ThomBordism

open Work.ThomBordism.PontryaginThom Work.ThomBordism.Grassmann

noncomputable section

variable {V : Work.ThomBordism.Man8} {k : ℕ}

/-- The span of the `ambFrame`-reindexed frame is the image of the span. -/
theorem padGaussND_span_ambFrame {k : ℕ} (F : Fin k → Work.Tubular.Euc (8 + k)) :
    Submodule.span ℝ (Set.range (Gauss.ambFrame F))
      = Submodule.map (Gauss.ambEquiv k).toLinearMap (Submodule.span ℝ (Set.range F)) := by
  have hrange : Set.range (Gauss.ambFrame F) = ⇑(Gauss.ambEquiv k) '' Set.range F := by
    ext v
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨F a, ⟨a, rfl⟩, rfl⟩
    · rintro ⟨u, ⟨a, rfl⟩, rfl⟩
      exact ⟨a, rfl⟩
  rw [hrange, Submodule.map_span]
  congr 1

/-- The determinant of the pair frame of the *corrected* normal frame `gframe` does not vanish: the
correction is by the invertible diagonal matrix `Hmat σ`. -/
theorem padGaussND_pairMat_gframe_det_ne_zero (hk : 1 ≤ k)
    (E : EmbeddingData V (8 + k)) (ND : NormalData V k E.e) (i : CoverIdx V k) {x : V.pt}
    (hx : x ∈ ND.D.baseSet i) :
    (OrthFrame.pairMat (tanFrame E i x) (Gauss.gframe E ND i x)).det ≠ 0 := by
  have hrel : ∀ b : Fin k, Gauss.gframe E ND i x b
      = ∑ b', Gauss.Hmat (k := k) (Gauss.sigma E ND i x) b' b
          • Work.Tubular.orthFrame E ND i x b' := by
    intro b
    rw [Gauss.gframe_apply]
    exact (Gauss.frameAct_Hmat (Gauss.sigma E ND i x) (Work.Tubular.orthFrame E ND i x) b).symm
  have hC : ∀ a : Fin 8, tanFrame E i x a
      = ∑ a', (1 : Matrix (Fin 8) (Fin 8) ℝ) a' a • tanFrame E i x a' :=
    fun a => (congrFun (Gauss.frameAct_one (k := 8) (tanFrame E i x)) a).symm
  have hblock := OrthFrame.pairMat_mul_fromBlocks (F := tanFrame E i x) (F' := tanFrame E i x)
    (G := Gauss.gframe E ND i x) (G' := Work.Tubular.orthFrame E ND i x) (C := 1)
    (M := Gauss.Hmat (k := k) (Gauss.sigma E ND i x)) hC hrel
  have hdet0 : (OrthFrame.pairMat (tanFrame E i x) (Gauss.gframe E ND i x)).det
      = (OrthFrame.pairMat (tanFrame E i x) (Work.Tubular.orthFrame E ND i x)).det
        * (Gauss.Hmat (k := k) (Gauss.sigma E ND i x)).det := by
    rw [hblock, Matrix.det_mul, Matrix.det_fromBlocks_zero₁₂, Matrix.det_one, one_mul]
  rw [hdet0]
  have h1 := pairMat_det_ne_zero E ND i hx
  have h2 : (Gauss.Hmat (k := k) (Gauss.sigma E ND i x)).det ≠ 0 := by
    rw [Gauss.Hmat_det (k := k) hk (Gauss.sigma E ND i x)]
    rcases Gauss.sigma_eq_one_or E ND i x with h | h <;> rw [h] <;> norm_num
  exact mul_ne_zero h1 h2

/-- **The pair sign of the corrected normal frame is the tangent frame sign.**  The telescoping
`Work.ThomBordism.sigmaTelescope_gauss` (`pairSign (flipTan δ) gframe = 1`) together with the
block-determinant rule for the diagonal change of frame `Hmat δ` of the tangent frame gives
`pairSign (tanFrame) (gframe) = δ`. -/
theorem padGaussND_pairSign_tanFrame_gframe (E : EmbeddingData V (8 + k))
    (ND : NormalData V k E.e) (hk : 1 ≤ k) (i : CoverIdx V k) {x : V.pt}
    (hx : x ∈ ND.D.baseSet i) :
    OrthFrame.pairSign (tanFrame E i x) (Gauss.gframe E ND i x)
      = FrameSigns.frameSign V i.1 x := by
  set δ : ℝ := FrameSigns.frameSign V i.1 x with hδdef
  have hδval : δ = 1 ∨ δ = -1 := by
    rcases FrameSigns.frameSign_eq_one_or_neg_one V i.1 x with h | h
    · exact Or.inl (by rw [hδdef, h])
    · exact Or.inr (by rw [hδdef, h])
  have hTEL : OrthFrame.pairSign (flipTan E i x δ) (Gauss.gframe E ND i x) = 1 :=
    sigmaTelescope_gauss E ND hk i x hx
  have hTEL' : (OrthFrame.pairMat (flipTan E i x δ) (Gauss.gframe E ND i x)).det.sign = 1 := hTEL
  have hC : ∀ a : Fin 8, flipTan E i x δ a
      = ∑ a', Gauss.Hmat (k := 8) δ a' a • tanFrame E i x a' := by
    intro a
    show flipTan E i x δ a
      = Gauss.frameAct (Gauss.Hmat (k := 8) δ) (tanFrame E i x) a
    rw [Gauss.frameAct_Hmat]
    by_cases ha : (a : ℕ) = 0 <;> simp [flipTan, ha]
  have hM1 : ∀ b : Fin k, Gauss.gframe E ND i x b
      = ∑ b', (1 : Matrix (Fin k) (Fin k) ℝ) b' b • Gauss.gframe E ND i x b' :=
    fun b => (congrFun (Gauss.frameAct_one (k := k) (Gauss.gframe E ND i x)) b).symm
  have hdet := padGaussND_pairMat_gframe_det_ne_zero hk E ND i hx
  have hCdet : (Gauss.Hmat (k := 8) δ).det ≠ 0 := by
    rw [Gauss.Hmat_det (k := 8) (by norm_num) δ]
    rcases hδval with h | h <;> rw [h] <;> norm_num
  have hMdet : (1 : Matrix (Fin k) (Fin k) ℝ).det ≠ 0 := by
    rw [Matrix.det_one]; norm_num
  have hmain := OrthFrame.sign_det_pairMat (F := flipTan E i x δ) (F' := tanFrame E i x)
    (G := Gauss.gframe E ND i x) (G' := Gauss.gframe E ND i x) (C := Gauss.Hmat (k := 8) δ)
    (M := 1) hC hM1 hdet hCdet hMdet
  rw [Gauss.Hmat_det (k := 8) (by norm_num) δ, Matrix.det_one, Real.sign_one, mul_one] at hmain
  rw [sign_eq_self_of_eq_one_or_neg_one hδval] at hmain
  rw [hTEL', one_mul] at hmain
  exact hmain


/-- **The change of the chart tangent frame between two charts, with source hypotheses.**  The
version of `Work.ThomBordism.OrthFrame.tanFrame_change` whose hypotheses are the *chart source
memberships* `x ∈ (coverChart i).1.source` rather than the base-set memberships of one normal datum:
two normal data of the same embedding need not have the same base sets, but each of them certifies
the chart source membership of its own index. -/
theorem padGaussND_tanFrame_change_source {k : ℕ} (E : EmbeddingData V (8 + k))
    (i j : CoverIdx V k) {x : V.pt}
    (hi : x ∈ (coverChart i).1.source) (hj : x ∈ (coverChart j).1.source) :
    ∃ C : Matrix (Fin 8) (Fin 8) ℝ,
      (∀ a : Fin 8, tanFrame E i x a = ∑ a', C a' a • tanFrame E j x a') ∧
      (C.det ≠ 0) ∧
      (C.det = LinearMap.det (ContinuousLinearMap.toLinearMap (fderiv ℝ
        (fun y => (coverChart j).1 ((coverChart i).1.symm y))
        ((coverChart i).1 x)))) := by
  classical
  have hdiffφ : DifferentiableAt ℝ (fun y => (coverChart j).1 ((coverChart i).1.symm y))
      ((coverChart i).1 x) := differentiableAt_chartChange (coverChart i) (coverChart j) hi hj
  have hdiffψ : DifferentiableAt ℝ (fun y => (coverChart i).1 ((coverChart j).1.symm y))
      ((coverChart j).1 x) := differentiableAt_chartChange (coverChart j) (coverChart i) hj hi
  have hφei : (fun y => (coverChart j).1 ((coverChart i).1.symm y)) ((coverChart i).1 x)
      = (coverChart j).1 x := by
    show (coverChart j).1 ((coverChart i).1.symm ((coverChart i).1 x)) = (coverChart j).1 x
    rw [(coverChart i).1.left_inv hi]
  have heq : (fun y => (coverChart i).1 ((coverChart j).1.symm y)) ∘
      (fun y => (coverChart j).1 ((coverChart i).1.symm y)) =ᶠ[nhds ((coverChart i).1 x)] id := by
    have hcont : ContinuousAt (coverChart i).1.symm ((coverChart i).1 x) :=
      ((coverChart i).1.continuousOn_symm.continuousWithinAt
        ((coverChart i).1.map_source hi)).continuousAt
        ((coverChart i).1.open_target.mem_nhds ((coverChart i).1.map_source hi))
    have hmem : (coverChart i).1.symm ((coverChart i).1 x) ∈ (coverChart j).1.source := by
      rw [(coverChart i).1.left_inv hi]; exact hj
    filter_upwards [((coverChart i).1.open_target).mem_nhds ((coverChart i).1.map_source hi),
      hcont.preimage_mem_nhds ((coverChart j).1.open_source.mem_nhds hmem)] with y hy hyj
    show (coverChart i).1 ((coverChart j).1.symm ((coverChart j).1 ((coverChart i).1.symm y))) = y
    rw [(coverChart j).1.left_inv hyj, (coverChart i).1.right_inv hy]
  refine ⟨LinearMap.toMatrix OrthFrame.stdBasis8 OrthFrame.stdBasis8 (ContinuousLinearMap.toLinearMap (fderiv ℝ
      (fun y => (coverChart j).1 ((coverChart i).1.symm y)) ((coverChart i).1 x))), ?_, ?_, ?_⟩
  · intro a
    have hchain := fderiv_chartRep_eq (E.e) (embedding_contMDiff E) (coverChart i) (coverChart j)
      hi hj
    show fderiv ℝ (chartRep E.e (coverChart i)) ((coverChart i).1 x)
        (EuclideanSpace.single a 1) = _
    rw [hchain, ContinuousLinearMap.comp_apply]
    rw [OrthFrame.clm_expand_basis (fderiv ℝ (fun y => (coverChart j).1 ((coverChart i).1.symm y))
      ((coverChart i).1 x)) a]
    rw [map_sum]
    refine Finset.sum_congr rfl fun a' _ => ?_
    rw [map_smul]
    rfl
  · rw [LinearMap.det_toMatrix]
    have hdψ' : DifferentiableAt ℝ (fun y => (coverChart i).1 ((coverChart j).1.symm y))
        ((fun y => (coverChart j).1 ((coverChart i).1.symm y)) ((coverChart i).1 x)) :=
      hφei ▸ hdiffψ
    have h1 : fderiv ℝ ((fun y => (coverChart i).1 ((coverChart j).1.symm y)) ∘
        (fun y => (coverChart j).1 ((coverChart i).1.symm y))) ((coverChart i).1 x)
        = (fderiv ℝ (fun y => (coverChart i).1 ((coverChart j).1.symm y))
            ((coverChart j).1 x)).comp
          (fderiv ℝ (fun y => (coverChart j).1 ((coverChart i).1.symm y))
            ((coverChart i).1 x)) :=
      hφei ▸ fderiv_comp ((coverChart i).1 x) hdψ' hdiffφ
    have h2 : fderiv ℝ ((fun y => (coverChart i).1 ((coverChart j).1.symm y)) ∘
        (fun y => (coverChart j).1 ((coverChart i).1.symm y))) ((coverChart i).1 x)
        = ContinuousLinearMap.id ℝ (Work.Tubular.Euc 8) := by
      rw [heq.fderiv_eq, fderiv_id]
    have hcomp :
        (fderiv ℝ (fun y => (coverChart i).1 ((coverChart j).1.symm y))
            ((coverChart j).1 x)).comp
          (fderiv ℝ (fun y => (coverChart j).1 ((coverChart i).1.symm y))
            ((coverChart i).1 x))
        = ContinuousLinearMap.id ℝ (Work.Tubular.Euc 8) := h1.symm.trans h2
    have hinj : Function.Injective
        (fderiv ℝ (fun y => (coverChart j).1 ((coverChart i).1.symm y))
          ((coverChart i).1 x)) := by
      intro u v huv
      have hu := congrArg (fun (F : Work.Tubular.Euc 8 →L[ℝ] Work.Tubular.Euc 8) => F u) hcomp
      have hv := congrArg (fun (F : Work.Tubular.Euc 8 →L[ℝ] Work.Tubular.Euc 8) => F v) hcomp
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] at hu hv
      rw [← hu, huv, hv]
    intro h0
    rw [LinearMap.det_eq_zero_iff_ker_ne_bot] at h0
    refine h0 ?_
    rw [LinearMap.ker_eq_bot]
    exact hinj
  · exact LinearMap.det_toMatrix OrthFrame.stdBasis8 (ContinuousLinearMap.toLinearMap (fderiv ℝ
      (fun y => (coverChart j).1 ((coverChart i).1.symm y))
      ((coverChart i).1 x)))

/-- **The two corrected Gauss frames of two normal data are `SO(k)`-related.** -/
theorem padGaussND_isSO_of_baseSet (E : EmbeddingData V (8 + k)) (hk : 1 ≤ k)
    (ND ND' : NormalData V k E.e) (i i' : CoverIdx V k) {x : V.pt}
    (hx : x ∈ ND.D.baseSet i) (hx' : x ∈ ND'.D.baseSet i') :
    ∃ A : Matrix (Fin k) (Fin k) ℝ, IsSO A ∧
      Gauss.gframe E ND i x = Gauss.frameAct A (Gauss.gframe E ND' i' x) := by
  -- the two frames span the same plane, hence differ by an orthogonal matrix
  have hsp : Submodule.span ℝ (Set.range (Gauss.ambGframe E ND i x))
      = Submodule.span ℝ (Set.range (Gauss.ambGframe E ND' i' x)) := by
    rw [show Gauss.ambGframe E ND i x = Gauss.ambFrame (Gauss.gframe E ND i x) from rfl,
      show Gauss.ambGframe E ND' i' x = Gauss.ambFrame (Gauss.gframe E ND' i' x) from rfl,
      padGaussND_span_ambFrame, padGaussND_span_ambFrame,
      Grassmann.span_gframe E ND i hx, Grassmann.span_gframe E ND' i' hx']
  have hproj := OrLift.frameProj_eq_of_span_eq (Gauss.orthonormal_ambGframe E ND' i' hx')
    (Gauss.orthonormal_ambGframe E ND i hx) hsp.symm
  obtain ⟨A, hAorth, hg, hdet⟩ := Grassmann.frameProj_eq_iff_soActFun
    ⟨Gauss.ambGframe E ND' i' x, Gauss.orthonormal_ambGframe E ND' i' hx'⟩
    ⟨Gauss.ambGframe E ND i x, Gauss.orthonormal_ambGframe E ND i hx⟩ hproj
  have hg' : Gauss.ambGframe E ND i x = Grassmann.soActFun A (Gauss.ambGframe E ND' i' x) := hg
  have hFF : Gauss.gframe E ND i x = Gauss.frameAct A (Gauss.gframe E ND' i' x) := by
    have h1 : Gauss.ambGframe E ND i x
        = Gauss.ambFrame (Gauss.frameAct A (Gauss.gframe E ND' i' x)) := by
      rw [hg', Gauss.ambFrame_frameAct]
      rfl
    funext b
    exact (Gauss.ambEquiv k).injective (congrFun h1 b)
  -- the orientation half: sign computations
  have hTF := padGaussND_pairSign_tanFrame_gframe E ND hk i hx
  have hTF' := padGaussND_pairSign_tanFrame_gframe E ND' hk i' hx'
  obtain ⟨C, hCrel, hCdet, hCeq⟩ :=
    padGaussND_tanFrame_change_source E i i' (ND.baseSet_sub i.1 i.2 x hx)
      (ND'.baseSet_sub i'.1 i'.2 x hx')
  have hδc : FrameSigns.frameSign V i.1 x * FrameSigns.frameSign V i'.1 x
      = Real.sign (LinearMap.det (ContinuousLinearMap.toLinearMap (fderiv ℝ
          (fun y => (coverChart i').1 ((coverChart i).1.symm y)) ((coverChart i).1 x)))) :=
    FrameSigns.frameSign_mul V i.1 i'.1 (ND.baseSet_sub i.1 i.2 x hx)
      (ND'.baseSet_sub i'.1 i'.2 x hx')
  have hδδ' : FrameSigns.frameSign V i.1 x * FrameSigns.frameSign V i'.1 x
      = Real.sign C.det := by
    rw [hδc, ← hCeq]
  have hMrel : ∀ b : Fin k, Gauss.gframe E ND i x b
      = ∑ b', A b' b • Gauss.gframe E ND' i' x b' := by
    intro b
    rw [hFF]
    rfl
  have hdetpair : (OrthFrame.pairMat (tanFrame E i' x) (Gauss.gframe E ND' i' x)).det ≠ 0 :=
    padGaussND_pairMat_gframe_det_ne_zero hk E ND' i' hx'
  have hAdet_ne : A.det ≠ 0 := by
    rcases hdet with h | h <;> rw [h] <;> norm_num
  have hmain := OrthFrame.sign_det_pairMat (F := tanFrame E i x) (F' := tanFrame E i' x)
    (G := Gauss.gframe E ND i x) (G' := Gauss.gframe E ND' i' x) (C := C) (M := A)
    hCrel hMrel hdetpair hCdet hAdet_ne
  have hsignA : Real.sign A.det = 1 := by
    have h1 : FrameSigns.frameSign V i.1 x * FrameSigns.frameSign V i'.1 x
        = Real.sign C.det * Real.sign A.det := by
      rw [← hTF, ← hTF']
      exact hmain
    rw [hδδ'] at h1
    have hCs : Real.sign C.det ≠ 0 := by
      rcases Real.sign_apply_eq_of_ne_zero C.det hCdet with h | h <;> rw [h] <;> norm_num
    exact mul_left_cancel₀ hCs (by rw [mul_one]; exact h1.symm)
  have hAdet : A.det = 1 := by
    have hpos : 0 < A.det := by
      rcases lt_trichotomy A.det 0 with h | h | h
      · rw [Real.sign_of_neg h] at hsignA
        norm_num at hsignA
      · rw [h, Real.sign_zero] at hsignA
        norm_num at hsignA
      · exact h
    rcases hdet with h | h
    · exact h
    · exfalso; linarith
  exact ⟨A, ⟨hAorth, hAdet⟩, hFF⟩

/-- **The padding commutes with the `SO(k)`-action on frames.** -/
theorem padGaussND_padIsom_frameAct {k : ℕ} (m : ℕ) (hm : 8 ≤ m)
    (A : Matrix (Fin k) (Fin k) ℝ) (F : Fin k → Work.Tubular.Euc (8 + k)) :
    (fun b => padIsomM k m hm (Gauss.frameAct A F b))
      = Gauss.frameAct A (fun b => padIsomM k m hm (F b)) := by
  funext b
  show padIsomM k m hm (∑ b', A b' b • F b') = ∑ b', A b' b • padIsomM k m hm (F b')
  rw [map_sum]
  exact Finset.sum_congr rfl fun b' _ => map_smul (padIsomM k m hm) (A b' b) (F b')

/-- **The padded `σ`-corrected Gauss map is independent of the normal datum.** -/
theorem padGaussFunM_eq_of_normalData {V : Work.ThomBordism.Man8} {k : ℕ} (hk : 1 ≤ k)
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k))
    (ND ND' : Work.ThomBordism.PontryaginThom.NormalData V k E.e) (m : ℕ) (hm : 8 ≤ m) (x : V.pt) :
    Work.ThomBordism.padGaussFunM E ND m hm x
      = Work.ThomBordism.padGaussFunM E ND' m hm x := by
  have hi : x ∈ ND.D.baseSet (ND.D.indexAt x) := ND.D.mem_baseSet_at x
  have hi' : x ∈ ND'.D.baseSet (ND'.D.indexAt x) := ND'.D.mem_baseSet_at x
  obtain ⟨A, hA, hFF⟩ :=
    padGaussND_isSO_of_baseSet E hk ND ND' (ND.D.indexAt x) (ND'.D.indexAt x) hi hi'
  have hpad : padGFrameM E ND m hm (ND.D.indexAt x) x
      = Gauss.frameAct A (padGFrameM E ND' m hm (ND'.D.indexAt x) x) := by
    show (fun b => padIsomM k m hm (Gauss.gframe E ND (ND.D.indexAt x) x b))
      = Gauss.frameAct A (fun b => padIsomM k m hm (Gauss.gframe E ND' (ND'.D.indexAt x) x b))
    rw [hFF]
    exact padGaussND_padIsom_frameAct m hm A (Gauss.gframe E ND' (ND'.D.indexAt x) x)
  refine (Quotient.sound (s := grassmannSetoid k m) ⟨⟨A, hA⟩, ?_⟩).symm
  apply Subtype.ext
  show padGFrameM E ND m hm (ND.D.indexAt x) x
    = Gauss.frameAct A (padGFrameM E ND' m hm (ND'.D.indexAt x) x)
  exact hpad

end

end Work.ThomBordism
