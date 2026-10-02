import Mathlib
import Submission.Work.Whitney.Basic
import Submission.Work.Whitney.nonempty_bundleIso_whitneySum_comm

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The real Whitney sum commutes with the interchange of the summands

This is the *real* counterpart of `Work.Whitney.nonempty_bundleIso_whitneySum_comm`: the real
Whitney sum `Work.Whitney.whitneySumR Z₁ Z₂` (model fibre `ℝ^{k₁+k₂}`, cover `ι₁ × ι₂`) is
isomorphic to `Work.Whitney.whitneySumR Z₂ Z₁` (model fibre `ℝ^{k₂+k₁}`, cover `ι₂ × ι₁`).

The proof is the exact analogue of the complex one.  The general gauge lemma
`Work.Whitney.nonempty_bundleIso_of_gauge_fibre` and the product-swap identity
`Work.Whitney.prodMap_prodComm_swap_apply` are already stated over an arbitrary field, so only the
real splitting `Work.Whitney.sumFibreR` needs its own swapping gauge `Work.Agree.sumCommGaugeR` and
the conjugation identity `Work.Agree.whitneySumR_comm_gauge_conj`.
-/

namespace Work.Agree

open Work.TangentClasses

noncomputable section

/-! ## The gauge interchanging the two real summands -/

/-- The continuous linear map underlying `Work.Agree.sumCommGaugeR`: swap the two summands
(`ℝ^{k₁} × ℝ^{k₂} → ℝ^{k₂} × ℝ^{k₁}`) and re-concatenate with the other splitting.  This is the real
analogue of `Work.Whitney.sumCommGaugeCLM`. -/
noncomputable def sumCommGaugeRCLM (k₁ k₂ : ℕ) :
    EuclideanSpace ℝ (Fin (k₁ + k₂)) →L[ℝ] EuclideanSpace ℝ (Fin (k₂ + k₁)) :=
  (Work.Whitney.sumFibreR k₂ k₁ : (EuclideanSpace ℝ (Fin k₂) × EuclideanSpace ℝ (Fin k₁)) →L[ℝ]
      EuclideanSpace ℝ (Fin (k₂ + k₁))).comp
    ((((ContinuousLinearEquiv.prodComm ℝ (EuclideanSpace ℝ (Fin k₁))
        (EuclideanSpace ℝ (Fin k₂))) :
          (EuclideanSpace ℝ (Fin k₁) × EuclideanSpace ℝ (Fin k₂)) →L[ℝ]
            (EuclideanSpace ℝ (Fin k₂) × EuclideanSpace ℝ (Fin k₁))).comp
      ((Work.Whitney.sumFibreR k₁ k₂).symm : EuclideanSpace ℝ (Fin (k₁ + k₂)) →L[ℝ]
        (EuclideanSpace ℝ (Fin k₁) × EuclideanSpace ℝ (Fin k₂)))))

/-- **The gauge interchanging the two real summands**: `ℝ^{k₁+k₂} ≃L[ℝ] ℝ^{k₂+k₁}` obtained from
the splittings `Work.Whitney.sumFibreR` and the swap of the two factors.  Its source and target model
fibres are *different*, exactly the situation covered by
`Work.Whitney.nonempty_bundleIso_of_gauge_fibre`. -/
noncomputable def sumCommGaugeR (k₁ k₂ : ℕ) :
    EuclideanSpace ℝ (Fin (k₁ + k₂)) ≃L[ℝ] EuclideanSpace ℝ (Fin (k₂ + k₁)) :=
  ((Work.Whitney.sumFibreR k₁ k₂).symm.trans
    ((ContinuousLinearEquiv.prodComm ℝ (EuclideanSpace ℝ (Fin k₁))
        (EuclideanSpace ℝ (Fin k₂))).trans (Work.Whitney.sumFibreR k₂ k₁)))

/-- The underlying continuous linear map of `Work.Agree.sumCommGaugeR`. -/
theorem sumCommGaugeR_coe (k₁ k₂ : ℕ) :
    ((sumCommGaugeR k₁ k₂ : EuclideanSpace ℝ (Fin (k₁ + k₂)) →L[ℝ]
        EuclideanSpace ℝ (Fin (k₂ + k₁)))) = sumCommGaugeRCLM k₁ k₂ := rfl

/-! ## The conjugation identity -/

/-- **The conjugation identity for the real swapping gauge.**  In the canonical trivialisations of
`whitneySumR Z₁ Z₂` and `whitneySumR Z₂ Z₁` (the latter indexed through the swap of the factors), the
transition functions of the two sums are conjugate by `Work.Agree.sumCommGaugeRCLM`; this is the
`hconj` hypothesis of `Work.Whitney.nonempty_bundleIso_of_gauge_fibre`.  It is the real analogue of
`Work.Whitney.whitneySum_comm_gauge_conj`. -/
theorem whitneySumR_comm_gauge_conj {k₁ k₂ : ℕ} {ι₁ ι₂ : Type}
    {B : Type} [TopologicalSpace B]
    (Z₁ : VectorBundleCore ℝ B (EuclideanSpace ℝ (Fin k₁)) ι₁)
    (Z₂ : VectorBundleCore ℝ B (EuclideanSpace ℝ (Fin k₂)) ι₂)
    (b : B) (i : ι₁ × ι₂) :
    ((Work.Whitney.whitneySumR Z₂ Z₁).coordChange
        ((Work.Whitney.whitneySumR Z₂ Z₁).indexAt b) ((Equiv.prodComm ι₁ ι₂) i) b).comp
        (sumCommGaugeRCLM k₁ k₂)
      = (sumCommGaugeRCLM k₁ k₂).comp
        ((Work.Whitney.whitneySumR Z₁ Z₂).coordChange
          ((Work.Whitney.whitneySumR Z₁ Z₂).indexAt b) i b) := by
  obtain ⟨i₁, i₂⟩ := i
  ext v i'
  simp only [Work.Whitney.whitneySumR_coordChange, Work.Whitney.whitneySumR_indexAt,
    sumCommGaugeRCLM, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    Equiv.prodComm_apply, ContinuousLinearEquiv.symm_apply_apply, Prod.swap_prod_mk]
  rw [Work.Whitney.prodMap_prodComm_swap_apply]

/-! ## The target -/

/-- **The real Whitney sum commutes with the interchange of the summands.** -/
theorem nonempty_bundleIso_whitneySumR_comm {k₁ k₂ : ℕ} {ι₁ ι₂ : Type}
    {B : Type} [TopologicalSpace B]
    (Z₁ : VectorBundleCore ℝ B (EuclideanSpace ℝ (Fin k₁)) ι₁)
    (Z₂ : VectorBundleCore ℝ B (EuclideanSpace ℝ (Fin k₂)) ι₂) :
    Nonempty (Work.Thom.BundleIso (Work.Whitney.whitneySumR Z₁ Z₂)
      (Work.Whitney.whitneySumR Z₂ Z₁)) := by
  refine Work.Whitney.nonempty_bundleIso_of_gauge_fibre (Work.Whitney.whitneySumR Z₁ Z₂)
    (Work.Whitney.whitneySumR Z₂ Z₁) (sumCommGaugeR k₁ k₂) (Equiv.prodComm ι₁ ι₂) ?_ ?_ ?_
  · intro i
    simp only [Work.Whitney.whitneySumR_baseSet, Equiv.prodComm_apply, Prod.fst_swap, Prod.snd_swap]
    exact Set.inter_comm _ _
  · intro b
    rfl
  · intro i b
    simpa only [sumCommGaugeR_coe] using whitneySumR_comm_gauge_conj Z₁ Z₂ b i

end

theorem whitneySumRComm {B : Type} [TopologicalSpace B] {k₁ k₂ : ℕ} {ι₁ ι₂ : Type}
    (Z₁ : Work.TangentClasses.RealBundle B (EuclideanSpace ℝ (Fin k₁)) ι₁)
    (Z₂ : Work.TangentClasses.RealBundle B (EuclideanSpace ℝ (Fin k₂)) ι₂) :
    Nonempty (Work.Thom.BundleIso (Work.Whitney.whitneySumR Z₁ Z₂)
      (Work.Whitney.whitneySumR Z₂ Z₁)) :=
  nonempty_bundleIso_whitneySumR_comm Z₁ Z₂

end Work.Agree
