import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Order.Group.Lattice
import Submission.Work.FTS.FireFix.Defs
import Submission.Work.FTS.RegPkgGal.Basic
import Submission.Work.FTS.FireFix.Clauses.PsiWt.aesm_pth_abs
import Submission.Work.FTS.FireFix.Clauses.PsiWt.integrableOn_sin_rpow_mul_cos_rpow
import Submission.Work.FTS.FireFix.Clauses.PsiWt.integrableOn_cos_sq_sin_rpow
import Submission.Work.FTS.FireFix.Clauses.PsiWt.integrableOn_indic_Iic
import Submission.Work.FTS.FireFix.Clauses.PsiWeightAux
import Submission.Work.FTS.FireFix.Clauses.PsiWt.integrableOn_Dth_sq_sin_rpow

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS.FireFix.Clauses.integrableOn_psi_weight`

Integrability, over the half-strip `(0,inf) x (-pi/2, pi/2)`, of the psi-weight integrand of the
reconstruction (with the cutoff `1_{q.1 <= L}`): the `Ca`-term, the `Cb`-term, the angular
`sin^{a-1}cos^{2a-1}` term and the `|d_theta g|` term, all times `q.1^{1/a-1} cos q.2`.

The `|d_theta g|` term is handled by an `L^2` Cauchy-Schwarz/AM-GM against the two weighted pieces
`(D_theta g)^2 sin(2theta)^{-gamma}` and `cos^2 theta sin(2theta)^{gamma-2}`; the first is
integrable by `HkMem (3a) 4` (the `H^4` field of `RegPkg'`), the second by elementary calculus.
The pointwise bookkeeping lives in `Work.FTS.FireFix.Clauses.psiWpsiLeWmaj`, the auxiliary
integrability statements in `Clauses/PsiWt/`.
-/

open MeasureTheory Set Filter Topology

namespace Work.FTS.FireFix.Clauses

set_option maxHeartbeats 1000000
theorem integrableOn_psi_weight {α S : ℝ} {A B : ℝ → ℝ} {g : ℝ → ℝ → ℝ → ℝ}
    (h : Work.FTS.RegPkgGal.RegPkg' α S A B g) {τ : ℝ} (hτ : τ ∈ Set.Icc 0 S)
    {Ca Cb Cc L : ℝ} (hCa : 0 ≤ Ca) (hCb : 0 ≤ Cb) (hCc : 0 ≤ Cc) (hL : 0 ≤ L) :
    MeasureTheory.IntegrableOn (fun q : ℝ × ℝ =>
      (if q.1 ≤ L then
        Ca / ((B τ * q.1) ^ (1 / (3 * α)) * Real.cos q.2)
        + Cb * (B τ * q.1) ^ ((3 * α - 1) / (3 * α))
        + Cc * (200 * α ^ 2 * (Real.sin (abs q.2)) ^ (α - 1) * (Real.cos q.2) ^ (2 * α - 1)
            + |Work.Spaces.pth (Work.FTS.Regularity.gSlice g τ) q.1 (abs q.2)|)
          / ((B τ * q.1) ^ (1 / (3 * α)))
      else 0) * q.1 ^ (1 / α - 1) * Real.cos q.2)
      (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2)) := by
  change MeasureTheory.IntegrableOn (psiWpsi α Ca Cb Cc L B g τ)
      (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2))
  have hssmeas : MeasurableSet (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2)) :=
    measurableSet_Ioi.prod measurableSet_Ioo
  have hα : 0 < α := h.hα
  have hα13 : α ≤ 1 / 3 := h.hα13
  have hb : 0 < B τ := h.hB τ hτ
  have hγ1 : 1 < Work.Spaces.gam (Work.FTS.Regularity.pExp α) :=
    Work.Spaces.one_lt_gam (Work.FTS.Regularity.pExp_pos hα)
  have hγ2 : Work.Spaces.gam (Work.FTS.Regularity.pExp α) ≤ 2 := by
    rw [Work.Spaces.gam, Work.FTS.Regularity.pExp]; linarith
  have hI1 : MeasureTheory.IntegrableOn (psiWq1 L)
      (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2)) :=
    PsiWt.integrableOn_indic_Iic hL
  have hI2 : MeasureTheory.IntegrableOn (psiWq2 α L)
      (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2)) :=
    PsiWt.integrableOn_sin_rpow_mul_cos_rpow hα hα13 hL
  have hI3 : MeasureTheory.IntegrableOn (psiWq3 α (Work.FTS.Regularity.gSlice g τ))
      (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2)) :=
    PsiWt.integrableOn_Dth_sq_sin_rpow h hτ
  have hI4 : MeasureTheory.IntegrableOn
      (psiWq4 (Work.Spaces.gam (Work.FTS.Regularity.pExp α)) L)
      (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2)) :=
    PsiWt.integrableOn_cos_sq_sin_rpow hγ1 hγ2 hL
  have hMaj : MeasureTheory.IntegrableOn (psiWmaj α Ca Cb Cc L B g τ)
      (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2)) := by
    have hM1 : MeasureTheory.IntegrableOn (fun q : ℝ × ℝ =>
        (Ca * (B τ) ^ (- (1 / (3 * α))) * (L ^ (2 / (3 * α) - 1))
          + Cb * (B τ) ^ (1 - 1 / (3 * α)) * (L ^ (2 / (3 * α)))) * psiWq1 L q)
        (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2)) :=
      psiIntegrableOnConstMul hI1
    have hM2 : MeasureTheory.IntegrableOn (fun q : ℝ × ℝ =>
        (Cc * 200 * α ^ 2 * (B τ) ^ (- (1 / (3 * α))) * (L ^ (2 / (3 * α) - 1)))
          * psiWq2 α L q)
        (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2)) :=
      psiIntegrableOnConstMul hI2
    have hM3 : MeasureTheory.IntegrableOn (fun q : ℝ × ℝ =>
        (Cc * (B τ) ^ (- (1 / (3 * α))) * (L ^ (2 / (3 * α) - 1)) / 2)
          * psiWq3 α (Work.FTS.Regularity.gSlice g τ) q)
        (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2)) :=
      psiIntegrableOnConstMul hI3
    have hM4 : MeasureTheory.IntegrableOn (fun q : ℝ × ℝ =>
        (Cc * (B τ) ^ (- (1 / (3 * α))) * (L ^ (2 / (3 * α) - 1)) / 2)
          * psiWq4 (Work.Spaces.gam (Work.FTS.Regularity.pExp α)) L q)
        (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2)) :=
      psiIntegrableOnConstMul hI4
    unfold psiWmaj
    exact ((hM1.add hM2).add hM3).add hM4
  have hmeas : AEStronglyMeasurable (psiWpsi α Ca Cb Cc L B g τ)
      (MeasureTheory.volume.restrict
        (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2))) := by
    have hp : AEStronglyMeasurable (fun q : ℝ × ℝ =>
        |Work.Spaces.pth (Work.FTS.Regularity.gSlice g τ) q.1 (abs q.2)|)
        (MeasureTheory.volume.restrict
          (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2))) :=
      continuous_abs.comp_aestronglyMeasurable (PsiWt.aesm_pth_abs h hτ)
    have hX : AEStronglyMeasurable (fun q : ℝ × ℝ => (B τ * q.1) ^ (1 / (3 * α)))
        (MeasureTheory.volume.restrict
          (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2))) :=
      ((psiMeasurableRpowConst _).comp
        (measurable_const.mul measurable_fst)).aestronglyMeasurable
    have hY : AEStronglyMeasurable (fun q : ℝ × ℝ =>
        (B τ * q.1) ^ ((3 * α - 1) / (3 * α)))
        (MeasureTheory.volume.restrict
          (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2))) :=
      ((psiMeasurableRpowConst _).comp
        (measurable_const.mul measurable_fst)).aestronglyMeasurable
    have hc : AEStronglyMeasurable (fun q : ℝ × ℝ => Real.cos q.2)
        (MeasureTheory.volume.restrict
          (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2))) :=
      (Real.measurable_cos.comp measurable_snd).aestronglyMeasurable
    have hsa : AEStronglyMeasurable (fun q : ℝ × ℝ => (Real.sin (abs q.2)) ^ (α - 1))
        (MeasureTheory.volume.restrict
          (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2))) :=
      ((psiMeasurableRpowConst _).comp
        (Real.measurable_sin.comp measurable_snd.abs)).aestronglyMeasurable
    have hc2 : AEStronglyMeasurable (fun q : ℝ × ℝ => (Real.cos q.2) ^ (2 * α - 1))
        (MeasureTheory.volume.restrict
          (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2))) :=
      ((psiMeasurableRpowConst _).comp
        (Real.measurable_cos.comp measurable_snd)).aestronglyMeasurable
    have he : AEStronglyMeasurable (fun q : ℝ × ℝ => q.1 ^ (1 / α - 1))
        (MeasureTheory.volume.restrict
          (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2))) :=
      ((psiMeasurableRpowConst _).comp measurable_fst).aestronglyMeasurable
    have hinner : AEStronglyMeasurable (psiWinner α Ca Cb Cc B g τ)
        (MeasureTheory.volume.restrict
          (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2))) := by
      have hXm : Measurable (fun q : ℝ × ℝ => (B τ * q.1) ^ (1 / (3 * α))) :=
        (psiMeasurableRpowConst _).comp (measurable_const.mul measurable_fst)
      have hYm : Measurable (fun q : ℝ × ℝ =>
          (B τ * q.1) ^ ((3 * α - 1) / (3 * α))) :=
        (psiMeasurableRpowConst _).comp (measurable_const.mul measurable_fst)
      have hcm : Measurable (fun q : ℝ × ℝ => Real.cos q.2) :=
        Real.measurable_cos.comp measurable_snd
      have hsam : Measurable (fun q : ℝ × ℝ => (Real.sin (abs q.2)) ^ (α - 1)) :=
        (psiMeasurableRpowConst _).comp (Real.measurable_sin.comp measurable_snd.abs)
      have hc2m : Measurable (fun q : ℝ × ℝ => (Real.cos q.2) ^ (2 * α - 1)) :=
        (psiMeasurableRpowConst _).comp (Real.measurable_cos.comp measurable_snd)
      have hMm : Measurable (fun q : ℝ × ℝ =>
          Ca / ((B τ * q.1) ^ (1 / (3 * α)) * Real.cos q.2)
          + Cb * (B τ * q.1) ^ ((3 * α - 1) / (3 * α))
          + Cc * (200 * α ^ 2 * (Real.sin (abs q.2)) ^ (α - 1)
              * (Real.cos q.2) ^ (2 * α - 1))
            / ((B τ * q.1) ^ (1 / (3 * α)))) :=
        (((measurable_const : Measurable (fun _ : ℝ × ℝ => Ca)).div
            (hXm.mul hcm)).add
          ((measurable_const : Measurable (fun _ : ℝ × ℝ => Cb)).mul hYm)).add
          (((measurable_const : Measurable (fun _ : ℝ × ℝ => Cc)).mul
            (((measurable_const : Measurable (fun _ : ℝ × ℝ => 200 * α ^ 2)).mul hsam).mul
              hc2m)).div hXm)
      have hBm : Measurable (fun q : ℝ × ℝ => Cc / ((B τ * q.1) ^ (1 / (3 * α)))) :=
        (measurable_const : Measurable (fun _ : ℝ × ℝ => Cc)).div hXm
      refine (hMm.aestronglyMeasurable.add (hBm.aestronglyMeasurable.mul hp)).congr
        (Filter.Eventually.of_forall (fun q => ?_))
      simp only [Pi.add_apply, Pi.mul_apply]
      unfold psiWinner
      ring
    have hite : AEStronglyMeasurable
        (fun q : ℝ × ℝ => if q.1 ≤ L then psiWinner α Ca Cb Cc B g τ q else 0)
        (MeasureTheory.volume.restrict
          (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2))) := by
      have hs : MeasurableSet {q : ℝ × ℝ | q.1 ≤ L} :=
        measurableSet_le measurable_fst measurable_const
      convert hinner.indicator hs using 1
      funext q
      by_cases hq : q.1 ≤ L
      · rw [Set.indicator_of_mem (show q ∈ {q : ℝ × ℝ | q.1 ≤ L} from hq), if_pos hq]
      · rw [Set.indicator_of_notMem (show q ∉ {q : ℝ × ℝ | q.1 ≤ L} from hq), if_neg hq]
    exact (hite.mul he).mul hc
  have hnull : (MeasureTheory.volume.restrict
        (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2)))
        {q : ℝ × ℝ | q.2 = 0} = 0 := by
    rw [MeasureTheory.Measure.restrict_apply' hssmeas]
    refine MeasureTheory.measure_mono_null (t := Set.univ ×ˢ ({0} : Set ℝ)) ?_ ?_
    · rintro q ⟨hq, -⟩
      exact ⟨Set.mem_univ q.1, hq⟩
    · rw [MeasureTheory.Measure.volume_eq_prod ℝ ℝ,
        MeasureTheory.Measure.prod_prod]
      simp [Real.volume_univ, Real.volume_singleton]
  have hbd : ∀ᵐ q ∂(MeasureTheory.volume.restrict
      (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2))),
      ‖psiWpsi α Ca Cb Cc L B g τ q‖ ≤ psiWmaj α Ca Cb Cc L B g τ q := by
    have h1 : ∀ᵐ q ∂(MeasureTheory.volume.restrict
        (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2))),
        (‖psiWpsi α Ca Cb Cc L B g τ q‖ ≤ psiWmaj α Ca Cb Cc L B g τ q) ∨ q.2 = 0 :=
      MeasureTheory.ae_restrict_of_forall_mem hssmeas (fun q hq => by
        have hq1 : 0 < q.1 := hq.1
        have hq2 : q.2 ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := hq.2
        by_cases h0 : q.2 = 0
        · exact Or.inr h0
        · exact Or.inl (psiWpsiLeWmaj h hτ hCa hCb hCc hL hq1 hq2 h0))
    have h2 : ∀ᵐ q ∂(MeasureTheory.volume.restrict
        (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2))), q.2 ≠ 0 := by
      rw [MeasureTheory.ae_iff]
      rw [show {q : ℝ × ℝ | ¬q.2 ≠ 0} = {q : ℝ × ℝ | q.2 = 0} from by ext q; simp]
      exact hnull
    exact (h1.and h2).mono (fun q hq => hq.1.resolve_right hq.2)
  exact hMaj.mono' hmeas hbd

end Work.FTS.FireFix.Clauses
