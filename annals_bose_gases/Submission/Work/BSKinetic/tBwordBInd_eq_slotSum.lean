import Mathlib.Tactic.Have
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BSKinetic.Defs
import Submission.Work.BSKinetic.peel_tBamp_gen
import Submission.Work.BSKinetic.swap_p_abox_tBamp_gen
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BSKinetic.tBwordBInd_eq_slotSum`

The FS-faithful small-box word `Work.UBBInputs8.tBwordBInd` is **slot-additive**: for an
`(n+1)`-particle state `Φ` (smooth), the `(n+1)`-body word equals the sum over the slots of the
box integral of the *one-body* word applied to the slot fibre,

    `tBwordBInd (n+1) ℓ d ε c u Φ
       = Σ_{i : Fin (n+1)} ∫_{r ∈ abox n ℓ} smallBoxWord1 ℓ d ε c u (slotState1 i Φ r)`.

Both halves of `tBwordBInd` decompose slot by slot:

* the FS mean-free count `cnPlusBoxInd`: peel the `i`-th coordinate out of `abox (n+1) ℓ`
  (`abox_integral_peel`) and identify the slot-`0` projection of the fibre with the slot-`i`
  projection of `Φ` at the inserted configuration (`boxQInd_slotState1`); the remaining
  `∫_{abox 1 ℓ}` is the fibre integral over `acube ℓ` (`integral_abox_one_eq_acube`).
* the spectral half `tBdiagFormInd`: the windowed amplitude `tBamp` is independent of the
  peeled slot (`peel_tBamp_gen`), and the residual amplitude is the `kinFT` of the windowed
  mean-free fibre; the `p`-integral over the fibre box is exchanged with the `u`-integral by
  `swap_p_abox_tBamp_gen`, while on the fibre side the amplitude is constant in the ambient
  configuration, so the `(ℓ³)⁻¹∫_{abox 1 ℓ}` collapses (`boxQInd_oneBody_energy`).
-/

noncomputable section

open MeasureTheory Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.BSKinetic

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)
open Submission.BoseGases

lemma measurableSet_dlBox {ℓ d : ℝ} (u : ℝ³) : MeasurableSet (dlBox ℓ d u) := by
  have : IsClosed (dlBox ℓ d u) := by
    unfold dlBox
    exact (acube_isClosed ℓ).inter ((acube_isClosed (ℓ * d)).preimage (by fun_prop))
  exact this.measurableSet

lemma integral_abox_one_eq_acube (ℓ : ℝ) (F : X 1 → ℝ) :
    (∫ x in abox 1 ℓ, F x) = ∫ y in acube ℓ, F (fun _ : Fin 1 => y) := by
  have hmp : MeasurePreserving (⇑(MeasurableEquiv.funUnique (Fin 1) ℝ³).symm)
      volume volume :=
    MeasurePreserving.symm _ (volume_preserving_funUnique (Fin 1) ℝ³)
  have hpre : (MeasurableEquiv.funUnique (Fin 1) ℝ³).symm ⁻¹' (abox 1 ℓ) = acube ℓ := by
    ext y
    simp only [Set.mem_preimage, abox, Set.mem_ofPred_eq, Fin.forall_fin_one]
    rfl
  have h := MeasureTheory.MeasurePreserving.setIntegral_preimage_emb hmp
    (MeasurableEquiv.funUnique (Fin 1) ℝ³).symm.measurableEmbedding F (abox 1 ℓ)
  rw [hpre] at h
  exact h.symm

lemma boxQ_slotState1 {n : ℕ} (volA : ℝ) (A : Set ℝ³) (i : Fin (n+1)) (Φ : X (n+1) → ℝ)
    (r : X n) (x : X 1) :
    Work.SmallBoxTBWord.boxQ volA A 0 (Work.BSKinetic.slotState1 i Φ r) x
      = Work.SmallBoxTBWord.boxQ volA A i Φ (Submission.BoseGases.kcInsN n i (x 0, r)) := by
  have hbox : Work.SmallBoxTBWord.boxQ volA A i Φ (Submission.BoseGases.kcInsN n i (x 0, r))
      = Φ (Submission.BoseGases.kcInsN n i (x 0, r))
        - (1/volA) * (∫ a in A, Φ (Submission.BoseGases.kcInsN n i (a, r))) := by
    have h : (∫ z_1 in A, Φ (Function.update (Submission.BoseGases.kcInsN n i (x 0, r)) i z_1))
        = ∫ a in A, Φ (Submission.BoseGases.kcInsN n i (a, r)) := by
      apply integral_congr_ae
      filter_upwards with a
      rw [Work.SmallBoxBridge.Fourier.update_kcInsN]
    simp only [Work.SmallBoxTBWord.boxQ, Work.SmallBoxTBWord.boxP]
    rw [h]
  rw [hbox]
  simp only [Work.SmallBoxTBWord.boxQ, Work.SmallBoxTBWord.boxP, Work.BSKinetic.slotState1]
  have h : (∫ z in A, Φ ((Submission.BoseGases.kcInsN n i) (Function.update x 0 z 0, r)))
      = ∫ a in A, Φ (Submission.BoseGases.kcInsN n i (a, r)) := by
    apply integral_congr_ae
    filter_upwards with a
    have hupd : Function.update x 0 a = (fun _ : Fin 1 => a) := by funext j; fin_cases j; simp
    rw [hupd]
  rw [h]

lemma boxQInd_slotState1 {n : ℕ} (volA : ℝ) (A : Set ℝ³) (i : Fin (n+1)) (Φ : X (n+1) → ℝ)
    (r : X n) (x : X 1) :
    Work.UBBInputs8.boxQInd volA A 0 (Work.BSKinetic.slotState1 i Φ r) x
      = Work.UBBInputs8.boxQInd volA A i Φ (Submission.BoseGases.kcInsN n i (x 0, r)) := by
  rw [Work.UBBInputs9.A.boxQInd_eq_indicator_mul_boxQ,
      Work.UBBInputs9.A.boxQInd_eq_indicator_mul_boxQ]
  show A.indicator (fun _ => (1:ℝ)) (x 0)
        * Work.SmallBoxTBWord.boxQ volA A 0 (Work.BSKinetic.slotState1 i Φ r) x
      = A.indicator (fun _ => (1:ℝ)) ((Submission.BoseGases.kcInsN n i (x 0, r)) i)
        * Work.SmallBoxTBWord.boxQ volA A i Φ (Submission.BoseGases.kcInsN n i (x 0, r))
  rw [Submission.BoseGases.kc_insN_apply_same, boxQ_slotState1]

lemma integrableOn_boxQInd_sq {n : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) {A : Set ℝ³}
    (hA : MeasurableSet A) (hAc : IsCompact A) (Φ : X (n+1) → ℝ)
    (hΦ : ContDiff ℝ (⊤ : ENat) Φ) (i : Fin (n+1)) :
    IntegrableOn (fun x : X (n+1) => (Work.UBBInputs8.boxQInd volA A i Φ x)^2)
      (abox (n+1) ℓ) volume := by
  have hbq : ContDiff ℝ (⊤ : ENat) (Work.SmallBoxTBWord.boxQ volA A i Φ) :=
    Work.SmallBoxTBWord.boxQ_contDiff_of_compact hAc volA i hΦ
  have hg : Integrable (fun x : X (n+1) => (Work.SmallBoxTBWord.boxQ volA A i Φ x)^2)
      ((volume : Measure (X (n+1))).restrict (abox (n+1) ℓ)) :=
    Submission.BoseGases.integrableOn_abox_of_continuous hℓ (hbq.continuous.pow 2)
  have hpoint : ∀ x : X (n+1),
      (Work.UBBInputs8.boxQInd volA A i Φ x)^2
        = A.indicator (fun _ => (1:ℝ)) (x i) * (Work.SmallBoxTBWord.boxQ volA A i Φ x)^2 := by
    intro x
    rw [Work.UBBInputs9.A.boxQInd_eq_indicator_mul_boxQ]
    simp only []
    rw [mul_pow]
    congr 1
    rw [sq]
    by_cases hx : x i ∈ A
    · rw [Set.indicator_of_mem hx]; ring
    · rw [Set.indicator_of_notMem hx]; ring
  have hpoint_le : ∀ x : X (n+1),
      (Work.UBBInputs8.boxQInd volA A i Φ x)^2 ≤ (Work.SmallBoxTBWord.boxQ volA A i Φ x)^2 := by
    intro x
    rw [hpoint x]
    have hc1 : A.indicator (fun _ => (1:ℝ)) (x i) ≤ 1 := by
      by_cases hx : x i ∈ A
      · rw [Set.indicator_of_mem hx]
      · rw [Set.indicator_of_notMem hx]; norm_num
    calc A.indicator (fun _ => (1:ℝ)) (x i) * Work.SmallBoxTBWord.boxQ volA A i Φ x ^ 2
        ≤ 1 * Work.SmallBoxTBWord.boxQ volA A i Φ x ^ 2 :=
          mul_le_mul_of_nonneg_right hc1 (sq_nonneg _)
      _ = Work.SmallBoxTBWord.boxQ volA A i Φ x ^ 2 := one_mul _
  have hbound : ∀ x : X (n+1), ‖(Work.UBBInputs8.boxQInd volA A i Φ x)^2‖
      ≤ (Work.SmallBoxTBWord.boxQ volA A i Φ x)^2 := by
    intro x
    rw [Real.norm_of_nonneg (sq_nonneg (Work.UBBInputs8.boxQInd volA A i Φ x))]
    exact hpoint_le x
  have hmeas : AEStronglyMeasurable
      (fun x : X (n+1) => (Work.UBBInputs8.boxQInd volA A i Φ x)^2)
      ((volume : Measure (X (n+1))).restrict (abox (n+1) ℓ)) := by
    apply Measurable.aestronglyMeasurable
    rw [show (fun x : X (n+1) => (Work.UBBInputs8.boxQInd volA A i Φ x)^2)
        = fun x : X (n+1) => A.indicator (fun _ => (1:ℝ)) (x i)
            * (Work.SmallBoxTBWord.boxQ volA A i Φ x)^2 from funext hpoint]
    exact ((measurable_const.indicator hA).comp (measurable_pi_apply i)).mul
      (hbq.continuous.measurable.pow_const 2)
  exact hg.mono' hmeas (Eventually.of_forall hbound)

lemma cnPlusBoxInd_slotStep {ℓ volA : ℝ} (hℓ : 0 < ℓ) {A : Set ℝ³}
    (hA : MeasurableSet A) (hAc : IsCompact A) (n : ℕ) (Φ : X (n+1) → ℝ)
    (hΦ : ContDiff ℝ (⊤ : ENat) Φ) (i : Fin (n+1)) :
    (∫ x in abox (n+1) ℓ, (Work.UBBInputs8.boxQInd volA A i Φ x)^2)
      = ∫ r in abox n ℓ, ∫ x in abox 1 ℓ,
          (Work.UBBInputs8.boxQInd volA A 0 (Work.BSKinetic.slotState1 i Φ r) x)^2 := by
  have hF : IntegrableOn (fun x : X (n+1) => (Work.UBBInputs8.boxQInd volA A i Φ x)^2)
      (abox (n+1) ℓ) volume := integrableOn_boxQInd_sq hℓ hA hAc Φ hΦ i
  rw [Submission.BoseGases.abox_integral_peel i _ hF]
  apply integral_congr_ae
  filter_upwards with r
  rw [integral_abox_one_eq_acube ℓ (fun x : X 1 =>
    (Work.UBBInputs8.boxQInd volA A 0 (Work.BSKinetic.slotState1 i Φ r) x)^2)]
  apply integral_congr_ae
  filter_upwards with y
  rw [boxQInd_slotState1]




lemma boxQInd_oneBody_energy {n : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ)
    (χ : ℝ³ → ℝ) {A : Set ℝ³} (hχsupp : ∀ z, z ∉ A → χ z = 0)
    (Φ : X (n+1) → ℝ) (i : Fin (n+1)) (r : X n) (p : ℝ³) :
    (ℓ^3)⁻¹ * ∫ x in abox 1 ℓ,
        ‖Work.SmallBoxTBWord.tBamp χ p
            (Work.UBBInputs8.boxQInd volA A 0 (Work.BSKinetic.slotState1 i Φ r)) 0 x‖^2
      = ‖Work.SmallBoxTBWord.tBamp χ p (Work.SmallBoxTBWord.boxQ volA A i Φ) i
          (Submission.BoseGases.kcInsN n i (0, r))‖^2 := by
  have hpt : ∀ x : X 1,
      Work.SmallBoxTBWord.tBamp χ p
          (Work.UBBInputs8.boxQInd volA A 0 (Work.BSKinetic.slotState1 i Φ r)) 0 x
        = Submission.BoseGases.kinFT (fun z : ℝ³ => (χ z : ℂ) *
            (Work.SmallBoxTBWord.boxQ volA A i Φ
              (Submission.BoseGases.kcInsN n i (z, r)) : ℂ)) p := by
    intro x
    rw [Work.UBBInputs9.A.tBamp_boxQInd hχsupp]
    rw [Work.SmallBoxTBWord.tBamp_eq_kinFT]
    congr 1
    funext z
    congr 1
    have hupd : Function.update x 0 z = (fun _ : Fin 1 => z) := by funext j; fin_cases j; simp
    rw [hupd, boxQ_slotState1]
  have hconst : Submission.BoseGases.kinFT (fun z : ℝ³ => (χ z : ℂ) *
            (Work.SmallBoxTBWord.boxQ volA A i Φ
              (Submission.BoseGases.kcInsN n i (z, r)) : ℂ)) p
        = Work.SmallBoxTBWord.tBamp χ p (Work.SmallBoxTBWord.boxQ volA A i Φ) i
          (Submission.BoseGases.kcInsN n i (0, r)) :=
      (Work.SmallBoxTBWord.tBamp_kcInsN_eq_kinFT i p r 0).symm
  rw [show (∫ x in abox 1 ℓ,
        ‖Work.SmallBoxTBWord.tBamp χ p
            (Work.UBBInputs8.boxQInd volA A 0 (Work.BSKinetic.slotState1 i Φ r)) 0 x‖^2)
      = ∫ x in abox 1 ℓ, ‖Submission.BoseGases.kinFT (fun z : ℝ³ => (χ z : ℂ) *
            (Work.SmallBoxTBWord.boxQ volA A i Φ
              (Submission.BoseGases.kcInsN n i (z, r)) : ℂ)) p‖^2 from by
    apply integral_congr_ae; filter_upwards with x; rw [hpt x]]
  rw [setIntegral_const, Measure.real_def, Submission.BoseGases.abox_volume 1 ℓ hℓ.le,
    ENNReal.toReal_ofReal (by positivity : (0:ℝ) ≤ (ℓ^3)^1), pow_one]
  rw [smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero 3 (ne_of_gt hℓ)), one_mul, hconst]

lemma tBdiagFormInd_slotStep {n : ℕ} {ℓ c volA : ℝ} (hℓ : 0 < ℓ)
    (χ : ℝ³ → ℝ) (hχcd : ContDiff ℝ (⊤ : ENat) χ) (hχcs : HasCompactSupport χ)
    {A : Set ℝ³} (hχsupp : ∀ z, z ∉ A → χ z = 0) (hAc : IsCompact A)
    (Φ : X (n+1) → ℝ) (hΦ : ContDiff ℝ (⊤ : ENat) Φ) (i : Fin (n+1)) :
    (((2*Real.pi)^3)⁻¹) * (∫ p : ℝ³, fsKinCoeff c ‖p‖ *
        ((ℓ^3)⁻¹ * ∫ x in abox (n+1) ℓ,
          ‖Work.SmallBoxTBWord.tBamp χ p (Work.UBBInputs8.boxQInd volA A i Φ) i x‖^2))
      = ∫ r in abox n ℓ, (((2*Real.pi)^3)⁻¹) *
          ∫ p : ℝ³, fsKinCoeff c ‖p‖ *
            ((ℓ^3)⁻¹ * ∫ x in abox 1 ℓ,
              ‖Work.SmallBoxTBWord.tBamp χ p
                (Work.UBBInputs8.boxQInd volA A 0 (Work.BSKinetic.slotState1 i Φ r)) 0 x‖^2) := by
  set Ψ : X (n+1) → ℝ := Work.SmallBoxTBWord.boxQ volA A i Φ with hΨdef
  have hΨcd : ContDiff ℝ (⊤ : ENat) Ψ :=
    Work.SmallBoxTBWord.boxQ_contDiff_of_compact hAc volA i hΦ
  have henergy : ∀ (r : X n) (p : ℝ³),
      (ℓ^3)⁻¹ * ∫ x in abox 1 ℓ,
          ‖Work.SmallBoxTBWord.tBamp χ p (Work.UBBInputs8.boxQInd volA A 0 (Work.BSKinetic.slotState1 i Φ r)) 0 x‖^2
        = ‖Work.SmallBoxTBWord.tBamp χ p Ψ i (Submission.BoseGases.kcInsN n i (0, r))‖^2 := by
    intro r p
    rw [boxQInd_oneBody_energy hℓ χ hχsupp Φ i r p]
  have hpeel : ∀ p : ℝ³, (ℓ^3)⁻¹ * ∫ x in abox (n+1) ℓ, ‖Work.SmallBoxTBWord.tBamp χ p Ψ i x‖^2
      = ∫ r in abox n ℓ, ‖Submission.BoseGases.kinFT (fun z : ℝ³ => (χ z : ℂ) *
          (Ψ (Submission.BoseGases.kcInsN n i (z, r)) : ℂ)) p‖^2 := by
    intro p
    refine Work.BSKinetic.peel_tBamp_gen hℓ hχcs hχcd.continuous ?_ hΨcd.continuous i p
    intro z hz
    by_contra h
    exact hz (subset_tsupport χ (Function.mem_support.mpr h))
  have hbq : ∀ p : ℝ³, (ℓ^3)⁻¹ * ∫ x in abox (n+1) ℓ,
        ‖Work.SmallBoxTBWord.tBamp χ p (Work.UBBInputs8.boxQInd volA A i Φ) i x‖^2
      = (ℓ^3)⁻¹ * ∫ x in abox (n+1) ℓ, ‖Work.SmallBoxTBWord.tBamp χ p Ψ i x‖^2 := by
    intro p; congr 1; apply integral_congr_ae; filter_upwards with x
    rw [Work.UBBInputs9.A.tBamp_boxQInd hχsupp]
  have hL1 : (((2*Real.pi)^3)⁻¹) * (∫ p : ℝ³, fsKinCoeff c ‖p‖ *
        ((ℓ^3)⁻¹ * ∫ x in abox (n+1) ℓ, ‖Work.SmallBoxTBWord.tBamp χ p (Work.UBBInputs8.boxQInd volA A i Φ) i x‖^2))
      = ∫ r in abox n ℓ, (((2*Real.pi)^3)⁻¹) *
          ∫ p : ℝ³, fsKinCoeff c ‖p‖ *
            ‖Work.SmallBoxTBWord.tBamp χ p Ψ i (Submission.BoseGases.kcInsN n i (0, r))‖^2 := by
    rw [show (∫ p : ℝ³, fsKinCoeff c ‖p‖ *
          ((ℓ^3)⁻¹ * ∫ x in abox (n+1) ℓ, ‖Work.SmallBoxTBWord.tBamp χ p (Work.UBBInputs8.boxQInd volA A i Φ) i x‖^2))
        = ∫ p : ℝ³, fsKinCoeff c ‖p‖ *
          ((ℓ^3)⁻¹ * ∫ x in abox (n+1) ℓ, ‖Work.SmallBoxTBWord.tBamp χ p Ψ i x‖^2) from by
      apply integral_congr_ae; filter_upwards with p; rw [hbq p]]
    rw [show (∫ p : ℝ³, fsKinCoeff c ‖p‖ *
          ((ℓ^3)⁻¹ * ∫ x in abox (n+1) ℓ, ‖Work.SmallBoxTBWord.tBamp χ p Ψ i x‖^2))
        = ∫ p : ℝ³, fsKinCoeff c ‖p‖ *
          (∫ r in abox n ℓ, ‖Submission.BoseGases.kinFT (fun z : ℝ³ => (χ z : ℂ) *
          (Ψ (Submission.BoseGases.kcInsN n i (z, r)) : ℂ)) p‖^2) from by
      apply integral_congr_ae; filter_upwards with p; rw [hpeel p]]
    rw [show (∫ p : ℝ³, fsKinCoeff c ‖p‖ *
          (∫ r in abox n ℓ, ‖Submission.BoseGases.kinFT (fun z : ℝ³ => (χ z : ℂ) *
          (Ψ (Submission.BoseGases.kcInsN n i (z, r)) : ℂ)) p‖^2))
        = ∫ p : ℝ³, fsKinCoeff c ‖p‖ *
          (∫ r in abox n ℓ, ‖Work.SmallBoxTBWord.tBamp χ p Ψ i (Submission.BoseGases.kcInsN n i (0, r))‖^2) from by
      apply integral_congr_ae; filter_upwards with p; congr 1
      apply integral_congr_ae; filter_upwards with r
      rw [Work.SmallBoxTBWord.tBamp_kcInsN_eq_kinFT]]
    rw [(Work.BSKinetic.swap_p_abox_tBamp_gen hℓ χ hχcd hχcs Ψ hΨcd i).2]
  rw [hL1]
  apply integral_congr_ae
  filter_upwards with r
  congr 1
  apply integral_congr_ae
  filter_upwards with p
  rw [henergy r p]





theorem tBwordBInd_eq_slotSum {ℓ d ε c : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) (n : ℕ)
    (u : EuclideanSpace ℝ (Fin 3)) (Φ : Submission.BoseGases.X (n + 1) → ℝ)
    (hΦ : ContDiff ℝ (⊤ : ENat) Φ) :
    Work.UBBInputs8.tBwordBInd (n + 1) ℓ d ε c u Φ
      = ∑ i : Fin (n + 1), ∫ r in Submission.BoseGases.abox n ℓ,
          Work.BSKinetic.smallBoxWord1 ℓ d ε c u (Work.BSKinetic.slotState1 i Φ r) := by
  have hℓd : 0 < ℓ * d := mul_pos hℓ hd
  set A : Set ℝ³ := Submission.BoseGases.dlBox ℓ d u with hAdef
  set volA : ℝ := Work.SmallBoxSliding.boxMass ℓ d u with hvolAdef
  set χ : ℝ³ → ℝ := Submission.BoseGases.chiB ℓ d u with hχdef
  have hAmeas : MeasurableSet A := measurableSet_dlBox u
  have hAc : IsCompact A := Work.SmallBoxTBWord.isCompact_dlBox hℓ hd u
  have hχcd : ContDiff ℝ (⊤ : ENat) χ := Work.SmallBoxTBWord.contDiff_chiB hℓ hd u
  have hχcs : HasCompactSupport χ := Work.SmallBoxTBWord.hasCompactSupport_chiB hℓ hd u
  have hχsupp : ∀ z, z ∉ A → χ z = 0 := by
    intro z hz
    by_contra h
    exact hz (Submission.BoseGases.chiB_support_mem hℓ hd u z h)
  have hstep : ∀ i : Fin (n+1),
      (∫ r in Submission.BoseGases.abox n ℓ,
        (Work.SmallBoxTBWord.tbGapCoeff (ℓ * d) ε * (∫ x in Submission.BoseGases.abox 1 ℓ,
            (Work.UBBInputs8.boxQInd volA A 0 (Work.BSKinetic.slotState1 i Φ r) x)^2)
          + (((2*Real.pi)^3)⁻¹) * ∫ p : ℝ³, Submission.BoseGases.fsKinCoeff c ‖p‖ *
              ((ℓ^3)⁻¹ * ∫ x in Submission.BoseGases.abox 1 ℓ,
                ‖Work.SmallBoxTBWord.tBamp χ p
                  (Work.UBBInputs8.boxQInd volA A 0 (Work.BSKinetic.slotState1 i Φ r)) 0 x‖^2)))
        = Work.SmallBoxTBWord.tbGapCoeff (ℓ * d) ε * (∫ x in Submission.BoseGases.abox (n+1) ℓ,
            (Work.UBBInputs8.boxQInd volA A i Φ x)^2)
          + (((2*Real.pi)^3)⁻¹) * ∫ p : ℝ³, Submission.BoseGases.fsKinCoeff c ‖p‖ *
              ((ℓ^3)⁻¹ * ∫ x in Submission.BoseGases.abox (n+1) ℓ,
                ‖Work.SmallBoxTBWord.tBamp χ p (Work.UBBInputs8.boxQInd volA A i Φ) i x‖^2) := by
    intro i
    have hGint : Integrable (fun r : X n => ∫ x in Submission.BoseGases.abox 1 ℓ,
        (Work.UBBInputs8.boxQInd volA A 0 (Work.BSKinetic.slotState1 i Φ r) x)^2)
        ((volume : Measure (X n)).restrict (Submission.BoseGases.abox n ℓ)) := by
      have hF : IntegrableOn (fun x : X (n+1) => (Work.UBBInputs8.boxQInd volA A i Φ x)^2)
          (Submission.BoseGases.abox (n+1) ℓ) volume := integrableOn_boxQInd_sq hℓ hAmeas hAc Φ hΦ i
      have hpeel_int := Submission.BoseGases.abox_peel_inner_integrable i
        (fun x : X (n+1) => (Work.UBBInputs8.boxQInd volA A i Φ x)^2) hF
      refine hpeel_int.congr ?_
      filter_upwards with r
      rw [integral_abox_one_eq_acube ℓ (fun x : X 1 =>
        (Work.UBBInputs8.boxQInd volA A 0 (Work.BSKinetic.slotState1 i Φ r) x)^2)]
      apply integral_congr_ae; filter_upwards with y
      rw [boxQInd_slotState1]
    have hKint : Integrable (fun r : X n =>
        (((2*Real.pi)^3)⁻¹) * ∫ p : ℝ³, Submission.BoseGases.fsKinCoeff c ‖p‖ *
          ((ℓ^3)⁻¹ * ∫ x in Submission.BoseGases.abox 1 ℓ,
            ‖Work.SmallBoxTBWord.tBamp χ p
              (Work.UBBInputs8.boxQInd volA A 0 (Work.BSKinetic.slotState1 i Φ r)) 0 x‖^2))
        ((volume : Measure (X n)).restrict (Submission.BoseGases.abox n ℓ)) := by
      have hΨcd : ContDiff ℝ (⊤ : ENat) (Work.SmallBoxTBWord.boxQ volA A i Φ) :=
        Work.SmallBoxTBWord.boxQ_contDiff_of_compact hAc volA i hΦ
      have hprod := (swap_p_abox_tBamp_gen (ℓ := ℓ) (c := c) hℓ χ hχcd hχcs
        (Work.SmallBoxTBWord.boxQ volA A i Φ) hΨcd i).1.integral_prod_right
      refine (hprod.const_mul (((2*Real.pi)^3)⁻¹)).congr ?_
      filter_upwards with r
      congr 1
      apply integral_congr_ae; filter_upwards with p
      rw [boxQInd_oneBody_energy hℓ χ hχsupp Φ i r p]
    rw [MeasureTheory.integral_add (hGint.const_mul _) hKint, MeasureTheory.integral_const_mul,
      ← cnPlusBoxInd_slotStep hℓ hAmeas hAc n Φ hΦ i,
      ← tBdiagFormInd_slotStep hℓ χ hχcd hχcs hχsupp hAc Φ hΦ i]
  simp only [Work.BSKinetic.smallBoxWord1, Work.UBBInputs8.tBwordBInd, Work.UBBInputs8.tBwordInd,
    Work.UBBInputs8.tBwordKinInd, Work.UBBInputs8.cnPlusBoxInd, Work.UBBInputs8.tBdiagFormInd,
    Fin.sum_univ_one]
  symm
  rw [show (∑ i : Fin (n+1), ∫ r in Submission.BoseGases.abox n ℓ,
        (Work.SmallBoxTBWord.tbGapCoeff (ℓ * d) ε * (∫ x in Submission.BoseGases.abox 1 ℓ,
            (Work.UBBInputs8.boxQInd volA A 0 (Work.BSKinetic.slotState1 i Φ r) x)^2)
          + (((2*Real.pi)^3)⁻¹) * ∫ p : ℝ³, Submission.BoseGases.fsKinCoeff c ‖p‖ *
              ((ℓ^3)⁻¹ * ∫ x in Submission.BoseGases.abox 1 ℓ,
                ‖Work.SmallBoxTBWord.tBamp χ p
                  (Work.UBBInputs8.boxQInd volA A 0 (Work.BSKinetic.slotState1 i Φ r)) 0 x‖^2)))
      = ∑ i : Fin (n+1),
          (Work.SmallBoxTBWord.tbGapCoeff (ℓ * d) ε * (∫ x in Submission.BoseGases.abox (n+1) ℓ,
              (Work.UBBInputs8.boxQInd volA A i Φ x)^2)
            + (((2*Real.pi)^3)⁻¹) * ∫ p : ℝ³, Submission.BoseGases.fsKinCoeff c ‖p‖ *
                ((ℓ^3)⁻¹ * ∫ x in Submission.BoseGases.abox (n+1) ℓ,
                  ‖Work.SmallBoxTBWord.tBamp χ p (Work.UBBInputs8.boxQInd volA A i Φ) i x‖^2))
      from Finset.sum_congr rfl (fun i _ => hstep i)]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
end Work.BSKinetic
