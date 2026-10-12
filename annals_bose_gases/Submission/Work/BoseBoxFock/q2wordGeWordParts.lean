import ChallengeDeps
import Mathlib.Order.CompletePartialOrder
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseBoxFock.massRowDiff_le
import Submission.Work.BoseBoxFock.n0MassWord_eq_sqSum
import Submission.Work.BoseBoxFock.q2PairWord_eq_sqFibre
import Submission.Work.BoseBoxFock.q2Regime
import Submission.Work.BoseBoxFock.wLoc_fibre_kernelCompare
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.q2wordGeWordParts` — the word-side half of the `Q₂` dictionary

`rowWordPartsH v h μ Φ ≤ q2word ℓ μ w₁ w₂ Φ + ½·errKafz·normB` (the lemma `wordParts_le_q2word`
of `pairRowS3Targets`).  The proof reduces (after `q2word_split` and the cancellation of the `q1`/`q4`
pair words) to the two one-sided mass comparisons

* `ℓ⁻³·M₂·n0MassWord − q2PairWord ≤ ℓ⁻³·e₂·(slot squares)` — the `T₂`-mass identity plus the
  two-sided fibre comparison `|M₂χ(x)² − fibre₂(x)| ≤ C₀(R/ℓ)²∫|wScaled ℓ g₂|` of
  `Work.BoseBoxFock.wLoc_fibre_kernelCompare` (`M₂ = ∫wScaled ℓ g₂ = Ŵ₁(0)+Ŵ₁ω(0)`, the row's own
  coefficient);
* `qOneMass − M₁·q2MassChi ≤ e₁·cnPlus` with `M₁ = ∫wScaled ℓ g₀ = Ŵ₁(0)` — the `−μ`-half;
* the slot-square count `Σᵢⱼ∫(aP_j(aQ_iΦ))² ≤ n·cnPlus ≤ n·𝓜·normB` from `SpectralNPlusLe`
  (`Work.BoseBox.cnPlus_le_of_spectralNPlusLe`).

The error terms are `≤ μ(a v)` up to a factor `1/4` each, paid by `½·errKafz v R μ 1·normB` via
`Work.BoseBoxFock.mu_a_le_errKafz`; the diluteness budget is `Work.BoseBoxFock.q2Regime`.
-/

noncomputable section
open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators

namespace Work.BoseBoxFock

open _root_.BoseGases
open Submission.BoseGases

set_option maxHeartbeats 2000000

/-- **Per-state key inequality** for the word/mass-row comparison. -/
theorem rowMassWord_le_hkey (v : ℝ³ → ℝ) (h : Work.UBB.ScatSol v) (hv : 0 ≤ v)
    (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : ℝ³) R) (hav : 0 < BoseGases.a v)
    {μ : ℝ} (hμ : 0 < μ)
    (hRℓ : R ≤ Work.BoseBox.sideAt μ (BoseGases.a v) * Submission.BoseGases.chiR0)
    {n : ℕ} (Ψf : Submission.BoseGases.X n → ℝ) (hΦc : Continuous Ψf)
    (hn : (n : ℝ) ≤ 2 * μ * Work.BoseBox.sideAt μ (BoseGases.a v) ^ 3)
    (hnorm : 0 < Work.BoseBoxFix.normB v μ n Ψf)
    (hspec : Work.BoseBox.SpectralNPlusLe (Work.BoseBox.sideAt μ (BoseGases.a v))
      (Work.BoseBox.bigM (Work.BoseBox.paramsAt μ (BoseGases.a v)) (BoseGases.a v) μ) Ψf)
    {C₀ : ℝ} (hC₀ : 0 ≤ C₀)
    (hrow : Work.BoseBoxFock.rowMassWord v h μ (Work.BoseBox.sideAt μ (BoseGases.a v)) Ψf
      = (Work.BoseBox.sideAt μ (BoseGases.a v) ^ 3)⁻¹
          * (∫ z : ℝ³, Submission.BoseGases.wScaled (Work.BoseBox.sideAt μ (BoseGases.a v))
              (Submission.BoseGases.g2 v h) z)
          * Work.BoseBoxFock.n0MassWord (n := n) (Work.BoseBox.sideAt μ (BoseGases.a v)) Ψf
        - μ * (∫ z : ℝ³, Submission.BoseGases.wScaled (Work.BoseBox.sideAt μ (BoseGases.a v))
              (Submission.BoseGases.g0 v h) z)
            * Submission.BoseGases.q2MassChi (ℓ := Work.BoseBox.sideAt μ (BoseGases.a v))
                (Φ := Ψf))
    (hfib₂ : ∀ z : ℝ³,
      (∫ ζ : ℝ³, Submission.BoseGases.wScaled (Work.BoseBox.sideAt μ (BoseGases.a v))
            (Submission.BoseGases.g2 v h) ζ)
          * (Submission.BoseGases.chiScale (Work.BoseBox.sideAt μ (BoseGases.a v)) z) ^ 2
        - C₀ * (R / Work.BoseBox.sideAt μ (BoseGases.a v)) ^ 2
            * (∫ ζ : ℝ³, |Submission.BoseGases.wScaled (Work.BoseBox.sideAt μ (BoseGases.a v))
                (Submission.BoseGases.g2 v h) ζ|)
      ≤ Submission.BoseGases.w1Fibre (Work.BoseBox.sideAt μ (BoseGases.a v))
          (Submission.BoseGases.wPairC (Work.BoseBox.sideAt μ (BoseGases.a v))
            (Submission.BoseGases.g2 v h)) z)
    (hfib₁up : ∀ z : ℝ³,
      Submission.BoseGases.w1Fibre (Work.BoseBox.sideAt μ (BoseGases.a v))
          (Submission.BoseGases.wPairC (Work.BoseBox.sideAt μ (BoseGases.a v))
            (Submission.BoseGases.g0 v h)) z
      ≤ (∫ ζ : ℝ³, Submission.BoseGases.wScaled (Work.BoseBox.sideAt μ (BoseGases.a v))
              (Submission.BoseGases.g0 v h) ζ)
            * (Submission.BoseGases.chiScale (Work.BoseBox.sideAt μ (BoseGases.a v)) z) ^ 2
        + C₀ * (R / Work.BoseBox.sideAt μ (BoseGases.a v)) ^ 2
            * (∫ ζ : ℝ³, |Submission.BoseGases.wScaled (Work.BoseBox.sideAt μ (BoseGases.a v))
                (Submission.BoseGases.g0 v h) ζ|))
    (hW₂ : (∫ ζ : ℝ³, |Submission.BoseGases.wScaled (Work.BoseBox.sideAt μ (BoseGases.a v))
        (Submission.BoseGases.g2 v h) ζ|) ≤ 32 * π * BoseGases.a v)
    (hW₁ : (∫ ζ : ℝ³, |Submission.BoseGases.wScaled (Work.BoseBox.sideAt μ (BoseGases.a v))
        (Submission.BoseGases.g0 v h) ζ|) ≤ 16 * π * BoseGases.a v)
    (hbudget : 256 * π * C₀ * (R / Work.BoseBox.sideAt μ (BoseGases.a v)) ^ 2
      * Work.BoseBox.bigM (Work.BoseBox.paramsAt μ (BoseGases.a v)) (BoseGases.a v) μ ≤ 1) :
    Work.BoseBoxFock.rowMassWord v h μ (Work.BoseBox.sideAt μ (BoseGases.a v)) Ψf
      ≤ Submission.BoseGases.q2PairWord (ℓ := Work.BoseBox.sideAt μ (BoseGases.a v)) (v := v) h
          (Φ := Ψf)
        - μ * Submission.BoseGases.qOneMass (ℓ := Work.BoseBox.sideAt μ (BoseGases.a v)) (v := v) h
            (Φ := Ψf)
        + (1 / 2) * Work.BoseFixR.errKafz v R μ 1 * Work.BoseBoxFix.normB v μ n Ψf := by
  set ℓ : ℝ := Work.BoseBox.sideAt μ (BoseGases.a v) with hℓdef
  set M₂ : ℝ := ∫ z : ℝ³, Submission.BoseGases.wScaled ℓ (Submission.BoseGases.g2 v h) z with hM₂def
  set M₁ : ℝ := ∫ z : ℝ³, Submission.BoseGases.wScaled ℓ (Submission.BoseGases.g0 v h) z with hM₁def
  set e₂ : ℝ := C₀ * (R / ℓ) ^ 2
    * (∫ ζ : ℝ³, |Submission.BoseGases.wScaled ℓ (Submission.BoseGases.g2 v h) ζ|) with he₂def
  set e₁ : ℝ := C₀ * (R / ℓ) ^ 2
    * (∫ ζ : ℝ³, |Submission.BoseGases.wScaled ℓ (Submission.BoseGases.g0 v h) ζ|) with he₁def
  have hℓpos' : 0 < ℓ := by rw [hℓdef]; exact Work.BoseBox.sideAt_pos hμ hav
  have hRℓ' : R ≤ ℓ * chiR0 := by rw [hℓdef]; exact hRℓ
  have hn' : (n : ℝ) ≤ 2 * μ * ℓ ^ 3 := by rw [hℓdef]; exact hn
  have hspec' : Work.BoseBox.SpectralNPlusLe ℓ
      (Work.BoseBox.bigM (Work.BoseBox.paramsAt μ (BoseGases.a v)) (BoseGases.a v) μ) Ψf := by
    rw [hℓdef]; exact hspec
  have hbudget' : 256 * π * C₀ * (R / ℓ) ^ 2
      * Work.BoseBox.bigM (Work.BoseBox.paramsAt μ (BoseGases.a v)) (BoseGases.a v) μ ≤ 1 := by
    rw [hℓdef]; exact hbudget
  have hM₂nn : 0 ≤ M₂ := by
    rw [hM₂def]
    exact wScaled_integral_nonneg hR hℓpos' hRℓ'
      (g2_nonneg_ae hR hv hvrad hv_supp h) (fun z hz => g2_zero_of_norm_ge hv_supp hz h)
  have he₂0 : 0 ≤ e₂ := by
    rw [he₂def]
    exact mul_nonneg (mul_nonneg hC₀ (sq_nonneg _)) (integral_nonneg (fun z => abs_nonneg _))
  have h𝓜nn : 0 ≤ Work.BoseBox.bigM (Work.BoseBox.paramsAt μ (BoseGases.a v)) (BoseGases.a v) μ := by
    rw [Work.BoseBox.bigM, Work.BoseBox.paramsAt, Work.BoseBox.fsParams]
    exact mul_nonneg (le_of_lt (Work.BoseBox.fsXp_pos (by positivity)))
      (Real.rpow_nonneg (by positivity) _)
  have hnorm0 : 0 ≤ Work.BoseBoxFix.normB v μ n Ψf := le_of_lt hnorm
  have hCnP : Submission.BoseGases.cnPlus ℓ Ψf
      ≤ Work.BoseBox.bigM (Work.BoseBox.paramsAt μ (BoseGases.a v)) (BoseGases.a v) μ
          * Work.BoseBoxFix.normB v μ n Ψf := by
    have hb := Work.BoseBox.cnPlus_le_of_spectralNPlusLe (N := n) (ℓ := ℓ)
      (𝓜 := Work.BoseBox.bigM (Work.BoseBox.paramsAt μ (BoseGases.a v)) (BoseGases.a v) μ)
      hℓpos' h𝓜nn hΦc hspec'
    have hE : Work.BoseBox.norm2N n ℓ Ψf = Work.BoseBoxFix.normB v μ n Ψf := by
      rw [Work.BoseBox.norm2N, Work.BoseBoxFix.normB, Work.BoseKinLoc.sqNormB, ← hℓdef]
    rwa [hE] at hb
  -- fibre bounds for the two kernels
  have hfibm₂ : AEStronglyMeasurable
      (Submission.BoseGases.w1Fibre ℓ (Submission.BoseGases.wPairC ℓ (Submission.BoseGases.g2 v h)))
      (volume.restrict (Submission.BoseGases.acube ℓ)) :=
    Submission.BoseGases.fibre_acube_aem (ℓ := ℓ) (h := Submission.BoseGases.g2 v h)
      (g2_integrable hR hv hvrad hv_supp h)
  have hfibm₁ : AEStronglyMeasurable
      (Submission.BoseGases.w1Fibre ℓ (Submission.BoseGases.wPairC ℓ (Submission.BoseGases.g0 v h)))
      (volume.restrict (Submission.BoseGases.acube ℓ)) :=
    Submission.BoseGases.fibre_acube_aem (ℓ := ℓ) (h := Submission.BoseGases.g0 v h)
      (g0_integrable hR hv_supp h)
  have hfibb₂ : ∀ z : ℝ³, z ∈ Submission.BoseGases.acube ℓ →
      |Submission.BoseGases.w1Fibre ℓ (Submission.BoseGases.wPairC ℓ (Submission.BoseGases.g2 v h)) z|
        ≤ Submission.BoseGases.chiSup ^ 2 * 2
            * (8 * π * BoseGases.a v + Submission.BoseGases.g0w0Mass (v := v) h) := by
    intro z _
    exact Submission.BoseGases.w2Fibre_acube_abs_le (v := v) (R := R) (ℓ := ℓ) hR hv hvrad hv_supp h
      hℓpos' hRℓ' z
  have hfibb₁ : ∀ z : ℝ³, z ∈ Submission.BoseGases.acube ℓ →
      |Submission.BoseGases.w1Fibre ℓ (Submission.BoseGases.wPairC ℓ (Submission.BoseGases.g0 v h)) z|
        ≤ Submission.BoseGases.chiSup ^ 2 * 2 * (8 * π * BoseGases.a v) := by
    intro z _
    exact Submission.BoseGases.w1c_fibre_acube_abs_le (v := v) (R := R) (ℓ := ℓ) hR hv hvrad hv_supp h
      hℓpos' hRℓ' z
  -- the two key applications
  have hD2 := n0MassWord_eq_sqSum (N := n) (ℓ := ℓ) hℓpos' (Φ := Ψf) hΦc
  have hD3 := q2PairWord_eq_sqFibre (N := n) (ℓ := ℓ) hℓpos' (v := v) hv hvrad hR hv_supp h hRℓ'
    (Φ := Ψf) hΦc
  have hP1 := massRowDiff_le (N := n) (ℓ := ℓ) (M₂ := M₂) (e₂ := e₂)
    (Cw := Submission.BoseGases.chiSup ^ 2 * 2
      * (8 * π * BoseGases.a v + Submission.BoseGases.g0w0Mass (v := v) h))
    hℓpos' hM₂nn he₂0 hΦc hfibm₂ hfibb₂ hfib₂
  have hbase : (ℓ ^ 3)⁻¹ * M₂ * Work.BoseBoxFock.n0MassWord (n := n) ℓ Ψf
      - Submission.BoseGases.q2PairWord (ℓ := ℓ) (v := v) h (Φ := Ψf)
      ≤ (ℓ ^ 3)⁻¹ * e₂
        * (∑ i : Fin n, ∑ j : Fin n, ∫ x in Submission.BoseGases.abox n ℓ,
            (Submission.BoseGases.aP ℓ j (Submission.BoseGases.aQ ℓ i Ψf) x) ^ 2) := by
    rw [hD2, hD3]
    exact hP1
  have hP2 := sum_slot_upper (N := n) (ℓ := ℓ) (M := M₁) (e := e₁)
    (Cw := Submission.BoseGases.chiSup ^ 2 * 2 * (8 * π * BoseGases.a v))
    hℓpos' hΦc hfibm₁ hfibb₁ hfib₁up
  have hbase2 : Submission.BoseGases.qOneMass (ℓ := ℓ) (v := v) h (Φ := Ψf)
      - M₁ * Submission.BoseGases.q2MassChi (ℓ := ℓ) (Φ := Ψf)
      ≤ e₁ * Submission.BoseGases.cnPlus ℓ Ψf := by
    simp only [Submission.BoseGases.qOneMass, Submission.BoseGases.q2MassChi]
    linarith [hP2]
  -- error bounds
  have hB0 : 0 ≤ (∑ i : Fin n, ∑ j : Fin n, ∫ x in Submission.BoseGases.abox n ℓ,
      (Submission.BoseGases.aP ℓ j (Submission.BoseGases.aQ ℓ i Ψf) x) ^ 2) :=
    Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ =>
      integral_nonneg (fun x => sq_nonneg _)))
  have hcn0 : 0 ≤ Submission.BoseGases.cnPlus ℓ Ψf :=
    Finset.sum_nonneg (fun i _ => integral_nonneg (fun x => sq_nonneg _))
  have hB : (∑ i : Fin n, ∑ j : Fin n, ∫ x in Submission.BoseGases.abox n ℓ,
      (Submission.BoseGases.aP ℓ j (Submission.BoseGases.aQ ℓ i Ψf) x) ^ 2)
      ≤ (2 * μ * ℓ ^ 3)
        * (Work.BoseBox.bigM (Work.BoseBox.paramsAt μ (BoseGases.a v)) (BoseGases.a v) μ
            * Work.BoseBoxFix.normB v μ n Ψf) := by
    calc (∑ i : Fin n, ∑ j : Fin n, ∫ x in Submission.BoseGases.abox n ℓ,
          (Submission.BoseGases.aP ℓ j (Submission.BoseGases.aQ ℓ i Ψf) x) ^ 2)
        ≤ (n : ℝ) * Submission.BoseGases.cnPlus ℓ Ψf := sum_sq_le hℓpos' hΦc
      _ ≤ (n : ℝ) * (Work.BoseBox.bigM (Work.BoseBox.paramsAt μ (BoseGases.a v)) (BoseGases.a v) μ
            * Work.BoseBoxFix.normB v μ n Ψf) :=
            mul_le_mul_of_nonneg_left hCnP (Nat.cast_nonneg n)
      _ ≤ (2 * μ * ℓ ^ 3)
            * (Work.BoseBox.bigM (Work.BoseBox.paramsAt μ (BoseGases.a v)) (BoseGases.a v) μ
                * Work.BoseBoxFix.normB v μ n Ψf) :=
            mul_le_mul_of_nonneg_right hn' (mul_nonneg h𝓜nn hnorm0)
  have he₂le : e₂ ≤ C₀ * (R / ℓ) ^ 2 * (32 * π * BoseGases.a v) := by
    rw [he₂def]
    exact mul_le_mul_of_nonneg_left hW₂ (mul_nonneg hC₀ (sq_nonneg _))
  have he₁le : e₁ ≤ C₀ * (R / ℓ) ^ 2 * (16 * π * BoseGases.a v) := by
    rw [he₁def]
    exact mul_le_mul_of_nonneg_left hW₁ (mul_nonneg hC₀ (sq_nonneg _))
  have hc₂0 : (0 : ℝ) ≤ C₀ * (R / ℓ) ^ 2 * (32 * π * BoseGases.a v) :=
    mul_nonneg (mul_nonneg hC₀ (sq_nonneg _)) (mul_nonneg (by positivity) hav.le)
  have hE1 : (ℓ ^ 3)⁻¹ * e₂
      * (∑ i : Fin n, ∑ j : Fin n, ∫ x in Submission.BoseGases.abox n ℓ,
          (Submission.BoseGases.aP ℓ j (Submission.BoseGases.aQ ℓ i Ψf) x) ^ 2)
      ≤ (1 / 4) * (μ * BoseGases.a v) * Work.BoseBoxFix.normB v μ n Ψf := by
    have hnn : 0 ≤ (ℓ ^ 3)⁻¹ := inv_nonneg.mpr (by positivity)
    have hstep1 : (ℓ ^ 3)⁻¹ * e₂
        * (∑ i : Fin n, ∑ j : Fin n, ∫ x in Submission.BoseGases.abox n ℓ,
            (Submission.BoseGases.aP ℓ j (Submission.BoseGases.aQ ℓ i Ψf) x) ^ 2)
        ≤ (ℓ ^ 3)⁻¹ * (C₀ * (R / ℓ) ^ 2 * (32 * π * BoseGases.a v))
          * (∑ i : Fin n, ∑ j : Fin n, ∫ x in Submission.BoseGases.abox n ℓ,
              (Submission.BoseGases.aP ℓ j (Submission.BoseGases.aQ ℓ i Ψf) x) ^ 2) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left he₂le hnn) hB0
    have hstep2 : (ℓ ^ 3)⁻¹ * (C₀ * (R / ℓ) ^ 2 * (32 * π * BoseGases.a v))
        * (∑ i : Fin n, ∑ j : Fin n, ∫ x in Submission.BoseGases.abox n ℓ,
            (Submission.BoseGases.aP ℓ j (Submission.BoseGases.aQ ℓ i Ψf) x) ^ 2)
        ≤ (ℓ ^ 3)⁻¹ * (C₀ * (R / ℓ) ^ 2 * (32 * π * BoseGases.a v))
          * ((2 * μ * ℓ ^ 3)
              * (Work.BoseBox.bigM (Work.BoseBox.paramsAt μ (BoseGases.a v)) (BoseGases.a v) μ
                  * Work.BoseBoxFix.normB v μ n Ψf)) :=
      mul_le_mul_of_nonneg_left hB (mul_nonneg hnn hc₂0)
    have hstep3 : (ℓ ^ 3)⁻¹ * (C₀ * (R / ℓ) ^ 2 * (32 * π * BoseGases.a v))
        * ((2 * μ * ℓ ^ 3)
            * (Work.BoseBox.bigM (Work.BoseBox.paramsAt μ (BoseGases.a v)) (BoseGases.a v) μ
                * Work.BoseBoxFix.normB v μ n Ψf))
        = 64 * π * C₀ * (R / ℓ) ^ 2 * BoseGases.a v
          * (μ * (Work.BoseBox.bigM (Work.BoseBox.paramsAt μ (BoseGases.a v)) (BoseGases.a v) μ
              * Work.BoseBoxFix.normB v μ n Ψf)) := by
      field_simp
      ring
    have hfin : 64 * π * C₀ * (R / ℓ) ^ 2 * BoseGases.a v
        * (μ * (Work.BoseBox.bigM (Work.BoseBox.paramsAt μ (BoseGases.a v)) (BoseGases.a v) μ
            * Work.BoseBoxFix.normB v μ n Ψf))
        ≤ (1 / 4) * (μ * BoseGases.a v) * Work.BoseBoxFix.normB v μ n Ψf := by
      nlinarith [hbudget', mul_nonneg hμ.le (mul_nonneg hav.le hnorm0)]
    linarith [hstep1, hstep2, hstep3, hfin]
  have hE2 : μ * (e₁ * Submission.BoseGases.cnPlus ℓ Ψf)
      ≤ (1 / 4) * (μ * BoseGases.a v) * Work.BoseBoxFix.normB v μ n Ψf := by
    have h1 : e₁ * Submission.BoseGases.cnPlus ℓ Ψf
        ≤ (C₀ * (R / ℓ) ^ 2 * (16 * π * BoseGases.a v))
          * (Work.BoseBox.bigM (Work.BoseBox.paramsAt μ (BoseGases.a v)) (BoseGases.a v) μ
              * Work.BoseBoxFix.normB v μ n Ψf) :=
      mul_le_mul he₁le hCnP hcn0 (mul_nonneg (mul_nonneg hC₀ (sq_nonneg _))
        (mul_nonneg (by positivity) hav.le))
    have h2 : μ * (e₁ * Submission.BoseGases.cnPlus ℓ Ψf)
        ≤ μ * ((C₀ * (R / ℓ) ^ 2 * (16 * π * BoseGases.a v))
          * (Work.BoseBox.bigM (Work.BoseBox.paramsAt μ (BoseGases.a v)) (BoseGases.a v) μ
              * Work.BoseBoxFix.normB v μ n Ψf)) :=
      mul_le_mul_of_nonneg_left h1 hμ.le
    have h3 : μ * ((C₀ * (R / ℓ) ^ 2 * (16 * π * BoseGases.a v))
          * (Work.BoseBox.bigM (Work.BoseBox.paramsAt μ (BoseGases.a v)) (BoseGases.a v) μ
              * Work.BoseBoxFix.normB v μ n Ψf))
        ≤ (1 / 4) * (μ * BoseGases.a v) * Work.BoseBoxFix.normB v μ n Ψf := by
      nlinarith [hbudget', mul_nonneg hμ.le (mul_nonneg hav.le hnorm0)]
    linarith [h2, h3]
  have herr : μ * BoseGases.a v ≤ Work.BoseFixR.errKafz v R μ 1 := mu_a_le_errKafz v R hμ hav
  have hmain : (ℓ ^ 3)⁻¹ * M₂ * Work.BoseBoxFock.n0MassWord (n := n) ℓ Ψf
      - Submission.BoseGases.q2PairWord (ℓ := ℓ) (v := v) h (Φ := Ψf)
      + μ * (Submission.BoseGases.qOneMass (ℓ := ℓ) (v := v) h (Φ := Ψf)
          - M₁ * Submission.BoseGases.q2MassChi (ℓ := ℓ) (Φ := Ψf))
      ≤ (1 / 2) * Work.BoseFixR.errKafz v R μ 1 * Work.BoseBoxFix.normB v μ n Ψf := by
    nlinarith [hbase, hbase2, hE1, hE2, herr, hnorm0]
  rw [hrow]
  linarith [hmain]

/-- The dev assembly of `q2wordGeWordParts`. -/
theorem q2wordGeWordParts (v : ℝ³ → ℝ) (h : Work.UBB.ScatSol v) (hv : 0 ≤ v)
    (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : ℝ³) R) (hav : 0 < BoseGases.a v)
    (fc fu : Work.BoseBoxFix.LowCut) (J : ℝ) (hB3 : Work.BoseBoxFix.NodeB3B v h R fc) :
    ∃ (ε₀ C : ℝ), 0 < ε₀ ∧ 0 ≤ C ∧
      ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
        J ≤ (Work.BoseBox.paramsAt μ (BoseGases.a v)).KB ^ 3 →
        ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (BoseGases.a v))),
          (n : ℝ) ≤ 2 * μ * Work.BoseBox.sideAt μ (BoseGases.a v) ^ 3 →
          0 < Work.BoseBoxFix.normB v μ n Φ →
          Work.BoseBoxFix.IsLowB v h J μ n Φ →
          Work.BoseBox.SpectralNPlusLe (Work.BoseBox.sideAt μ (BoseGases.a v))
            (Work.BoseBox.bigM (Work.BoseBox.paramsAt μ (BoseGases.a v)) (BoseGases.a v) μ)
            (Φ : Submission.BoseGases.X n → ℝ) →
          Work.BoseBoxFock.rowWordPartsH v h μ Φ
            ≤ Submission.BoseGases.q2word (N := n) (Work.BoseBoxFock.ellH v μ) μ
                  (Submission.BoseGases.wLoc (Work.BoseBoxFock.ellH v μ) (Submission.BoseGases.g0 v h) 0)
                  (Submission.BoseGases.wLoc (Work.BoseBoxFock.ellH v μ) (Submission.BoseGases.g2 v h) 0)
                  (Φ : Submission.BoseGases.X n → ℝ)
              + (1 / 2) * Work.BoseFixR.errKafz v R μ C * Work.BoseBoxFix.normB v μ n Φ := by
  obtain ⟨C₀, hC₀0, hC₀⟩ := wLoc_fibre_kernelCompare
  obtain ⟨ε₀r, hε₀rpos, hregr⟩ := q2Regime (A := BoseGases.a v) (R := R)
    (chiSup := Submission.BoseGases.chiSup) (Cχ := Submission.BoseGases.chiTaylorC)
    hav hR (le_of_lt Submission.BoseGases.chiSup_pos) Submission.BoseGases.chiTaylorC_spec.1
  obtain ⟨ε₀b, hε₀bpos, hregb⟩ := q2Regime (A := BoseGases.a v) (R := R)
    (chiSup := Submission.BoseGases.chiSup) (Cχ := C₀ / (4 * Submission.BoseGases.chiSup))
    hav hR (le_of_lt Submission.BoseGases.chiSup_pos)
    (div_nonneg hC₀0 (mul_nonneg (by norm_num) (le_of_lt Submission.BoseGases.chiSup_pos)))
  refine ⟨min 1 (min ε₀r ε₀b), 1, lt_min one_pos (lt_min hε₀rpos hε₀bpos), zero_le_one, ?_⟩
  intro μ hAdm _hKB n Φ hn hnorm _hlow hspec
  obtain ⟨hμ, hμa3, _hPar⟩ := hAdm
  have ht2r : μ * (BoseGases.a v) ^ 3 ≤ ε₀r :=
    le_trans hμa3 (le_trans (min_le_right 1 (min ε₀r ε₀b)) (min_le_left ε₀r ε₀b))
  have ht2b : μ * (BoseGases.a v) ^ 3 ≤ ε₀b :=
    le_trans hμa3 (le_trans (min_le_right 1 (min ε₀r ε₀b)) (min_le_right ε₀r ε₀b))
  obtain ⟨hRℓ, _⟩ := hregr μ hμ ht2r
  obtain ⟨_, hbudgetb⟩ := hregb μ hμ ht2b
  have hΦc : Continuous (Φ : Submission.BoseGases.X n → ℝ) := Φ.contDiff.continuous
  have hbudget : 256 * π * C₀ * (R / Work.BoseBox.sideAt μ (BoseGases.a v)) ^ 2
      * Work.BoseBox.bigM (Work.BoseBox.paramsAt μ (BoseGases.a v)) (BoseGases.a v) μ ≤ 1 := by
    have hb : 1024 * π * Submission.BoseGases.chiSup * (C₀ / (4 * Submission.BoseGases.chiSup))
        * R ^ 2 * Work.BoseBox.bigM (Work.BoseBox.paramsAt μ (BoseGases.a v)) (BoseGases.a v) μ
        * (Work.BoseBox.sideAt μ (BoseGases.a v) ^ 2)⁻¹ ≤ 1 := by
      simpa only [div_eq_mul_inv] using hbudgetb
    have h1 : 1024 * π * Submission.BoseGases.chiSup * (C₀ / (4 * Submission.BoseGases.chiSup))
        = 256 * π * C₀ := by
      field_simp [ne_of_gt Submission.BoseGases.chiSup_pos]
      ring
    rw [h1] at hb
    have hsq : (R / Work.BoseBox.sideAt μ (BoseGases.a v)) ^ 2
        = R ^ 2 * (Work.BoseBox.sideAt μ (BoseGases.a v) ^ 2)⁻¹ := by
      rw [div_pow, div_eq_mul_inv]
    rw [hsq]
    calc 256 * π * C₀ * (R ^ 2 * (Work.BoseBox.sideAt μ (BoseGases.a v) ^ 2)⁻¹)
          * Work.BoseBox.bigM (Work.BoseBox.paramsAt μ (BoseGases.a v)) (BoseGases.a v) μ
        = 256 * π * C₀ * R ^ 2 * Work.BoseBox.bigM (Work.BoseBox.paramsAt μ (BoseGases.a v))
            (BoseGases.a v) μ * (Work.BoseBox.sideAt μ (BoseGases.a v) ^ 2)⁻¹ := by ring
      _ ≤ 1 := hb
  have htsg0 : tsupport (Submission.BoseGases.g0 v h) ⊆ Metric.ball (0 : ℝ³) R := by
    have hsuppsub : Function.support (Submission.BoseGases.g0 v h) ⊆ Function.support v := by
      intro x hx
      simp only [Function.mem_support] at hx ⊢
      exact fun h0 => hx (by simp [Submission.BoseGases.g0, h0])
    exact subset_trans (closure_mono hsuppsub) hv_supp
  have htsg2 : tsupport (Submission.BoseGases.g2 v h) ⊆ Metric.ball (0 : ℝ³) R := by
    have hsuppsub : Function.support (Submission.BoseGases.g2 v h) ⊆ Function.support v := by
      intro x hx
      simp only [Function.mem_support] at hx ⊢
      exact fun h0 => hx (by simp [Submission.BoseGases.g2, h0])
    exact subset_trans (closure_mono hsuppsub) hv_supp
  have hcmp₂ : ∀ x : ℝ³,
      |(∫ z : ℝ³, Submission.BoseGases.wScaled (Work.BoseBox.sideAt μ (BoseGases.a v))
            (Submission.BoseGases.g2 v h) z)
          * (Submission.BoseGases.chiScale (Work.BoseBox.sideAt μ (BoseGases.a v)) x) ^ 2
        - Submission.BoseGases.w1Fibre (Work.BoseBox.sideAt μ (BoseGases.a v))
            (Submission.BoseGases.wPairC (Work.BoseBox.sideAt μ (BoseGases.a v))
              (Submission.BoseGases.g2 v h)) x|
      ≤ C₀ * (R / Work.BoseBox.sideAt μ (BoseGases.a v)) ^ 2
          * (∫ z : ℝ³, |Submission.BoseGases.wScaled (Work.BoseBox.sideAt μ (BoseGases.a v))
              (Submission.BoseGases.g2 v h) z|) := by
    intro x
    have hc := (hC₀ (g := Submission.BoseGases.g2 v h) (R := R)
      (ℓ := Work.BoseBox.sideAt μ (BoseGases.a v)) hR (Work.BoseBox.sideAt_pos hμ hav) hRℓ
      (g2_even hvrad h) htsg2 (g2_integrable hR hv hvrad hv_supp h)).1 x
    simpa only [wLocKC_chat_zero_eq_integral, wLoc0_eq_wPairC_fn] using hc
  have hcmp₁ : ∀ x : ℝ³,
      |(∫ z : ℝ³, Submission.BoseGases.wScaled (Work.BoseBox.sideAt μ (BoseGases.a v))
            (Submission.BoseGases.g0 v h) z)
          * (Submission.BoseGases.chiScale (Work.BoseBox.sideAt μ (BoseGases.a v)) x) ^ 2
        - Submission.BoseGases.w1Fibre (Work.BoseBox.sideAt μ (BoseGases.a v))
            (Submission.BoseGases.wPairC (Work.BoseBox.sideAt μ (BoseGases.a v))
              (Submission.BoseGases.g0 v h)) x|
      ≤ C₀ * (R / Work.BoseBox.sideAt μ (BoseGases.a v)) ^ 2
          * (∫ z : ℝ³, |Submission.BoseGases.wScaled (Work.BoseBox.sideAt μ (BoseGases.a v))
              (Submission.BoseGases.g0 v h) z|) := by
    intro x
    have hc := (hC₀ (g := Submission.BoseGases.g0 v h) (R := R)
      (ℓ := Work.BoseBox.sideAt μ (BoseGases.a v)) hR (Work.BoseBox.sideAt_pos hμ hav) hRℓ
      (g0_even hvrad h) htsg0 (g0_integrable hR hv_supp h)).1 x
    simpa only [wLocKC_chat_zero_eq_integral, wLoc0_eq_wPairC_fn] using hc
  have hfib₂ : ∀ z : ℝ³,
      (∫ ζ : ℝ³, Submission.BoseGases.wScaled (Work.BoseBox.sideAt μ (BoseGases.a v))
            (Submission.BoseGases.g2 v h) ζ)
          * (Submission.BoseGases.chiScale (Work.BoseBox.sideAt μ (BoseGases.a v)) z) ^ 2
        - C₀ * (R / Work.BoseBox.sideAt μ (BoseGases.a v)) ^ 2
            * (∫ ζ : ℝ³, |Submission.BoseGases.wScaled (Work.BoseBox.sideAt μ (BoseGases.a v))
                (Submission.BoseGases.g2 v h) ζ|)
      ≤ Submission.BoseGases.w1Fibre (Work.BoseBox.sideAt μ (BoseGases.a v))
          (Submission.BoseGases.wPairC (Work.BoseBox.sideAt μ (BoseGases.a v))
            (Submission.BoseGases.g2 v h)) z := by
    intro z
    linarith [(abs_le.mp (hcmp₂ z)).2]
  have hfib₁up : ∀ z : ℝ³,
      Submission.BoseGases.w1Fibre (Work.BoseBox.sideAt μ (BoseGases.a v))
          (Submission.BoseGases.wPairC (Work.BoseBox.sideAt μ (BoseGases.a v))
            (Submission.BoseGases.g0 v h)) z
      ≤ (∫ ζ : ℝ³, Submission.BoseGases.wScaled (Work.BoseBox.sideAt μ (BoseGases.a v))
              (Submission.BoseGases.g0 v h) ζ)
            * (Submission.BoseGases.chiScale (Work.BoseBox.sideAt μ (BoseGases.a v)) z) ^ 2
        + C₀ * (R / Work.BoseBox.sideAt μ (BoseGases.a v)) ^ 2
            * (∫ ζ : ℝ³, |Submission.BoseGases.wScaled (Work.BoseBox.sideAt μ (BoseGases.a v))
                (Submission.BoseGases.g0 v h) ζ|) := by
    intro z
    have h := (abs_le.mp (hcmp₁ z)).1
    linarith
  have hW₂ : (∫ ζ : ℝ³, |Submission.BoseGases.wScaled (Work.BoseBox.sideAt μ (BoseGases.a v))
      (Submission.BoseGases.g2 v h) ζ|) ≤ 32 * π * BoseGases.a v :=
    abs_wScaled_g2_le (v := v) h (R := R) (ℓ := Work.BoseBox.sideAt μ (BoseGases.a v))
      hR hv hvrad hv_supp (Work.BoseBox.sideAt_pos hμ hav) hRℓ
  have hW₁ : (∫ ζ : ℝ³, |Submission.BoseGases.wScaled (Work.BoseBox.sideAt μ (BoseGases.a v))
      (Submission.BoseGases.g0 v h) ζ|) ≤ 16 * π * BoseGases.a v :=
    abs_wScaled_g0_le (v := v) h (R := R) (ℓ := Work.BoseBox.sideAt μ (BoseGases.a v))
      hR hv hvrad hv_supp (Work.BoseBox.sideAt_pos hμ hav) hRℓ
  -- the row identity
  have hrow : Work.BoseBoxFock.rowMassWord v h μ (Work.BoseBox.sideAt μ (BoseGases.a v))
        (Φ : Submission.BoseGases.X n → ℝ)
      = (Work.BoseBox.sideAt μ (BoseGases.a v) ^ 3)⁻¹
          * (∫ z : ℝ³, Submission.BoseGases.wScaled (Work.BoseBox.sideAt μ (BoseGases.a v))
              (Submission.BoseGases.g2 v h) z)
          * Work.BoseBoxFock.n0MassWord (n := n) (Work.BoseBox.sideAt μ (BoseGases.a v))
              (Φ : Submission.BoseGases.X n → ℝ)
        - μ * (∫ z : ℝ³, Submission.BoseGases.wScaled (Work.BoseBox.sideAt μ (BoseGases.a v))
              (Submission.BoseGases.g0 v h) z)
            * Submission.BoseGases.q2MassChi (ℓ := Work.BoseBox.sideAt μ (BoseGases.a v))
                (Φ := (Φ : Submission.BoseGases.X n → ℝ)) := by
    have hℓpos : 0 < Work.BoseBox.sideAt μ (BoseGases.a v) := Work.BoseBox.sideAt_pos hμ hav
    have hchat1 : Work.BoseFixR.chat (Submission.BoseGases.wScaled
        (Work.BoseBox.sideAt μ (BoseGases.a v)) (Submission.BoseGases.g0 v h)) 0
        = ∫ z : ℝ³, Submission.BoseGases.wScaled (Work.BoseBox.sideAt μ (BoseGases.a v))
            (Submission.BoseGases.g0 v h) z := chat_zero _
    have hchat2 : Work.BoseFixR.chat (Submission.BoseGases.wScaled
        (Work.BoseBox.sideAt μ (BoseGases.a v))
        (fun y : ℝ³ => Submission.BoseGases.g0 v h y * Classical.choose h y)) 0
        = ∫ z : ℝ³, Submission.BoseGases.wScaled (Work.BoseBox.sideAt μ (BoseGases.a v))
            (fun y : ℝ³ => Submission.BoseGases.g0 v h y * Classical.choose h y) z := chat_zero _
    have hMsplit : (∫ z : ℝ³, Submission.BoseGases.wScaled (Work.BoseBox.sideAt μ (BoseGases.a v))
          (Submission.BoseGases.g2 v h) z)
        = (∫ z : ℝ³, Submission.BoseGases.wScaled (Work.BoseBox.sideAt μ (BoseGases.a v))
              (Submission.BoseGases.g0 v h) z)
          + (∫ z : ℝ³, Submission.BoseGases.wScaled (Work.BoseBox.sideAt μ (BoseGases.a v))
              (fun y : ℝ³ => Submission.BoseGases.g0 v h y * Classical.choose h y) z) := by
      rw [g2_eq_g0_add_g0w0 v h, wScaled_add]
      exact integral_add
        (wScaled_integrable_ae hℓpos hR.le hRℓ (g0_integrable hR hv_supp h)
          (fun z hz => g0_zero_of_norm_ge hv_supp hz h))
        (wScaled_integrable_ae hℓpos hR.le hRℓ (g0w0_integrable hR hv hvrad hv_supp h)
          (fun z hz => by
            rw [mul_eq_zero]
            exact Or.inl (g0_zero_of_norm_ge hv_supp hz h)))
    simp only [Work.BoseBoxFock.rowMassWord, hchat1, hchat2, ← hMsplit]
  have hkey := rowMassWord_le_hkey v h hv hvrad hR hv_supp hav hμ hRℓ
    (Φ : Submission.BoseGases.X n → ℝ) hΦc hn hnorm hspec hC₀0 hrow hfib₂ hfib₁up hW₂ hW₁ hbudget
  rw [Work.BoseBoxFock.rowWordPartsH, ellH_eq_sideAt_of_pos hμ hav, Work.BoseBoxFock.rowWordParts,
    q2word_split (Work.BoseBox.sideAt μ (BoseGases.a v)) μ h (Φ := (Φ : Submission.BoseGases.X n → ℝ))]
  linarith [hkey]

end Work.BoseBoxFock
