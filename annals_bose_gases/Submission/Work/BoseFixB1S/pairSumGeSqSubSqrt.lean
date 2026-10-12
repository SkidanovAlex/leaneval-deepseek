import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1.abs_pairIntegral_le_sqrt
import Submission.Work.BoseFixB1.qLHSwordB_ge_neg_bandS
import Submission.Work.BoseFixB1S.boxPairValue
import Submission.Work.BoseFixB1S.boxWeightedPairMass
import Submission.Work.BoseFixB1S.mfPairRowManifestB1
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB1S

open MeasureTheory

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ## 1. Toolbox

Three elementary ingredients, independent of the Bose-gas setting. -/

/-- **A bounded measurable factor times an integrable weight is integrable.** -/
theorem integrable_mul_of_bound_of_integrable {α : Type*} [MeasurableSpace α]
    {μ : MeasureTheory.Measure α} {f wgt : α → ℝ} (hw : MeasureTheory.Integrable wgt μ)
    (hf : Measurable f) {D : ℝ} (hfb : ∀ᵐ x ∂μ, |f x| ≤ D) :
    MeasureTheory.Integrable (fun x => f x * wgt x) μ := by
  have hdom : MeasureTheory.Integrable (fun x => D * |wgt x|) μ := hw.abs.const_mul D
  refine MeasureTheory.Integrable.mono' hdom
    (hf.aestronglyMeasurable.mul hw.aestronglyMeasurable) ?_
  filter_upwards [hfb] with x hx
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul_of_nonneg_right hx (abs_nonneg _)

/-- **The pointwise square expansion, integrated.**  If `h = f + g` pointwise and the three
weighted squares/pairings are integrable, then
`∫ h²w = ∫ f²w + 2∫ fg w + ∫ g²w`. -/
theorem integral_sq_mul_eq_add {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α}
    {f g h w : α → ℝ} (heq : ∀ x, h x = f x + g x)
    (hf2 : MeasureTheory.Integrable (fun x => f x ^ 2 * w x) μ)
    (hfg : MeasureTheory.Integrable (fun x => f x * g x * w x) μ)
    (hg2 : MeasureTheory.Integrable (fun x => g x ^ 2 * w x) μ) :
    (∫ x, h x ^ 2 * w x ∂μ)
      = (∫ x, f x ^ 2 * w x ∂μ) + 2 * (∫ x, f x * g x * w x ∂μ)
        + (∫ x, g x ^ 2 * w x ∂μ) := by
  have hfun : (fun x => h x ^ 2 * w x)
      = ((fun x => f x ^ 2 * w x) + (fun x => 2 * (f x * g x * w x)))
        + (fun x => g x ^ 2 * w x) := by
    funext x
    simp only [Pi.add_apply]
    rw [heq x]
    ring
  rw [hfun, MeasureTheory.integral_add'
      (f := (fun x => f x ^ 2 * w x) + (fun x => 2 * (f x * g x * w x)))
      (g := fun x => g x ^ 2 * w x) (hf2.add (hfg.const_mul 2)) hg2,
    MeasureTheory.integral_add' (f := fun x => f x ^ 2 * w x)
      (g := fun x => 2 * (f x * g x * w x)) hf2 (hfg.const_mul 2),
    MeasureTheory.integral_const_mul]

/-- **The scalar inequality.**  If `|C| ≤ √(2·A2·D)` with `A2, D ≥ 0` then
`(√A2 − √(D/2))² ≤ A2 + C + D/2`. -/
theorem sq_sub_sqrt_le {A2 D C : ℝ} (hA2 : 0 ≤ A2) (hD : 0 ≤ D)
    (hC : |C| ≤ Real.sqrt (2 * A2 * D)) :
    (Real.sqrt A2 - Real.sqrt (D / 2)) ^ 2 ≤ A2 + C + D / 2 := by
  have hD2 : 0 ≤ D / 2 := by linarith
  have hsqrt4 : Real.sqrt (4 : ℝ) = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have hkey : Real.sqrt (2 * A2 * D) = 2 * (Real.sqrt A2 * Real.sqrt (D / 2)) := by
    have h1 : 2 * A2 * D = 4 * (A2 * (D / 2)) := by ring
    rw [h1, Real.sqrt_mul (show (0 : ℝ) ≤ 4 by norm_num) (A2 * (D / 2)), hsqrt4,
      Real.sqrt_mul hA2 (D / 2)]
  have hClow : -(Real.sqrt (2 * A2 * D)) ≤ C := by
    have h := neg_abs_le C
    linarith
  rw [hkey] at hClow
  have hexp : (Real.sqrt A2 - Real.sqrt (D / 2)) ^ 2
      = A2 + D / 2 - 2 * (Real.sqrt A2 * Real.sqrt (D / 2)) := by
    rw [sub_sq, Real.sq_sqrt hA2, Real.sq_sqrt hD2]
    ring
  rw [hexp]
  linarith

/-! ## 2. Integrability of the four pair products

The four weighted integrands attached to a pair of distinct slots, obtained from the integrability
of the kernel alone by the uniform bounds on the analysis box. -/

theorem pairProductsIntegrable {n : ℕ} {ℓ V : ℝ} (hℓ : 0 < ℓ) (hV : 0 < V)
    {A : Set E3} (hA : MeasurableSet A) (hVeq : V = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    {w : E3 → E3 → ℝ} {Φ : Submission.BoseGases.X n → ℝ} (hΦc : Continuous Φ)
    (hint : ∀ p ∈ Submission.BoseGases.pairSet n,
      MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X n => w (x p.1) (x p.2))
        (Submission.BoseGases.abox n ℓ))
    {p : Fin n × Fin n} (hp : p ∈ Submission.BoseGases.pairSet n) :
    MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X n =>
        (Work.UBBInputs8.boxPInd V A p.1 (Work.UBBInputs8.boxPInd V A p.2 Φ) x) ^ 2
          * w (x p.1) (x p.2)) (Submission.BoseGases.abox n ℓ)
    ∧ MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X n =>
        (Work.UBBInputs8.boxPInd V A p.1 (Work.UBBInputs8.boxPInd V A p.2 Φ) x)
          * (Φ x - Work.UBBInputs8.boxPInd V A p.1 (Work.UBBInputs8.boxPInd V A p.2 Φ) x)
          * w (x p.1) (x p.2)) (Submission.BoseGases.abox n ℓ)
    ∧ MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X n =>
        (Φ x - Work.UBBInputs8.boxPInd V A p.1 (Work.UBBInputs8.boxPInd V A p.2 Φ) x) ^ 2
          * w (x p.1) (x p.2)) (Submission.BoseGases.abox n ℓ)
    ∧ MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X n =>
        (Φ x) ^ 2 * w (x p.1) (x p.2)) (Submission.BoseGases.abox n ℓ) := by
  classical
  obtain ⟨C, hC0, hΦb, hPb, _hQb⟩ := Work.BoseFixB1S.boxBounds hℓ hV hA hVeq hAc hΦc
  have hFb : ∀ x ∈ Submission.BoseGases.abox n ℓ,
      |Work.UBBInputs8.boxPInd V A p.1 (Work.UBBInputs8.boxPInd V A p.2 Φ) x| ≤ C :=
    fun x hx => Work.BoseFixB1S.abs_boxPInd_le hℓ hV hA hVeq hAc p.1 (C := C) (hPb p.2) x hx
  have hFm : Measurable (fun x : Submission.BoseGases.X n =>
      Work.UBBInputs8.boxPInd V A p.1 (Work.UBBInputs8.boxPInd V A p.2 Φ) x) :=
    Work.BoseFixB1S.measurable_boxPInd V A hA p.1
      (Work.BoseFixB1S.measurable_boxPInd V A hA p.2 hΦc.measurable)
  have hGb : ∀ x ∈ Submission.BoseGases.abox n ℓ,
      |Φ x - Work.UBBInputs8.boxPInd V A p.1 (Work.UBBInputs8.boxPInd V A p.2 Φ) x| ≤ 2 * C := by
    intro x hx
    calc |Φ x - Work.UBBInputs8.boxPInd V A p.1 (Work.UBBInputs8.boxPInd V A p.2 Φ) x|
        ≤ |Φ x| + |Work.UBBInputs8.boxPInd V A p.1
            (Work.UBBInputs8.boxPInd V A p.2 Φ) x| := abs_sub _ _
      _ ≤ C + C := add_le_add (hΦb x hx) (hFb x hx)
      _ = 2 * C := by ring
  have hGm : Measurable (fun x : Submission.BoseGases.X n =>
      Φ x - Work.UBBInputs8.boxPInd V A p.1 (Work.UBBInputs8.boxPInd V A p.2 Φ) x) :=
    hΦc.measurable.sub hFm
  have hwint : MeasureTheory.Integrable (fun x : Submission.BoseGases.X n => w (x p.1) (x p.2))
      ((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X n)).restrict
        (Submission.BoseGases.abox n ℓ)) := hint p hp
  have hCnn : (0 : ℝ) ≤ C := hC0
  have hae : ∀ᵐ x ∂((MeasureTheory.volume : MeasureTheory.Measure
        (Submission.BoseGases.X n)).restrict (Submission.BoseGases.abox n ℓ)),
      x ∈ Submission.BoseGases.abox n ℓ :=
    MeasureTheory.self_mem_ae_restrict (Submission.BoseGases.abox_measurable n ℓ)
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine integrable_mul_of_bound_of_integrable hwint (hFm.pow_const 2) (D := C ^ 2) ?_
    filter_upwards [hae] with x hx
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (hFb x hx) 2
  · refine integrable_mul_of_bound_of_integrable hwint (hFm.mul hGm) (D := C * (2 * C)) ?_
    filter_upwards [hae] with x hx
    rw [abs_mul]
    exact mul_le_mul (hFb x hx) (hGb x hx) (abs_nonneg _) hCnn
  · refine integrable_mul_of_bound_of_integrable hwint (hGm.pow_const 2) (D := (2 * C) ^ 2) ?_
    filter_upwards [hae] with x hx
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (hGb x hx) 2
  · refine integrable_mul_of_bound_of_integrable hwint (hΦc.measurable.pow_const 2)
      (D := C ^ 2) ?_
    filter_upwards [hae] with x hx
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (hΦb x hx) 2

/-! ## 3. The summed pair-mass identity (hypothesis-free in the kernel) -/

private theorem pairSet_eq_empty_of_le_one {N : ℕ} (hN : N ≤ 1) :
    Submission.BoseGases.pairSet N = ∅ := by
  rw [Submission.BoseGases.pairSet, Finset.eq_empty_iff_forall_notMem]
  intro q hq
  rw [Finset.mem_filter] at hq
  exact hq.2 (Fin.ext (by have h1 := q.1.isLt; have h2 := q.2.isLt; omega))

/-- **The summed pair-mass identity**, with the unused hypotheses (`hsupp`, `hint`, `hmass`) of
`Work.BoseFixB1S.boxWeightedPairMass` removed. -/
theorem pairMassSumEq {N : ℕ} {ℓ V : ℝ} (hℓ : 0 < ℓ) (hV : 0 < V)
    {A : Set E3} (hA : MeasurableSet A) (hVeq : V = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    (w : E3 → E3 → ℝ) (Φ : Submission.BoseGases.X N → ℝ) :
    (∑ p ∈ Submission.BoseGases.pairSet N,
        ∫ x in Submission.BoseGases.abox N ℓ,
          (Work.UBBInputs8.boxPInd V A p.1 (Work.UBBInputs8.boxPInd V A p.2 Φ) x) ^ 2
            * w (x p.1) (x p.2))
      = (Work.BoseFixB1S.boxM2 V A w / V ^ 2) * Work.BoseFixB1S.boxPairCount V ℓ A Φ := by
  classical
  rcases N with _ | _ | p
  · rw [Work.BoseFixB1S.boxPairCount,
      pairSet_eq_empty_of_le_one (by norm_num : (0 : ℕ) ≤ 1)]
    simp
  · rw [Work.BoseFixB1S.boxPairCount,
      pairSet_eq_empty_of_le_one (by norm_num : (1 : ℕ) ≤ 1)]
    simp
  · rw [Work.BoseFixB1S.boxPairCount, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun q hq => ?_)
    have hne : q.1 ≠ q.2 := (Finset.mem_filter.mp hq).2
    obtain ⟨j', hj'⟩ := Fin.exists_succAbove_eq (x := q.2) (y := q.1) hne.symm
    rw [← hj']
    exact Work.BoseFixB1S.pairMassValue hℓ hV hA hVeq hAc w q.1 j'

/-! ## 4. The abstract pairing assembly -/

/-- **The pairing assembly.**  With `Φ = F p + G p` pointwise, a non-negative weight `wt`, the
four integrability facts per pair, and the mass identity `Σ_p ∫ F p²·wt p = 2·A2`,

`(√A2 − √(½ Σ_p ∫ G p²·wt p))² ≤ ∫ Φ²·(½ Σ_p wt p)`.

The proof is the sharp Cauchy–Schwarz/AM–GM pairing: the cross sum `Σ_p ∫ F p G p wt p` is bounded
by `√(2·A2·D)` with `D = Σ_p ∫ G p² wt p`, and `∫Φ²·(½Σwt) = A2 + (cross sum) + D/2`. -/
theorem pairingAssembly {ι : Type*} (s : Finset ι) {α : Type*} [MeasurableSpace α]
    {μ : MeasureTheory.Measure α} {F G wt : ι → α → ℝ} {Φ : α → ℝ} {A2 : ℝ}
    (hw : ∀ p x, 0 ≤ wt p x) (heq : ∀ p x, Φ x = F p x + G p x)
    (hF : ∀ p ∈ s, MeasureTheory.Integrable (fun x => F p x ^ 2 * wt p x) μ)
    (hFG : ∀ p ∈ s, MeasureTheory.Integrable (fun x => F p x * G p x * wt p x) μ)
    (hG : ∀ p ∈ s, MeasureTheory.Integrable (fun x => G p x ^ 2 * wt p x) μ)
    (hΦ : ∀ p ∈ s, MeasureTheory.Integrable (fun x => Φ x ^ 2 * wt p x) μ)
    (hmass : (∑ p ∈ s, ∫ x, F p x ^ 2 * wt p x ∂μ) = 2 * A2) :
    (Real.sqrt A2 - Real.sqrt ((∑ p ∈ s, ∫ x, G p x ^ 2 * wt p x ∂μ) / 2)) ^ 2
      ≤ ∫ x, Φ x ^ 2 * ((1 / 2) * ∑ p ∈ s, wt p x) ∂μ := by
  have hA2nn : 0 ≤ A2 := by
    have h1 : 0 ≤ ∑ p ∈ s, ∫ x, F p x ^ 2 * wt p x ∂μ :=
      Finset.sum_nonneg (fun p _ =>
        MeasureTheory.integral_nonneg (fun x => mul_nonneg (sq_nonneg _) (hw p x)))
    linarith
  have hDnn : 0 ≤ ∑ p ∈ s, ∫ x, G p x ^ 2 * wt p x ∂μ :=
    Finset.sum_nonneg (fun p _ =>
      MeasureTheory.integral_nonneg (fun x => mul_nonneg (sq_nonneg _) (hw p x)))
  have hCS : |∑ p ∈ s, ∫ x, F p x * G p x * wt p x ∂μ|
      ≤ Real.sqrt (2 * A2 * (∑ p ∈ s, ∫ x, G p x ^ 2 * wt p x ∂μ)) := by
    have h := Work.BoseFixB1.abs_pairIntegral_le_sqrt s (f := F) (g := G) (w := wt) hw hF hG hFG
    rwa [hmass] at h
  have hpairSum : (∫ x, Φ x ^ 2 * ((1 / 2) * ∑ p ∈ s, wt p x) ∂μ)
      = (1 / 2) * (∑ p ∈ s, ∫ x, Φ x ^ 2 * wt p x ∂μ) := by
    have hpt : ∀ x, Φ x ^ 2 * ((1 / 2) * ∑ p ∈ s, wt p x)
        = (1 / 2) * (∑ p ∈ s, Φ x ^ 2 * wt p x) := by
      intro x
      calc Φ x ^ 2 * ((1 / 2) * ∑ p ∈ s, wt p x)
          = Φ x ^ 2 * (∑ p ∈ s, (1 / 2) * wt p x) := by rw [Finset.mul_sum]
        _ = ∑ p ∈ s, Φ x ^ 2 * ((1 / 2) * wt p x) := by rw [Finset.mul_sum]
        _ = ∑ p ∈ s, (1 / 2) * (Φ x ^ 2 * wt p x) :=
            Finset.sum_congr rfl (fun p _ => by ring)
        _ = (1 / 2) * ∑ p ∈ s, Φ x ^ 2 * wt p x := by rw [Finset.mul_sum]
    rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpt),
      MeasureTheory.integral_const_mul,
      MeasureTheory.integral_finsetSum s (fun p hp => hΦ p hp)]
  have hsplit : (∑ p ∈ s, ∫ x, Φ x ^ 2 * wt p x ∂μ)
      = 2 * A2 + 2 * (∑ p ∈ s, ∫ x, F p x * G p x * wt p x ∂μ)
        + (∑ p ∈ s, ∫ x, G p x ^ 2 * wt p x ∂μ) := by
    have hper : ∀ p ∈ s, (∫ x, Φ x ^ 2 * wt p x ∂μ)
        = (∫ x, F p x ^ 2 * wt p x ∂μ) + 2 * (∫ x, F p x * G p x * wt p x ∂μ)
          + (∫ x, G p x ^ 2 * wt p x ∂μ) :=
      fun p hp => integral_sq_mul_eq_add (heq p) (hF p hp) (hFG p hp) (hG p hp)
    rw [Finset.sum_congr rfl hper, Finset.sum_add_distrib, Finset.sum_add_distrib, hmass,
      Finset.mul_sum]
  refine le_trans (sq_sub_sqrt_le hA2nn hDnn hCS) ?_
  rw [hpairSum, hsplit]
  linarith

/-! ## 5. The target -/

theorem pairSumGeSqSubSqrt {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v) (hv : 0 ≤ v) {M : ℕ} {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) {u : EuclideanSpace ℝ (Fin 3)} {n : ℕ} (Φ : Work.BoseKinLoc.BoxState n ℓ) (hV : 0 < Work.SmallBoxSliding.boxMass ℓ d u) (hM2 : 0 ≤ Work.BoseFixB1S.boxM2 (Work.SmallBoxSliding.boxMass ℓ d u) (Submission.BoseGases.dlBox ℓ d u) (Submission.BoseGases.wSmallPair M ℓ d u v)) (hint : ∀ p ∈ Submission.BoseGases.pairSet n, MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X n => Submission.BoseGases.wSmallPair M ℓ d u v (x p.1) (x p.2)) (Submission.BoseGases.abox n ℓ)) : (Real.sqrt (Work.BoseFixB1S.boxM2 (Work.SmallBoxSliding.boxMass ℓ d u) (Submission.BoseGases.dlBox ℓ d u) (Submission.BoseGases.wSmallPair M ℓ d u v) * Work.BoseFixB1S.boxPairCount (Work.SmallBoxSliding.boxMass ℓ d u) ℓ (Submission.BoseGases.dlBox ℓ d u) (Φ : Submission.BoseGases.X n → ℝ) / (2 * (Work.SmallBoxSliding.boxMass ℓ d u) ^ 2)) - Real.sqrt ((∑ p ∈ Submission.BoseGases.pairSet n, ∫ x in Submission.BoseGases.abox n ℓ, (((Φ : Submission.BoseGases.X n → ℝ) x) - Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u) (Submission.BoseGases.dlBox ℓ d u) p.1 (Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u) (Submission.BoseGases.dlBox ℓ d u) p.2 (Φ : Submission.BoseGases.X n → ℝ)) x) ^ 2 * Submission.BoseGases.wSmallPair M ℓ d u v (x p.1) (x p.2)) / 2)) ^ 2 ≤ Work.BoseFixB1.pairSum v M ℓ d u (Φ : Submission.BoseGases.X n → ℝ) := by
  classical
  rw [Work.BoseFixB1.pairSum]
  set V : ℝ := Work.SmallBoxSliding.boxMass ℓ d u with hVdef
  set A : Set E3 := Submission.BoseGases.dlBox ℓ d u with hAdef
  set w : E3 → E3 → ℝ := Submission.BoseGases.wSmallPair M ℓ d u v with hwdef
  have hVpos : 0 < V := hV
  have hVeq : V = (MeasureTheory.volume A).toReal := by
    rw [hVdef, hAdef, Work.SmallBoxSliding.boxMass_eq_measureReal, MeasureTheory.Measure.real_def]
  have hAmeas : MeasurableSet A := by
    rw [hAdef]; exact Work.SmallBoxSliding.measurableSet_dlBox ℓ d u
  have hAc : A ⊆ Submission.BoseGases.acube ℓ := by
    rw [hAdef]; exact Set.inter_subset_left
  have hΦc : Continuous (Φ : Submission.BoseGases.X n → ℝ) := Φ.contDiff.continuous
  have hint' : ∀ p ∈ Submission.BoseGases.pairSet n,
      MeasureTheory.Integrable (fun x : Submission.BoseGases.X n => w (x p.1) (x p.2))
        ((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X n)).restrict
          (Submission.BoseGases.abox n ℓ)) := fun p hp => hint p hp
  let F : Fin n × Fin n → Submission.BoseGases.X n → ℝ := fun p x =>
    Work.UBBInputs8.boxPInd V A p.1 (Work.UBBInputs8.boxPInd V A p.2 Φ) x
  let G : Fin n × Fin n → Submission.BoseGases.X n → ℝ := fun p x =>
    (Φ : Submission.BoseGases.X n → ℝ) x - F p x
  let wt : Fin n × Fin n → Submission.BoseGases.X n → ℝ := fun p x => w (x p.1) (x p.2)
  have hwnn : ∀ p x, 0 ≤ wt p x := fun p x => by
    show 0 ≤ w (x p.1) (x p.2)
    rw [hwdef]
    exact Work.BoseFixB1.wSmallPair_nonneg_qLHS hv M ℓ d u (x p.1) (x p.2)
  have heqFG : ∀ p x, (Φ : Submission.BoseGases.X n → ℝ) x = F p x + G p x := by
    intro p x
    dsimp only [G]
    ring
  have hF : ∀ p ∈ Submission.BoseGases.pairSet n,
      MeasureTheory.Integrable (fun x : Submission.BoseGases.X n => F p x ^ 2 * wt p x)
        ((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X n)).restrict
          (Submission.BoseGases.abox n ℓ)) :=
    fun p hp => (pairProductsIntegrable hℓ hVpos hAmeas hVeq hAc hΦc hint' hp).1
  have hFG : ∀ p ∈ Submission.BoseGases.pairSet n,
      MeasureTheory.Integrable (fun x : Submission.BoseGases.X n => F p x * G p x * wt p x)
        ((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X n)).restrict
          (Submission.BoseGases.abox n ℓ)) :=
    fun p hp => (pairProductsIntegrable hℓ hVpos hAmeas hVeq hAc hΦc hint' hp).2.1
  have hG : ∀ p ∈ Submission.BoseGases.pairSet n,
      MeasureTheory.Integrable (fun x : Submission.BoseGases.X n => G p x ^ 2 * wt p x)
        ((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X n)).restrict
          (Submission.BoseGases.abox n ℓ)) :=
    fun p hp => (pairProductsIntegrable hℓ hVpos hAmeas hVeq hAc hΦc hint' hp).2.2.1
  have hΦi : ∀ p ∈ Submission.BoseGases.pairSet n,
      MeasureTheory.Integrable
        (fun x : Submission.BoseGases.X n => (Φ : Submission.BoseGases.X n → ℝ) x ^ 2 * wt p x)
        ((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X n)).restrict
          (Submission.BoseGases.abox n ℓ)) :=
    fun p hp => (pairProductsIntegrable hℓ hVpos hAmeas hVeq hAc hΦc hint' hp).2.2.2
  have hmass : (∑ p ∈ Submission.BoseGases.pairSet n,
      ∫ x in Submission.BoseGases.abox n ℓ,
        (Work.UBBInputs8.boxPInd V A p.1 (Work.UBBInputs8.boxPInd V A p.2 Φ) x) ^ 2
          * w (x p.1) (x p.2))
      = 2 * (Work.BoseFixB1S.boxM2 V A w * Work.BoseFixB1S.boxPairCount V ℓ A Φ
          / (2 * V ^ 2)) := by
    have hmm := pairMassSumEq (N := n) (ℓ := ℓ) (V := V) hℓ hVpos hAmeas hVeq hAc w
      (Φ : Submission.BoseGases.X n → ℝ)
    rw [hmm]
    have hVne : V ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt hVpos)
    field_simp
  have hkey := pairingAssembly (Submission.BoseGases.pairSet n) (F := F) (G := G) (wt := wt)
    (Φ := (Φ : Submission.BoseGases.X n → ℝ))
    (A2 := Work.BoseFixB1S.boxM2 V A w * Work.BoseFixB1S.boxPairCount V ℓ A Φ / (2 * V ^ 2))
    (μ := (MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X n)).restrict
      (Submission.BoseGases.abox n ℓ))
    hwnn heqFG hF hFG hG hΦi hmass
  exact hkey

end Work.BoseFixB1S
