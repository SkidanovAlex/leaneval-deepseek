import ChallengeDeps
import Submission.Work.BoseFixB1S.Clean.Fragments
import Submission.Work.BoseFixB1S.boxPInd_boxComp
import Submission.Work.BoseFixB1S.mf_boxQ0_integrable_inputs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1.SectorAux.boxFragmentsIntegrableGood`

The **state-generic** (`GoodState`) form of the pair-fragment integrability at the *singular,
localised* sliding kernel `wSmallPair M ℓ d u (g₂ v h)` of FS `eq:HBU`, together with the two
side integrability statements that the sector assembly needs:

* `∀ p ∈ pairSet N`, the fragment `(P_i Q_j Φ)(P_i P_j Φ) · w₂(xᵢ,xⱼ)` is `IntegrableOn (abox N ℓ)`;
* `wSmallPair M ℓ d u (g₂ v h)` is `Integrable` on `dlBox ℓ d u ×ˢ dlBox ℓ d u`;
* the `w₁`-fibre `w1Fibre ℓ (wSmall1Pair h M ℓ d u)` is `IntegrableOn (dlBox ℓ d u)`.

The difference with `Work.BoseFixB1.Clean.boxFragmentsIntegrable` (and with
`Work.BoseFixB1.SectorPiece.fragsIntegrable_of_measurable_bound`) is only in *how* the state is
presented: here the hypothesis is `Work.BoseFixB1S.GoodState ℓ Φ`, i.e. `Φ` is measurable and
bounded on the compact box, which is precisely the two facts those lemmas consume.

The first fragment is the integrability brick `Work.BoseFixB1.integrableOn_slot_wSmallPair`
applied to the *bounded measurable* slot multiplier
`S = P_i(Q_jΦ)·P_i(P_jΦ)`: the two box readings are measurable
(`measurable_boxPInd`, `measurable_boxQIndAux`) and bounded on the box by `2C` and `C`
(`abs_boxPInd_le_nonneg`, `abs_boxQInd_le_nonneg` — the `0 ≤ volA` versions, since
`0 < boxMass ℓ d u` is *not* assumed).

The two `dlBox` statements are the general-parameter versions of the two private lemmas of
`Submission/Work/BoseFixB1S/mf_boxQ0_integrable_inputs.lean`: the pair kernel is dominated by
`χ_{B}(x)·|g₂(x−y)|·χ_{B}(y)`, whose `L¹`-integrability is the pairing form of the FS pointwise
domination (`pairing_le_chiSq_mul_abs_integral` + `abs_wSmallPair_g2_chiB_le`); the fibre is
bounded uniformly in `z` by `wSmall1Pair_fibre_abs_le` while `dlBox ℓ d u` has finite measure.
-/

noncomputable section

open MeasureTheory

namespace Work.BoseFixB1.SectorAux

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-! ## Elementary helpers -/

/-- `v` vanishes outside `ball 0 R` (from the support hypothesis on its closed support). -/
private theorem vZeroS {v : ℝ³ → ℝ} {R : ℝ}
    (hv_supp : tsupport v ⊆ Metric.ball (0 : ℝ³) R) {z : ℝ³} (hz : R ≤ ‖z‖) : v z = 0 := by
  by_contra h
  have hmem : z ∈ tsupport v := subset_tsupport v (by simpa using h)
  have hball : z ∈ Metric.ball (0 : ℝ³) R := hv_supp hmem
  have hlt : ‖z‖ < R := by simpa [Metric.mem_ball, dist_eq_norm] using hball
  linarith

/-- `|a·b| ≤ A·B` for `A, B ≥ 0` and `|a| ≤ A`, `|b| ≤ B`. -/
private theorem abs_pair_mul_le' {a b A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (ha : |a| ≤ A) (hb : |b| ≤ B) : |a * b| ≤ A * B := by
  rw [abs_mul]
  exact mul_le_mul ha hb (abs_nonneg _) hA

/-! ## The two `dlBox` integrability statements, at general parameters -/

/-- **The localised two-body kernel with numerator `g₂` is integrable on `dlBox ×ˢ dlBox`.**

The kernel is dominated by `2·(smallConvLower M)⁻¹·χ_{B}(x)·|g₂(x−y)|·χ_{B}(y)`, and
`pairing_le_chiSq_mul_abs_integral` (Tonelli + translation invariance + AM–GM) shows that the
`χ ⊗ |g₂| ⊗ χ` pairing is *globally* integrable as soon as `g₂ ∈ L¹` and `χ_{B}` is a nonnegative
continuous compactly supported cutoff; restricting to `dlBox ×ˢ dlBox` is then monotonicity. -/
theorem integrable_wSmallPair_g2_dlBox_aux {v : ℝ³ → ℝ} {R0 : ℝ}
    (h : Work.UBB.ScatSol v) (hv : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v)
    (hR0 : 0 < R0) (hv_supp : tsupport v ⊆ Metric.ball (0 : ℝ³) R0)
    {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (hRd : R0 ≤ ℓ * d / 16) (hRχ : R0 ≤ ℓ * Submission.BoseGases.chiR0) (u : ℝ³) :
    MeasureTheory.Integrable
      (fun p : ℝ³ × ℝ³ =>
        Submission.BoseGases.wSmallPair M ℓ d u (Submission.BoseGases.g2 v h) p.1 p.2)
      ((MeasureTheory.volume : MeasureTheory.Measure (ℝ³ × ℝ³)).restrict
        (Submission.BoseGases.dlBox ℓ d u ×ˢ Submission.BoseGases.dlBox ℓ d u)) := by
  have hχ0 : ∀ x : ℝ³, 0 ≤ Submission.BoseGases.chiSmallB M ℓ d u x :=
    fun x => Submission.BoseGases.chiSmallB_nonneg M ℓ d u x
  have hχc : Continuous (fun x : ℝ³ => Submission.BoseGases.chiSmallB M ℓ d u x) :=
    Submission.BoseGases.chiSmallB_continuous hM hℓ hd u
  have hχs : HasCompactSupport (fun x : ℝ³ => Submission.BoseGases.chiSmallB M ℓ d u x) :=
    Submission.BoseGases.chiSmallB_hasCompactSupport hM hℓ u
  have hg2 : MeasureTheory.Integrable (Submission.BoseGases.g2 v h) :=
    Submission.BoseGases.g2_integrable hR0 hv hvrad hv_supp h
  -- the pairing bound, globally in `L¹(ℝ³ × ℝ³)`
  obtain ⟨hmaj_full, -⟩ := Work.BoseFixB1S.pairing_le_chiSq_mul_abs_integral hχ0 hχc hχs hg2
  -- restrict the majorant to the box
  have hmaj : MeasureTheory.Integrable
      (fun p : ℝ³ × ℝ³ => 2 * (Work.SmallBoxSliding.smallConvLower M)⁻¹ *
        (Submission.BoseGases.chiSmallB M ℓ d u p.1 *
          |Submission.BoseGases.g2 v h (p.1 - p.2)| *
          Submission.BoseGases.chiSmallB M ℓ d u p.2))
      ((MeasureTheory.volume : MeasureTheory.Measure (ℝ³ × ℝ³)).restrict
        (Submission.BoseGases.dlBox ℓ d u ×ˢ Submission.BoseGases.dlBox ℓ d u)) :=
    (hmaj_full.const_mul (2 * (Work.SmallBoxSliding.smallConvLower M)⁻¹)).mono_measure
      Measure.restrict_le_self
  refine MeasureTheory.Integrable.mono' hmaj ?_ ?_
  · -- a.e. strong measurability of the kernel
    have hchiB : Measurable (fun x : ℝ³ => Submission.BoseGases.chiSmallB M ℓ d u x) := hχc.measurable
    have h1 : AEMeasurable (fun p : ℝ³ × ℝ³ => Submission.BoseGases.chiSmallB M ℓ d u p.1)
        (MeasureTheory.volume : MeasureTheory.Measure (ℝ³ × ℝ³)) :=
      (hchiB.comp measurable_fst).aemeasurable
    have h2 : AEMeasurable (fun p : ℝ³ × ℝ³ => Submission.BoseGases.chiSmallB M ℓ d u p.2)
        (MeasureTheory.volume : MeasureTheory.Measure (ℝ³ × ℝ³)) :=
      (hchiB.comp measurable_snd).aemeasurable
    have h3 : AEMeasurable (fun p : ℝ³ × ℝ³ => Submission.BoseGases.g2 v h (p.1 - p.2))
        (MeasureTheory.volume : MeasureTheory.Measure (ℝ³ × ℝ³)) :=
      Work.BoseFixB1S.subPair_aemeasurable hg2.aemeasurable
    have h4 : AEMeasurable
        (fun p : ℝ³ × ℝ³ => Submission.BoseGases.convScaleSmall M (ℓ * d) (p.1 - p.2))
        (MeasureTheory.volume : MeasureTheory.Measure (ℝ³ × ℝ³)) :=
      (Work.BoseFixB1.aestronglyMeasurable_convScaleSmall_diff M (ℓ * d)
        (MeasureTheory.volume : MeasureTheory.Measure (ℝ³ × ℝ³))).aemeasurable
    have h5 : AEMeasurable (fun p : ℝ³ × ℝ³ => Submission.BoseGases.convScale ℓ (p.1 - p.2))
        (MeasureTheory.volume : MeasureTheory.Measure (ℝ³ × ℝ³)) :=
      ((Submission.BoseGases.convScale_continuous ℓ).measurable.comp
        (measurable_fst.sub measurable_snd)).aemeasurable
    have h6 : AEMeasurable (fun p : ℝ³ × ℝ³ =>
        Submission.BoseGases.chiSmallB M ℓ d u p.1 *
          ((Submission.BoseGases.g2 v h (p.1 - p.2)
            / Submission.BoseGases.convScaleSmall M (ℓ * d) (p.1 - p.2))
            / Submission.BoseGases.convScale ℓ (p.1 - p.2)) *
        Submission.BoseGases.chiSmallB M ℓ d u p.2)
        (MeasureTheory.volume : MeasureTheory.Measure (ℝ³ × ℝ³)) :=
      (h1.mul ((h3.div h4).div h5)).mul h2
    refine (h6.aestronglyMeasurable.mono_measure
      (Measure.restrict_le_self (μ := (MeasureTheory.volume : MeasureTheory.Measure (ℝ³ × ℝ³)))
        (s := Submission.BoseGases.dlBox ℓ d u ×ˢ Submission.BoseGases.dlBox ℓ d u))).congr ?_
    exact Filter.Eventually.of_forall (fun p => by
      simp only [Submission.BoseGases.wSmallPair, Submission.BoseGases.wSmallScaled])
  · -- the a.e. pointwise bound by the majorant
    refine Filter.Eventually.of_forall (fun p => ?_)
    rw [Real.norm_eq_abs]
    calc |Submission.BoseGases.wSmallPair M ℓ d u (Submission.BoseGases.g2 v h) p.1 p.2|
        ≤ 2 * (Work.SmallBoxSliding.smallConvLower M)⁻¹ *
            Submission.BoseGases.chiSmallB M ℓ d u p.1 *
            |Submission.BoseGases.g2 v h (p.1 - p.2)| *
            Submission.BoseGases.chiSmallB M ℓ d u p.2 :=
          Work.BoseFixB1S.abs_wSmallPair_g2_chiB_le hv_supp hR0 h hM hℓ hd hRd hRχ u p.1 p.2
      _ = 2 * (Work.SmallBoxSliding.smallConvLower M)⁻¹ *
            (Submission.BoseGases.chiSmallB M ℓ d u p.1 *
              |Submission.BoseGases.g2 v h (p.1 - p.2)| *
              Submission.BoseGases.chiSmallB M ℓ d u p.2) := by ring

/-- **The `w₁`-fibre is integrable on `dlBox`.**

The fibre bound `Work.BoseFixB1.wSmall1Pair_fibre_abs_le` is *uniform* in `z` (it is the
`L¹`-norm of `g₀`, smeared by the two cutoff factors), and `dlBox ℓ d u` has finite measure
(`Work.SmallBoxSliding.volume_dlBox_lt_top`), so `Integrable.of_bound` applies.  Measurability
is `Work.BoseFixB1.aestronglyMeasurable_wSmallPairFibre`, transported from `acube ℓ` to the
smaller set `dlBox ℓ d u`. -/
theorem integrableOn_w1Fibre_dlBox_aux {v : ℝ³ → ℝ} {R0 : ℝ}
    (h : Work.UBB.ScatSol v) (hv : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v)
    (hR0 : 0 < R0) (hv_supp : tsupport v ⊆ Metric.ball (0 : ℝ³) R0)
    {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (hRd : R0 ≤ ℓ * d / 16) (hRχ : R0 ≤ ℓ * Submission.BoseGases.chiR0) (u : ℝ³) :
    MeasureTheory.IntegrableOn
      (fun z : ℝ³ => Submission.BoseGases.w1Fibre ℓ
        (Submission.BoseGases.wSmall1Pair h M ℓ d u) z)
      (Submission.BoseGases.dlBox ℓ d u) := by
  have hg0 : MeasureTheory.Integrable (Submission.BoseGases.g0 v h) :=
    Submission.BoseGases.g0_integrable hR0 hv_supp h
  have hfin : IsFiniteMeasure
      ((MeasureTheory.volume : MeasureTheory.Measure ℝ³).restrict
        (Submission.BoseGases.dlBox ℓ d u)) :=
    isFiniteMeasure_restrict.mpr
      (ne_of_lt (Work.SmallBoxSliding.volume_dlBox_lt_top hℓ d u))
  have hmeas : AEStronglyMeasurable
      (fun z : ℝ³ => Submission.BoseGases.w1Fibre ℓ
        (Submission.BoseGases.wSmall1Pair h M ℓ d u) z)
      ((MeasureTheory.volume : MeasureTheory.Measure ℝ³).restrict
        (Submission.BoseGases.dlBox ℓ d u)) := by
    have h0 := Work.BoseFixB1.aestronglyMeasurable_wSmallPairFibre (ℓ := ℓ) (d := d) M u
      hg0.aemeasurable
    refine (h0.mono_measure (Measure.restrict_mono
      (Work.SmallBoxSliding.dlBox_subset_acube ℓ d u) le_rfl)).congr ?_
    exact Filter.Eventually.of_forall (fun z => by
      simp only [Submission.BoseGases.w1Fibre, Submission.BoseGases.wSmall1Pair])
  refine MeasureTheory.Integrable.of_bound hmeas
    ((Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M)
      * ((2 * (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M)
          / Work.SmallBoxSliding.smallConvLower M)
        * (8 * Real.pi * _root_.BoseGases.a v)))
    (Filter.Eventually.of_forall (fun z => ?_))
  rw [Real.norm_eq_abs, Submission.BoseGases.w1Fibre]
  simpa only [Submission.BoseGases.wSmall1Pair] using
    Work.BoseFixB1.wSmall1Pair_fibre_abs_le hv_supp hR0 hv hvrad h hM hℓ hd hRd hRχ u z

/-! ## The target -/

theorem boxFragmentsIntegrableGood {v : EuclideanSpace ℝ (Fin 3) → ℝ} {R0 : ℝ}
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R0) (hR0 : 0 < R0)
    (hv : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v) (hv1 : MeasureTheory.MemLp v 1)
    (h : ∃ w : EuclideanSpace ℝ (Fin 3) → ℝ,
      _root_.BoseGases.IsRadial w ∧ _root_.BoseGases.IsScatteringSolution w v)
    {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (hR : R0 ≤ ℓ * d / 16) (hRχ : R0 ≤ ℓ * Submission.BoseGases.chiR0)
    (u : EuclideanSpace ℝ (Fin 3)) {N : ℕ} {Φ : Submission.BoseGases.X N → ℝ}
    (hΦg : Work.BoseFixB1S.GoodState ℓ Φ) :
    (∀ p ∈ Submission.BoseGases.pairSet N, MeasureTheory.IntegrableOn
        (fun x : Submission.BoseGases.X N =>
          (Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
              (Submission.BoseGases.dlBox ℓ d u) p.1
              (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
                (Submission.BoseGases.dlBox ℓ d u) p.2 Φ) x)
            * (Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
                (Submission.BoseGases.dlBox ℓ d u) p.1
                (Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
                  (Submission.BoseGases.dlBox ℓ d u) p.2 Φ) x)
            * (Submission.BoseGases.wSmallPair M ℓ d u (Submission.BoseGases.g2 v h)
                (x p.1) (x p.2)))
        (Submission.BoseGases.abox N ℓ) MeasureTheory.volume)
    ∧ (MeasureTheory.Integrable (fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
        Submission.BoseGases.wSmallPair M ℓ d u (Submission.BoseGases.g2 v h) p.1 p.2)
        ((MeasureTheory.volume : MeasureTheory.Measure
          (EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3))).restrict
            (Submission.BoseGases.dlBox ℓ d u ×ˢ Submission.BoseGases.dlBox ℓ d u)))
    ∧ (MeasureTheory.IntegrableOn (fun z : EuclideanSpace ℝ (Fin 3) =>
        Submission.BoseGases.w1Fibre ℓ (Submission.BoseGases.wSmall1Pair h M ℓ d u) z)
        (Submission.BoseGases.dlBox ℓ d u)) := by
  set volA : ℝ := Work.SmallBoxSliding.boxMass ℓ d u with hvolAdef
  set A : Set ℝ³ := Submission.BoseGases.dlBox ℓ d u with hAdef
  have hAms : MeasurableSet A := by
    rw [hAdef]; exact Work.SmallBoxSliding.measurableSet_dlBox ℓ d u
  have hAc : A ⊆ Submission.BoseGases.acube ℓ := by
    rw [hAdef]; exact Work.SmallBoxSliding.dlBox_subset_acube ℓ d u
  have hvolA : volA = (MeasureTheory.volume A).toReal := by
    rw [hvolAdef, hAdef, Work.SmallBoxSliding.boxMass_eq_measureReal,
      MeasureTheory.Measure.real_def]
  have hvol0 : 0 ≤ volA := by rw [hvolA]; exact ENNReal.toReal_nonneg
  obtain ⟨hΦm, C, hΦb⟩ := hΦg
  -- the bound `C` is nonnegative, `abox N ℓ` being nonempty
  have hC0 : 0 ≤ C := le_trans (abs_nonneg (Φ 0))
    (hΦb 0 (Submission.BoseGases.zero_mem_abox (N := N) (ℓ := ℓ) hℓ.le))
  have h2C : (0 : ℝ) ≤ 2 * C := by linarith
  have hQΦ : ∀ k : Fin N, ∀ x ∈ Submission.BoseGases.abox N ℓ,
      |Work.UBBInputs8.boxQInd volA A k Φ x| ≤ 2 * C :=
    fun k => Work.BoseFixB1.Clean.abs_boxQInd_le_nonneg hℓ hvol0 hAms hvolA hAc k hC0 hΦb
  have hPΦ : ∀ k : Fin N, ∀ x ∈ Submission.BoseGases.abox N ℓ,
      |Work.UBBInputs8.boxPInd volA A k Φ x| ≤ C :=
    fun k => Work.BoseFixB1.Clean.abs_boxPInd_le_nonneg hℓ hvol0 hAms hvolA hAc k hC0 hΦb
  -- the two numerators
  have hg2int : MeasureTheory.Integrable (Submission.BoseGases.g2 v h) :=
    Submission.BoseGases.g2_integrable hR0 hv hvrad hv_supp h
  have hg2supp : ∀ z : ℝ³, R0 ≤ ‖z‖ → Submission.BoseGases.g2 v h z = 0 :=
    fun z hz => Submission.BoseGases.g2_zero_of_norm_ge hv_supp hz h
  have hfrag : ∀ p ∈ Submission.BoseGases.pairSet N, MeasureTheory.IntegrableOn
      (fun x : Submission.BoseGases.X N =>
        (Work.UBBInputs8.boxPInd volA A p.1 (Work.UBBInputs8.boxQInd volA A p.2 Φ) x)
          * (Work.UBBInputs8.boxPInd volA A p.1 (Work.UBBInputs8.boxPInd volA A p.2 Φ) x)
          * (Submission.BoseGases.wSmallPair M ℓ d u (Submission.BoseGases.g2 v h)
              (x p.1) (x p.2)))
      (Submission.BoseGases.abox N ℓ) MeasureTheory.volume := by
    intro p hp
    have hpne : p.1 ≠ p.2 := (Finset.mem_filter.mp hp).2
    have hQm : Measurable (Work.UBBInputs8.boxQInd volA A p.2 Φ) :=
      Work.BoseFixB1.Clean.measurable_boxQIndAux volA A hAms p.2 hΦm
    have hPm : Measurable (Work.UBBInputs8.boxPInd volA A p.2 Φ) :=
      Work.BoseFixB1S.measurable_boxPInd volA A hAms p.2 hΦm
    have hS1m : Measurable (fun x : Submission.BoseGases.X N =>
        Work.UBBInputs8.boxPInd volA A p.1 (Work.UBBInputs8.boxQInd volA A p.2 Φ) x) :=
      Work.BoseFixB1S.measurable_boxPInd volA A hAms p.1 hQm
    have hS2m : Measurable (fun x : Submission.BoseGases.X N =>
        Work.UBBInputs8.boxPInd volA A p.1 (Work.UBBInputs8.boxPInd volA A p.2 Φ) x) :=
      Work.BoseFixB1S.measurable_boxPInd volA A hAms p.1 hPm
    have hS1b : ∀ x ∈ Submission.BoseGases.abox N ℓ,
        |Work.UBBInputs8.boxPInd volA A p.1 (Work.UBBInputs8.boxQInd volA A p.2 Φ) x| ≤ 2 * C :=
      Work.BoseFixB1.Clean.abs_boxPInd_le_nonneg (C := 2 * C) hℓ hvol0 hAms hvolA hAc p.1 h2C
        (hQΦ p.2)
    have hS2b : ∀ x ∈ Submission.BoseGases.abox N ℓ,
        |Work.UBBInputs8.boxPInd volA A p.1 (Work.UBBInputs8.boxPInd volA A p.2 Φ) x| ≤ C :=
      Work.BoseFixB1.Clean.abs_boxPInd_le_nonneg hℓ hvol0 hAms hvolA hAc p.1 hC0 (hPΦ p.2)
    have hSm : MeasureTheory.AEStronglyMeasurable
        (fun x : Submission.BoseGases.X N =>
          (Work.UBBInputs8.boxPInd volA A p.1 (Work.UBBInputs8.boxQInd volA A p.2 Φ) x)
            * (Work.UBBInputs8.boxPInd volA A p.1 (Work.UBBInputs8.boxPInd volA A p.2 Φ) x))
        (MeasureTheory.volume.restrict (Submission.BoseGases.abox N ℓ)) :=
      (hS1m.mul hS2m).aestronglyMeasurable
    have hSb : ∀ᵐ x ∂(MeasureTheory.volume.restrict (Submission.BoseGases.abox N ℓ)),
        |(Work.UBBInputs8.boxPInd volA A p.1 (Work.UBBInputs8.boxQInd volA A p.2 Φ) x)
            * (Work.UBBInputs8.boxPInd volA A p.1 (Work.UBBInputs8.boxPInd volA A p.2 Φ) x)|
          ≤ (2 * C) * C := by
      rw [MeasureTheory.ae_restrict_iff' (Submission.BoseGases.abox_measurable N ℓ)]
      exact Filter.Eventually.of_forall (fun x hx =>
        abs_pair_mul_le' h2C hC0 (hS1b x hx) (hS2b x hx))
    exact Work.BoseFixB1.integrableOn_slot_wSmallPair (N := N) (ℓ := ℓ) (d := d) (R := R0)
      (f := Submission.BoseGases.g2 v h)
      (S := fun x : Submission.BoseGases.X N =>
        (Work.UBBInputs8.boxPInd volA A p.1 (Work.UBBInputs8.boxQInd volA A p.2 Φ) x)
          * (Work.UBBInputs8.boxPInd volA A p.1 (Work.UBBInputs8.boxPInd volA A p.2 Φ) x))
      (B := (2 * C) * C) hℓ hd hg2int hg2supp hM hR hRχ u hpne hSm (by positivity) hSb
  refine ⟨hfrag, ?_, ?_⟩
  · exact integrable_wSmallPair_g2_dlBox_aux (v := v) (R0 := R0) h hv hvrad hR0 hv_supp hM hℓ hd
      hR hRχ u
  · exact integrableOn_w1Fibre_dlBox_aux (v := v) (R0 := R0) h hv hvrad hR0 hv_supp hM hℓ hd
      hR hRχ u

end Work.BoseFixB1.SectorAux
