import ChallengeDeps
import Submission.Work.BoseFixB1S.abs_wSmallPair_g2_chiB_le
import Submission.Work.BoseFixB1S.flatBranchDefs
import Submission.Work.BoseFixB1S.pairing_le_chiSq_mul_abs_integral
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB1S

open MeasureTheory

set_option autoImplicit false
set_option linter.unusedVariables false

noncomputable section

-- NOTE: `ℝ³` is the *global* `notation "ℝ³" => EuclideanSpace ℝ (Fin 3)` of
-- `Submission.Work.BoseKinLoc.Defs`, which is in the import cone of this file; a
-- `local notation` here would be ambiguous.

/-! ## The two parametric integrability statements

Both are stated for the raw data `M, ℓ, d, u` (and the radius `R0 = R` of the support of `v`),
so that the target theorem is a pure unfolding of the abbreviations `boxA`, `boxW1`, `boxW2`. -/

/-- **The localised two-body kernel with numerator `g₂` is integrable on `dlBox ×ˢ dlBox`.**

The route is the *pairing* form of the FS pointwise domination rather than a uniform bound: the
kernel is dominated by `2·(smallConvLower M)⁻¹·χ_{B}(x)·|g₂(x−y)|·χ_{B}(y)`, and
`pairing_le_chiSq_mul_abs_integral` (Tonelli + translation invariance + AM–GM) shows that this
last expression is *globally* integrable as soon as `g₂ ∈ L¹` and `χ_{B}` is a nonnegative
continuous compactly supported cutoff; restricting to `dlBox ×ˢ dlBox` is then monotonicity.

(The exponent-`2` diagonal singularity of `g₂` is integrable in three dimensions, which is why
the pairing form is the right one: a *uniform* bound on `g₂` is not available under the standing
FS hypotheses, which only assume `v ∈ L¹`, `v ≥ 0`, `v` radial, compactly supported.) -/
private theorem integrable_wSmallPair_g2_dlBox {v : ℝ³ → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : ℝ³) R)
    {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (hRd : R ≤ ℓ * d / 16) (hRχ : R ≤ ℓ * Submission.BoseGases.chiR0) (u : ℝ³) :
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
    Submission.BoseGases.g2_integrable hR hv hvrad hv_supp h
  -- the pairing bound, globally in `L¹(ℝ³ × ℝ³)`
  obtain ⟨hmaj_full, -⟩ := pairing_le_chiSq_mul_abs_integral hχ0 hχc hχs hg2
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
      subPair_aemeasurable hg2.aemeasurable
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
          abs_wSmallPair_g2_chiB_le hv_supp hR h hM hℓ hd hRd hRχ u p.1 p.2
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
private theorem integrableOn_w1Fibre_dlBox {v : ℝ³ → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : ℝ³) R)
    {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (hRd : R ≤ ℓ * d / 16) (hRχ : R ≤ ℓ * Submission.BoseGases.chiR0) (u : ℝ³) :
    MeasureTheory.IntegrableOn
      (fun z : ℝ³ => Submission.BoseGases.w1Fibre ℓ
        (Submission.BoseGases.wSmall1Pair h M ℓ d u) z)
      (Submission.BoseGases.dlBox ℓ d u) := by
  have hg0 : MeasureTheory.Integrable (Submission.BoseGases.g0 v h) :=
    Submission.BoseGases.g0_integrable hR hv_supp h
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
    Work.BoseFixB1.wSmall1Pair_fibre_abs_le hv_supp hR hv hvrad h hM hℓ hd hRd hRχ u z

/-- **The two integrability side conditions of `boxQ0_ge_counts` at FS's parameters.**
Route for the pair kernel: `Work.BoseFixB1S.abs_wSmallPair_g2_chiB_le` bounds
`|wSmallPair M ℓ d u (g2 v h) x y|` by `C·chiSmallB M ℓ d u x·|g2 v h (x−y)|·chiSmallB M ℓ d u y`,
and the `χ ⊗ |g₂| ⊗ χ` pairing is globally integrable (`pairing_le_chiSq_mul_abs_integral`),
hence integrable on `dlBox ℓ d u ×ˢ dlBox ℓ d u`.  For the fibre:
`Work.BoseFixB1.wSmall1Pair_fibre_abs_le` bounds `|w1Fibre ℓ (wSmall1Pair h M ℓ d u) z|`
uniformly by `Cfib`, and `dlBox ℓ d u` has finite measure
(`Work.SmallBoxSliding.volume_dlBox_lt_top`). -/
theorem mf_boxQ0_integrable_inputs {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ}
    (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    {μ : ℝ} {u : EuclideanSpace ℝ (Fin 3)}
    (hℓ : 0 < Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
    (hd : 0 < (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d)
    (hR16 : R ≤ Work.BoseBox.sideAt μ (_root_.BoseGases.a v)
      * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d / 16)
    (hRχ : R ≤ Work.BoseBox.sideAt μ (_root_.BoseGases.a v) * Submission.BoseGases.chiR0) :
    MeasureTheory.Integrable
        (fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
          Work.BoseFixB1S.boxW2 h μ u p.1 p.2)
        (MeasureTheory.volume.restrict
          (Work.BoseFixB1S.boxA v μ u ×ˢ Work.BoseFixB1S.boxA v μ u))
      ∧ MeasureTheory.IntegrableOn
          (fun z : EuclideanSpace ℝ (Fin 3) =>
            Submission.BoseGases.w1Fibre (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Work.BoseFixB1S.boxW1 h μ u) z)
          (Work.BoseFixB1S.boxA v μ u) := by
  have hM1 : 1 ≤ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M := by
    rw [Work.BoseFixB1.M_eq_mValue]
    norm_num [Work.BoseBox.mValue]
  refine ⟨?_, ?_⟩
  · simpa only [boxW2, boxA] using
      integrable_wSmallPair_g2_dlBox (v := v) h hv hvrad hR hv_supp hM1 hℓ hd hR16 hRχ u
  · simpa only [boxW1, boxA] using
      integrableOn_w1Fibre_dlBox (v := v) h hv hvrad hR hv_supp hM1 hℓ hd hR16 hRχ u

end

end Work.BoseFixB1S
