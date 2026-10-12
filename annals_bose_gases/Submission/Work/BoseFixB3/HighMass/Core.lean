import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB3.HighMass.OneBody
import Submission.Work.BoseFixB3.HighMass.aemeasurable_momForm_fibre
import Submission.Work.BoseFixB3.HighMass.highSlot_sq_peel
import Submission.Work.BoseFixB3.HighMass.lowMult_sq_le_ae_of_nonpos
import Submission.Work.BoseFixB3.HighMass.momForm_eq_sq_of_d_eq_zero
import Submission.Work.BoseFixB3.HighMass.momForm_fibre_peel
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB3.HighMass.Core`

The one-body inequality lying behind FS `eq:QLs_giveNplusH`:

  `∫_{acube ℓ} (Q₀ψ − f_L Q₀ψ)² ≤ momForm ℓ d 0 ψ`,   for `κ = (d²ℓ)⁻¹`,

together with its slot-lifted form
`∫_{abox (m+1) ℓ} (Q̄_{L,i}Q_iΦ)² ≤ ℓ⁻³ ∫_{abox (m+1) ℓ} 1_{Λ}(xᵢ)·momForm(fibreᵢΦ x)`.

-/

noncomputable section

open scoped Real Topology BigOperators ENNReal
open MeasureTheory Filter Metric

namespace Work.BoseFixB3.HighMass

open _root_.BoseGases Submission.BoseGases Work.BoseBoxFix Work.BoseKinLoc Work.BSKinetic
open Work.BoseKinLoc.Sector Work.BoseKinLoc.Kinetic

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false


/-! ## 1. The localised mean-free state is in `L¹ ∩ L²` -/

/-- The complexified mean-free box state `1_{acube ℓ}·Q₀ψ` of a **continuous** `ψ` is in
`L¹ ∩ L²`: it is supported in the box `acube ℓ` (finite volume) and bounded there by
compactness of `acube ℓ` and continuity of `ψ − m₀`. -/
lemma memLp_boxState {ℓ : ℝ} (hℓ : 0 < ℓ) {ψ : ℝ³ → ℝ} (hψ : Continuous ψ) :
    MemLp (fun z : ℝ³ => ((indU ℓ 0 z : ℝ) : ℂ) * ((bsQ ℓ 0 ψ z : ℝ) : ℂ)) 1 volume
      ∧ MemLp (fun z : ℝ³ => ((indU ℓ 0 z : ℝ) : ℂ) * ((bsQ ℓ 0 ψ z : ℝ) : ℂ)) 2 volume := by
  have hbox_meas : MeasurableSet (acube ℓ) := acube_measurable ℓ
  have hvol : volume (acube ℓ) ≠ ∞ := (acube_lt_top ℓ hℓ.le).ne
  have hQc : Continuous (bsQ ℓ 0 ψ) := by
    show Continuous (fun x : ℝ³ => ψ x - bsMean ℓ 0 ψ)
    exact hψ.sub continuous_const
  obtain ⟨C, hC⟩ := (acube_compact hℓ).exists_bound_of_continuousOn hQc.continuousOn
  have hM0 : 0 ≤ max C 0 := le_max_right _ _
  have hC' : ∀ x ∈ acube ℓ, ‖bsQ ℓ 0 ψ x‖ ≤ max C 0 :=
    fun x hx => le_trans (hC x hx) (le_max_left _ _)
  have hfun : (fun z : ℝ³ => ((indU ℓ 0 z : ℝ) : ℂ) * ((bsQ ℓ 0 ψ z : ℝ) : ℂ))
      = (acube ℓ).indicator (fun z => ((bsQ ℓ 0 ψ z : ℝ) : ℂ)) := by
    rw [indU_zero]
    funext z
    by_cases hz : z ∈ acube ℓ <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, hz]
  have haesm : AEStronglyMeasurable
      ((acube ℓ).indicator (fun z => ((bsQ ℓ 0 ψ z : ℝ) : ℂ))) volume :=
    ((Complex.continuous_ofReal.comp hQc).aestronglyMeasurable).indicator hbox_meas
  have hbound : ∀ᵐ z ∂volume,
      ‖(acube ℓ).indicator (fun z => ((bsQ ℓ 0 ψ z : ℝ) : ℂ)) z‖
        ≤ ‖(acube ℓ).indicator (fun _ => ((max C 0 : ℝ) : ℂ)) z‖ := by
    refine Eventually.of_forall (fun z => ?_)
    by_cases hz : z ∈ acube ℓ
    · rw [Set.indicator_of_mem hz, Set.indicator_of_mem hz]
      rw [show ‖((bsQ ℓ 0 ψ z : ℝ) : ℂ)‖ = ‖bsQ ℓ 0 ψ z‖ from by simp]
      rw [show ‖(((max C 0 : ℝ) : ℂ))‖ = ‖(max C 0 : ℝ)‖ from by simp]
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hM0]
      exact hC' z hz
    · simp [hz]
  constructor
  · rw [hfun]
    exact (memLp_indicator_const 1 hbox_meas ((max C 0 : ℝ) : ℂ) (Or.inr hvol)).mono
      haesm hbound
  · rw [hfun]
    exact (memLp_indicator_const 2 hbox_meas ((max C 0 : ℝ) : ℂ) (Or.inr hvol)).mono
      haesm hbound

/-! ## 2. The one-body inequality -/

/-- **The one-body inequality behind FS `eq:QLs_giveNplusH`.**

For `κ = (d²ℓ)⁻¹`, `ℓ > 0` and a continuous one-body state `Ψ`, the squared
complementary cut-off `1 − f_L` of the mean-free box state is dominated by the
large-momentum form of `Ψ` in the box:

  `∫_{acube ℓ} (Q₀Ψ − f_L(Q₀Ψ))² ≤ momForm ℓ d 0 Ψ`.

For `κ > 0` this is `oneBody_box_le` (the weak/duality bound with weight `(1−f_L)²`)
followed by the pointwise symbol bound `(1−f_L)² ≤ 1_{(d²ℓ)⁻¹,∞)}` of `one_sub_sq_le_momProj`.
For `κ = 0` (equivalently `d = 0`) the cut-off is trivial (`f = 1` on `(−∞,1]`), the
multiplier is either the identity or `0` a.e. (`lowMult_sq_le_ae_of_nonpos`), and
`momForm ℓ 0 0 Ψ = ∫_{acube ℓ}(Q₀Ψ)²`. -/
theorem oneBody_le_momForm {fc : LowCut} {κ d ℓ : ℝ} (hκ : κ = (d ^ 2 * ℓ)⁻¹)
    (hℓ : 0 < ℓ) {Ψ : ℝ³ → ℝ} (hΨc : Continuous Ψ) :
    ∫ y in acube ℓ, (bsQ ℓ 0 Ψ y - lowMult fc κ ℓ (bsQ ℓ 0 Ψ) y) ^ 2
      ≤ momForm ℓ d 0 Ψ := by
  by_cases hd : d = 0
  · -- ### The degenerate branch `d = 0`, i.e. `κ = 0`
    subst hd
    have hκ0 : κ = 0 := by rw [hκ]; norm_num
    have hQc : Continuous (bsQ ℓ 0 Ψ) := by
      show Continuous (fun x : ℝ³ => Ψ x - bsMean ℓ 0 Ψ)
      exact hΨc.sub continuous_const
    -- the mean-free box state is integrable
    have hmaj : Integrable (fun y : ℝ³ => (bsQ ℓ 0 Ψ y) ^ 2) (volume.restrict (acube ℓ)) :=
      ContinuousOn.integrableOn_compact (acube_compact hℓ) (hQc.pow 2).continuousOn
    -- the trivial cut-off makes the multiplier the identity or zero a.e.
    have hae := lowMult_sq_le_ae_of_nonpos (fc := fc) (κ := κ) (ℓ := ℓ) hκ0.le hℓ hQc
    have hstep : ∫ y in acube ℓ, (bsQ ℓ 0 Ψ y - lowMult fc κ ℓ (bsQ ℓ 0 Ψ) y) ^ 2
        ≤ ∫ y in acube ℓ, (bsQ ℓ 0 Ψ y) ^ 2 :=
      integral_mono_of_nonneg (Eventually.of_forall fun y => sq_nonneg _) hmaj hae
    rw [momForm_eq_sq_of_d_eq_zero hℓ hΨc]
    exact hstep
  · -- ### The genuine branch `d ≠ 0`, i.e. `κ > 0`
    have hκpos : 0 < κ := by
      rw [hκ]
      exact inv_pos.mpr (mul_pos (sq_pos_of_ne_zero hd) hℓ)
    have hQc : Continuous (bsQ ℓ 0 Ψ) := by
      show Continuous (fun x : ℝ³ => Ψ x - bsMean ℓ 0 Ψ)
      exact hΨc.sub continuous_const
    obtain ⟨C, hC⟩ := (acube_compact hℓ).exists_bound_of_continuousOn hQc.continuousOn
    have hbound : ∀ x ∈ acube ℓ, |bsQ ℓ 0 Ψ x| ≤ max C 0 := by
      intro x hx
      simpa [Real.norm_eq_abs] using le_trans (hC x hx) (le_max_left C 0)
    have h1 := oneBody_box_le (fc := fc) (κ := κ) (ℓ := ℓ) hκpos hℓ
      (Ψ := bsQ ℓ 0 Ψ) hQc.measurable hbound
    -- the test function of the duality bound
    set g : ℝ³ → ℂ := fun z => (((acube ℓ).indicator (bsQ ℓ 0 Ψ) z : ℝ) : ℂ) with hgdef
    have hgeq : (fun z : ℝ³ => ((indU ℓ 0 z : ℝ) : ℂ) * ((bsQ ℓ 0 Ψ z : ℝ) : ℂ)) = g := by
      rw [hgdef, indU_zero]
      funext z
      by_cases hz : z ∈ acube ℓ <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, hz]
    obtain ⟨hg1, hg2⟩ := memLp_boxState (ℓ := ℓ) hℓ hΨc
    have hg1' : MemLp g 1 volume := hgeq ▸ hg1
    have hg2' : MemLp g 2 volume := hgeq ▸ hg2
    obtain ⟨hkinint, -⟩ := kinFT_sq_of_memLp hg1' hg2'
    -- `momForm ℓ d 0 Ψ = (2π)⁻³ ∫ momProj·‖kinFT g‖²`
    have hmom : momForm ℓ d 0 Ψ
        = ((2 * π) ^ 3)⁻¹ * ∫ p : ℝ³, momProj ℓ d p * ‖kinFT g p‖ ^ 2 := by
      rw [momForm_eq_indicator Ψ, hgdef]
    -- the weighted integral is integrable
    have hmomint : Integrable (fun p : ℝ³ => momProj ℓ d p * ‖kinFT g p‖ ^ 2) := by
      have hm : Measurable (momProj ℓ d) := by
        unfold momProj
        exact Measurable.ite (measurableSet_lt measurable_const continuous_norm.measurable)
          measurable_const measurable_const
      refine hkinint.mono' (hm.aestronglyMeasurable.mul hkinint.aestronglyMeasurable) ?_
      filter_upwards with p
      rw [Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg (momProj_nonneg ℓ d p) (sq_nonneg _))]
      exact mul_le_of_le_one_left (sq_nonneg _) (momProj_le_one ℓ d p)
    -- discard the cut-off, replacing it by the larger high-momentum indicator
    have hweight : ∫ p : ℝ³, (1 - fc.f (‖p‖ / κ)) ^ 2 * ‖kinFT g p‖ ^ 2
        ≤ ∫ p : ℝ³, momProj ℓ d p * ‖kinFT g p‖ ^ 2 :=
      integral_mono_of_nonneg
        (Eventually.of_forall fun p => mul_nonneg (sq_nonneg _) (sq_nonneg _))
        hmomint
        (Eventually.of_forall fun p =>
          mul_le_mul_of_nonneg_right (one_sub_sq_le_momProj hκ hℓ p) (sq_nonneg _))
    rw [hmom]
    exact le_trans h1 (mul_le_mul_of_nonneg_left hweight (by positivity))

/-! ## 2b. Nonnegativity of `momForm` -/

/-- `momForm` is an integral of a nonnegative density, hence nonnegative. -/
lemma momForm_nonneg (ℓ d : ℝ) (u : E3) (ψ : E3 → ℝ) : 0 ≤ momForm ℓ d u ψ := by
  rw [momForm]
  exact mul_nonneg (by positivity)
    (integral_nonneg fun p => mul_nonneg (momProj_nonneg ℓ d p) (sq_nonneg _))

/-! ## 3. The parametric `momForm` of an inserted fibre is integrable -/

/-- **Integrability of the parametric `momForm` of an inserted fibre.**

For a continuous `(m+1)`-body state `Φ` and an insertion slot `i`, the function

  `r ↦ momForm ℓ d 0 (z ↦ Φ (kcInsN m i (z,r)))`

is integrable on the remaining box `abox m ℓ`: it is a.e. measurable
(`aemeasurable_momForm_fibre`) and bounded by `∫_{acube ℓ}(Q₀Ψ_r)² ≤ (2M)²ℓ³`, where
`M` bounds `Φ` on the compact box `abox (m+1) ℓ` (`momForm_le_sq`). -/
lemma integrable_momForm_fibre {ℓ d : ℝ} (hℓ : 0 < ℓ) {m : ℕ}
    {Φ : X (m + 1) → ℝ} (hΦ : Continuous Φ) (i : Fin (m + 1)) :
    Integrable (fun r : X m => momForm ℓ d 0 (fun z : E3 => Φ (kcInsN m i (z, r))))
      (volume.restrict (abox m ℓ)) := by
  -- a uniform bound for `Φ` on the compact box `abox (m+1) ℓ`
  obtain ⟨M, hM⟩ := (abox_compact (m + 1) hℓ).exists_bound_of_continuousOn hΦ.continuousOn
  set M' : ℝ := max M 0 with hM'def
  have hM'nn : 0 ≤ M' := hM'def ▸ le_max_right M 0
  have hMb : ∀ x ∈ abox (m + 1) ℓ, ‖Φ x‖ ≤ M' :=
    fun x hx => hM'def ▸ le_trans (hM x hx) (le_max_left M 0)
  -- the fibre states are continuous
  have hcont : ∀ r : X m, Continuous (fun z : E3 => Φ (kcInsN m i (z, r))) := fun r =>
    hΦ.comp ((kcInsN_cont i).comp (continuous_id.prodMk continuous_const))
  -- the mean-free fibre is bounded by `2M'` on the box
  have hbsQ : ∀ (r : X m) (y : E3), r ∈ abox m ℓ → y ∈ acube ℓ →
      |bsQ ℓ 0 (fun z : E3 => Φ (kcInsN m i (z, r))) y| ≤ 2 * M' := by
    intro r y hr hy
    have hstep : ∀ z ∈ acube ℓ, ‖Φ (kcInsN m i (z, r))‖ ≤ M' := by
      intro z hz
      have hz' : kcInsN m i (z, r) ∈ abox (m + 1) ℓ :=
        (mem_abox_iff (m + 1) ℓ _).mpr (fun j => by
          by_cases hj : j = i
          · subst hj; simpa [kc_insN_apply_same] using hz
          · obtain ⟨k, hk⟩ := Fin.exists_succAbove_eq hj
            subst hk; simpa [kc_insN_apply_succ] using hr k)
      simpa using hMb _ hz'
    have hmean : |bsMean ℓ 0 (fun z : E3 => Φ (kcInsN m i (z, r)))| ≤ M' := by
      have h1 : ‖∫ z in acube ℓ, Φ (kcInsN m i (z, r))‖ ≤ M' * (volume (acube ℓ)).toReal := by
        have h := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := acube ℓ) (C := M')
          (acube_lt_top ℓ hℓ.le) hstep
        simpa [Measure.real] using h
      rw [acube_volume ℓ hℓ.le, ENNReal.toReal_ofReal (by positivity)] at h1
      have hℓ3 : (0 : ℝ) < ℓ ^ 3 := by positivity
      rw [bsMean]
      simp only [smul_zero, zero_add]
      calc |(ℓ ^ 3)⁻¹ * ∫ z in acube ℓ, Φ (kcInsN m i (z, r))|
          = (ℓ ^ 3)⁻¹ * ‖∫ z in acube ℓ, Φ (kcInsN m i (z, r))‖ := by
            rw [abs_mul, abs_of_pos (inv_pos.mpr hℓ3), Real.norm_eq_abs]
        _ ≤ (ℓ ^ 3)⁻¹ * (M' * ℓ ^ 3) :=
            mul_le_mul_of_nonneg_left h1 (le_of_lt (inv_pos.mpr hℓ3))
        _ = M' := by field_simp
    have habs : |Φ (kcInsN m i (y, r))| ≤ M' := by
      simpa using hstep y hy
    have hsub : bsQ ℓ 0 (fun z : E3 => Φ (kcInsN m i (z, r))) y
        = Φ (kcInsN m i (y, r)) - bsMean ℓ 0 (fun z : E3 => Φ (kcInsN m i (z, r))) := rfl
    rw [hsub]
    exact (abs_sub _ _).trans (by linarith)
  refine IntegrableOn.of_bound (abox_lt_top m ℓ hℓ.le) ?_ ((2 * M') ^ 2 * ℓ ^ 3) ?_
  · exact (aemeasurable_momForm_fibre (ℓ := ℓ) (d := d) hΦ i).aestronglyMeasurable.restrict
  · filter_upwards [ae_restrict_mem (abox_measurable m ℓ)] with r hr
    have h2Mnn : 0 ≤ (2 * M') ^ 2 := sq_nonneg _
    rw [Real.norm_eq_abs,
      abs_of_nonneg (momForm_nonneg ℓ d 0 (fun z : E3 => Φ (kcInsN m i (z, r))))]
    refine le_trans (momForm_le_sq hℓ (hcont r)) ?_
    calc ∫ y in acube ℓ, (bsQ ℓ 0 (fun z : E3 => Φ (kcInsN m i (z, r))) y) ^ 2
        ≤ ∫ y in acube ℓ, (2 * M') ^ 2 := by
          refine integral_mono_of_nonneg (Eventually.of_forall fun y => sq_nonneg _) ?_ ?_
          · exact IntegrableOn.of_bound (μ := volume) (s := acube ℓ)
              (f := fun _ : E3 => (2 * M') ^ 2)
              (acube_lt_top ℓ hℓ.le) continuous_const.aestronglyMeasurable ((2 * M') ^ 2)
              (Eventually.of_forall fun y =>
                le_of_eq (by rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ((2:ℝ) * M'))]))
          · filter_upwards [ae_restrict_mem (acube_measurable ℓ)] with y hy
            simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (hbsQ r y hr hy) 2
      _ = (2 * M') ^ 2 * ℓ ^ 3 := by
          rw [setIntegral_const, Measure.real, acube_volume ℓ hℓ.le,
            ENNReal.toReal_ofReal (by positivity), smul_eq_mul, mul_comm]

/-! ## 4. The slot-lifted inequality -/

/-- **FS `eq:QLs_giveNplusH`, slot by slot.**

The slot-`i` squared `Q̄_{L,i}Q_i`-mass in the box `abox (m+1) ℓ` is dominated by the
normalised slot-`i` lifting of the large-momentum form:

  `∫_{abox (m+1) ℓ}(Q̄_{L,i}Q_iΦ)² ≤ ℓ⁻³∫_{abox (m+1) ℓ} 1_{Λ(0)}(xᵢ)·momForm(fibreᵢΦ x)`.

Both sides are peeled along the slot `i` (`highSlot_sq_peel`, `momForm_fibre_peel`); the
peeled inequality is `oneBody_le_momForm` fibre-wise in the remaining coordinates, which
needs the majorant `r ↦ momForm ℓ d 0 Ψ_r` to be integrable (`integrable_momForm_fibre`).
When the left integrand is *not* integrable its Bochner integral is `0`, and the right
side is nonnegative. -/
theorem slot_le_momForm {fc : LowCut} {κ ℓ d : ℝ} (hκ : κ = (d ^ 2 * ℓ)⁻¹) (hℓ : 0 < ℓ)
    {m : ℕ} (i : Fin (m + 1)) {Φ : X (m + 1) → ℝ} (hΦ : Continuous Φ) :
    ∫ x in abox (m + 1) ℓ, (highSlot fc κ ℓ i (aQ ℓ i Φ) x) ^ 2
      ≤ ℓ ^ (-3 : ℤ) * ∫ x in abox (m + 1) ℓ,
          indU ℓ 0 (x i) * momForm ℓ d 0 (fibre (m + 1) i Φ x) := by
  by_cases hInt : IntegrableOn
      (fun x : X (m + 1) => (highSlot fc κ ℓ i (aQ ℓ i Φ) x) ^ 2) (abox (m + 1) ℓ)
  · -- ### Case A: the left integrand is integrable; peel both sides and compare fibre-wise
    rw [highSlot_sq_peel (fc := fc) (κ := κ) (ℓ := ℓ) hℓ i hΦ hInt,
      momForm_fibre_peel (ℓ := ℓ) (d := d) hℓ i (Φ := Φ)]
    have hfib : (fun r : X m => momForm ℓ d 0
          (fibre (m + 1) i Φ (kcInsN m i (0, r))))
        = fun r : X m => momForm ℓ d 0 (fun z : E3 => Φ (kcInsN m i (z, r))) := by
      funext r
      rw [fibre_kcInsN i Φ (0 : E3) r]
    rw [hfib]
    refine integral_mono_of_nonneg (Eventually.of_forall fun r => ?_)
      (integrable_momForm_fibre (ℓ := ℓ) (d := d) hℓ hΦ i) (Eventually.of_forall fun r => ?_)
    · exact integral_nonneg (fun y => sq_nonneg _)
    · -- the fibre-wise one-body inequality
      have hc : Continuous (fun z : E3 => Φ (kcInsN m i (z, r))) :=
        hΦ.comp ((kcInsN_cont i).comp (continuous_id.prodMk continuous_const))
      exact oneBody_le_momForm (fc := fc) (κ := κ) (d := d) (ℓ := ℓ) hκ hℓ hc
  · -- ### Case B: the left integral is junk (`0`), the right side is nonnegative
    rw [integral_undef hInt]
    refine mul_nonneg (by positivity) (integral_nonneg fun x => ?_)
    have h1 : (0 : ℝ) ≤ indU ℓ 0 (x i) := Set.indicator_nonneg (fun _ _ => zero_le_one) _
    have h2 : (0 : ℝ) ≤ momForm ℓ d 0 (fibre (m + 1) i Φ x) := by
      rw [momForm]
      exact mul_nonneg (by positivity)
        (integral_nonneg fun p => mul_nonneg (momProj_nonneg ℓ d p) (sq_nonneg _))
    exact mul_nonneg h1 h2

end Work.BoseFixB3.HighMass
