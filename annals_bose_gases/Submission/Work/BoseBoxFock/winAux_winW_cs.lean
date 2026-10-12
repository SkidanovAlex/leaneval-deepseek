import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.WinAuxDefs
import Submission.Work.BoseFixB1S.integral_sq_le_measure_mul_integral_sq
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.winAux_winW_cs` — the `L¹`/`L²` Cauchy–Schwarz bound for `winW`

`winW ℓ ψ = 1_{Λ(ℓ)}·|Q_{Λ(ℓ)}ψ|` is the nonnegative bridge weight of the W-route
(`WinAuxDefs`).  It is supported on the cube `Λ(ℓ) = acube ℓ`, whose Lebesgue volume is `ℓ³`,
and its square is the indicator of the cube of the squared mean-free state:

    `winW ℓ ψ z ^ 2 = 1_{acube ℓ}(z)·(Q_{Λ(ℓ)}ψ z)²`,   hence   `∫ winW² = gapBare ℓ 0 ψ`.

Cauchy–Schwarz on the finite measure space `(acube ℓ, volume)` — in its `L²`-form
`(∫ f)² ≤ (∫ f²)·volume s` for `f` vanishing off a finite-measure set `s`
(`Work.BoseFixB1S.integral_sq_le_measure_mul_integral_sq`) — then gives

    `(∫ winW)² ≤ ℓ³·∫ winW² = ℓ³·gapBare ℓ 0 ψ`,

which is the statement.  This is the `L¹`-side estimate that the image-sum assembly of the W-route
(`WinAuxAssembly`) consumes; no smoothness of `ψ` beyond continuity is used.
-/

noncomputable section

open MeasureTheory

open scoped Real

namespace Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ## 1. Continuity of the mean-free state and `L²`-membership of `winW` -/

/-- The box-mean-free projection `Q_{Λ(ℓ)}ψ = ψ − (mean of ψ over Λ(ℓ))` of a continuous state is
continuous: it is `ψ` minus a constant. -/
lemma continuous_Qfree_zero {ℓ : ℝ} {ψ : E3 → ℝ} (hψ : Continuous ψ) :
    Continuous (Work.BoseKinLoc.Qfree ℓ 0 ψ) := by
  unfold Work.BoseKinLoc.Qfree Work.BSKinetic.bsQ
  exact hψ.sub continuous_const

/-- `winW ℓ ψ = 1_{Λ(ℓ)}·|Q_{Λ(ℓ)}ψ|` is the indicator of the compact cube of a continuous
function, so it is a.e. strongly measurable for every `ψ`. -/
lemma aestronglyMeasurable_winW (ℓ : ℝ) {ψ : E3 → ℝ} (hψ : Continuous ψ) :
    AEStronglyMeasurable (winW ℓ ψ) (volume : Measure E3) := by
  have hQc : Continuous (Work.BoseKinLoc.Qfree ℓ 0 ψ) := continuous_Qfree_zero hψ
  unfold winW
  exact ((continuous_abs.comp hQc).aestronglyMeasurable).indicator
    (Submission.BoseGases.acube_measurable ℓ)

/-- **`winW` is square-integrable** for `ℓ > 0` and continuous `ψ`: its square is the indicator of
the compact cube `acube ℓ` of the continuous function `(Q_{Λ(ℓ)}ψ)²`. -/
lemma integrable_winW_sq {ℓ : ℝ} (hℓ : 0 < ℓ) {ψ : E3 → ℝ} (hψ : Continuous ψ) :
    Integrable (fun z : E3 => winW ℓ ψ z ^ 2) (volume : Measure E3) := by
  have hQc : Continuous (Work.BoseKinLoc.Qfree ℓ 0 ψ) := continuous_Qfree_zero hψ
  have hpt : (fun z : E3 => winW ℓ ψ z ^ 2)
      = (Submission.BoseGases.acube ℓ).indicator
          (fun z => (Work.BoseKinLoc.Qfree ℓ 0 ψ z) ^ 2) :=
    funext fun z => winW_sq_eq ℓ ψ z
  rw [hpt]
  exact ((ContinuousOn.integrableOn_compact (μ := volume)
      (Submission.BoseGases.acube_compact hℓ) (hQc.pow 2).continuousOn).integrable_indicator
        (Submission.BoseGases.acube_measurable ℓ))

/-- `winW ℓ ψ ∈ L²` (this is the hypothesis under which Cauchy–Schwarz is invoked). -/
lemma memLp_winW {ℓ : ℝ} (hℓ : 0 < ℓ) {ψ : E3 → ℝ} (hψ : Continuous ψ) :
    MemLp (winW ℓ ψ) 2 (volume : Measure E3) :=
  (MeasureTheory.memLp_two_iff_integrable_sq (aestronglyMeasurable_winW ℓ hψ)).mpr
    (integrable_winW_sq hℓ hψ)

/-! ## 2. The two brute identities: `∫ winW² = gapBare`, `volume (acube ℓ) = ℓ³` -/

/-- The anchored box `Λ(0) = lamBox ℓ 0` is the centred cube `acube ℓ`. -/
lemma lamBox_zero_eq_acube (ℓ : ℝ) :
    Work.BoseKinLoc.lamBox ℓ 0 = Submission.BoseGases.acube ℓ := by
  ext x
  simp only [Work.BoseKinLoc.lamBox, Work.BSKinetic.bsBox, Set.mem_ofPred_eq, smul_zero,
    sub_zero]

/-- **The square of the bridge weight integrates to the bare mean-free box mass**:
`∫ winW² = gapBare ℓ 0 ψ`. -/
lemma integral_winW_sq (ℓ : ℝ) (ψ : E3 → ℝ) :
    (∫ z : E3, winW ℓ ψ z ^ 2) = Work.BoseKinLoc.gapBare ℓ 0 ψ := by
  have hpt : (fun z : E3 => winW ℓ ψ z ^ 2)
      = (Submission.BoseGases.acube ℓ).indicator
          (fun z => (Work.BoseKinLoc.Qfree ℓ 0 ψ z) ^ 2) :=
    funext fun z => winW_sq_eq ℓ ψ z
  have hgap : Work.BoseKinLoc.gapBare ℓ 0 ψ
      = ∫ z in Submission.BoseGases.acube ℓ, (Work.BoseKinLoc.Qfree ℓ 0 ψ z) ^ 2 := by
    rw [Work.BoseKinLoc.gapBare, lamBox_zero_eq_acube]
  rw [hpt, integral_indicator (Submission.BoseGases.acube_measurable ℓ), hgap]

/-- The volume of the anchored box: `|Λ(0)| = ℓ³`. -/
lemma volume_acube_toReal {ℓ : ℝ} (hℓ : 0 ≤ ℓ) :
    ((volume : Measure E3) (Submission.BoseGases.acube ℓ)).toReal = ℓ ^ 3 := by
  rw [Submission.BoseGases.acube_volume ℓ hℓ, ENNReal.toReal_ofReal (by positivity)]

/-! ## 3. The target -/

theorem winAux_winW_cs {ℓ : ℝ} (hℓ : 0 < ℓ) {ψ : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) :
    (∫ z : EuclideanSpace ℝ (Fin 3), Work.BoseBoxFock.winW ℓ ψ z) ^ 2
      ≤ ℓ ^ 3 * Work.BoseKinLoc.gapBare ℓ 0 ψ := by
  have hfin : (volume : Measure E3) (Submission.BoseGases.acube ℓ) ≠ ⊤ := by
    rw [Submission.BoseGases.acube_volume ℓ hℓ.le]
    exact ENNReal.ofReal_ne_top
  have hCS := Work.BoseFixB1S.integral_sq_le_measure_mul_integral_sq
    (μ := (volume : Measure E3)) (s := Submission.BoseGases.acube ℓ)
    (Submission.BoseGases.acube_measurable ℓ) hfin
    (memLp_winW hℓ hψ.continuous)
    (fun x hx => winW_of_notMem hx)
  calc (∫ z : E3, winW ℓ ψ z) ^ 2
      ≤ (∫ z : E3, winW ℓ ψ z ^ 2) *
          ((volume : Measure E3) (Submission.BoseGases.acube ℓ)).toReal := hCS
    _ = Work.BoseKinLoc.gapBare ℓ 0 ψ * ℓ ^ 3 := by
          rw [integral_winW_sq, volume_acube_toReal hℓ.le]
    _ = ℓ ^ 3 * Work.BoseKinLoc.gapBare ℓ 0 ψ := by ring

end Work.BoseBoxFock
