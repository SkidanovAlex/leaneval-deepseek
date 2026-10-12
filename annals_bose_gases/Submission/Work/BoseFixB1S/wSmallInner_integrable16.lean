import ChallengeDeps
import Submission.Work.BoseFixB1B.pairRung.nuPairWNuBounds
import Submission.Work.BoseFixB1S.abs_wSmallInner_le_of_lower
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1S.wSmallInner_integrable16`

The localised Bogoliubov kernel's inner factor `wSmallInner M ℓ d (g₀ v h)` — the renormalised
potential `𝒲(z) = g₀(z)/((χ_M⋆χ_M)(z/(ℓd))·(χ⋆χ)(z/ℓ))` — is integrable under the paper's
*explicit* box regime `16R ≤ ℓ`, `16R ≤ ℓd`, without appealing to the opaque witness
`Submission.BoseGases.chiR0`.

The two denominators are controlled separately:

* the `ℓd`-scale one is `≥ smallConvLower M` on the support of `g₀` by the regime
  `R ≤ ℓd/16` (`Work.SmallBoxSliding.abs_wSmallScaled_le`, used inside
  `Work.BoseFixB1S.abs_wSmallInner_le_of_lower`);
* the `ℓ`-scale one is `≥ convCubeLower ℓ R > 0` on the range ball by `16R ≤ ℓ` (the explicit
  cube-of-half-side lower bound `Work.LocRepoint.convScale_cube_lower`, valid whenever
  `R < ℓ/2`).

Hence `|wSmallInner …| ≤ (1/(smallConvLower M · convCubeLower ℓ R))·|g₀|` pointwise, and
integrability follows from `Integrable (g₀ v h)` by dominated convergence.
-/

namespace Work.BoseFixB1S

open MeasureTheory

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem wSmallInner_integrable16 {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    {R : ℝ} (hR : 0 < R) (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1)
    (hvrad : _root_.BoseGases.IsRadial v)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    {M : ℕ} (hM : 1 ≤ M) :
    ∀ {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) (hRℓ : 16 * R ≤ ℓ) (hRd : 16 * R ≤ ℓ * d),
      MeasureTheory.Integrable
        (Work.BoseFixB1B.wSmallInner M ℓ d (Submission.BoseGases.g0 v h)) := by
  intro ℓ d hℓ hd hRℓ hRd
  -- the two regime hypotheses give `R ≤ ℓd/16` and `R < ℓ/2`
  have hRd16 : R ≤ ℓ * d / 16 := by linarith
  have hRhalf : R < ℓ / 2 := by linarith
  -- an explicit positive lower bound for the big-box denominator on the range ball
  set c : ℝ := Work.LocRepoint.convCubeLower ℓ R with hcdef
  have hcpos : 0 < c := by
    rw [hcdef]
    exact Work.LocRepoint.convCubeLower_pos hℓ hRhalf
  have hconv : ∀ z : E3, ‖z‖ ≤ R → c ≤ Submission.BoseGases.convScale ℓ z := by
    intro z hz
    rw [hcdef]
    exact Work.LocRepoint.convScale_cube_lower hℓ hRhalf hz
  -- `g₀` vanishes off the range ball and is integrable
  have hsupp : ∀ z : E3, R ≤ ‖z‖ → Submission.BoseGases.g0 v h z = 0 :=
    fun z hz => Submission.BoseGases.g0_zero_of_norm_ge hv_supp hz h
  have hgi : MeasureTheory.Integrable (Submission.BoseGases.g0 v h) :=
    Submission.BoseGases.g0_integrable hR hv_supp h
  set W : E3 → ℝ := Work.BoseFixB1B.wSmallInner M ℓ d (Submission.BoseGases.g0 v h) with hWdef
  -- pointwise domination by a multiple of `|g₀|`
  have hpt : ∀ z, |W z|
      ≤ (1 / (Work.SmallBoxSliding.smallConvLower M * c))
          * |Submission.BoseGases.g0 v h z| := by
    intro z
    rw [hWdef]
    exact abs_wSmallInner_le_of_lower hM hℓ hd hcpos hRd16 hconv h hsupp z
  -- measurability (as a quotient of measurable functions)
  have hmeas_f : AEMeasurable (fun z : E3 => Submission.BoseGases.g0 v h z
      / Submission.BoseGases.convScaleSmall M (ℓ * d) z
      / Submission.BoseGases.convScale ℓ z) MeasureTheory.volume := by
    have hcomp : Continuous (fun x : E3 => (ℓ * d)⁻¹ • x) := by fun_prop
    have h1 : AEMeasurable (Submission.BoseGases.convScaleSmall M (ℓ * d)) MeasureTheory.volume :=
      ((Submission.BoseGases.conv3Small_continuous hM).comp hcomp).aemeasurable
    have h2 : AEMeasurable (Submission.BoseGases.convScale ℓ) MeasureTheory.volume :=
      (Submission.BoseGases.convScale_continuous ℓ).aemeasurable
    have h3 : AEMeasurable (Submission.BoseGases.g0 v h) MeasureTheory.volume :=
      hgi.aestronglyMeasurable.aemeasurable
    exact (h3.div h1).div h2
  have hmeas : AEMeasurable W MeasureTheory.volume := by
    rw [hWdef]
    exact hmeas_f
  have hcint : MeasureTheory.Integrable (fun z =>
      (1 / (Work.SmallBoxSliding.smallConvLower M * c))
        * |Submission.BoseGases.g0 v h z|) :=
    hgi.abs.const_mul _
  exact MeasureTheory.Integrable.mono' hcint hmeas.aestronglyMeasurable
    (Filter.Eventually.of_forall hpt)

end Work.BoseFixB1S
