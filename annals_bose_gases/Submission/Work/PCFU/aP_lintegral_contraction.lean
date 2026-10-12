import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.PCFU.aP_aQ_sq_le
import Submission.Work.PCFU.abox_cube_peel
import Submission.Work.PCFU.aemeasurable_fibre_lintegral
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.PCFU

open MeasureTheory
open scoped ENNReal

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- **The fibre Cauchy–Schwarz step, pointwise in the configuration.**

For `0 < ℓ` and any `f : E3 → ℝ` (no measurability assumed),

  `ℓ³ · ((1/ℓ³)·∫_{acube ℓ} f)² ≤ ∫⁻_{acube ℓ} (f)²`,

the mean-square bound on the fibre.  The proof is a case split: if `f` is not Bochner
integrable then the mean is `0` by the junk convention (`integral_undef`); if it is
integrable, then `f` is a.e. strongly measurable, so the finiteness of the `lintegral`
of `ofReal (f²)` (which is `⊤` in the other case, making the bound trivial) is equivalent
to `f² ∈ L¹` (`lintegral_ofReal_ne_top_iff_integrable`), and the Cauchy–Schwarz inequality
`fibre_sq_le` applies. -/
private lemma fibre_ofReal_sq_le {ℓ : ℝ} (hℓ : 0 < ℓ) {f : E3 → ℝ} :
    ENNReal.ofReal (ℓ ^ 3)
        * ENNReal.ofReal (((1 / ℓ ^ 3) * ∫ u in Submission.BoseGases.acube ℓ, f u) ^ 2)
      ≤ ∫⁻ u in Submission.BoseGases.acube ℓ, ENNReal.ofReal ((f u) ^ 2) := by
  by_cases hint : Integrable f (volume.restrict (Submission.BoseGases.acube ℓ))
  · by_cases htop : (∫⁻ u in Submission.BoseGases.acube ℓ, ENNReal.ofReal ((f u) ^ 2)) = ⊤
    · rw [htop]; exact le_top
    · have hae : AEStronglyMeasurable (fun u : E3 => (f u) ^ 2)
          (volume.restrict (Submission.BoseGases.acube ℓ)) :=
        hint.aestronglyMeasurable.pow 2
      have hf2 : Integrable (fun u : E3 => (f u) ^ 2)
          (volume.restrict (Submission.BoseGases.acube ℓ)) :=
        (lintegral_ofReal_ne_top_iff_integrable hae
          (Filter.Eventually.of_forall (fun u => sq_nonneg (f u)))).mp htop
      have hCS : ℓ ^ 3 * ((1 / ℓ ^ 3) * ∫ u in Submission.BoseGases.acube ℓ, f u) ^ 2
          ≤ ∫ u in Submission.BoseGases.acube ℓ, (f u) ^ 2 := (fibre_sq_le hℓ hf2).1
      calc ENNReal.ofReal (ℓ ^ 3)
            * ENNReal.ofReal (((1 / ℓ ^ 3) * ∫ u in Submission.BoseGases.acube ℓ, f u) ^ 2)
          = ENNReal.ofReal (ℓ ^ 3
              * ((1 / ℓ ^ 3) * ∫ u in Submission.BoseGases.acube ℓ, f u) ^ 2) :=
            (ENNReal.ofReal_mul (by positivity)).symm
        _ ≤ ENNReal.ofReal (∫ u in Submission.BoseGases.acube ℓ, (f u) ^ 2) :=
            ENNReal.ofReal_le_ofReal hCS
        _ = ∫⁻ u in Submission.BoseGases.acube ℓ, ENNReal.ofReal ((f u) ^ 2) :=
            ofReal_integral_eq_lintegral_ofReal hf2
              (Filter.Eventually.of_forall (fun u => sq_nonneg (f u)))
  · have hz : ∫ u in Submission.BoseGases.acube ℓ, f u = 0 := integral_undef hint
    rw [hz]
    simp

/-- **The `L²`-contraction of the box projection `Pᵢ = aP ℓ i` in `lintegral` form.**

`Submission.BoseGases.aP ℓ i Ξ x = (1/ℓ³)·∫_{u ∈ acube ℓ} Ξ (x[i ↦ u])` is the fibre mean over the
centred cube `acube ℓ` of side `ℓ`, i.e. the conditional expectation onto the `σ`-algebra of the
coordinates other than `i`; hence it is an `L²`-contraction on the box `abox n ℓ = (acube ℓ)^n`:

    ∫⁻_{abox n ℓ} (Pᵢ Ξ)² ≤ ∫⁻_{abox n ℓ} Ξ² .

This is the `ℝ≥0∞`/`lintegral` form of that contraction, with no hypothesis beyond
`AEMeasurable Ξ`.  The Bochner form (needing `IntegrableOn (fun x => Ξ x ^ 2) (abox n ℓ)`) is already
PROVED as `Work.PCFU.aP_aQ_sq_le` in `Submission/Work/PCFU/aP_aQ_sq_le.lean`, but it degenerates to
`0 ≤ _` in the Bochner-junk case, which is exactly the case this `lintegral` form must still control.
(Note: `Submission/Work/PCFU/aP_lintegral_sq_le.lean` holds the same statement as an abandoned
`sorry` stub; do NOT import it.  It is not part of anyone's import cone.)

Route.  `aP ℓ i Ξ x = (1/ℓ³) * ∫ u in acube ℓ, Ξ (Function.update x i u)`.
* Pointwise, for every `x`, with `f u := Ξ (Function.update x i u)` and `M := ∫ u in acube ℓ, f u`,
  `ENNReal.ofReal ((aP ℓ i Ξ x)^2) ≤ ENNReal.ofReal (1/ℓ³) * ∫⁻ u in acube ℓ, ENNReal.ofReal ((f u)^2)`.
  If `¬ Integrable f (volume.restrict (acube ℓ))` then `M = 0` (`MeasureTheory.integral_undef`) and
  the left side is `0`.  If `Integrable f` and the right `∫⁻` is `⊤`, this is trivial; otherwise
  `f ∈ L²` and `M² ≤ ℓ³·∫ f²` (Cauchy–Schwarz; the PROVED `Work.PCFU.fibre_sq_le` in
  `Submission/Work/PCFU/aP_aQ_sq_le.lean` is exactly this step) together with
  `MeasureTheory.ofReal_integral_eq_lintegral_ofReal` gives it.  The equivalence
  "`∫⁻ ofReal(f²) ≠ ⊤` ⟺ `f² ∈ L¹`" is `lintegral_ofReal_ne_top_iff_integrable` or similar
  (search Mathlib; `lowMult_lintegral_sq_le.lean` in this directory uses the same conversion).
* `lintegral_mono` in `x`, then the constant pull-out
  (`MeasureTheory.lintegral_const_mul_le`, which needs no measurability hypothesis).
* the peel `Work.PCFU.abox_cube_peel` (`Submission/Work/PCFU/abox_cube_peel.lean`):
  `∫⁻ x in abox n ℓ, ∫⁻ u in acube ℓ, F (Function.update x i u) = ENNReal.ofReal (ℓ^3) * ∫⁻ x in abox n ℓ, F x`
  for `AEMeasurable F (volume.restrict (abox n ℓ))`; here `F = fun x => ENNReal.ofReal ((Ξ x)^2)`.
  Finally `ENNReal.ofReal (1/ℓ³) * ENNReal.ofReal (ℓ^3) = 1`
  (`← ENNReal.ofReal_mul`, `one_div_mul_cancel`, `ENNReal.ofReal_one`).
No induction on `n` is needed; the case `n = 0` is vacuous (`i : Fin 0`) via `Fin.elim0`. -/
theorem aP_lintegral_contraction {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (i : Fin n)
    {Ξ : Submission.BoseGases.X n → ℝ}
    (hΞ : AEMeasurable Ξ (MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X n))) :
    (∫⁻ x in Submission.BoseGases.abox n ℓ,
        ENNReal.ofReal ((Submission.BoseGases.aP ℓ i Ξ x) ^ 2))
      ≤ ∫⁻ x in Submission.BoseGases.abox n ℓ, ENNReal.ofReal ((Ξ x) ^ 2) := by
  have hℓ3 : (0 : ℝ) < ℓ ^ 3 := by positivity
  -- a.e. measurability of the squared modulus, on the whole space and on the box
  have hFmeas : AEMeasurable (fun y : Submission.BoseGases.X n => ENNReal.ofReal ((Ξ y) ^ 2))
      (MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X n)) :=
    (by fun_prop : Measurable fun t : ℝ => ENNReal.ofReal (t ^ 2)).comp_aemeasurable' hΞ
  have hF : AEMeasurable (fun y : Submission.BoseGases.X n => ENNReal.ofReal ((Ξ y) ^ 2))
      ((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X n)).restrict
        (Submission.BoseGases.abox n ℓ)) := hFmeas.restrict
  -- the slot peel of the box
  have hpeel := abox_cube_peel (n := n) (ℓ := ℓ) hℓ i
      (fun y : Submission.BoseGases.X n => ENNReal.ofReal ((Ξ y) ^ 2)) hF
  -- pointwise fibre bound (note the factor `ℓ³` on the left)
  have hpoint : ∀ x : Submission.BoseGases.X n,
      ENNReal.ofReal (ℓ ^ 3) * ENNReal.ofReal ((Submission.BoseGases.aP ℓ i Ξ x) ^ 2)
        ≤ ∫⁻ u in Submission.BoseGases.acube ℓ,
            ENNReal.ofReal ((Ξ (Function.update x i u)) ^ 2) := by
    intro x
    simpa only [Submission.BoseGases.aP] using
      fibre_ofReal_sq_le (ℓ := ℓ) hℓ (f := fun u => Ξ (Function.update x i u))
  have hmono : (∫⁻ x in Submission.BoseGases.abox n ℓ,
        ENNReal.ofReal (ℓ ^ 3) * ENNReal.ofReal ((Submission.BoseGases.aP ℓ i Ξ x) ^ 2))
      ≤ ∫⁻ x in Submission.BoseGases.abox n ℓ,
          ∫⁻ u in Submission.BoseGases.acube ℓ,
            ENNReal.ofReal ((Ξ (Function.update x i u)) ^ 2) :=
    lintegral_mono (fun x => hpoint x)
  -- the constant pulls out (`lintegral_const_mul'` needs no measurability)
  have hconst : (∫⁻ x in Submission.BoseGases.abox n ℓ,
        ENNReal.ofReal (ℓ ^ 3) * ENNReal.ofReal ((Submission.BoseGases.aP ℓ i Ξ x) ^ 2))
      = ENNReal.ofReal (ℓ ^ 3) * ∫⁻ x in Submission.BoseGases.abox n ℓ,
          ENNReal.ofReal ((Submission.BoseGases.aP ℓ i Ξ x) ^ 2) :=
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  rw [hpeel, hconst] at hmono
  -- cancel the (finite, nonvanishing) factor `ℓ³`
  exact (ENNReal.mul_le_mul_iff_right
    (by rw [ENNReal.ofReal_ne_zero_iff]; exact hℓ3) ENNReal.ofReal_ne_top).mp hmono

end Work.PCFU
