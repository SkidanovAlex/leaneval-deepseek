import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.AeMom.Defs
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set Filter

namespace Work.FTS.ClassC.HonestCut

/-!
# From a finite iterated `lintegral` to honest integrability

The technical step `HkMemAe_of_lintegral` is a pure measure-theory statement: for a
*pointwise nonnegative* integrand `f z θ` whose iterated Lebesgue integral over
`(0,∞) × Iθ` is finite, the `θ`-slices are integrable for almost every `z > 0` and the
function `z ↦ ∫ θ, f z θ` is integrable on `(0,∞)`.

This is exactly what turns the `H^k`-finiteness assumption (an `HkSq` bound, which is
naturally proved as a bound on the iterated `lintegral` `∫⁻ z ∫⁻ θ ofReal (integrand)`)
into the honest statement `HkMem α 0 Ψ` modulo the null set where a slice blows up.

The pointwise nonnegativity is automatic for the level-`0` weighted integrand
(`HkIntegrand_zero_nonneg`: it is a sum of squares and of zero terms), so the general
lemma below is applied to it verbatim.
-/

/-- The level-`0` weighted integrand of `HkIntegrand` is nonnegative: for `k = 0` the
definition reduces to the single square `(Ψ z θ · w z / sin(2θ)^{η/2})²` (the mixed sum
is empty because its condition `1 ≤ i ∧ i + j ≤ 0` is false for `i = j = 0`). -/
theorem HkIntegrand_zero_nonneg (α : ℝ) (Ψ : ℝ → ℝ → ℝ) (z θ : ℝ) :
    0 ≤ Work.Spaces.HkIntegrand α 0 Ψ z θ := by
  simp only [Work.Spaces.HkIntegrand]
  refine add_nonneg (Finset.sum_nonneg fun i _ => sq_nonneg _) ?_
  refine Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => ?_
  split_ifs with h
  · exact sq_nonneg _
  · exact le_refl 0

/-- **Finiteness of an iterated `lintegral` gives honest integrability.**  Let
`f : ℝ → ℝ → ℝ` be pointwise nonnegative, with `θ`-slices satisfying
`∫⁻ θ in Iθ, ofReal (f z θ) < ∞` in the `lintegral` sense, the whole iterated `lintegral`
bounded by `ofReal C`, and the outer function `z ↦ ∫⁻ θ, ofReal (f z θ)` a.e.-measurable
on `(0,∞)`.  Then

* for almost every `z ∈ (0,∞)` the slice `θ ↦ f z θ` is integrable on `Iθ`, and
* `z ↦ ∫ θ in Iθ, f z θ` is integrable on `(0,∞)`.

The proof is the standard one: the outer `lintegral` being `< ∞` makes the outer
function finite a.e. (`ae_lt_top'`), finiteness of the slice identifies the honest
Bochner integral of the slice with `(∫⁻ θ, ofReal (f z θ)).toReal`, and this outer
function is integrable because its `ofReal`-`lintegral` is exactly the given one. -/
theorem ae_integrableOn_and_integrableOn_of_lintegral_le {f : ℝ → ℝ → ℝ} {C : ℝ}
    (hnn : ∀ z θ, 0 ≤ f z θ)
    (hslmeas : ∀ z ∈ Set.Ioi 0,
      AEMeasurable (fun θ => ENNReal.ofReal (f z θ)) (volume.restrict Work.Spaces.Iθ))
    (hfin : (∫⁻ z in Set.Ioi 0, ∫⁻ θ in Work.Spaces.Iθ,
        ENNReal.ofReal (f z θ)) ≤ ENNReal.ofReal C)
    (hmeas : AEMeasurable (fun z => ∫⁻ θ in Work.Spaces.Iθ,
        ENNReal.ofReal (f z θ)) (volume.restrict (Set.Ioi 0))) :
    (∀ᵐ z ∂(volume.restrict (Set.Ioi 0)),
        IntegrableOn (fun θ => f z θ) Work.Spaces.Iθ) ∧
      IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ, f z θ) (Set.Ioi 0) := by
  set G : ℝ → ENNReal := fun z => ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (f z θ) with hG
  have hGmeas : AEMeasurable G (volume.restrict (Set.Ioi 0)) := hmeas
  have hfin' : (∫⁻ z in Set.Ioi 0, G z) ≠ ⊤ :=
    ne_of_lt (lt_of_le_of_lt hfin ENNReal.ofReal_lt_top)
  have hGlt : ∀ᵐ z ∂(volume.restrict (Set.Ioi 0)), G z < ⊤ :=
    MeasureTheory.ae_lt_top' hGmeas hfin'
  have hmem : ∀ᵐ z : ℝ ∂(volume.restrict (Set.Ioi (0 : ℝ))), z ∈ Set.Ioi (0 : ℝ) :=
    MeasureTheory.ae_restrict_mem measurableSet_Ioi
  -- the slices are integrable a.e.
  have hsl : ∀ᵐ z ∂(volume.restrict (Set.Ioi 0)),
      IntegrableOn (fun θ => f z θ) Work.Spaces.Iθ := by
    filter_upwards [hmem, hGlt] with z hz hlt
    have hms : AEMeasurable (fun θ => ENNReal.ofReal (f z θ))
        (volume.restrict Work.Spaces.Iθ) := hslmeas z hz
    have has : AEStronglyMeasurable (fun θ => f z θ) (volume.restrict Work.Spaces.Iθ) := by
      refine (hms.ennreal_toReal.aestronglyMeasurable).congr ?_
      filter_upwards with θ
      exact ENNReal.toReal_ofReal (hnn z θ)
    exact (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable has
      (Filter.Eventually.of_forall fun θ => hnn z θ)).mp (ne_of_lt hlt)
  -- the honest slice integral agrees with the `toReal` of the `lintegral`, a.e.
  have hP_eq : (fun z => ∫ θ in Work.Spaces.Iθ, f z θ)
      =ᵐ[volume.restrict (Set.Ioi 0)] fun z => (G z).toReal := by
    filter_upwards [hmem, hGlt] with z hz hlt
    have hms : AEMeasurable (fun θ => ENNReal.ofReal (f z θ))
        (volume.restrict Work.Spaces.Iθ) := hslmeas z hz
    have h1 : (∫ θ in Work.Spaces.Iθ, f z θ)
        = ∫ θ in Work.Spaces.Iθ, (ENNReal.ofReal (f z θ)).toReal := by
      refine MeasureTheory.integral_congr_ae ?_
      filter_upwards with θ
      exact (ENNReal.toReal_ofReal (hnn z θ)).symm
    rw [h1, MeasureTheory.integral_toReal hms
      (Filter.Eventually.of_forall fun θ => ENNReal.ofReal_lt_top)]
  have hP_asm : AEStronglyMeasurable (fun z => ∫ θ in Work.Spaces.Iθ, f z θ)
      (volume.restrict (Set.Ioi 0)) :=
    (hmeas.ennreal_toReal.aestronglyMeasurable).congr hP_eq.symm
  have hP_nn : 0 ≤ᵐ[volume.restrict (Set.Ioi 0)]
      (fun z => ∫ θ in Work.Spaces.Iθ, f z θ) :=
    hP_eq.mono fun z hz => by rw [hz]; exact ENNReal.toReal_nonneg
  have hP_fin : (∫⁻ z in Set.Ioi 0, ENNReal.ofReal (∫ θ in Work.Spaces.Iθ, f z θ)) ≠ ⊤ := by
    have heq : (∫⁻ z in Set.Ioi 0, ENNReal.ofReal (∫ θ in Work.Spaces.Iθ, f z θ))
        = ∫⁻ z in Set.Ioi 0, G z := by
      refine MeasureTheory.lintegral_congr_ae ?_
      filter_upwards [hP_eq, hGlt] with z h1 h2
      rw [h1]
      exact ENNReal.ofReal_toReal (ne_of_lt h2)
    rw [heq]
    exact ne_of_lt (lt_of_le_of_lt hfin ENNReal.ofReal_lt_top)
  exact ⟨hsl, (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable hP_asm hP_nn).mp hP_fin⟩

theorem HkMemAe_of_lintegral {α : ℝ} {Ψ : ℝ → ℝ → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hslmeas : ∀ z ∈ Work.Spaces.Iz,
      AEMeasurable (fun θ => ENNReal.ofReal (Work.Spaces.HkIntegrand α 0 Ψ z θ))
        (MeasureTheory.volume.restrict Work.Spaces.Iθ))
    (hfin : (∫⁻ z in Set.Ioi 0, ∫⁻ θ in Work.Spaces.Iθ,
        ENNReal.ofReal (Work.Spaces.HkIntegrand α 0 Ψ z θ)) ≤ ENNReal.ofReal C)
    (hmeas : AEMeasurable (fun z => ∫⁻ θ in Work.Spaces.Iθ,
        ENNReal.ofReal (Work.Spaces.HkIntegrand α 0 Ψ z θ))
        (MeasureTheory.volume.restrict (Set.Ioi 0))) :
    (∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
        MeasureTheory.IntegrableOn (fun θ => Work.Spaces.HkIntegrand α 0 Ψ z θ)
          Work.Spaces.Iθ) ∧
      MeasureTheory.IntegrableOn
        (fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 Ψ z θ)
        (Set.Ioi 0) := by
  exact ae_integrableOn_and_integrableOn_of_lintegral_le
    (fun z θ => HkIntegrand_zero_nonneg α Ψ z θ)
    (fun z hz => hslmeas z (Set.Ioi_subset_Ici_self hz)) hfin hmeas

end Work.FTS.ClassC.HonestCut
