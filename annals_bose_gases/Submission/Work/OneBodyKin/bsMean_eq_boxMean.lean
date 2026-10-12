import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.OneBodyKin.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.OneBodyKin.bsMean_eq_boxMean`

The box mean `bsMean ℓ u ψ = (ℓ³)⁻¹ ∫_{Λ(u)} ψ` of the *moving* box `Λ(u) = ℓu + acube ℓ`
rewritten as a sliding average over the *unit* cube:

    `bsMean ℓ u ψ = ∫_{s ∈ acube 1} ψ (ℓ • (u + s))`.

This is the normalisation used to write the mean-free projection of the moving box family as the
convolution form of the cross term `Work.OneBodyKin.bsMean_bsPair_eq_symbol`: it exhibits the
`u`-dependence of the mean as a translation of the argument of `ψ` by `ℓ·s`.
-/

noncomputable section

open MeasureTheory

namespace Work.OneBodyKin

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

open Submission.BoseGases

set_option autoImplicit false

/-- `ℓ • s ∈ acube ℓ ↔ s ∈ acube 1` for `ℓ > 0`. -/
private lemma smul_mem_acube_iff {ℓ : ℝ} (hℓ : 0 < ℓ) (s : ℝ³) :
    ℓ • s ∈ acube ℓ ↔ s ∈ acube 1 := by
  rw [mem_acube_iff, mem_acube_iff]
  constructor
  · intro h m
    have hm : ℓ * s.ofLp m ∈ Set.Icc (-ℓ / 2) (ℓ / 2) := by simpa using h m
    constructor
    · have h1 : (-ℓ / 2) / ℓ ≤ s.ofLp m := (div_le_iff₀ hℓ).mpr (by rw [mul_comm]; exact hm.1)
      have h2 : (-ℓ / 2) / ℓ = -(1 / 2 : ℝ) := by field_simp
      linarith
    · have h1 : s.ofLp m ≤ (ℓ / 2) / ℓ := (le_div_iff₀ hℓ).mpr (by rw [mul_comm]; exact hm.2)
      have h2 : (ℓ / 2) / ℓ = (1 / 2 : ℝ) := by field_simp
      linarith
  · intro h m
    have hm := h m
    have h1 := mul_le_mul_of_nonneg_left hm.1 (le_of_lt hℓ)
    have h2 := mul_le_mul_of_nonneg_left hm.2 (le_of_lt hℓ)
    show ℓ * s.ofLp m ∈ Set.Icc (-ℓ / 2) (ℓ / 2)
    exact ⟨by nlinarith [h1], by nlinarith [h2]⟩

/-- The box mean of the moving box is the unit-cube average of `ψ (ℓ • (u + ·))`. -/
theorem bsMean_eq_boxMean {ℓ : ℝ} (hℓ : 0 < ℓ) (ψ : ℝ³ → ℝ) (u : ℝ³) :
    Work.BSKinetic.bsMean ℓ u ψ = ∫ s in acube 1, ψ (ℓ • (u + s)) := by
  -- the pointwise indicator identity under the substitution `z = ℓ • s`
  have hind : ∀ s : ℝ³, (acube ℓ).indicator (fun z : ℝ³ => ψ (ℓ • u + z)) (ℓ • s)
      = (acube 1).indicator (fun t : ℝ³ => ψ (ℓ • u + ℓ • t)) s := by
    intro s
    by_cases hs : s ∈ acube 1
    · rw [Set.indicator_of_mem ((smul_mem_acube_iff hℓ s).mpr hs), Set.indicator_of_mem hs]
    · rw [Set.indicator_of_notMem hs,
        Set.indicator_of_notMem (fun hc => hs ((smul_mem_acube_iff hℓ s).mp hc))]
  have hstep : (∫ z in acube ℓ, ψ (ℓ • u + z)) = ℓ ^ 3 * ∫ s in acube 1, ψ (ℓ • u + ℓ • s) := by
    rw [← integral_indicator (acube_measurable ℓ), ← integral_indicator (acube_measurable 1)]
    rw [integral_comp_smul_right (g := fun z : ℝ³ =>
      (acube ℓ).indicator (fun z : ℝ³ => ψ (ℓ • u + z)) z) hℓ]
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall (fun s => ?_))
    exact hind s
  rw [Work.BSKinetic.bsMean, hstep, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero 3 (ne_of_gt hℓ)),
    one_mul]
  refine setIntegral_congr_fun (acube_measurable 1) (fun s _ => ?_)
  rw [smul_add]

end Work.OneBodyKin
