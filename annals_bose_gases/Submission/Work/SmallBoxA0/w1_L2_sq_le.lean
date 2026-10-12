import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.SmallBoxA0.lintegral_sub_sq_le
import Submission.Work.SmallBoxA0.sub_pullback_ae
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SmallBoxA0

open MeasureTheory Metric
open scoped ContDiff Topology Real BigOperators
open Submission BoseGases
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

set_option linter.unusedVariables false

/-- `L²`-mass of the χ-renormalised pairing kernel on the two-particle small box:
`∫_{abox 2 s} (wPairC s (g₀ v h))² ≤ 4·chiSup⁴·s³·∫ g₀²`.

The kernel `wPairC s f x y = χ_s(x)·(f(x−y)/(χ⋆χ)_s(x−y))·χ_s(y)` is pointwise at
most `2·chiSup²·|f(x−y)|` (dilute regime `R ≤ s·chiR0`, so `(χ⋆χ)_s ≥ 1/2` on the
support of `f = g₀ v h`, and `|χ_s| ≤ chiSup`); squaring and integrating the
"diagonal-overlap" estimate `∫_{(x,y) ∈ Λ(s)²} (g₀(x−y))² ≤ s³·∫ g₀²` (Fubini +
translation invariance of Lebesgue measure on the cube, which has volume `s³`)
gives the bound. -/
lemma w1_L2_sq_le {s R : ℝ} (hs : 0 < s) (hR : 0 < R)
    {v : ℝ³ → ℝ} (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v)
    (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R) (hRs : R ≤ s * chiR0)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hint : Integrable (fun z : ℝ³ => (g0 v h z) ^ 2)) :
    (∫ p in abox 2 s, (wPairC s (g0 v h) (p 0) (p 1)) ^ 2)
      ≤ 4 * chiSup ^ 4 * s ^ 3 * (∫ z : ℝ³, (g0 v h z) ^ 2) := by
  set f : ℝ³ → ℝ := g0 v h with hf
  have hsupp : ∀ z : ℝ³, R ≤ ‖z‖ → f z = 0 := by
    intro z hz
    rw [hf]
    exact g0_zero_of_norm_ge hv_supp hz h
  -- `f` is locally integrable (the scattering equation's right-hand side), hence a.e. strongly measurable
  have hfl : LocallyIntegrable f := by
    rw [hf]
    exact (Classical.choose_spec h).2.rhs_integrable
  have hfaesm : AEStronglyMeasurable f volume := hfl.aestronglyMeasurable
  -- a measurable representative of `f`
  set g : ℝ³ → ℝ := AEStronglyMeasurable.mk f hfaesm with hg
  have hgm : Measurable g := by
    rw [hg]
    exact hfaesm.stronglyMeasurable_mk.measurable
  have hfg' : f =ᵐ[volume] g := by
    rw [hg]
    exact hfaesm.ae_eq_mk
  have hsq_eq : (fun z : ℝ³ => (f z) ^ 2) =ᵐ[volume] (fun z : ℝ³ => (g z) ^ 2) := by
    filter_upwards [hfg'] with z hz
    rw [hz]
  have hintg : Integrable (fun z : ℝ³ => (g z) ^ 2) := hint.congr hsq_eq
  have hMg : (∫ z : ℝ³, (g z) ^ 2) = ∫ z : ℝ³, (f z) ^ 2 :=
    (integral_congr_ae hsq_eq).symm
  -- the pullback of `f =ᵐ g` along the difference map on the two-particle box
  have hae_box : (fun p : X 2 => f (p 0 - p 1))
      =ᵐ[volume.restrict (abox 2 s)] (fun p : X 2 => g (p 0 - p 1)) :=
    sub_pullback_ae hs hgm hfg'
  -- pointwise bound for the kernel with numerator `f`
  have hpt : ∀ x y : ℝ³, (wPairC s f x y) ^ 2 ≤ 4 * chiSup ^ 4 * (f (x - y)) ^ 2 :=
    fun x y => wPairC_sq_le hs (le_of_lt hR) hRs hsupp x y
  -- a.e. comparison of the two kernels
  have hae_le : (fun p : X 2 => (wPairC s f (p 0) (p 1)) ^ 2)
      ≤ᵐ[volume.restrict (abox 2 s)]
        (fun p : X 2 => 4 * chiSup ^ 4 * (g (p 0 - p 1)) ^ 2) := by
    have h1 : ∀ᵐ p ∂(volume.restrict (abox 2 s)),
        (wPairC s f (p 0) (p 1)) ^ 2 ≤ 4 * chiSup ^ 4 * (f (p 0 - p 1)) ^ 2 :=
      Filter.Eventually.of_forall (fun p => hpt (p 0) (p 1))
    filter_upwards [h1, hae_box] with p hle hbox
    rw [hbox] at hle
    exact hle
  -- measurability of the majorant numerator
  have hsub_meas : Measurable (fun p : X 2 => p 0 - p 1) := by fun_prop
  have hgm2 : Measurable (fun p : X 2 => g (p 0 - p 1)) := hgm.comp hsub_meas
  have hAg : Measurable (fun p : X 2 => (g (p 0 - p 1)) ^ 2) :=
    hgm2.pow measurable_const
  have hD2 := lintegral_sub_sq_le hs hgm hintg
  -- the majorant numerator is integrable on the box
  have hAg_int : Integrable (fun p : X 2 => (g (p 0 - p 1)) ^ 2)
      (volume.restrict (abox 2 s)) := by
    refine ⟨hAg.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_norm]
    calc ∫⁻ p, ENNReal.ofReal ‖(g (p 0 - p 1)) ^ 2‖ ∂(volume.restrict (abox 2 s))
        = ∫⁻ p, ENNReal.ofReal ((g (p 0 - p 1)) ^ 2) ∂(volume.restrict (abox 2 s)) := by
          apply lintegral_congr; intro p
          rw [Real.norm_of_nonneg (sq_nonneg _)]
      _ ≤ ENNReal.ofReal (s ^ 3 * ∫ z : ℝ³, (g z) ^ 2) := hD2
      _ < ⊤ := ENNReal.ofReal_lt_top
  have h_int_maj : Integrable (fun p : X 2 => 4 * chiSup ^ 4 * (g (p 0 - p 1)) ^ 2)
      (volume.restrict (abox 2 s)) := hAg_int.const_mul _
  -- main monotonicity
  have hmono : (∫ p in abox 2 s, (wPairC s f (p 0) (p 1)) ^ 2)
      ≤ ∫ p in abox 2 s, 4 * chiSup ^ 4 * (g (p 0 - p 1)) ^ 2 := by
    apply integral_mono_of_nonneg
    · filter_upwards with p
      exact sq_nonneg _
    · exact h_int_maj
    · exact hae_le
  have hsplit : (∫ p in abox 2 s, 4 * chiSup ^ 4 * (g (p 0 - p 1)) ^ 2)
      = 4 * chiSup ^ 4 * (∫ p in abox 2 s, (g (p 0 - p 1)) ^ 2) := by
    rw [integral_const_mul]
  -- the diagonal-overlap bound on the cube
  have hAg_bound : (∫ p in abox 2 s, (g (p 0 - p 1)) ^ 2)
      ≤ s ^ 3 * (∫ z : ℝ³, (f z) ^ 2) := by
    have h1 : (∫ p in abox 2 s, (g (p 0 - p 1)) ^ 2)
        = (∫⁻ p in abox 2 s, ENNReal.ofReal ((g (p 0 - p 1)) ^ 2)).toReal := by
      rw [integral_eq_lintegral_of_nonneg_ae]
      · filter_upwards with p
        exact sq_nonneg _
      · exact hAg.aestronglyMeasurable
    rw [h1]
    calc (∫⁻ p in abox 2 s, ENNReal.ofReal ((g (p 0 - p 1)) ^ 2)).toReal
        ≤ (ENNReal.ofReal (s ^ 3 * ∫ z : ℝ³, (g z) ^ 2)).toReal :=
          ENNReal.toReal_mono ENNReal.ofReal_lt_top.ne hD2
      _ = s ^ 3 * (∫ z : ℝ³, (g z) ^ 2) := ENNReal.toReal_ofReal (by positivity)
      _ = s ^ 3 * (∫ z : ℝ³, (f z) ^ 2) := by rw [hMg]
  have hfin : (∫ p in abox 2 s, (wPairC s f (p 0) (p 1)) ^ 2)
      ≤ 4 * chiSup ^ 4 * s ^ 3 * (∫ z : ℝ³, (f z) ^ 2) := by
    calc (∫ p in abox 2 s, (wPairC s f (p 0) (p 1)) ^ 2)
        ≤ ∫ p in abox 2 s, 4 * chiSup ^ 4 * (g (p 0 - p 1)) ^ 2 := hmono
      _ = 4 * chiSup ^ 4 * (∫ p in abox 2 s, (g (p 0 - p 1)) ^ 2) := hsplit
      _ ≤ 4 * chiSup ^ 4 * (s ^ 3 * (∫ z : ℝ³, (f z) ^ 2)) :=
          mul_le_mul_of_nonneg_left hAg_bound (by positivity)
      _ = 4 * chiSup ^ 4 * s ^ 3 * (∫ z : ℝ³, (f z) ^ 2) := by ring
  rwa [hf] at hfin

end Work.SmallBoxA0
