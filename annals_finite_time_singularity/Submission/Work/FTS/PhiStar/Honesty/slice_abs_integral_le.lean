import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.PhiStar.Honesty.slice_abs_integrable
import Submission.Work.FTS.PhiStar.Honesty.slice_pointwise_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The `L¹`-norms of the two first-order angular slices are dominated by the `ℋ¹` integrand

For a source `F` which is `C^∞` on the open quadrant and honest in the weighted space `ℋ¹`
(`Work.Spaces.HkMem α 1 F`), and for radii `0 < a ≤ t`,

  `∫_θ |F t θ| ≤ ∫_θ HkIntegrand α 1 F t θ + π/4`,
  `∫_θ |∂_zF t θ| ≤ (∫_θ HkIntegrand α 1 F t θ)/a² + π/4`.

The pointwise input (proved in `Honesty.slice_pointwise_le`) is that on the *open* angular
interval `(0,π/2)` the two slices are dominated by the `ℋ¹` integrand:

  `|F t θ| ≤ HkIntegrand α 1 F t θ + 1/2`,
  `|∂_zF t θ| ≤ HkIntegrand α 1 F t θ / a² + 1/2`,

which follows from the two summands `i = 0`, `i = 1` of `HkIntegrand α 1 F` (for `θ ∈ (0,π/2)`
the weight factor `w t / sin(2θ)^{η/2}` is `≥ 1`, so `(F t θ)² ≤ HkIntegrand α 1 F t θ` and
`t²(∂_zF t θ)² ≤ HkIntegrand α 1 F t θ`, and `t ≥ a > 0` converts the second into
`(∂_zF t θ)² ≤ HkIntegrand α 1 F t θ / a²`) together with `|x| ≤ x² + 1/2`.

The two exceptional points `θ = 0, π/2` (where `sin(2θ) = 0` collapses the weight and the bound
need not hold) form a null set, so the bounds hold a.e. on `Iθ = [0,π/2]`.  The functions
`θ ↦ |F t θ|` and `θ ↦ |∂_zF t θ|` are integrable on the slice (this is `slice_abs_integrable`),
as is `θ ↦ HkIntegrand α 1 F t θ` (this is the first conjunct of `HkMem α 1 F`, at any `t ∈ Iz`),
so `integral_mono_ae` over the finite measure space `Iθ` (of measure `π/2`) gives the two claims,
the additive constant being `(1/2)·(π/2) = π/4`.
-/

namespace Work.FTS.PhiStar.Honesty

open MeasureTheory Set Filter
open scoped Real Topology

set_option autoImplicit false

/-- The integral of the constant `1/2` over the angular interval `Iθ = [0,π/2]` is `π/4`. -/
private lemma integral_Iθ_half : (∫ θ in Work.Spaces.Iθ, ((1 : ℝ) / 2)) = Real.pi / 4 := by
  rw [MeasureTheory.setIntegral_const, Work.Spaces.Iθ, MeasureTheory.Measure.real,
    Real.volume_Icc,
    ENNReal.toReal_ofReal (by linarith [Real.pi_pos] : (0 : ℝ) ≤ Real.pi / 2 - 0)]
  ring

/-! ## The main lemma -/

theorem slice_abs_integral_le {α : ℝ} {F : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen F) (hF : Work.Spaces.HkMem α 1 F)
    {a t : ℝ} (ha : 0 < a) (hat : a ≤ t) :
    (∫ θ in Work.Spaces.Iθ, |F t θ|)
        ≤ (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 1 F t θ) + Real.pi / 4 ∧
      (∫ θ in Work.Spaces.Iθ, |Work.Spaces.pz F t θ|)
        ≤ (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 1 F t θ) / a ^ 2
          + Real.pi / 4 := by
  have ht : 0 < t := lt_of_lt_of_le ha hat
  have htIz : t ∈ Work.Spaces.Iz := Set.mem_Ici.mpr ht.le
  have hHk : IntegrableOn (fun θ : ℝ => Work.Spaces.HkIntegrand α 1 F t θ)
      Work.Spaces.Iθ := hF.1 t htIz
  obtain ⟨hFint, hPint⟩ := slice_abs_integrable hsm hF ht
  -- `Iθ` and the open interval `(0,π/2)` differ by the null set `{0, π/2}`
  have hmeq : volume.restrict Work.Spaces.Iθ
      = volume.restrict (Set.Ioo (0 : ℝ) (π / 2)) := by
    rw [Work.Spaces.Iθ]
    exact (Measure.restrict_congr_set MeasureTheory.Ioo_ae_eq_Icc).symm
  have hconst : IntegrableOn (fun _ : ℝ => (1 : ℝ) / 2) Work.Spaces.Iθ :=
    MeasureTheory.integrableOn_const (C := (1 / 2 : ℝ)) (s := Work.Spaces.Iθ)
      (by rw [Work.Spaces.Iθ, Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
  have hpt : ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
      |F t θ| ≤ Work.Spaces.HkIntegrand α 1 F t θ + 1 / 2 ∧
        |Work.Spaces.pz F t θ| ≤ Work.Spaces.HkIntegrand α 1 F t θ / a ^ 2 + 1 / 2 :=
    fun θ hθ => slice_pointwise_le ha hat hθ
  constructor
  · have hg : IntegrableOn
        (fun θ : ℝ => Work.Spaces.HkIntegrand α 1 F t θ + 1 / 2) Work.Spaces.Iθ :=
      hHk.add hconst
    have hle : (fun θ : ℝ => |F t θ|)
        ≤ᵐ[volume.restrict Work.Spaces.Iθ]
          (fun θ : ℝ => Work.Spaces.HkIntegrand α 1 F t θ + 1 / 2) := by
      rw [hmeq]
      exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo
        (fun θ hθ => (hpt θ hθ).1)
    calc (∫ θ in Work.Spaces.Iθ, |F t θ|)
        ≤ ∫ θ in Work.Spaces.Iθ, (Work.Spaces.HkIntegrand α 1 F t θ + 1 / 2) :=
          integral_mono_ae hFint hg hle
      _ = (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 1 F t θ) + Real.pi / 4 := by
          rw [integral_add hHk hconst, integral_Iθ_half]
  · have hHk2 : IntegrableOn (fun θ : ℝ => Work.Spaces.HkIntegrand α 1 F t θ / a ^ 2)
        Work.Spaces.Iθ := hHk.div_const _
    have hg : IntegrableOn
        (fun θ : ℝ => Work.Spaces.HkIntegrand α 1 F t θ / a ^ 2 + 1 / 2) Work.Spaces.Iθ :=
      hHk2.add hconst
    have hle : (fun θ : ℝ => |Work.Spaces.pz F t θ|)
        ≤ᵐ[volume.restrict Work.Spaces.Iθ]
          (fun θ : ℝ => Work.Spaces.HkIntegrand α 1 F t θ / a ^ 2 + 1 / 2) := by
      rw [hmeq]
      exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo
        (fun θ hθ => (hpt θ hθ).2)
    calc (∫ θ in Work.Spaces.Iθ, |Work.Spaces.pz F t θ|)
        ≤ ∫ θ in Work.Spaces.Iθ, (Work.Spaces.HkIntegrand α 1 F t θ / a ^ 2 + 1 / 2) :=
          integral_mono_ae hPint hg hle
      _ = (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 1 F t θ) / a ^ 2 + Real.pi / 4 := by
          rw [integral_add hHk2 hconst, MeasureTheory.integral_div, integral_Iθ_half]

end Work.FTS.PhiStar.Honesty
