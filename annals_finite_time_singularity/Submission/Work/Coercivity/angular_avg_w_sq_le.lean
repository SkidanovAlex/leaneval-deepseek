import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.Coercivity.Defs
import Submission.Work.Spaces.Defs
import Submission.Work.Coercivity.EL12z_ae_slice
import Submission.Work.Coercivity.slice_cs_K
import Submission.Work.Coercivity.K_facts
import Submission.Work.Coercivity.prod_slice_facts
import Submission.Work.Coercivity.aesm_angAvg

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Coercivity

set_option autoImplicit false

/-- The angular averaging step of Lemma `HardyWeight`: the squared angular average
`g z = ∫ θ in Spaces.Iθ, Spaces.K θ * f z θ` against the radial weight `w` is controlled by
the `θ`-energy of `f` against `w`.

Intended proof: from the joint integrability hypothesis `hfw` (Fubini) one obtains
integrability of `z ↦ (w z)² * ∫ θ in Iθ, (f z θ)²` on `Iz`; for a.e. `z` the slice
`f z ·` lies in `L²(Iθ)` and the Cauchy–Schwarz inequality gives
`(∫ θ, K θ * f z θ)² ≤ (∫ θ, K θ²) * (∫ θ, (f z θ)²)`, while
`∫ θ in Spaces.Iθ, (Spaces.K θ)² ≤ 3` because `K θ = 3 sin θ cos²θ` satisfies
`K θ² = 9 sin²θ cos⁴θ ≤ 9 sin θ cos²θ = 3 K θ` pointwise on `Iθ` (using
`0 ≤ sin θ cos²θ ≤ 1`) and `∫ θ in Spaces.Iθ, Spaces.K θ = 1`.  Multiplying by
`(w z)² ≥ 0` and integrating over `Iz` gives the conclusion.

Measurability of `z ↦ ∫ θ in Iθ, Spaces.K θ * f z θ` comes from `hf : HardyHyp f`:
`HardyHyp.hcont` makes `z ↦ L12dens K f z = (∫ θ, K θ * f z θ)/z` continuous on `(0,∞)`,
so `z ↦ ∫ θ, K θ * f z θ = z * L12dens K f z` is continuous (hence a.e. strongly
measurable) there, and `{0}` is null. -/
theorem angular_avg_w_sq_le (f : ℝ → ℝ → ℝ) (hf : HardyHyp f)
    (hfw : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => (f z θ * Spaces.w z) ^ 2)) (Spaces.Iz ×ˢ Spaces.Iθ)) :
    MeasureTheory.IntegrableOn
        (fun z => (∫ θ in Spaces.Iθ, Spaces.K θ * f z θ) ^ 2 * (Spaces.w z) ^ 2) Spaces.Iz ∧
      ∫ z in Spaces.Iz, (∫ θ in Spaces.Iθ, Spaces.K θ * f z θ) ^ 2 * (Spaces.w z) ^ 2
        ≤ 3 * ∫ z in Spaces.Iz, (Spaces.w z) ^ 2 * (∫ θ in Spaces.Iθ, (f z θ) ^ 2) := by
  obtain ⟨hKnn, _hK2pt, _hKint1, hKsq⟩ := K_facts
  obtain ⟨hsl, hSint, hSF⟩ := prod_slice_facts f hfw
  -- `K ^ 2` is integrable on the compact interval `Iθ`
  have hKcont : Continuous fun θ : ℝ => (Spaces.K θ) ^ 2 := by
    unfold Spaces.K; fun_prop
  have hKi : MeasureTheory.IntegrableOn (fun θ => (Spaces.K θ) ^ 2) Spaces.Iθ := by
    refine hKcont.continuousOn.integrableOn_compact ?_
    rw [Spaces.Iθ]; exact isCompact_Icc
  -- transfer the a.e. slice statement from `(0,∞)` to `Iz`
  have hμeq : MeasureTheory.volume.restrict (Set.Ioi (0:ℝ))
      = MeasureTheory.volume.restrict Spaces.Iz :=
    MeasureTheory.Measure.restrict_congr_set (MeasureTheory.Ioi_ae_eq_Ici (a := (0:ℝ)))
  have hsl' : ∀ᵐ z ∂(MeasureTheory.volume.restrict Spaces.Iz),
      MeasureTheory.IntegrableOn (fun θ => (f z θ) ^ 2) Spaces.Iθ :=
    hμeq ▸ EL12z_ae_slice f hfw
  -- the pointwise a.e. angular Cauchy–Schwarz bound
  have hbound : ∀ᵐ z ∂(MeasureTheory.volume.restrict Spaces.Iz),
      (∫ θ in Spaces.Iθ, Spaces.K θ * f z θ) ^ 2 * (Spaces.w z) ^ 2
        ≤ 3 * ((Spaces.w z) ^ 2 * ∫ θ in Spaces.Iθ, (f z θ) ^ 2) := by
    filter_upwards [hsl'] with z hL2
    have hcs := slice_cs_K f z hKnn hKi hKsq hL2
    have hw2 : (0:ℝ) ≤ (Spaces.w z) ^ 2 := sq_nonneg _
    calc (∫ θ in Spaces.Iθ, Spaces.K θ * f z θ) ^ 2 * (Spaces.w z) ^ 2
        ≤ (3 * ∫ θ in Spaces.Iθ, (f z θ) ^ 2) * (Spaces.w z) ^ 2 :=
          mul_le_mul_of_nonneg_right hcs hw2
      _ = 3 * ((Spaces.w z) ^ 2 * ∫ θ in Spaces.Iθ, (f z θ) ^ 2) := by ring
  -- the dominating function is integrable
  have hRint : MeasureTheory.Integrable
      (fun z => 3 * ((Spaces.w z) ^ 2 * ∫ θ in Spaces.Iθ, (f z θ) ^ 2))
      (MeasureTheory.volume.restrict Spaces.Iz) :=
    (hSint.congr (Filter.Eventually.of_forall fun z => hSF z)).const_mul 3
  -- integrability of the left-hand integrand, and the comparison of integrals
  have hGint : MeasureTheory.Integrable
      (fun z => (∫ θ in Spaces.Iθ, Spaces.K θ * f z θ) ^ 2 * (Spaces.w z) ^ 2)
      (MeasureTheory.volume.restrict Spaces.Iz) := by
    refine hRint.mono' (aesm_angAvg f hf) ?_
    filter_upwards [hbound] with z hz
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))]
    exact hz
  refine ⟨hGint, ?_⟩
  have hmono := MeasureTheory.integral_mono_ae hGint hRint hbound
  have hc : (∫ z, 3 * ((Spaces.w z) ^ 2 * ∫ θ in Spaces.Iθ, (f z θ) ^ 2)
        ∂(MeasureTheory.volume.restrict Spaces.Iz))
      = 3 * ∫ z, (Spaces.w z) ^ 2 * (∫ θ in Spaces.Iθ, (f z θ) ^ 2)
        ∂(MeasureTheory.volume.restrict Spaces.Iz) := MeasureTheory.integral_const_mul 3 _
  calc ∫ z in Spaces.Iz, (∫ θ in Spaces.Iθ, Spaces.K θ * f z θ) ^ 2 * (Spaces.w z) ^ 2
      ≤ ∫ z in Spaces.Iz, 3 * ((Spaces.w z) ^ 2 * ∫ θ in Spaces.Iθ, (f z θ) ^ 2) := hmono
    _ = 3 * ∫ z in Spaces.Iz,
          (Spaces.w z) ^ 2 * (∫ θ in Spaces.Iθ, (f z θ) ^ 2) := hc

end Work.Coercivity
