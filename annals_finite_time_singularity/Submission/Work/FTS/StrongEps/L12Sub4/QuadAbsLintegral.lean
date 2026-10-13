import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.StrongEps.L12Sub4.Defs
import Submission.Work.FTS.OpenPkg.l12zero_field

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.L12Sub4

/-! ## Elementary regularity facts for the weighted integrand `K(θ)|f z θ|/z` -/

/-- `(z,θ) ↦ |f z θ|` is continuous on the open quadrant as soon as `f` is smooth there. -/
private theorem continuousOn_abs_uncurry {f : ℝ → ℝ → ℝ}
    (hso : Work.FTS.EllipticEst.SmoothOpen f) :
    ContinuousOn (fun p : ℝ × ℝ => |f p.1 p.2|) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
  have hcont : ContinuousOn (Function.uncurry f) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
    simpa only [Work.FTS.EllipticEst.Q0] using hso.continuousOn
  exact hcont.abs

/-- The full weighted integrand `(z,θ) ↦ K(θ)|f z θ|/z` is continuous on the open quadrant
(`z` never vanishes there). -/
private theorem continuousOn_quadWeightedAbs {f : ℝ → ℝ → ℝ}
    (hso : Work.FTS.EllipticEst.SmoothOpen f) :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.K p.2 * |f p.1 p.2| / p.1)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
  have hK : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.K p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
    Work.Coercivity.K_facts_continuous.comp_continuousOn continuous_snd.continuousOn
  exact (hK.mul (continuousOn_abs_uncurry hso)).div continuousOn_fst
    (fun p hp => ne_of_gt hp.1)

/-- **Angular slice integrability.**  For `z > 0` the slice `θ ↦ K(θ)|f z θ|/z` is integrable
on `Iθ`: it is dominated by `(3/(2z))((f z θ)² + 1)`, whose θ-integral is finite by the
`ℋ⁴`-membership hypothesis. -/
private theorem integrableOn_sliceWeightedAbs {α : ℝ} {f : ℝ → ℝ → ℝ}
    (hso : Work.FTS.EllipticEst.SmoothOpen f) (hm : Work.Spaces.HkMem α 4 f) {z : ℝ}
    (hz : 0 < z) :
    MeasureTheory.IntegrableOn (fun θ : ℝ => Work.Spaces.K θ * |f z θ| / z)
      Work.Spaces.Iθ := by
  have hsl : MeasureTheory.IntegrableOn (fun θ : ℝ => (f z θ) ^ 2) Work.Spaces.Iθ :=
    Work.FTS.OpenPkg.l12zero_slice_sq_integrableOn α hso hm hz
  have hconst : MeasureTheory.IntegrableOn (fun _ : ℝ => (1 : ℝ)) Work.Spaces.Iθ := by
    rw [Work.Spaces.Iθ]
    exact (continuousOn_const (c := (1 : ℝ))).integrableOn_compact isCompact_Icc
  have hmaj : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (3 / (2 * z)) * ((f z θ) ^ 2 + 1)) Work.Spaces.Iθ := by
    have h1 : MeasureTheory.IntegrableOn (fun θ : ℝ => (f z θ) ^ 2 + 1) Work.Spaces.Iθ :=
      hsl.add hconst
    exact h1.const_mul (3 / (2 * z))
  refine hmaj.mono'
    (Work.Spaces.aesm_slice_of_continuousOn_Qd _
      (continuousOn_quadWeightedAbs hso) hz) ?_
  refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => ?_)
  have hKnn : 0 ≤ Work.Spaces.K θ := Work.Coercivity.K_facts_nonneg θ hθ
  have hKle : Work.Spaces.K θ ≤ 3 := Work.Coercivity.K_facts_le_three θ hθ
  have hval : 0 ≤ Work.Spaces.K θ * |f z θ| / z :=
    div_nonneg (mul_nonneg hKnn (abs_nonneg _)) (le_of_lt hz)
  rw [Real.norm_eq_abs, abs_of_nonneg hval]
  have h1 : Work.Spaces.K θ * |f z θ| / z ≤ 3 * |f z θ| / z := by
    apply div_le_div_of_nonneg_right _ (le_of_lt hz)
    exact mul_le_mul_of_nonneg_right hKle (abs_nonneg _)
  have h2 : 3 * |f z θ| / z = (3 / (2 * z)) * (2 * |f z θ|) := by
    field_simp
  have ham : 2 * |f z θ| ≤ (f z θ) ^ 2 + 1 := by
    nlinarith [sq_nonneg (|f z θ| - 1), sq_abs (f z θ)]
  have hcz : 0 ≤ 3 / (2 * z) := by positivity
  calc Work.Spaces.K θ * |f z θ| / z ≤ 3 * |f z θ| / z := h1
    _ = (3 / (2 * z)) * (2 * |f z θ|) := h2
    _ ≤ (3 / (2 * z)) * ((f z θ) ^ 2 + 1) := mul_le_mul_of_nonneg_left ham hcz

/-! ## Integrability of the radial density -/

/-- **The radial density `z ↦ ∫_θ K(θ)|f z θ|/z` is integrable on `(0,∞)`.**

The pointwise Cauchy–Schwarz of `L12dens_sq_slice` gives
`|∫_θ K|f|/z| ≤ √3·√(∫_θ f²)/z`; writing `1/z = ((1+z)/z)·(1/(1+z))` shows this is
`√3·√((∫_θ f²)w(z))·(1/(1+z))`, and Young's inequality dominates the product of the two
square-integrable factors `√((∫_θ f²)w)` (finite by `phiWeight_slice_le` + `hm.2`) and
`1/(1+z)` (finite by `InvOneAddSq`). -/
private theorem integrableOn_densityAbs {α : ℝ} {f : ℝ → ℝ → ℝ}
    (hso : Work.FTS.EllipticEst.SmoothOpen f) (hm : Work.Spaces.HkMem α 4 f) :
    MeasureTheory.IntegrableOn
      (fun z : ℝ => ∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * |f z θ| / z)
      (Set.Ioi (0 : ℝ)) := by
  have hcont : ContinuousOn (Function.uncurry f) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
    simpa only [Work.FTS.EllipticEst.Q0] using hso.continuousOn
  -- (1) the Hardy-weighted angular energy is integrable
  have hPhi : MeasureTheory.IntegrableOn
      (fun r : ℝ => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f r θ)
      (Set.Ioi (0 : ℝ)) := hm.2.mono_set Set.Ioi_subset_Ici_self
  have henergy_aesm : MeasureTheory.AEStronglyMeasurable
      (fun r : ℝ => (∫ θ in Work.Spaces.Iθ, (f r θ) ^ 2) * ((1 + r) / r) ^ 2)
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) :=
    Work.FTS.OpenPkg.l12zero_energy_aesm hcont
  have hfin : MeasureTheory.IntegrableOn
      (fun r : ℝ => (∫ θ in Work.Spaces.Iθ, (f r θ) ^ 2) * ((1 + r) / r) ^ 2)
      (Set.Ioi (0 : ℝ)) := by
    refine hPhi.mono' henergy_aesm ?_
    filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioi] with r hr
    rw [Real.norm_of_nonneg (mul_nonneg (integral_nonneg fun θ => sq_nonneg _)
      (sq_nonneg _))]
    exact Work.FTS.H2.L12Q.phiWeight_slice_le α f hm r hr
  -- (2) almost-everywhere strong measurability of the density
  have hdensity_aesm : MeasureTheory.AEStronglyMeasurable
      (fun z : ℝ => ∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * |f z θ| / z)
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) := by
    have hjoint : MeasureTheory.AEStronglyMeasurable
        (Function.uncurry fun z θ => Work.Spaces.K θ * |f z θ| / z)
        ((MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
      (Work.Spaces.aesm_of_continuousOn_Qd _
        (continuousOn_quadWeightedAbs hso)).mono_measure
        (Measure.prod_mono (Measure.restrict_mono_set volume Set.Ioi_subset_Ici_self) le_rfl)
    simpa only [Function.uncurry] using hjoint.integral_prod_right'
  -- (3) an integrable majorant
  have hmaj : MeasureTheory.IntegrableOn
      (fun z : ℝ => 3 * ((∫ θ in Work.Spaces.Iθ, (f z θ) ^ 2) * ((1 + z) / z) ^ 2)
        + (1 / (1 + z)) ^ 2) (Set.Ioi (0 : ℝ)) :=
    (hfin.const_mul 3).add Work.FTS.H2.InvOneAddSq.1
  refine hmaj.mono' hdensity_aesm ?_
  filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioi] with z hz
  -- the pointwise domination
  have hz0 : (0 : ℝ) < z := hz
  set P : ℝ := ∫ θ in Work.Spaces.Iθ, (f z θ) ^ 2 with hPdef
  have hPnn : 0 ≤ P := by rw [hPdef]; exact integral_nonneg fun θ => sq_nonneg _
  have hsl : MeasureTheory.IntegrableOn (fun θ : ℝ => (f z θ) ^ 2) Work.Spaces.Iθ :=
    Work.FTS.OpenPkg.l12zero_slice_sq_integrableOn α hso hm hz
  have hslabs : MeasureTheory.IntegrableOn (fun θ : ℝ => |f z θ| ^ 2) Work.Spaces.Iθ :=
    hsl.congr_fun (fun θ _ => (sq_abs (f z θ)).symm) measurableSet_Icc
  have hdens : Work.FM.L12dens Work.Spaces.K (fun z θ => |f z θ|) z
      = ∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * |f z θ| / z := by
    rw [Work.FM.L12dens, Work.Spaces.Iθ]
  have hcs := Work.Coercivity.L12dens_sq_slice (fun z θ => |f z θ|)
    Work.Coercivity.integral_Itheta_K hz hslabs
  have hPabs : (∫ θ in Work.Spaces.Iθ, |f z θ| ^ 2) = P := by
    rw [hPdef]
    exact integral_congr_ae (Filter.Eventually.of_forall fun θ => sq_abs (f z θ))
  rw [hPabs, hdens] at hcs
  -- `hcs : (∫_θ K θ |f z θ|/z)^2 ≤ 3 * P / z^2`
  have hstep1 : |∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * |f z θ| / z|
      ≤ Real.sqrt 3 * Real.sqrt P / z := by
    rw [← Real.sqrt_sq_eq_abs (∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * |f z θ| / z)]
    refine le_trans (Real.sqrt_le_sqrt hcs) ?_
    rw [Real.sqrt_div (by linarith : (0 : ℝ) ≤ 3 * P), Real.sqrt_sq_eq_abs,
      abs_of_pos hz0, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 3) P]
  have hstep2 : Real.sqrt 3 * Real.sqrt P / z
      = Real.sqrt 3 * Real.sqrt (P * ((1 + z) / z) ^ 2) * (1 / (1 + z)) := by
    have hsz : Real.sqrt (P * ((1 + z) / z) ^ 2) = Real.sqrt P * ((1 + z) / z) := by
      rw [Real.sqrt_mul hPnn, Real.sqrt_sq_eq_abs,
        abs_of_nonneg (by positivity : (0 : ℝ) ≤ (1 + z) / z)]
    have hkey : Real.sqrt P / z = Real.sqrt (P * ((1 + z) / z) ^ 2) * (1 / (1 + z)) := by
      rw [hsz]
      field_simp
    rw [mul_div_assoc, hkey]
    ring
  have hstep3 : Real.sqrt 3 * Real.sqrt (P * ((1 + z) / z) ^ 2) * (1 / (1 + z))
      ≤ 3 * (P * ((1 + z) / z) ^ 2) + (1 / (1 + z)) ^ 2 := by
    have hu : Real.sqrt (P * ((1 + z) / z) ^ 2) ^ 2 = P * ((1 + z) / z) ^ 2 :=
      Real.sq_sqrt (by positivity)
    have h3 : Real.sqrt 3 ^ 2 = (3 : ℝ) := Real.sq_sqrt (by norm_num)
    nlinarith [sq_nonneg (Real.sqrt 3 * Real.sqrt (P * ((1 + z) / z) ^ 2)
      - (1 / (1 + z)))]
  have hgoal : ‖∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * |f z θ| / z‖
      ≤ 3 * ((∫ θ in Work.Spaces.Iθ, (f z θ) ^ 2) * ((1 + z) / z) ^ 2)
        + (1 / (1 + z)) ^ 2 := by
    rw [Real.norm_eq_abs, ← hPdef]
    exact le_trans hstep1 (le_trans (le_of_eq hstep2) hstep3)
  exact hgoal

/-! ## The main estimate -/

/-- **The weighted `L¹` size of an `ℋ⁴` profile**, in the quadrant (`dθ dr`, weight `K(θ)/r`):
for `α ∈ (0,1]`, `f` smooth on the open quadrant with honest `ℋ⁴`-membership,

  `∫⁻_z∈(0,∞) ∫⁻_θ∈Iθ ofReal (K(θ) |f z θ| / z) ≤ ofReal (4 ‖f‖_{ℋ⁴})`.

The constant is universal (independent of `α` and `f`).

Hints: everything is nonnegative, so it suffices to bound the corresponding Bochner integrals and
convert with `MeasureTheory.ofReal_integral_eq_lintegral_ofReal`.  The chain is the one of
`Work.FTS.Nonlinear.Pieces.L12_zero_le_weak` / `Work.FTS.OpenPkg.l12zero_field`: by definition
`L₁₂(|f|)(0) = ∫_{r>0} ∫_θ K(θ)|f r θ|/r ≥ 0` (`L12_zero_eq_double` of `Defs`), and
`|L₁₂(|f|)(0)| ≤ 3 √(∫_{r>0} (∫_θ f²) ((1+r)/r)²)` by `L12_zero_le_weak` applied to `|f|` (its two
integrability hypotheses are literally those of `f`: `(∫_θ (|f|)²) = ∫_θ f²`; they are available from
`Work.FTS.OpenPkg.l12zero_slice_sq_integrableOn` and `Work.FTS.H2.L12Q.phiWeight_slice_le` +
`hm.2`), while `∫_{r>0} (∫_θ f²) ((1+r)/r)² ≤ ∫_{r>0}∫_θ HkIntegrand α 4 f = HkSq α 4 f`.
For the `ofReal` conversion one needs integrability of the nonnegative product integrand
`(z,θ) ↦ K θ |f z θ|/z` on `Ioi 0 ×ˢ Iθ`; it is finite by the same Cauchy–Schwarz chain performed at
the level of `∫⁻` (equivalently: `Integrable.mono'` against a majorant whose integral is the finite
quantity above), or one argues that the `lintegral` equals `ofReal` of the Bochner integral once the
latter is finite. -/
theorem QuadAbsLintegral {α : ℝ} (hα : α ∈ Set.Ioc 0 1) {f : ℝ → ℝ → ℝ}
    (hso : Work.FTS.EllipticEst.SmoothOpen f) (hm : Work.Spaces.HkMem α 4 f) :
    (∫⁻ z in Set.Ioi 0, ∫⁻ θ in Work.Spaces.Iθ,
        ENNReal.ofReal (Work.Spaces.K θ * |f z θ| / z))
      ≤ ENNReal.ofReal (4 * Work.Spaces.HkNorm α 4 f) := by
  -- the estimate is uniform in `α`; the range hypothesis on `α` is not needed
  have _hαpos : (0 : ℝ) < α := hα.1
  have hcont : ContinuousOn (Function.uncurry f) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
    simpa only [Work.FTS.EllipticEst.Q0] using hso.continuousOn
  -- integrability of the radial density, and its positivity
  have hdensity : MeasureTheory.IntegrableOn
      (fun z : ℝ => ∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * |f z θ| / z)
      (Set.Ioi (0 : ℝ)) := integrableOn_densityAbs hso hm
  have hnonneg : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))),
      0 ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * |f z θ| / z :=
    MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi (fun z hz =>
      integral_nonneg_of_ae (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc
        (fun θ hθ => div_nonneg (mul_nonneg (Work.Coercivity.K_facts_nonneg θ hθ)
          (abs_nonneg _)) (le_of_lt hz))))
  -- the two `ofReal`-conversions
  have hslice : ∀ z ∈ Set.Ioi (0 : ℝ),
      (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (Work.Spaces.K θ * |f z θ| / z))
        = ENNReal.ofReal (∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * |f z θ| / z) :=
    fun z hz => (MeasureTheory.ofReal_integral_eq_lintegral_ofReal
      (integrableOn_sliceWeightedAbs hso hm hz)
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ =>
        div_nonneg (mul_nonneg (Work.Coercivity.K_facts_nonneg θ hθ) (abs_nonneg _))
          (le_of_lt hz)))).symm
  have houter : (∫⁻ z in Set.Ioi 0, ENNReal.ofReal
        (∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * |f z θ| / z))
      = ENNReal.ofReal (∫ z in Set.Ioi 0, ∫ θ in Work.Spaces.Iθ,
          Work.Spaces.K θ * |f z θ| / z) :=
    (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hdensity hnonneg).symm
  -- the estimate for the Bochner integral
  have hbound : (∫ z in Set.Ioi 0, ∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * |f z θ| / z)
      ≤ 4 * Work.Spaces.HkNorm α 4 f := by
    have hL12 : (∫ z in Set.Ioi 0, ∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * |f z θ| / z)
        = Work.Construction.L12 (fun z θ => |f z θ|) 0 := (L12_zero_eq_double _).symm
    rw [hL12]
    have hsl : ∀ᵐ r ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))),
        MeasureTheory.IntegrableOn (fun θ : ℝ => (|f r θ|) ^ 2) Work.Spaces.Iθ := by
      filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioi] with r hr
      exact (Work.FTS.OpenPkg.l12zero_slice_sq_integrableOn α hso hm hr).congr_fun
        (fun θ _ => (sq_abs (f r θ)).symm) measurableSet_Icc
    have hmeas : MeasureTheory.AEStronglyMeasurable
        (fun r : ℝ => (∫ θ in Work.Spaces.Iθ, (|f r θ|) ^ 2) * ((1 + r) / r) ^ 2)
        (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) := by
      refine (Work.FTS.OpenPkg.l12zero_energy_aesm hcont).congr ?_
      filter_upwards with r
      congr 1
      exact integral_congr_ae (Filter.Eventually.of_forall fun θ => (sq_abs (f r θ)).symm)
    have hPhi : MeasureTheory.IntegrableOn
        (fun r : ℝ => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f r θ)
        (Set.Ioi (0 : ℝ)) := hm.2.mono_set Set.Ioi_subset_Ici_self
    have hbd : ∀ᵐ r ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))),
        (∫ θ in Work.Spaces.Iθ, (|f r θ|) ^ 2) * ((1 + r) / r) ^ 2
          ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f r θ := by
      filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioi] with r hr
      rw [integral_congr_ae (Filter.Eventually.of_forall fun θ => sq_abs (f r θ))]
      exact Work.FTS.H2.L12Q.phiWeight_slice_le α f hm r hr
    have hmain := Work.FTS.OpenPkg.l12zero_of_weight_bound
      (f := fun z θ => |f z θ|) hsl hmeas hPhi hbd
    have hHkSq : (∫ r in Set.Ioi 0, ∫ θ in Work.Spaces.Iθ,
          Work.Spaces.HkIntegrand α 4 f r θ) = Work.Spaces.HkSq α 4 f := by
      rw [Work.Spaces.HkSq, Work.Spaces.Iz]
      exact MeasureTheory.setIntegral_congr_set
        (MeasureTheory.Ioi_ae_eq_Ici (a := (0 : ℝ)))
    rw [hHkSq] at hmain
    have hN : 0 ≤ Work.Spaces.HkNorm α 4 f := Real.sqrt_nonneg _
    calc Work.Construction.L12 (fun z θ => |f z θ|) 0
        ≤ |Work.Construction.L12 (fun z θ => |f z θ|) 0| := le_abs_self _
      _ ≤ 3 * Real.sqrt (Work.Spaces.HkSq α 4 f) := hmain
      _ = 3 * Work.Spaces.HkNorm α 4 f := rfl
      _ ≤ 4 * Work.Spaces.HkNorm α 4 f := by linarith
  calc (∫⁻ z in Set.Ioi 0, ∫⁻ θ in Work.Spaces.Iθ,
        ENNReal.ofReal (Work.Spaces.K θ * |f z θ| / z))
      = ∫⁻ z in Set.Ioi 0, ENNReal.ofReal
          (∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * |f z θ| / z) :=
        MeasureTheory.setLIntegral_congr_fun measurableSet_Ioi hslice
    _ = ENNReal.ofReal (∫ z in Set.Ioi 0, ∫ θ in Work.Spaces.Iθ,
          Work.Spaces.K θ * |f z θ| / z) := houter
    _ ≤ ENNReal.ofReal (4 * Work.Spaces.HkNorm α 4 f) := ENNReal.ofReal_le_ofReal hbound

end Work.FTS.StrongEps.L12Sub4
