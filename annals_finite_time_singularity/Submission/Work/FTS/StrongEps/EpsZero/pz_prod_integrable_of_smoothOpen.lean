/-
Copyright: work module for the Elgindi finite-time singularity project.

# Joint integrability of `K(θ) · ∂_z f(z,θ)` on `(0,∞) × Iθ` from `SmoothOpen` + `ℋ¹`

For a datum `f` which is `C^∞` on the open quadrant `(0,∞) × (0,π/2)`
(`Work.FTS.EllipticEst.SmoothOpen`) and honest in the weighted space `ℋ¹`
(`Work.Spaces.HkMem α 1 f`) the function

  `(z,θ) ↦ K(θ) · ∂_z f(z,θ)`,  `K(θ) = 3 sin θ cos²θ`,

is integrable on `(0,∞) × Iθ`.  This is the Fubini input of the zero-mode identity
`Work.FTS.Apriori.ZeroMode.L12_Dz_zero`; the hypothesis `HkMem α 1` is the honest
first-order membership, which controls exactly the two objects used below.

**Route.**  `K` is bounded by `3` on `Iθ`, and on the open quadrant

  `∂_z f = D_z f / z`,  `1/(z w z) = z/(1+z)²`  (`w z = (1+z)²/z²`),

so the `i = 1` summand `(D_z f · w / sin(2θ)^{η/2})²` of the `ℋ¹`-integrand controls
`∂_z f` up to the factor `(z/(1+z)²)²`.  Concretely, for `z > 0`,

  `∫_θ |K(θ) ∂_z f(z,θ)| ≤ 3 ∫_θ |∂_z f(z,θ)|
      ≤ 3 √(π/2) · z/(1+z)² · √(∫_θ HkIntegrand α 1 f z θ)`   (`pz_abs_slice_le_sqrt_Hk`),

and the right-hand side is a product of two `L²((0,∞))`-functions
(`z ↦ z/(1+z)²` is square-integrable, `∫_z ∫_θ HkIntegrand < ∞` is `HkMem α 1`),
hence `L¹` by AM–GM.  The joint a.e. strong measurability comes from continuity on
the open quadrant, the complement of which in `Ioi 0 ×ˢ Iθ` is null; the identity
`IntegrableOn g (s ×ˢ t) = Integrable g ((volume|_{s}).prod (volume|_{t}))` is
`Measure.prod_restrict`.

Everything here is `sorry`-free and rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.integrable_prod_of_iterated
import Submission.Work.Spaces.aesm_of_continuousOn_Qd
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.Elliptic.L12densFacts
import Submission.Work.FTS.PhiStar.Honesty.pz_abs_slice_le_sqrt_Hk
import Submission.Work.Coercivity.K_facts

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsZero

set_option autoImplicit false
set_option maxHeartbeats 800000

/-! ## Almost everywhere strong measurability on `Ioi 0 ×ˢ Iθ` -/

/-- Continuity on the open quadrant gives a.e. strong measurability for the product of the
restrictions of Lebesgue measure to `Ioi 0 = (0,∞)` and to `Iθ = [0,π/2]`.  Indeed that product
measure is the restriction of the planar Lebesgue measure to `Ioi 0 ×ˢ Iθ`, which equals the
open quadrant up to a null set (the difference being contained in the two boundary lines
`θ = 0` and `θ = π/2`).  (The `z ∈ [0,∞)`-analogue is `Work.Spaces.aesm_of_continuousOn_Qd`.) -/
theorem aesm_prod_Ioi_of_continuousOn_Q0 {g : ℝ × ℝ → ℝ}
    (hg : ContinuousOn g (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2))) :
    AEStronglyMeasurable g ((volume.restrict (Set.Ioi 0)).prod (volume.restrict Work.Spaces.Iθ)) := by
  have hθ : Work.Spaces.Iθ =ᵐ[volume] Set.Ioo (0 : ℝ) (π / 2) :=
    (MeasureTheory.Ioo_ae_eq_Icc (μ := volume) (a := 0) (b := π / 2)).symm
  have hprod : (Set.Ioi 0 ×ˢ Work.Spaces.Iθ : Set (ℝ × ℝ))
      =ᵐ[volume.prod volume] (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
    MeasureTheory.Measure.set_prod_ae_eq (Filter.EventuallyEq.refl _ _) hθ
  have hUm : MeasurableSet (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo 0 (π / 2)) :=
    (isOpen_Ioi.prod isOpen_Ioo).measurableSet
  have hmain : AEStronglyMeasurable g
      ((volume.prod volume).restrict (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2))) :=
    hg.aestronglyMeasurable hUm
  rw [MeasureTheory.Measure.prod_restrict, MeasureTheory.Measure.restrict_congr_set hprod]
  exact hmain

/-! ## The elementary radial integral -/

/-- `z ↦ 1/(1+z)²` is integrable on `(0,∞)` (with value `1`); the antiderivative
`z ↦ -1/(1+z)` is nondecreasing and tends to `0` at `+∞`. -/
theorem integrableOn_one_div_one_add_sq :
    IntegrableOn (fun z : ℝ => 1 / (1 + z) ^ 2) (Set.Ioi 0) := by
  have hcont : ContinuousWithinAt (fun z : ℝ => -1 / (1 + z)) (Set.Ici 0) 0 := by
    refine (ContinuousAt.div continuousAt_const
      (continuousAt_const.add continuousAt_id) ?_).continuousWithinAt
    norm_num
  have hderiv : ∀ x ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (fun z : ℝ => -1 / (1 + z)) ((-1) * (-1 / (1 + x) ^ 2)) x := by
    intro x hx
    have hx' : (0 : ℝ) < x := hx
    have h0 : (0 : ℝ) < 1 + x := by linarith
    have h1 : HasDerivAt (fun z : ℝ => (1 + z)⁻¹) (-1 / (1 + x) ^ 2) x :=
      ((hasDerivAt_id x).const_add (1 : ℝ)).inv (ne_of_gt h0)
    exact h1.const_mul (-1)
  have hpos : ∀ x ∈ Set.Ioi (0 : ℝ), 0 ≤ ((-1) * (-1 / (1 + x) ^ 2)) := by
    intro x hx
    have hx' : (0 : ℝ) < x := hx
    have h0 : (0 : ℝ) < 1 + x := by linarith
    have heq : (-1) * (-1 / (1 + x) ^ 2) = 1 / (1 + x) ^ 2 := by ring
    rw [heq]; positivity
  have hlim : Tendsto (fun z : ℝ => -1 / (1 + z)) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_left atTop (1 : ℝ) tendsto_id)
  have hint : IntegrableOn (fun z : ℝ => (-1) * (-1 / (1 + z) ^ 2)) (Set.Ioi 0) :=
    integrableOn_Ioi_deriv_of_nonneg hcont hderiv hpos hlim
  refine hint.congr (Filter.Eventually.of_forall fun z => ?_)
  ring

/-- `(z/(1+z)²)² ≤ 1/(1+z)²` for `z > 0` (equivalently `z² ≤ (1+z)²`). -/
private theorem sq_div_one_add_sq_sq_le {z : ℝ} (hz : 0 < z) :
    (z / (1 + z) ^ 2) ^ 2 ≤ 1 / (1 + z) ^ 2 := by
  have h0 : 0 < 1 + z := by linarith
  rw [div_pow]
  rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < ((1 + z) ^ 2) ^ 2)
    (by positivity : (0 : ℝ) < (1 + z) ^ 2)]
  nlinarith [sq_nonneg (1 + z), h0]

/-! ## The main lemma -/

theorem pz_prod_integrable_of_smoothOpen {α : ℝ} {f : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α 1 f) :
    MeasureTheory.IntegrableOn
      (fun p : ℝ × ℝ => Work.Spaces.K p.2 * Work.Spaces.pz f p.1 p.2)
      (Set.Ioi 0 ×ˢ Work.Spaces.Iθ) := by
  show Integrable (fun p : ℝ × ℝ => Work.Spaces.K p.2 * Work.Spaces.pz f p.1 p.2)
    (volume.restrict (Set.Ioi 0 ×ˢ Work.Spaces.Iθ))
  rw [MeasureTheory.Measure.volume_eq_prod, ← MeasureTheory.Measure.prod_restrict]
  -- the integrand is continuous on the open quadrant, hence a.e. strongly measurable
  have hcont : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.K p.2 * Work.Spaces.pz f p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
    refine ContinuousOn.mul ?_ ?_
    · exact Work.Coercivity.K_facts_continuous.comp_continuousOn continuous_snd.continuousOn
    · exact (hsm.pz).continuousOn
  have hAESM := aesm_prod_Ioi_of_continuousOn_Q0 hcont
  have hK3 : ∀ θ ∈ Work.Spaces.Iθ, |Work.Spaces.K θ| ≤ 3 := by
    intro θ hθ
    rw [abs_of_nonneg (Work.Coercivity.K_facts_nonneg θ hθ)]
    exact Work.Coercivity.K_facts_le_three θ hθ
  -- angular slices are integrable
  have hslice : ∀ᵐ z ∂(volume.restrict (Set.Ioi 0)),
      Integrable (fun θ => Work.Spaces.K θ * Work.Spaces.pz f z θ)
        (volume.restrict Work.Spaces.Iθ) := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z hz
    have hzpos : 0 < z := hz
    have habs := (Work.FTS.PhiStar.Honesty.slice_abs_integrable hsm hmem hzpos).2
    have hmeas : AEStronglyMeasurable (fun θ : ℝ => Work.Spaces.K θ * Work.Spaces.pz f z θ)
        (volume.restrict Work.Spaces.Iθ) := by
      have h1 : AEStronglyMeasurable (fun θ : ℝ => Work.Spaces.pz f z θ)
          (volume.restrict Work.Spaces.Iθ) := by
        simpa only [Work.Spaces.pzIter_succ, Work.Spaces.pzIter_zero] using
          hsm.aesm_slice_pzIter 1 hzpos
      exact (Work.Coercivity.K_facts_continuous.measurable.aestronglyMeasurable).mul h1
    refine Integrable.mono' (habs.const_mul 3) hmeas ?_
    filter_upwards [MeasureTheory.ae_restrict_of_forall_mem
      (show MeasurableSet Work.Spaces.Iθ from measurableSet_Icc)
      (fun θ hθ => hK3 θ hθ)] with θ hθ
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_right hθ (abs_nonneg _)
  -- the outer integral is integrable, by Cauchy–Schwarz against `ℋ¹`
  have houter : Integrable (fun z => ∫ θ, ‖Work.Spaces.K θ * Work.Spaces.pz f z θ‖
      ∂(volume.restrict Work.Spaces.Iθ)) (volume.restrict (Set.Ioi 0)) := by
    have hHk_int : Integrable (fun z : ℝ => ∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α 1 f z θ) (volume.restrict (Set.Ioi 0)) :=
      hmem.2.mono_set Set.Ioi_subset_Ici_self
    have hAcont : ContinuousOn (fun z : ℝ => 3 * Real.sqrt (π / 2) * (z / (1 + z) ^ 2))
        (Set.Ioi 0) := by
      refine ContinuousOn.mul continuousOn_const ?_
      refine ContinuousOn.div continuousOn_id ?_ ?_
      · exact (continuousOn_const.add continuousOn_id).pow 2
      · intro z hz
        have hz' : (0 : ℝ) < z := hz
        positivity
    have hA2 : Integrable (fun z : ℝ => (3 * Real.sqrt (π / 2) * (z / (1 + z) ^ 2)) ^ 2)
        (volume.restrict (Set.Ioi 0)) := by
      refine Integrable.mono' ((integrableOn_one_div_one_add_sq).const_mul (9 * (π / 2))) ?_ ?_
      · exact (hAcont.pow 2).aestronglyMeasurable measurableSet_Ioi
      · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z hz
        have hzpos : 0 < z := hz
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        have hle := sq_div_one_add_sq_sq_le hzpos
        have h9 : (3 * Real.sqrt (π / 2) * (z / (1 + z) ^ 2)) ^ 2
            = 9 * (π / 2) * (z / (1 + z) ^ 2) ^ 2 := by
          rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ π / 2)]
          ring
        rw [h9]
        have hpi : (0 : ℝ) < π / 2 := by positivity
        nlinarith [hle, hpi]
    have hB2 : Integrable (fun z : ℝ => (Real.sqrt (∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α 1 f z θ)) ^ 2) (volume.restrict (Set.Ioi 0)) := by
      refine hHk_int.congr (Filter.Eventually.of_forall fun z => ?_)
      exact (Real.sq_sqrt (MeasureTheory.integral_nonneg fun θ =>
        Work.Spaces.HkIntegrand_nonneg α 1 f z θ)).symm
    have hBaesm : AEStronglyMeasurable
        (fun z : ℝ => Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 1 f z θ))
        (volume.restrict (Set.Ioi 0)) :=
      (Real.continuous_sqrt.measurable.comp_aemeasurable hHk_int.aemeasurable).aestronglyMeasurable
    have hAB : Integrable (fun z : ℝ => (3 * Real.sqrt (π / 2) * (z / (1 + z) ^ 2))
          * Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 1 f z θ))
        (volume.restrict (Set.Ioi 0)) := by
      have hmaj : Integrable (fun z : ℝ =>
          (3 * Real.sqrt (π / 2) * (z / (1 + z) ^ 2)) ^ 2 / 2
            + (Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 1 f z θ)) ^ 2 / 2)
          (volume.restrict (Set.Ioi 0)) :=
        (hA2.div_const 2).add (hB2.div_const 2)
      refine Integrable.mono' hmaj ?_ ?_
      · exact (hAcont.aestronglyMeasurable measurableSet_Ioi).mul hBaesm
      · filter_upwards with z
        rw [Real.norm_eq_abs, abs_mul]
        nlinarith [sq_nonneg (|3 * Real.sqrt (π / 2) * (z / (1 + z) ^ 2)|
            - |Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 1 f z θ)|),
          sq_abs (3 * Real.sqrt (π / 2) * (z / (1 + z) ^ 2)),
          sq_abs (Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 1 f z θ))]
    have hAESM_int : AEStronglyMeasurable
        (fun z => ∫ θ, ‖Work.Spaces.K θ * Work.Spaces.pz f z θ‖ ∂(volume.restrict Work.Spaces.Iθ))
        (volume.restrict (Set.Ioi 0)) := by
      simpa only [Function.uncurry] using
        (hAESM.norm).integral_prod_right' (μ := volume.restrict (Set.Ioi 0))
          (ν := volume.restrict Work.Spaces.Iθ)
    refine Integrable.mono' hAB hAESM_int ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z hz
    have hzpos : 0 < z := hz
    have habs := (Work.FTS.PhiStar.Honesty.slice_abs_integrable hsm hmem hzpos).2
    rw [Real.norm_eq_abs,
      abs_of_nonneg (MeasureTheory.integral_nonneg fun θ => norm_nonneg _)]
    calc ∫ θ, ‖Work.Spaces.K θ * Work.Spaces.pz f z θ‖ ∂(volume.restrict Work.Spaces.Iθ)
        ≤ ∫ θ, 3 * |Work.Spaces.pz f z θ| ∂(volume.restrict Work.Spaces.Iθ) := by
          refine MeasureTheory.integral_mono_of_nonneg
            (Filter.Eventually.of_forall fun θ => norm_nonneg _) (habs.const_mul 3) ?_
          filter_upwards [MeasureTheory.ae_restrict_of_forall_mem
            (show MeasurableSet Work.Spaces.Iθ from measurableSet_Icc)
            (fun θ hθ => hK3 θ hθ)] with θ hθ
          rw [Real.norm_eq_abs, abs_mul]
          exact mul_le_mul_of_nonneg_right hθ (abs_nonneg _)
      _ = 3 * ∫ θ, |Work.Spaces.pz f z θ| ∂(volume.restrict Work.Spaces.Iθ) :=
          MeasureTheory.integral_const_mul 3 _
      _ ≤ 3 * (Real.sqrt (π / 2) * (z / (1 + z) ^ 2)
            * Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 1 f z θ)) :=
          mul_le_mul_of_nonneg_left
            (Work.FTS.PhiStar.Honesty.pz_abs_slice_le_sqrt_Hk hsm hmem hzpos) (by norm_num)
      _ = (3 * Real.sqrt (π / 2) * (z / (1 + z) ^ 2))
            * Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 1 f z θ) := by ring
  exact (MeasureTheory.integrable_prod_iff hAESM).mpr ⟨hslice, houter⟩

end Work.FTS.StrongEps.EpsZero
