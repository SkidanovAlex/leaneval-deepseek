/-
Copyright: work module for the Elgindi finite-time singularity project.

# Slice facts for `|∂_z²u · sinθcos²θ|` from `HkMem α 0 (z² ∂_z²u)`

`Work.FTS.EllipticEst.AngAWeak.absPzIter2SliceFacts`:

for `u` of class `C^∞` on the open quadrant and `z² ∂_z²u ∈ ℋ⁰` in the weighted sense
`Work.Spaces.HkMem α 0`, and every `0 < a < b`:

* the uncurried integrand `(x,θ) ↦ |∂_z²u(x,θ)| · |sinθcos²θ|` is integrable on the box
  `[a,b] ×ˢ Iθ`;
* its angular integral `x ↦ ∫_θ |∂_z²u(x,θ)| · |sinθcos²θ|` is integrable on `[a,b]`.

## Route

The single pointwise input is the AM–GM absorption
`Work.FTS.EllipticEst.abs_mul_sinCos2_le_weighted` (`|f·sinθcos²θ| ≤ (f·w/sin(2θ)^{η/2})² + 1`)
combined with `Work.Spaces.sq_le_HkIntegrand_z` at `i = 0` for the datum `z² ∂_z²u`, which
converts the weighted square into the level-`0` summand of `HkIntegrand`; on the compact
interval `[a,b]` the factor `z⁴ ≥ a⁴` produces the uniform domination

  `|∂_z²u z θ| · |sinθcos²θ| ≤ a⁻⁴ · HkIntegrand α 0 (z² ∂_z²u) z θ + 1`.

The angular slices are then integrable by `hmZ.1` (`Integrable.mono'`), and the iterated
angular integral is integrable by `hmZ.2` after Fubini (`aesm_uncurry_restrict_open` +
`AEStronglyMeasurable.integral_prod_right'`).  The box integrability is the ready-made
`Work.FTS.EllipticEst.integrableOn_box_of_slice_of_nonneg`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.EllipticEst.Endpt.boxIntegrable_pzIter2Psi
import Submission.Work.Spaces.Defs
import Submission.Work.Elliptic.Defs
import Submission.Work.FTS.EllipticEst.abs_mul_sinCos2_le_weighted
import Submission.Work.FTS.EllipticEst.aesm_uncurry_restrict_open

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set Filter
open scoped Real Topology

namespace Work.FTS.EllipticEst.AngAWeak

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-- The angular profile `sinθcos²θ` is continuous. -/
private lemma continuous_sinCos2_ang : Continuous Work.Elliptic.sinCos2 := by
  show Continuous (fun θ : ℝ => Real.sin θ * Real.cos θ ^ 2)
  exact Real.continuous_sin.mul (Real.continuous_cos.pow 2)

/-- `sinθcos²θ ≥ 0` on the angular domain. -/
private lemma sinCos2_nonneg_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ Work.Elliptic.sinCos2 θ := by
  obtain ⟨h0, h1⟩ := hθ
  have hs : 0 ≤ Real.sin θ := Real.sin_nonneg_of_nonneg_of_le_pi h0 (by linarith [Real.pi_pos])
  have hc : 0 ≤ Real.cos θ := Real.cos_nonneg_of_neg_pi_div_two_le_of_le (by linarith) h1
  rw [Work.Elliptic.sinCos2]
  positivity

/-- The angular interval has finite Lebesgue measure (in the `≠ ⊤` form). -/
private lemma volume_Iθ_ne_top : (volume : Measure ℝ) Work.Spaces.Iθ ≠ ⊤ := by
  rw [Work.Spaces.Iθ, Real.volume_Icc]
  exact ENNReal.ofReal_ne_top

/-- A compact interval has finite Lebesgue measure (in the `≠ ⊤` form). -/
private lemma volume_Icc_ne_top (a b : ℝ) : (volume : Measure ℝ) (Set.Icc a b) ≠ ⊤ := by
  rw [Real.volume_Icc]
  exact ENNReal.ofReal_ne_top

/-- **Pointwise domination on the box.**

For `0 < a ≤ z` and `θ ∈ Iθ`,

  `|∂_z²u z θ| · |sinθcos²θ| ≤ a⁻⁴ · HkIntegrand α 0 (z² ∂_z²u) z θ + 1`.

This is `abs_mul_sinCos2_le_weighted` (absorbing the angular profile into the weighted square
`(∂_z²u · w/sin(2θ)^{η/2})²` plus `1`), followed by `sq_le_HkIntegrand_z` at `i = 0` for the
datum `z² ∂_z²u` (whose `i = 0` summand is `z⁴` times that square) and the trivial `z⁴ ≥ a⁴`. -/
private lemma pointwise_bound {α : ℝ} {u : ℝ → ℝ → ℝ} {a z θ : ℝ}
    (ha : 0 < a) (hz : a ≤ z) (hθ : θ ∈ Work.Spaces.Iθ) :
    |Work.Spaces.pzIter 2 u z θ| * |Work.Elliptic.sinCos2 θ|
      ≤ (a ^ 4)⁻¹ * Work.Spaces.HkIntegrand α 0
            (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 u z θ) z θ + 1 := by
  have hzpos : 0 < z := lt_of_lt_of_le ha hz
  have h1 : |Work.Spaces.pzIter 2 u z θ| * |Work.Elliptic.sinCos2 θ|
      ≤ (Work.Spaces.pzIter 2 u z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 + 1 := by
    have hh := Work.FTS.EllipticEst.abs_mul_sinCos2_le_weighted
      (f := fun θ => Work.Spaces.pzIter 2 u z θ) hzpos hθ
    rwa [abs_mul] at hh
  have hz4 : z ^ 4 ≠ 0 := pow_ne_zero 4 (ne_of_gt hzpos)
  have h2 : (Work.Spaces.pzIter 2 u z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
      = (z ^ 4)⁻¹ * ((z ^ 2 * Work.Spaces.pzIter 2 u z θ)
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
    rw [eq_inv_mul_iff_mul_eq₀ hz4]
    ring
  have h3 : ((z ^ 2 * Work.Spaces.pzIter 2 u z θ)
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
      ≤ Work.Spaces.HkIntegrand α 0
          (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 u z θ) z θ := by
    have hh := Work.Spaces.sq_le_HkIntegrand_z α 0
      (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 u z θ) z θ 0 (Nat.zero_le 0)
    simpa using hh
  have hcinv : (0 : ℝ) ≤ (a ^ 4)⁻¹ := by positivity
  have hzipow : (z ^ 4)⁻¹ ≤ (a ^ 4)⁻¹ := by
    rw [inv_le_inv₀ (by positivity : (0 : ℝ) < z ^ 4) (by positivity : (0 : ℝ) < a ^ 4)]
    exact pow_le_pow_left₀ ha.le hz 4
  have hX : (0 : ℝ) ≤ ((z ^ 2 * Work.Spaces.pzIter 2 u z θ)
      * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := sq_nonneg _
  calc |Work.Spaces.pzIter 2 u z θ| * |Work.Elliptic.sinCos2 θ|
      ≤ (Work.Spaces.pzIter 2 u z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 + 1 := h1
    _ = (z ^ 4)⁻¹ * ((z ^ 2 * Work.Spaces.pzIter 2 u z θ)
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 + 1 := by
        rw [h2]
    _ ≤ (a ^ 4)⁻¹ * ((z ^ 2 * Work.Spaces.pzIter 2 u z θ)
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 + 1 := by
        have hstep := mul_le_mul_of_nonneg_right hzipow hX
        linarith
    _ ≤ (a ^ 4)⁻¹ * Work.Spaces.HkIntegrand α 0
          (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 u z θ) z θ + 1 := by
        have hstep := mul_le_mul_of_nonneg_left h3 hcinv
        linarith

/-- **The two slice facts on a fixed compact interval.** -/
private theorem slice_facts_aux {α : ℝ} {u : ℝ → ℝ → ℝ}
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry u)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (hmZ : Work.Spaces.HkMem α 0 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 u z θ))
    {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    MeasureTheory.IntegrableOn
        (Function.uncurry (fun x θ : ℝ =>
          |Work.Spaces.pzIter 2 u x θ| * |Work.Elliptic.sinCos2 θ|))
        (Set.Icc a b ×ˢ Work.Spaces.Iθ)
      ∧ MeasureTheory.IntegrableOn
        (fun x : ℝ => ∫ θ in Work.Spaces.Iθ,
          |Work.Spaces.pzIter 2 u x θ| * |Work.Elliptic.sinCos2 θ|)
        (Set.Icc a b) := by
  have hu : Work.FTS.EllipticEst.SmoothOpen u := Work.FTS.EllipticEst.smoothOpen_of_forall hsm
  have hsub : Set.Icc a b ⊆ Work.Spaces.Iz := fun x hx => by
    rw [Work.Spaces.Iz]; exact le_trans (le_of_lt ha) hx.1
  have hcont : ContinuousOn (fun p : ℝ × ℝ =>
      |Work.Spaces.pzIter 2 u p.1 p.2| * |Work.Elliptic.sinCos2 p.2|)
      Work.FTS.EllipticEst.Q0 :=
    (((hu.pzIter 2).continuousOn).abs).mul
      (((continuous_sinCos2_ang.comp continuous_snd).continuousOn).abs)
  haveI : IsFiniteMeasure (volume.restrict Work.Spaces.Iθ) := by
    rw [Work.Spaces.Iθ]; infer_instance
  haveI : IsFiniteMeasure (volume.restrict (Set.Icc a b)) :=
    ⟨by rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, Real.volume_Icc]
        exact ENNReal.ofReal_lt_top⟩
  -- ## Angular slices: dominated by the level-`0` integrand of `z² ∂_z²u`
  have hsl : ∀ s ∈ Set.Icc a b, Integrable (fun θ : ℝ =>
      |Work.Spaces.pzIter 2 u s θ| * |Work.Elliptic.sinCos2 θ|)
      (volume.restrict Work.Spaces.Iθ) := by
    intro s hs
    have hspos : 0 < s := lt_of_lt_of_le ha hs.1
    have hsz : s ∈ Work.Spaces.Iz := hsub hs
    have hdom : Integrable (fun θ : ℝ => (a ^ 4)⁻¹ * Work.Spaces.HkIntegrand α 0
        (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 u z θ) s θ + 1)
        (volume.restrict Work.Spaces.Iθ) :=
      ((hmZ.1 s hsz).const_mul ((a ^ 4)⁻¹)).add (integrable_const 1)
    refine hdom.mono' ?_ ?_
    · exact Work.Spaces.aesm_slice_of_continuousOn_Qd
        (fun p : ℝ × ℝ => |Work.Spaces.pzIter 2 u p.1 p.2| * |Work.Elliptic.sinCos2 p.2|)
        hcont hspos
    · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => ?_)
      rw [Real.norm_of_nonneg (mul_nonneg (abs_nonneg _) (abs_nonneg _))]
      exact pointwise_bound ha hs.1 hθ
  -- ## The iterated angular integral
  have hint : MeasureTheory.IntegrableOn (fun s : ℝ => ∫ θ in Work.Spaces.Iθ,
      |Work.Spaces.pzIter 2 u s θ| * |Work.Elliptic.sinCos2 θ|) (Set.Icc a b) := by
    have hJint : MeasureTheory.IntegrableOn (fun s : ℝ => ∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α 0 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 u z θ) s θ)
        (Set.Icc a b) := hmZ.2.mono_set hsub
    have hDint : MeasureTheory.IntegrableOn (fun s : ℝ =>
        (a ^ 4)⁻¹ * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0
          (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 u z θ) s θ)
        + (∫ θ in Work.Spaces.Iθ, (1 : ℝ))) (Set.Icc a b) :=
      ((hJint.const_mul ((a ^ 4)⁻¹)).add
        (MeasureTheory.integrableOn_const (C := (∫ θ in Work.Spaces.Iθ, (1 : ℝ)))
          (volume_Icc_ne_top a b)))
    refine hDint.mono' ?_ ?_
    · have hprod : MeasureTheory.AEStronglyMeasurable
          (fun p : ℝ × ℝ => |Work.Spaces.pzIter 2 u p.1 p.2| * |Work.Elliptic.sinCos2 p.2|)
          ((volume.restrict (Set.Ioc a b)).prod (volume.restrict Work.Spaces.Iθ)) :=
        Work.FTS.EllipticEst.aesm_uncurry_restrict_open _ hcont ha.le
      have h4 : MeasureTheory.AEStronglyMeasurable (fun s : ℝ => ∫ θ : ℝ,
          |Work.Spaces.pzIter 2 u s θ| * |Work.Elliptic.sinCos2 θ|
            ∂(volume.restrict Work.Spaces.Iθ)) (volume.restrict (Set.Ioc a b)) :=
        hprod.integral_prod_right'
      rw [← MeasureTheory.Measure.restrict_congr_set
        (MeasureTheory.Ioc_ae_eq_Icc (a := a) (b := b))]
      exact h4
    · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun z hz => ?_)
      have hzpos : 0 < z := lt_of_lt_of_le ha hz.1
      have hsz : z ∈ Work.Spaces.Iz := hsub hz
      have hFnn : 0 ≤ ∫ θ in Work.Spaces.Iθ,
          |Work.Spaces.pzIter 2 u z θ| * |Work.Elliptic.sinCos2 θ| := by
        refine MeasureTheory.integral_nonneg_of_ae ?_
        filter_upwards [MeasureTheory.ae_restrict_mem
          (show MeasurableSet Work.Spaces.Iθ from measurableSet_Icc)] with θ hθ
        exact mul_nonneg (abs_nonneg _) (abs_nonneg _)
      rw [Real.norm_of_nonneg hFnn]
      have hdInt : Integrable (fun θ : ℝ => (a ^ 4)⁻¹ * Work.Spaces.HkIntegrand α 0
          (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 u z θ) z θ + 1)
          (volume.restrict Work.Spaces.Iθ) :=
        ((hmZ.1 z hsz).const_mul ((a ^ 4)⁻¹)).add (integrable_const 1)
      have hf1 : Integrable (fun θ : ℝ => (a ^ 4)⁻¹ * Work.Spaces.HkIntegrand α 0
          (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 u z θ) z θ)
          (volume.restrict Work.Spaces.Iθ) :=
        (hmZ.1 z hsz).const_mul ((a ^ 4)⁻¹)
      have hf2 : Integrable (fun _ : ℝ => (1 : ℝ)) (volume.restrict Work.Spaces.Iθ) :=
        integrable_const 1
      have hmono : (∫ θ in Work.Spaces.Iθ,
            |Work.Spaces.pzIter 2 u z θ| * |Work.Elliptic.sinCos2 θ|)
          ≤ ∫ θ in Work.Spaces.Iθ, ((a ^ 4)⁻¹ * Work.Spaces.HkIntegrand α 0
              (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 u z θ) z θ + 1) :=
        MeasureTheory.integral_mono_of_nonneg
          (Eventually.of_forall (fun θ => mul_nonneg (abs_nonneg _) (abs_nonneg _)))
          hdInt
          (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc
            (fun θ hθ => pointwise_bound ha hz.1 hθ))
      calc (∫ θ in Work.Spaces.Iθ,
            |Work.Spaces.pzIter 2 u z θ| * |Work.Elliptic.sinCos2 θ|)
          ≤ ∫ θ in Work.Spaces.Iθ, ((a ^ 4)⁻¹ * Work.Spaces.HkIntegrand α 0
              (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 u z θ) z θ + 1) := hmono
        _ = (a ^ 4)⁻¹ * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0
              (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 u z θ) z θ)
            + (∫ θ in Work.Spaces.Iθ, (1 : ℝ)) := by
            rw [MeasureTheory.integral_add hf1 hf2, MeasureTheory.integral_const_mul]
  refine ⟨?_, hint⟩
  exact Work.FTS.EllipticEst.integrableOn_box_of_slice_of_nonneg ha hab hcont
    (fun z _ θ _ => mul_nonneg (abs_nonneg _) (abs_nonneg _)) hsl hint

theorem absPzIter2SliceFacts {α : ℝ} {u : ℝ → ℝ → ℝ}
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry u)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (hmZ : Work.Spaces.HkMem α 0 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 u z θ)) :
    (∀ a b : ℝ, 0 < a → a < b → MeasureTheory.IntegrableOn
        (Function.uncurry (fun x θ : ℝ =>
          |Work.Spaces.pzIter 2 u x θ| * |Work.Elliptic.sinCos2 θ|))
        (Set.Icc a b ×ˢ Work.Spaces.Iθ))
    ∧ (∀ a b : ℝ, 0 < a → a < b → MeasureTheory.IntegrableOn
        (fun x : ℝ => ∫ θ in Work.Spaces.Iθ,
          |Work.Spaces.pzIter 2 u x θ| * |Work.Elliptic.sinCos2 θ|)
        (Set.Icc a b)) := by
  constructor
  · intro a b ha hab
    exact (slice_facts_aux hsm hmZ ha hab).1
  · intro a b ha hab
    exact (slice_facts_aux hsm hmZ ha hab).2

end Work.FTS.EllipticEst.AngAWeak
