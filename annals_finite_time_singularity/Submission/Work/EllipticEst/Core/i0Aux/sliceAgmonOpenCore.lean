/-
Work module for the Elgindi finite-time-singularity project.

# The open-class angular Agmon inequality

`sliceAgmonOpenCore` is the one-dimensional weighted Agmon estimate

  `c ∫_{Iθ} (f')² σ  ≤  - ∫_{Iθ} f f'' σ + C ∫_{Iθ} f² σ`,   `σ = thEta = sin(2θ)^{-η}`,

for `f` of class `C²` on the **open** interval `(0, π/2)` whose two traces vanish and whose three
weighted energies are finite.

The proof uses the primitive `Φ` of `Defs.lean` (`PhiIdentity`), the endpoint rate
`EndpointRate`, the sharp weighted Hardy inequality `SharpHardyOpen`, and the two "small value"
lemmas `PhiGeNearZero`/`PhiLeNearPi` that produce the two sequences of interior points along which
`Φ` is small.  Passing to the limit in `PhiIdentity` (via the general sub-interval limit lemma
`SliceAgmonOpen.tendsto_subinterval`) and inserting the sharp Hardy bound gives the claim.

The final bookkeeping is the pure arithmetic lemma `SliceAgmonOpen.agFinal`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.EllipticEst.hardy_shift_two_same_weight
import Submission.Work.EllipticEst.Core.sliceBoundaryLimit
import Submission.Work.EllipticEst.Core.i0Aux.SliceAgmonOpen.Defs
import Submission.Work.EllipticEst.Core.i0Aux.SliceAgmonOpen.EndpointRate
import Submission.Work.EllipticEst.Core.i0Aux.SliceAgmonOpen.PhiIdentity
import Submission.Work.EllipticEst.Core.i0Aux.SliceAgmonAux.SharpHardyOpenAux
import Submission.Work.EllipticEst.Core.i0Aux.SliceAgmonOpen.PhiGeNearZero
import Submission.Work.EllipticEst.Core.i0Aux.SliceAgmonOpen.PhiLeNearPi
import Submission.Work.EllipticEst.Core.i0Aux.SliceAgmonOpen.tendsto_subinterval
import Submission.Work.EllipticEst.Core.i0Aux.SliceAgmonOpen.agFinal

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.EllipticEst.Core.i0Aux

/-- The integrand of the integration-by-parts identity `PhiIdentity`. -/
private def agIntegrand (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  (deriv f x) ^ 2 * Work.FTS.EllipticEst.thEta x
    + f x * deriv (deriv f) x * Work.FTS.EllipticEst.thEta x
    - 2 * Work.Spaces.eta * (f x) ^ 2 * Work.FTS.EllipticEst.thEta x
    - 2 * Work.Spaces.eta * (1 + Work.Spaces.eta) * (f x) ^ 2
        * (Real.cos (2 * x)) ^ 2 * (Real.sin (2 * x)) ^ (-(2 + Work.Spaces.eta))

/-- Splitting the integral of a linear combination into the combination of the integrals. -/
private theorem integral_decomp {F G H K : ℝ → ℝ} {c d : ℝ} {s : Set ℝ}
    (hF : MeasureTheory.IntegrableOn F s) (hG : MeasureTheory.IntegrableOn G s)
    (hH : MeasureTheory.IntegrableOn (fun x => c * H x) s)
    (hK : MeasureTheory.IntegrableOn (fun x => d * K x) s) :
    (∫ x in s, (F x + G x - c * H x - d * K x))
      = (∫ x in s, F x) + (∫ x in s, G x) - c * (∫ x in s, H x)
        - d * (∫ x in s, K x) := by
  have h1 : MeasureTheory.IntegrableOn (fun x => F x + G x) s := hF.add hG
  have h2 : MeasureTheory.IntegrableOn (fun x => F x + G x - c * H x) s := h1.sub hH
  have e1 : (∫ x in s, (F x + G x - c * H x - d * K x))
      = (∫ x in s, (F x + G x - c * H x)) - (∫ x in s, d * K x) :=
    MeasureTheory.integral_sub h2 hK
  have e2 : (∫ x in s, (F x + G x - c * H x))
      = (∫ x in s, (F x + G x)) - (∫ x in s, c * H x) :=
    MeasureTheory.integral_sub h1 hH
  have e3 : (∫ x in s, (F x + G x)) = (∫ x in s, F x) + (∫ x in s, G x) :=
    MeasureTheory.integral_add hF hG
  have e4 : (∫ x in s, c * H x) = c * (∫ x in s, H x) :=
    MeasureTheory.integral_const_mul c H
  have e5 : (∫ x in s, d * K x) = d * (∫ x in s, K x) :=
    MeasureTheory.integral_const_mul d K
  rw [e1, e2, e3, e4, e5]

/-- The angular Agmon inequality of the open slice class. -/
theorem sliceAgmonOpenCore : ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ f : ℝ → ℝ,
    ContDiffOn ℝ 2 f (Set.Ioo 0 (Real.pi / 2)) →
    Filter.Tendsto f (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) →
    Filter.Tendsto f (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) →
    MeasureTheory.IntegrableOn (fun θ : ℝ => (deriv f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ →
    MeasureTheory.IntegrableOn (fun θ : ℝ => (f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ →
    MeasureTheory.IntegrableOn (fun θ : ℝ => f θ * deriv (deriv f) θ * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ →
    c * (∫ θ in Work.Spaces.Iθ, (deriv f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
      ≤ - (∫ θ in Work.Spaces.Iθ, f θ * deriv (deriv f) θ * Work.FTS.EllipticEst.thEta θ)
        + C * (∫ θ in Work.Spaces.Iθ, (f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ) := by
  have hcc : (0 : ℝ) < 1 / 200 := by norm_num
  have hCC : (0 : ℝ) < 2 * Work.Spaces.eta := by linarith [Work.Spaces.eta_pos]
  refine ⟨1 / 200, 2 * Work.Spaces.eta, hcc, hCC, ?_⟩
  intro f hf h0 h1 hA hN hP
  -- ## the open interval
  have hmemT : Set.Ioo (0 : ℝ) (Real.pi / 2) ⊆ Work.Spaces.Iθ :=
    fun x hx => ⟨le_of_lt hx.1, le_of_lt hx.2⟩
  have hAoo : MeasureTheory.IntegrableOn
      (fun x : ℝ => (deriv f x) ^ 2 * Work.FTS.EllipticEst.thEta x)
      (Set.Ioo 0 (Real.pi / 2)) := hA.mono_set hmemT
  have hNoo : MeasureTheory.IntegrableOn
      (fun x : ℝ => (f x) ^ 2 * Work.FTS.EllipticEst.thEta x)
      (Set.Ioo 0 (Real.pi / 2)) := hN.mono_set hmemT
  have hPoo : MeasureTheory.IntegrableOn
      (fun x : ℝ => f x * deriv (deriv f) x * Work.FTS.EllipticEst.thEta x)
      (Set.Ioo 0 (Real.pi / 2)) := hP.mono_set hmemT
  -- ## the two imported inputs
  obtain ⟨hrate0, hrate1⟩ := EndpointRate hf h0 h1 hA
  obtain ⟨hHqintIθ, hHardyIθ⟩ := SliceAgmonAux.sharpHardyOpenAux hf hrate0 hrate1 hA
  have hHqint : MeasureTheory.IntegrableOn
      (fun x : ℝ => (f x) ^ 2 * (Real.sin (2 * x)) ^ (-(2 + Work.Spaces.eta)))
      (Set.Ioo 0 (Real.pi / 2)) := hHqintIθ.mono_set hmemT
  have hcos : ContinuousOn (fun x : ℝ => (Real.cos (2 * x)) ^ 2)
      (Set.Icc 0 (Real.pi / 2)) :=
    (((Real.continuous_cos.comp (continuous_const.mul continuous_id)).continuousOn).pow 2)
  have hJIoo_int : MeasureTheory.IntegrableOn
      (fun x : ℝ => (f x) ^ 2 * (Real.cos (2 * x)) ^ 2
        * (Real.sin (2 * x)) ^ (-(2 + Work.Spaces.eta)))
      (Set.Ioo 0 (Real.pi / 2)) := by
    have h0' : MeasureTheory.IntegrableOn
        (fun x : ℝ => ((f x) ^ 2 * (Real.sin (2 * x)) ^ (-(2 + Work.Spaces.eta)))
          * (Real.cos (2 * x)) ^ 2)
        (Set.Ioo 0 (Real.pi / 2)) :=
      hHqint.mul_continuousOn_of_subset hcos measurableSet_Ioo isCompact_Icc
        (fun x hx => ⟨le_of_lt hx.1, le_of_lt hx.2⟩)
    exact h0'.congr_fun (fun x hx => by ring) measurableSet_Ioo
  have hG3int : MeasureTheory.IntegrableOn
      (fun x : ℝ => (2 * Work.Spaces.eta) * ((f x) ^ 2 * Work.FTS.EllipticEst.thEta x))
      (Set.Ioo 0 (Real.pi / 2)) := hNoo.const_mul (2 * Work.Spaces.eta)
  have hG4int : MeasureTheory.IntegrableOn
      (fun x : ℝ => (2 * Work.Spaces.eta * (1 + Work.Spaces.eta))
        * ((f x) ^ 2 * (Real.cos (2 * x)) ^ 2
          * (Real.sin (2 * x)) ^ (-(2 + Work.Spaces.eta))))
      (Set.Ioo 0 (Real.pi / 2)) :=
    hJIoo_int.const_mul (2 * Work.Spaces.eta * (1 + Work.Spaces.eta))
  have hGint : MeasureTheory.IntegrableOn (agIntegrand f) (Set.Ioo 0 (Real.pi / 2)) := by
    have hsrc : MeasureTheory.IntegrableOn
        (fun x : ℝ => ((deriv f x) ^ 2 * Work.FTS.EllipticEst.thEta x
            + f x * deriv (deriv f) x * Work.FTS.EllipticEst.thEta x
            - (2 * Work.Spaces.eta) * ((f x) ^ 2 * Work.FTS.EllipticEst.thEta x)
            - (2 * Work.Spaces.eta * (1 + Work.Spaces.eta))
                * ((f x) ^ 2 * (Real.cos (2 * x)) ^ 2
                  * (Real.sin (2 * x)) ^ (-(2 + Work.Spaces.eta)))))
        (Set.Ioo 0 (Real.pi / 2)) :=
      ((hAoo.add hPoo).sub hG3int).sub hG4int
    exact hsrc.congr_fun (fun x hx => by simp only [agIntegrand]; ring) measurableSet_Ioo
  -- ## identifying the `Ioo`-integrals with the `Iθ`-integrals
  have hAoo_eq : (∫ x in Set.Ioo 0 (Real.pi / 2),
        (deriv f x) ^ 2 * Work.FTS.EllipticEst.thEta x)
      = (∫ x in Work.Spaces.Iθ, (deriv f x) ^ 2 * Work.FTS.EllipticEst.thEta x) :=
    MeasureTheory.setIntegral_congr_set MeasureTheory.Ioo_ae_eq_Icc
  have hNoo_eq : (∫ x in Set.Ioo 0 (Real.pi / 2),
        (f x) ^ 2 * Work.FTS.EllipticEst.thEta x)
      = (∫ x in Work.Spaces.Iθ, (f x) ^ 2 * Work.FTS.EllipticEst.thEta x) :=
    MeasureTheory.setIntegral_congr_set MeasureTheory.Ioo_ae_eq_Icc
  have hPoo_eq : (∫ x in Set.Ioo 0 (Real.pi / 2),
        f x * deriv (deriv f) x * Work.FTS.EllipticEst.thEta x)
      = (∫ x in Work.Spaces.Iθ, f x * deriv (deriv f) x * Work.FTS.EllipticEst.thEta x) :=
    MeasureTheory.setIntegral_congr_set MeasureTheory.Ioo_ae_eq_Icc
  have hHqoo_eq : (∫ x in Set.Ioo 0 (Real.pi / 2),
        (f x) ^ 2 * (Real.sin (2 * x)) ^ (-(2 + Work.Spaces.eta)))
      = (∫ x in Work.Spaces.Iθ,
          (f x) ^ 2 * (Real.sin (2 * x)) ^ (-(2 + Work.Spaces.eta))) :=
    MeasureTheory.setIntegral_congr_set MeasureTheory.Ioo_ae_eq_Icc
  have hAnn : 0 ≤ (∫ x in Set.Ioo 0 (Real.pi / 2),
      (deriv f x) ^ 2 * Work.FTS.EllipticEst.thEta x) :=
    MeasureTheory.setIntegral_nonneg measurableSet_Ioo
      (fun x hx => mul_nonneg (sq_nonneg _)
        (Work.FTS.EllipticEst.thEta_nonneg ⟨le_of_lt hx.1, le_of_lt hx.2⟩))
  -- ## the two sequences of interior points where `Phi` is small
  choose a ha using fun n : ℕ =>
    SliceAgmonOpen.PhiGeNearZero hf hrate0 (1 / ((n : ℝ) + 1)) (1 / ((n : ℝ) + 1))
      (by positivity) (by positivity)
  choose b hb using fun n : ℕ =>
    SliceAgmonOpen.PhiLeNearPi hf hrate1 (Real.pi / 2 - 1 / ((n : ℝ) + 1))
      (1 / ((n : ℝ) + 1))
      (by
        have h : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
        linarith) (by positivity)
  have ha_pos : ∀ n : ℕ, 0 < a n := fun n => (ha n).1.1
  have ha_lt : ∀ n : ℕ, a n < 1 / ((n : ℝ) + 1) := fun n => (ha n).1.2
  have ha_bd : ∀ n : ℕ, -(1 / ((n : ℝ) + 1)) ≤ Phi f (a n) := fun n => (ha n).2
  have hb_gt : ∀ n : ℕ, Real.pi / 2 - 1 / ((n : ℝ) + 1) < b n := fun n => (hb n).1.1
  have hb_lt : ∀ n : ℕ, b n < Real.pi / 2 := fun n => (hb n).1.2
  have hb_bd : ∀ n : ℕ, Phi f (b n) ≤ 1 / ((n : ℝ) + 1) := fun n => (hb n).2
  have hratio : Filter.Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) Filter.atTop (nhds 0) := by
    have hnat : Filter.Tendsto (fun n : ℕ => ((n : ℝ) + 1)) Filter.atTop Filter.atTop :=
      tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_natCast_atTop_atTop
    have h2 : Filter.Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) Filter.atTop (nhds 0) :=
      tendsto_inv_atTop_zero.comp hnat
    simpa [one_div] using h2
  have ha_tend : Filter.Tendsto a Filter.atTop (nhds 0) :=
    squeeze_zero' (Eventually.of_forall (fun n => le_of_lt (ha_pos n)))
      (Eventually.of_forall (fun n => le_of_lt (ha_lt n))) hratio
  have ha_within : Filter.Tendsto a Filter.atTop (nhdsWithin (0 : ℝ) (Set.Ioi 0)) := by
    rw [tendsto_nhdsWithin_iff]
    exact ⟨ha_tend, Eventually.of_forall (fun n => ha_pos n)⟩
  have hbsub : Filter.Tendsto (fun n : ℕ => Real.pi / 2 - b n) Filter.atTop (nhds 0) :=
    squeeze_zero' (Eventually.of_forall (fun n => by linarith [hb_lt n]))
      (Eventually.of_forall (fun n => by linarith [hb_gt n])) hratio
  have hb_tend : Filter.Tendsto b Filter.atTop (nhds (Real.pi / 2)) := by
    have h2 : Filter.Tendsto (fun n : ℕ => Real.pi / 2 - (Real.pi / 2 - b n))
        Filter.atTop (nhds (Real.pi / 2 - 0)) := tendsto_const_nhds.sub hbsub
    have h3 : (fun n : ℕ => Real.pi / 2 - (Real.pi / 2 - b n)) = b := by
      funext n; ring
    rw [h3] at h2
    simpa using h2
  have hb_within : Filter.Tendsto b Filter.atTop
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) := by
    rw [tendsto_nhdsWithin_iff]
    exact ⟨hb_tend, Eventually.of_forall (fun n => hb_lt n)⟩
  have hanb : ∀ n : ℕ, 1 ≤ n → a n < b n := by
    intro n hn
    have h1 := ha_lt n
    have h2 := hb_gt n
    have hle : 1 / ((n : ℝ) + 1) ≤ 1 / 2 := by
      apply one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2)
      have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      linarith
    have h4 : 2 * (1 / ((n : ℝ) + 1)) ≤ Real.pi / 2 := by
      nlinarith [hle, Real.pi_gt_three]
    linarith
  have hab : ∀ᶠ n : ℕ in Filter.atTop, a n < b n :=
    Filter.eventually_atTop.mpr ⟨1, fun n hn => hanb n hn⟩
  -- ## `PhiIdentity` along the sequences
  have hPhi_eq : ∀ᶠ n : ℕ in Filter.atTop,
      (∫ x in Set.Ioo (a n) (b n), agIntegrand f x) = Phi f (b n) - Phi f (a n) := by
    filter_upwards [hab] with n hn
    have hh : Phi f (b n) - Phi f (a n)
        = ∫ x in Set.Ioo (a n) (b n), agIntegrand f x := by
      rw [PhiIdentity hf (ha_pos n) (le_of_lt hn) (hb_lt n),
        intervalIntegral.integral_of_le (le_of_lt hn),
        MeasureTheory.integral_Ioc_eq_integral_Ioo]
      apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioo
      intro x hx
      simp only [agIntegrand]
    exact hh.symm
  have hGtend := SliceAgmonOpen.tendsto_subinterval hGint ha_within hb_within hab
  have hPhi_tend : Filter.Tendsto (fun n : ℕ => Phi f (b n) - Phi f (a n)) Filter.atTop
      (nhds (∫ x in Set.Ioo 0 (Real.pi / 2), agIntegrand f x)) :=
    Filter.Tendsto.congr' hPhi_eq hGtend
  have hPhi_bd : ∀ n : ℕ, Phi f (b n) - Phi f (a n) ≤ 2 * (1 / ((n : ℝ) + 1)) := by
    intro n; linarith [hb_bd n, ha_bd n]
  have hPhi_lim : Filter.Tendsto (fun n : ℕ => 2 * (1 / ((n : ℝ) + 1))) Filter.atTop
      (nhds 0) := by
    have h := hratio.const_mul (2 : ℝ)
    simpa using h
  have hLraw : (∫ x in Set.Ioo 0 (Real.pi / 2), agIntegrand f x) ≤ 0 :=
    le_of_tendsto_of_tendsto hPhi_tend hPhi_lim (Eventually.of_forall hPhi_bd)
  -- ## expanding the limit integral
  have hG_decomp : (∫ x in Set.Ioo 0 (Real.pi / 2), agIntegrand f x)
      = (∫ x in Set.Ioo 0 (Real.pi / 2), (deriv f x) ^ 2 * Work.FTS.EllipticEst.thEta x)
        + (∫ x in Set.Ioo 0 (Real.pi / 2),
            f x * deriv (deriv f) x * Work.FTS.EllipticEst.thEta x)
        - (2 * Work.Spaces.eta)
          * (∫ x in Set.Ioo 0 (Real.pi / 2),
              (f x) ^ 2 * Work.FTS.EllipticEst.thEta x)
        - (2 * Work.Spaces.eta * (1 + Work.Spaces.eta))
          * (∫ x in Set.Ioo 0 (Real.pi / 2), (f x) ^ 2 * (Real.cos (2 * x)) ^ 2
              * (Real.sin (2 * x)) ^ (-(2 + Work.Spaces.eta))) := by
    rw [show (∫ x in Set.Ioo 0 (Real.pi / 2), agIntegrand f x)
        = ∫ x in Set.Ioo 0 (Real.pi / 2),
            ((deriv f x) ^ 2 * Work.FTS.EllipticEst.thEta x
              + f x * deriv (deriv f) x * Work.FTS.EllipticEst.thEta x
              - (2 * Work.Spaces.eta) * ((f x) ^ 2 * Work.FTS.EllipticEst.thEta x)
              - (2 * Work.Spaces.eta * (1 + Work.Spaces.eta))
                  * ((f x) ^ 2 * (Real.cos (2 * x)) ^ 2
                    * (Real.sin (2 * x)) ^ (-(2 + Work.Spaces.eta)))) from by
      apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioo
      intro x hx
      simp only [agIntegrand]
      ring]
    exact integral_decomp hAoo hPoo hG3int hG4int
  -- ## the sharp Hardy bound on the `cos²`-weighted integral
  have hJle' : (1 + Work.Spaces.eta) ^ 2
        * (∫ x in Set.Ioo 0 (Real.pi / 2), (f x) ^ 2 * (Real.cos (2 * x)) ^ 2
            * (Real.sin (2 * x)) ^ (-(2 + Work.Spaces.eta)))
      ≤ (∫ x in Set.Ioo 0 (Real.pi / 2),
          (deriv f x) ^ 2 * Work.FTS.EllipticEst.thEta x) := by
    have h1 : (∫ x in Set.Ioo 0 (Real.pi / 2), (f x) ^ 2 * (Real.cos (2 * x)) ^ 2
          * (Real.sin (2 * x)) ^ (-(2 + Work.Spaces.eta)))
        ≤ (∫ x in Set.Ioo 0 (Real.pi / 2),
            (f x) ^ 2 * (Real.sin (2 * x)) ^ (-(2 + Work.Spaces.eta))) := by
      refine MeasureTheory.setIntegral_mono_on (hf := hJIoo_int) (hg := hHqint)
        measurableSet_Ioo ?_
      intro x hx
      have hs : 0 ≤ (Real.sin (2 * x)) ^ (-(2 + Work.Spaces.eta)) :=
        Real.rpow_nonneg (le_of_lt (sin_two_pos hx)) _
      calc (f x) ^ 2 * (Real.cos (2 * x)) ^ 2 * (Real.sin (2 * x)) ^ (-(2 + Work.Spaces.eta))
          = (f x) ^ 2 * ((Real.cos (2 * x)) ^ 2
              * (Real.sin (2 * x)) ^ (-(2 + Work.Spaces.eta))) := by ring
        _ ≤ (f x) ^ 2 * (1 * (Real.sin (2 * x)) ^ (-(2 + Work.Spaces.eta))) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right (Real.cos_sq_le_one (2 * x)) hs) (sq_nonneg _)
        _ = (f x) ^ 2 * (Real.sin (2 * x)) ^ (-(2 + Work.Spaces.eta)) := by ring
    have h2 : (1 + Work.Spaces.eta) ^ 2
          * (∫ x in Set.Ioo 0 (Real.pi / 2),
              (f x) ^ 2 * (Real.sin (2 * x)) ^ (-(2 + Work.Spaces.eta)))
        = (1 + Work.Spaces.eta) ^ 2
          * (∫ x in Work.Spaces.Iθ,
              (f x) ^ 2 * (Real.sin (2 * x)) ^ (-(2 + Work.Spaces.eta))) :=
      congrArg (fun y => (1 + Work.Spaces.eta) ^ 2 * y) hHqoo_eq
    have h3 : (1 + Work.Spaces.eta) ^ 2
          * (∫ x in Work.Spaces.Iθ,
              (f x) ^ 2 * (Real.sin (2 * x)) ^ (-(2 + Work.Spaces.eta)))
        ≤ (∫ x in Work.Spaces.Iθ, (deriv f x) ^ 2 * Work.FTS.EllipticEst.thEta x) :=
      hHardyIθ
    have h4 : (∫ x in Work.Spaces.Iθ, (deriv f x) ^ 2 * Work.FTS.EllipticEst.thEta x)
        = (∫ x in Set.Ioo 0 (Real.pi / 2),
            (deriv f x) ^ 2 * Work.FTS.EllipticEst.thEta x) := hAoo_eq.symm
    calc (1 + Work.Spaces.eta) ^ 2
          * (∫ x in Set.Ioo 0 (Real.pi / 2), (f x) ^ 2 * (Real.cos (2 * x)) ^ 2
              * (Real.sin (2 * x)) ^ (-(2 + Work.Spaces.eta)))
        ≤ (1 + Work.Spaces.eta) ^ 2
          * (∫ x in Set.Ioo 0 (Real.pi / 2),
              (f x) ^ 2 * (Real.sin (2 * x)) ^ (-(2 + Work.Spaces.eta))) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = (1 + Work.Spaces.eta) ^ 2
          * (∫ x in Work.Spaces.Iθ,
              (f x) ^ 2 * (Real.sin (2 * x)) ^ (-(2 + Work.Spaces.eta))) := h2
      _ ≤ (∫ x in Work.Spaces.Iθ, (deriv f x) ^ 2 * Work.FTS.EllipticEst.thEta x) := h3
      _ = (∫ x in Set.Ioo 0 (Real.pi / 2),
            (deriv f x) ^ 2 * Work.FTS.EllipticEst.thEta x) := h4
  -- ## the final arithmetic
  have hnum : (1 / 200)
        * (∫ x in Set.Ioo 0 (Real.pi / 2),
            (deriv f x) ^ 2 * Work.FTS.EllipticEst.thEta x)
      + (∫ x in Set.Ioo 0 (Real.pi / 2),
          f x * deriv (deriv f) x * Work.FTS.EllipticEst.thEta x)
      ≤ 2 * Work.Spaces.eta
        * (∫ x in Set.Ioo 0 (Real.pi / 2),
            (f x) ^ 2 * Work.FTS.EllipticEst.thEta x) :=
    SliceAgmonOpen.agFinal
      (A := ∫ x in Set.Ioo 0 (Real.pi / 2),
        (deriv f x) ^ 2 * Work.FTS.EllipticEst.thEta x)
      (P := ∫ x in Set.Ioo 0 (Real.pi / 2),
        f x * deriv (deriv f) x * Work.FTS.EllipticEst.thEta x)
      (N := ∫ x in Set.Ioo 0 (Real.pi / 2),
        (f x) ^ 2 * Work.FTS.EllipticEst.thEta x)
      (J := ∫ x in Set.Ioo 0 (Real.pi / 2), (f x) ^ 2 * (Real.cos (2 * x)) ^ 2
        * (Real.sin (2 * x)) ^ (-(2 + Work.Spaces.eta)))
      (eta := Work.Spaces.eta) Work.Spaces.eta_pos
      (by norm_num [Work.Spaces.eta]) hAnn
      (by linarith [hLraw, hG_decomp]) hJle'
  rw [hAoo_eq, hNoo_eq, hPoo_eq] at hnum
  linarith [hnum]

end Work.EllipticEst.Core.i0Aux
