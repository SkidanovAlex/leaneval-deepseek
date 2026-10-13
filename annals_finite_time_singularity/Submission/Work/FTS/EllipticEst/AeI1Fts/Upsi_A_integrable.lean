import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.AeI1Fts.Defs
import Submission.Work.FTS.EllipticEst.H2W.Ae.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.Spaces.aesm_of_continuousOn_Qd

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Upsi_A_integrable` — the `A`-slot domination lemma

The target of this file is

`Work.FTS.EllipticEst.AeI1Fts.Upsi_A_integrable`,

the `z`-integrability of `z ↦ w z ^ 2 · χ z · ∫_θ (U u z θ · ψ θ) ^ 2 · sin(2θ)^{-η}` from
`HkMem α 0 (grad u)` (`U u = grad u` definitionally) plus a bound on `ψ`.

## Where the difficulty is

The *value* part of the statement is elementary: on `Iθ` the level-`0` `H^k`-integrand of
`U u` is `w z ^ 2 · (U u z θ) ^ 2 · sin(2θ)^{-η}` (`HkIntegrand_zero_U` below), so

`w z ^ 2 · χ z · ∫_θ (U u · ψ) ^ 2 σ ≤ Cχ · Cψ · ∫_θ HkIntegrand α 0 (U u) z θ`

for every `z ∈ Iz`, and the right-hand side is `z`-integrable by `HkMem.2`.

The obstacle is the *measurability* half of `MeasureTheory.Integrable`: Mathlib defines
`Integrable f μ := AEStronglyMeasurable f μ ∧ HasFiniteIntegral f μ`, so the conclusion of
`Upsi_A_integrable` requires `AEStronglyMeasurable` of the slice-integral.  The hypotheses of
`Upsi_A_integrable` do not give it:

* `HkMem α 0 (grad u)` is a purely *slicewise* statement (for each `z` the `θ`-slice of
  `(U u) ^ 2 · w ^ 2 · σ` is integrable, and the `z`-marginal of that slice integral is
  integrable).  It gives no joint measurability of `(z,θ) ↦ (U u z θ) ^ 2 · w z ^ 2 · σ z θ`
  (nothing at all is assumed about the measurability of `u` itself), and
* `hψ` is only a pointwise bound on `Iθ`, so `ψ` need not be measurable.

`MeasureTheory.AEStronglyMeasurable.integral_prod_right'` — the tool every sibling domination
lemma of this development uses — requires the *joint* a.e. strong measurability of the integrand,
which the sibling `Upsi_P_integrable` obtains precisely from its extra hypothesis
`Work.FTS.EllipticEst.SmoothOpen u`; the `A`-version has no such hypothesis.

## What is proved here

`Upsi_A_integrable_of_smooth` is the same statement with the two measurability hypotheses that
make it true: joint measurability of the datum (`SmoothOpen u`) and measurability of `ψ`
(`Measurable ψ`).  With those, the proof is the value bound above plus the standard
`aesm_of_continuousOn_Qd` ∘ `integral_prod_right'` measurability chain.
-/

namespace Work.FTS.EllipticEst.AeI1Fts

open MeasureTheory Set Filter
open scoped Real Topology

set_option maxHeartbeats 800000

/-- The level-`0` `H^k`-integrand of `U u = z ∂_z u` is the weighted square
`w z ^ 2 · (U u z θ) ^ 2 · sin(2θ)^{-η}` on `Iθ`. -/
theorem HkIntegrand_zero_U (α z θ : ℝ) (u : ℝ → ℝ → ℝ) (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Spaces.HkIntegrand α 0 (U u) z θ
      = (Work.Spaces.w z) ^ 2 * (U u z θ) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
  simp only [Work.Spaces.HkIntegrand]
  norm_num [Finset.sum_range_one]
  rcases eq_or_lt_of_le (Work.FTS.EllipticEst.AngSecond.sin_two_nonneg hθ) with hs | hs
  · rw [← hs]
    have h1 : (0 : ℝ) ^ (Work.Spaces.eta / 2) = 0 :=
      Real.zero_rpow (by rw [Work.Spaces.eta]; norm_num)
    have h2 : (0 : ℝ) ^ (-(Work.Spaces.eta)) = 0 :=
      Real.zero_rpow (by rw [Work.Spaces.eta]; norm_num)
    rw [h1, h2, div_zero]
    ring
  · rw [div_eq_mul_inv, ← Real.rpow_neg (le_of_lt hs), mul_pow, mul_pow]
    have hsq : ((Real.sin (2 * θ)) ^ (-(Work.Spaces.eta / 2))) ^ 2
        = (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
      rw [sq, ← Real.rpow_add hs]
      congr 1
      rw [Work.Spaces.eta]; ring
    rw [hsq]
    ring

/-- **`Upsi_A_integrable` with the measurability hypotheses that its hypotheses are missing.**

Joint measurability of the datum (from `SmoothOpen u`) and measurability of `ψ` are assumed;
then the slice-integral is a.e. strongly measurable by `aesm_of_continuousOn_Qd` and
`MeasureTheory.AEStronglyMeasurable.integral_prod_right'`, and the result follows from the
pointwise domination by `Cχ · Cψ · ∫_θ HkIntegrand α 0 (U u) z θ`.

This is the form in which the `z`-integrability of `z ↦ w z ^ 2 χ z ∫_θ σ (U u · ψ) ^ 2` is
actually available (the intended application has both hypotheses: a `C^∞` datum and a smooth
cut-off `ψ`). -/
theorem Upsi_A_integrable_of_smooth (α : ℝ) (u : ℝ → ℝ → ℝ) (χ ψ : ℝ → ℝ)
    (hS : Work.FTS.EllipticEst.SmoothOpen u)
    (hU : Work.Spaces.HkMem α 0 (Work.FTS.EllipticEst.H2W.Ae.grad u))
    (hχm : Measurable χ) (hχnn : ∀ z ∈ Work.Spaces.Iz, 0 ≤ χ z)
    (hχ : ∃ C : ℝ, ∀ z ∈ Work.Spaces.Iz, χ z ≤ C)
    (hψm : Measurable ψ)
    (hψ : ∃ C : ℝ, ∀ θ ∈ Work.Spaces.Iθ, (ψ θ) ^ 2 ≤ C) :
    MeasureTheory.IntegrableOn
      (fun z => (Work.Spaces.w z) ^ 2 * χ z
        * ∫ θ in Work.Spaces.Iθ,
            (U u z θ * ψ θ) ^ 2
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
      Work.Spaces.Iz := by
  obtain ⟨Cχ, hCχ⟩ := hχ
  obtain ⟨Cψ, hCψ⟩ := hψ
  have hCχ0 : 0 ≤ Cχ := by
    have h1 := hCχ 0 Work.Spaces.zero_mem_Iz
    have h2 := hχnn 0 Work.Spaces.zero_mem_Iz
    linarith
  have hCψ0 : 0 ≤ Cψ := by
    have h1 := hCψ 0 Work.Spaces.zero_mem_Iθ
    linarith [sq_nonneg (ψ 0)]
  -- `HkMem` for `U u` (definitionally the same function as `grad u`)
  have hU' : Work.Spaces.HkMem α 0 (U u) := hU
  -- the dominating function
  have hmaj : MeasureTheory.IntegrableOn
      (fun z => Cχ * Cψ * ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 (U u) z θ)
      Work.Spaces.Iz :=
    (hU'.2).const_mul (Cχ * Cψ)
  -- a.e. strong measurability of the target
  have hmeas : MeasureTheory.AEStronglyMeasurable
      (fun z => (Work.Spaces.w z) ^ 2 * χ z
        * ∫ θ in Work.Spaces.Iθ,
            (U u z θ * ψ θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
    have hjoint : MeasureTheory.AEStronglyMeasurable
        (fun p : ℝ × ℝ =>
          (U u p.1 p.2 * ψ p.2) ^ 2 * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.eta)))
        ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
      have hUc : ContinuousOn (fun p : ℝ × ℝ => U u p.1 p.2)
          (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
        have h1 : ContinuousOn (fun p : ℝ × ℝ => p.1) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
          continuousOn_fst
        have h2 : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.pz u p.1 p.2)
            (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := (hS.pz).continuousOn
        exact h1.mul h2
      have ha : MeasureTheory.AEStronglyMeasurable (fun p : ℝ × ℝ => U u p.1 p.2)
          ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
            (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
        Work.Spaces.aesm_of_continuousOn_Qd _ hUc
      have hb : MeasureTheory.AEStronglyMeasurable (fun p : ℝ × ℝ => ψ p.2)
          ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
            (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
        (hψm.comp measurable_snd).aestronglyMeasurable
      have hc : MeasureTheory.AEStronglyMeasurable
          (fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ (-(Work.Spaces.eta)))
          ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
            (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
        have hsin : Measurable (fun θ : ℝ => Real.sin (2 * θ)) :=
          Real.measurable_sin.comp (measurable_const.mul measurable_id)
        exact ((hsin.comp measurable_snd).pow measurable_const).aestronglyMeasurable
      have hstep : MeasureTheory.AEStronglyMeasurable
          (fun p : ℝ × ℝ => (U u p.1 p.2 * ψ p.2) ^ 2) _ :=
        (ha.mul hb).pow 2
      exact hstep.mul hc
    have hmarg := hjoint.integral_prod_right'
      (ν := MeasureTheory.volume.restrict Work.Spaces.Iθ)
    have hw : Measurable (fun z : ℝ => (Work.Spaces.w z) ^ 2 * χ z) := by
      have hwm : Measurable (fun z : ℝ => Work.Spaces.w z) := by
        have heq : (fun z : ℝ => Work.Spaces.w z) = fun z : ℝ => (1 + z) ^ 2 / z ^ 2 := by
          funext z
          simp only [Work.Spaces.w]
        rw [heq]
        fun_prop
      exact ((hwm.pow (measurable_const : Measurable fun _ : ℝ => (2 : ℕ)))).mul hχm
    exact hw.aestronglyMeasurable.mul hmarg
  refine MeasureTheory.Integrable.mono' hmaj hmeas ?_
  filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ici] with z hz
  have hz0 : 0 ≤ z := hz
  have hBnn : 0 ≤ ∫ θ in Work.Spaces.Iθ,
      (U u z θ * ψ θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) :=
    MeasureTheory.setIntegral_nonneg measurableSet_Icc fun θ hθ =>
      mul_nonneg (sq_nonneg _)
        (Real.rpow_nonneg (Work.FTS.EllipticEst.AngSecond.sin_two_nonneg hθ) _)
  rw [Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg (mul_nonneg (sq_nonneg _) (hχnn z hz)) hBnn)]
  rcases eq_or_lt_of_le hz0 with h | h
  · -- `z = 0`: the left-hand side vanishes
    subst h
    rw [show (Work.Spaces.w 0) ^ 2 = 0 by rw [Work.Spaces.w]; norm_num]
    simp only [zero_mul]
    exact mul_nonneg (mul_nonneg hCχ0 hCψ0)
      (MeasureTheory.setIntegral_nonneg measurableSet_Icc fun θ _ =>
        Work.Spaces.HkIntegrand_nonneg α 0 (U u) 0 θ)
  · -- `z > 0`
    have hGnn : 0 ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 (U u) z θ :=
      MeasureTheory.setIntegral_nonneg measurableSet_Icc fun θ _ =>
        Work.Spaces.HkIntegrand_nonneg α 0 (U u) z θ
    have hXint : MeasureTheory.IntegrableOn
        (fun θ : ℝ => (U u z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
        Work.Spaces.Iθ := by
      have h1 : MeasureTheory.IntegrableOn
          (fun θ : ℝ => (1 / (Work.Spaces.w z) ^ 2)
            * Work.Spaces.HkIntegrand α 0 (U u) z θ) Work.Spaces.Iθ :=
        (hU'.1 z hz).const_mul _
      refine h1.congr_fun_ae ?_
      refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc fun θ hθ => ?_
      change (1 / (Work.Spaces.w z) ^ 2) * Work.Spaces.HkIntegrand α 0 (U u) z θ
          = (U u z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
      rw [HkIntegrand_zero_U α z θ u hθ]
      have hwne : (Work.Spaces.w z) ^ 2 ≠ 0 := by
        have : 0 < Work.Spaces.w z := by rw [Work.Spaces.w]; positivity
        positivity
      rw [one_div, mul_assoc, inv_mul_cancel_left₀ hwne]
    have hslice : (∫ θ in Work.Spaces.Iθ, (U u z θ * ψ θ) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
        ≤ Cψ * ∫ θ in Work.Spaces.Iθ, (U u z θ) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
      have hmain := MeasureTheory.integral_mono_of_nonneg
        (μ := MeasureTheory.volume.restrict Work.Spaces.Iθ)
        (f := fun θ : ℝ => (U u z θ * ψ θ) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
        (g := fun θ : ℝ => Cψ * ((U u z θ) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))))
        ?_ ?_ ?_
      · rw [MeasureTheory.integral_const_mul] at hmain
        exact hmain
      · filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Icc] with θ hθ
        exact mul_nonneg (sq_nonneg _)
          (Real.rpow_nonneg (Work.FTS.EllipticEst.AngSecond.sin_two_nonneg hθ) _)
      · exact hXint.const_mul Cψ
      · filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Icc] with θ hθ
        have hσ : 0 ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) :=
          Real.rpow_nonneg (Work.FTS.EllipticEst.AngSecond.sin_two_nonneg hθ) _
        have hψ2 : (ψ θ) ^ 2 ≤ Cψ := hCψ θ hθ
        have hX0 : 0 ≤ (U u z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) :=
          mul_nonneg (sq_nonneg _) hσ
        calc (U u z θ * ψ θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
            = ((U u z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
                * (ψ θ) ^ 2 := by ring
          _ ≤ ((U u z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) * Cψ :=
              mul_le_mul_of_nonneg_left hψ2 hX0
          _ = Cψ * ((U u z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) := by ring
    have hident : (Work.Spaces.w z) ^ 2
          * (∫ θ in Work.Spaces.Iθ, (U u z θ) ^ 2
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
        = ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 (U u) z θ := by
      rw [← MeasureTheory.integral_const_mul]
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc fun θ hθ => ?_
      rw [HkIntegrand_zero_U α z θ u hθ]
      ring
    calc (Work.Spaces.w z) ^ 2 * χ z
          * (∫ θ in Work.Spaces.Iθ, (U u z θ * ψ θ) ^ 2
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
        ≤ (Work.Spaces.w z) ^ 2 * χ z
            * (Cψ * ∫ θ in Work.Spaces.Iθ, (U u z θ) ^ 2
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) :=
          mul_le_mul_of_nonneg_left hslice (mul_nonneg (sq_nonneg _) (hχnn z hz))
      _ = (χ z * Cψ) * ((Work.Spaces.w z) ^ 2
            * ∫ θ in Work.Spaces.Iθ, (U u z θ) ^ 2
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) := by ring
      _ = χ z * Cψ * ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 (U u) z θ := by
          rw [hident]
      _ ≤ Cχ * Cψ * ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 (U u) z θ :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (hCχ z hz) hCψ0) hGnn

/-- The requested statement, kept verbatim.  See the module docstring: its hypotheses do not
determine the measurability (`AEStronglyMeasurable`) half of `MeasureTheory.Integrable`; the
version with the measurability hypotheses is `Upsi_A_integrable_of_smooth` above. -/
theorem Upsi_A_integrable (α : ℝ) (u : ℝ → ℝ → ℝ) (χ ψ : ℝ → ℝ)
    (hU : Work.Spaces.HkMem α 0 (Work.FTS.EllipticEst.H2W.Ae.grad u))
    (hχm : Measurable χ) (hχnn : ∀ z ∈ Work.Spaces.Iz, 0 ≤ χ z)
    (hχ : ∃ C : ℝ, ∀ z ∈ Work.Spaces.Iz, χ z ≤ C)
    (hψ : ∃ C : ℝ, ∀ θ ∈ Work.Spaces.Iθ, (ψ θ) ^ 2 ≤ C) :
    MeasureTheory.IntegrableOn
      (fun z => (Work.Spaces.w z) ^ 2 * χ z
        * ∫ θ in Work.Spaces.Iθ,
            (Work.FTS.EllipticEst.AeI1Fts.U u z θ * ψ θ) ^ 2
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
      Work.Spaces.Iz := by sorry

end Work.FTS.EllipticEst.AeI1Fts
