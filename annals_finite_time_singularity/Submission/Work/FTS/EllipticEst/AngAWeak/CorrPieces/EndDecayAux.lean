/-
Copyright: work module for the Elgindi finite-time singularity project.

# Elementary estimates for the right-endpoint analysis of `corrSlice_integrable`

This module collects the small pointwise/integration facts used by the endpoint decay
`Work.FTS.EllipticEst.AngAWeak.CorrPieces.endDecay`:

* `aesm_Lzero1` — `Lzero1 u` is a.e. strongly measurable on any measurable subset of `(0, π/2)`
  (it is built from derivatives and `u`, which is continuous there);
* `one_div_fluxDen_le` — the reciprocal of the flux denominator
  `cos s · sin²(2s)` is at most `(π³/32)(π/2-s)^{-3}`, from the elementary trig comparison
  `cos s ≥ (2/π)(π/2-s)`, `sin 2s ≥ (4/π)(π/2-s)`;
* `delta_rpow_integral_le` — `∫_a^b (π/2-s)^((q-1)/2) ds ≤ 2` for `π/4 ≤ a ≤ b ≤ π/2`, `q > 0`.
-/
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Submission.Work.FTS.EllipticEst.AngAWeak.chiDefs
import Submission.Work.FTS.EllipticEst.AngAWeak.SRSAux.TrigCompare

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.AngAWeak.CorrPieces

set_option autoImplicit false

/-- `Lzero1 u` is a.e. strongly measurable on any measurable subset of the open interval
`(0, π/2)` on which `u` is continuous: it is a combination of `deriv (deriv u)`,
`deriv (tan · u)` (both measurable) and `u`. -/
lemma aesm_Lzero1 {u : ℝ → ℝ} {s : Set ℝ} (hs : s ⊆ Set.Ioo (0 : ℝ) (Real.pi / 2))
    (hms : MeasurableSet s)
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n u (Set.Ioo (0 : ℝ) (Real.pi / 2))) :
    MeasureTheory.AEStronglyMeasurable (fun θ => Work.FTS.EllipticEst.Lzero1 u θ)
      (MeasureTheory.volume.restrict s) := by
  have hu : MeasureTheory.AEStronglyMeasurable u (MeasureTheory.volume.restrict s) :=
    ((hsm 0).mono hs).continuousOn.aestronglyMeasurable hms
  have hd1 : MeasureTheory.AEStronglyMeasurable (fun θ => deriv (fun t => deriv u t) θ)
      (MeasureTheory.volume.restrict s) :=
    (measurable_deriv (fun t => deriv u t)).aestronglyMeasurable
  have hd2 : MeasureTheory.AEStronglyMeasurable (fun θ => deriv (fun t => Real.tan t * u t) θ)
      (MeasureTheory.volume.restrict s) :=
    (measurable_deriv (fun t => Real.tan t * u t)).aestronglyMeasurable
  have h : MeasureTheory.AEStronglyMeasurable
      (fun θ => -deriv (fun t => deriv u t) θ + deriv (fun t => Real.tan t * u t) θ
        - 6 * u θ) (MeasureTheory.volume.restrict s) :=
    (hd1.neg.add hd2).sub (hu.const_mul 6)
  simpa only [Work.FTS.EllipticEst.Lzero1] using h

/-- On `(π/4, π/2)` the flux denominator is at least `(32/π³)(π/2-s)³`, so its reciprocal is at
most `(π³/32)/(π/2-s)³`. -/
lemma one_div_fluxDen_le {s : ℝ} (hs : s ∈ Set.Ioo (Real.pi / 4) (Real.pi / 2)) :
    1 / (Real.cos s * (Real.sin (2 * s)) ^ 2)
      ≤ (Real.pi ^ 3 / 32) / (Real.pi / 2 - s) ^ 3 := by
  have hδ : 0 < Real.pi / 2 - s := by linarith [hs.2, Real.pi_pos]
  obtain ⟨-, -, -, -, hsin, hcos, -, -, -, -, hlow, -⟩ :=
    Work.FTS.EllipticEst.AngAWeak.SRSAux.TrigCompare (q := 1) one_pos s hs
  have hD : 0 < Real.cos s * (Real.sin (2 * s)) ^ 2 := by positivity
  have hpos : 0 < (32 / Real.pi ^ 3) * (Real.pi / 2 - s) ^ 3 := by positivity
  have hmain : 1 / (Real.cos s * (Real.sin (2 * s)) ^ 2)
      ≤ 1 / ((32 / Real.pi ^ 3) * (Real.pi / 2 - s) ^ 3) :=
    one_div_le_one_div_of_le hpos hlow
  have hval : 1 / ((32 / Real.pi ^ 3) * (Real.pi / 2 - s) ^ 3)
      = (Real.pi ^ 3 / 32) / (Real.pi / 2 - s) ^ 3 := by
    have h1 : (Real.pi / 2 - s) ^ 3 ≠ 0 :=
      ne_of_gt (by positivity : (0 : ℝ) < (Real.pi / 2 - s) ^ 3)
    have h2 : (32 : ℝ) / Real.pi ^ 3 ≠ 0 :=
      ne_of_gt (by positivity : (0 : ℝ) < 32 / Real.pi ^ 3)
    field_simp
  rwa [hval] at hmain

/-- The right-endpoint integral of `(π/2-s)^((q-1)/2)`: for `q > 0` and
`π/4 ≤ a ≤ b ≤ π/2`,
`∫_a^b (π/2-s)^((q-1)/2) ds = (2/(q+1))((π/2-a)^((q+1)/2) - (π/2-b)^((q+1)/2)) ≤ 2`. -/
lemma delta_rpow_integral_le {q a b : ℝ} (hq : 0 < q) (ha : Real.pi / 4 ≤ a)
    (hab : a ≤ b) (hb : b ≤ Real.pi / 2) :
    ∫ s in a..b, (Real.pi / 2 - s) ^ ((q - 1) / 2) ≤ 2 := by
  have hr : -1 < (q - 1) / 2 := by linarith
  have hsub : ∫ s in a..b, (Real.pi / 2 - s) ^ ((q - 1) / 2)
      = ∫ u in (Real.pi / 2 - b)..(Real.pi / 2 - a), u ^ ((q - 1) / 2) := by
    have h := intervalIntegral.integral_comp_sub_left (fun u : ℝ => u ^ ((q - 1) / 2))
      (Real.pi / 2) (a := a) (b := b)
    simpa using h
  rw [hsub, integral_rpow (Or.inl hr)]
  have he : (q - 1) / 2 + 1 = (q + 1) / 2 := by ring
  rw [he]
  have h1 : (0 : ℝ) ≤ (Real.pi / 2 - b) ^ ((q + 1) / 2) :=
    Real.rpow_nonneg (by linarith [hb, Real.pi_pos]) _
  have h2 : (Real.pi / 2 - a) ^ ((q + 1) / 2) ≤ 1 :=
    Real.rpow_le_one (by linarith [Real.pi_pos]) (by nlinarith [Real.pi_le_four, ha])
      (by linarith)
  have hden : 0 < (q + 1) / 2 := by linarith
  rw [div_le_iff₀ hden]
  linarith

end Work.FTS.EllipticEst.AngAWeak.CorrPieces
