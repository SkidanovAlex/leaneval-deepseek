/-
# The *wild* radial integration by parts of the Elgindi project

For the radial weight `w(z) = (1+z)²/z²` and two merely `C¹` functions `φ, ψ` on `(0,∞)`, we
prove

  `∫_0^∞ w² φ (z ψ') = ∫_0^∞ w² (-(z φ') - ((z-3)/(1+z)) φ) ψ`

under the two integrability hypotheses on the two integrands and the two decay hypotheses on
the flux `Φ(z) = z w(z)² φ(z) ψ(z)` (a limit `0` at `0⁺` and at `+∞`).

This is the integration by parts of the identity

  `Φ' = w² (z φ') ψ + w² (z ψ') φ + w² ((z-3)/(1+z)) φ ψ`,

whose middle and last terms are the two pieces of the right-hand side `w² (-(z φ') - ((z-3)/(1+z)) φ) ψ`
with the negative sign: `Φ' = (w² φ (z ψ')) - (w² (-(z φ') - ((z-3)/(1+z)) φ) ψ)`.  Since the flux
vanishes at both ends of `(0,∞)`, the fundamental theorem of calculus on `Ioi 0`
(`MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto`) gives `∫ Φ' = 0`, and the two
integrability hypotheses let one split `∫ Φ'` into the difference of the two integrals.

The pointwise identity uses `z w(z)² = (1+z)⁴/z³`, whose derivative is
`w(z)² ((z-3)/(1+z))`.

No regularity beyond `ContDiffOn ℝ 1` on the open half-line is used (in particular nothing at
`z = 0`, where `w` is discontinuous): the endpoint information is entirely carried by the two
flux limits.
-/
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Prop

set_option autoImplicit false

/-- The derivative of the "flux weight" `z ↦ z·w(z)²` at a point `z > 0`: on a neighbourhood of
`z` it is the rational function `y ↦ (1+y)⁴/y³`, whose derivative is
`w(z)²·((z-3)/(1+z))`. -/
private lemma hasDerivAt_zw2 (z : ℝ) (hz : 0 < z) :
    HasDerivAt (fun y : ℝ => y * (Work.Spaces.w y) ^ 2)
      ((Work.Spaces.w z) ^ 2 * ((z - 3) / (1 + z))) z := by
  have hzne : z ≠ 0 := ne_of_gt hz
  have hEq : (fun y : ℝ => y * (Work.Spaces.w y) ^ 2) =ᶠ[nhds z]
      (fun y : ℝ => (1 + y) ^ 4 / y ^ 3) := by
    filter_upwards [isOpen_ne.mem_nhds hzne] with y hy
    rw [Work.Spaces.w]
    field_simp
  have hdiff : DifferentiableAt ℝ (fun y : ℝ => (1 + y) ^ 4 / y ^ 3) z :=
    DifferentiableAt.div (by fun_prop) (by fun_prop) (pow_ne_zero 3 hzne)
  have hd : HasDerivAt (fun y : ℝ => (1 + y) ^ 4 / y ^ 3)
      (deriv (fun y : ℝ => (1 + y) ^ 4 / y ^ 3) z) z := hdiff.hasDerivAt
  refine (hd.congr_of_eventuallyEq hEq).congr_deriv ?_
  rw [deriv_fun_div (c := fun y : ℝ => (1 + y) ^ 4) (d := fun y : ℝ => y ^ 3)
      (by fun_prop) (by fun_prop) (pow_ne_zero 3 hzne),
    deriv_fun_pow (f := fun y : ℝ => 1 + y) (by fun_prop) 4,
    deriv_fun_pow (f := fun y : ℝ => y) (by fun_prop) 3,
    deriv_const_add (f := fun y : ℝ => y) (1 : ℝ), congr_fun deriv_id'' z]
  rw [Work.Spaces.w]
  field_simp
  ring

/-- A one-sided limit `0` at `0⁺` together with the value `0` at `0` gives continuity of `f` within
`[0,∞)` at `0`.  (The filters `𝓝[>] 0` and `𝓝[≥] 0` are not comparable, so the value information
is genuinely used.) -/
private lemma continuousWithinAt_Ici_of_tendsto {f : ℝ → ℝ}
    (h0 : Tendsto f (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds 0)) (hf0 : f 0 = 0) :
    ContinuousWithinAt f (Set.Ici 0) 0 := by
  rw [ContinuousWithinAt, hf0]
  intro s hs
  rw [Filter.mem_map]
  have h1 : f ⁻¹' s ∈ nhdsWithin (0 : ℝ) (Set.Ioi 0) := Filter.mem_map.mp (h0 hs)
  rw [nhdsWithin, mem_inf_iff_superset] at h1
  rw [nhdsWithin, mem_inf_iff_superset]
  obtain ⟨t1, ht1, t2, ht2, hsub⟩ := h1
  refine ⟨t1, ht1, t2 ∪ {0}, ?_, ?_⟩
  · intro x hx
    rcases eq_or_lt_of_le (Set.mem_Ici.mp hx) with h | h
    · exact Or.inr (by simp [h])
    · exact Or.inl (ht2 h)
  · intro y hy
    rcases hy.2 with h | h
    · exact hsub ⟨hy.1, h⟩
    · rw [Set.mem_singleton_iff] at h
      rw [h]
      simpa [Set.mem_preimage, hf0] using mem_of_mem_nhds hs

theorem radialIbpWild {φ ψ : ℝ → ℝ}
    (hφ : ContDiffOn ℝ 1 φ (Set.Ioi 0)) (hψ : ContDiffOn ℝ 1 ψ (Set.Ioi 0))
    (hint1 : MeasureTheory.IntegrableOn (fun z => (Work.Spaces.w z) ^ 2 * φ z * (z * deriv ψ z)) (Set.Ioi 0))
    (hint2 : MeasureTheory.IntegrableOn (fun z => (Work.Spaces.w z) ^ 2
      * (-(z * deriv φ z) - ((z - 3) / (1 + z)) * φ z) * ψ z) (Set.Ioi 0))
    (hf0 : Filter.Tendsto (fun z => z * (Work.Spaces.w z) ^ 2 * φ z * ψ z) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0))
    (hf1 : Filter.Tendsto (fun z => z * (Work.Spaces.w z) ^ 2 * φ z * ψ z) Filter.atTop (nhds 0)) :
    (∫ z in Set.Ioi 0, (Work.Spaces.w z) ^ 2 * φ z * (z * deriv ψ z))
      = ∫ z in Set.Ioi 0, (Work.Spaces.w z) ^ 2
          * (-(z * deriv φ z) - ((z - 3) / (1 + z)) * φ z) * ψ z := by
  -- the pointwise derivative of the flux `z ↦ z w(z)² φ(z) ψ(z)`
  have hderiv : ∀ z ∈ Set.Ioi (0:ℝ),
      HasDerivAt (fun y : ℝ => y * (Work.Spaces.w y) ^ 2 * φ y * ψ y)
        ((Work.Spaces.w z) ^ 2 * φ z * (z * deriv ψ z)
          - (Work.Spaces.w z) ^ 2
              * (-(z * deriv φ z) - ((z - 3) / (1 + z)) * φ z) * ψ z) z := by
    intro z hz
    have hA : HasDerivAt (fun y : ℝ => y * (Work.Spaces.w y) ^ 2)
        ((Work.Spaces.w z) ^ 2 * ((z - 3) / (1 + z))) z := hasDerivAt_zw2 z hz
    have hφd : HasDerivAt φ (deriv φ z) z :=
      ((hφ.differentiableOn (by norm_num)).differentiableAt (isOpen_Ioi.mem_nhds hz)).hasDerivAt
    have hψd : HasDerivAt ψ (deriv ψ z) z :=
      ((hψ.differentiableOn (by norm_num)).differentiableAt (isOpen_Ioi.mem_nhds hz)).hasDerivAt
    have hprod : HasDerivAt (fun y : ℝ => (y * (Work.Spaces.w y) ^ 2) * (φ y * ψ y))
        (((Work.Spaces.w z) ^ 2 * ((z - 3) / (1 + z))) * (φ z * ψ z)
          + (z * (Work.Spaces.w z) ^ 2) * (deriv φ z * ψ z + φ z * deriv ψ z)) z :=
      hA.mul (hφd.mul hψd)
    have hFB : (fun y : ℝ => y * (Work.Spaces.w y) ^ 2 * φ y * ψ y) =ᶠ[nhds z]
        (fun y : ℝ => (y * (Work.Spaces.w y) ^ 2) * (φ y * ψ y)) :=
      Filter.Eventually.of_forall (fun y => by ring)
    exact (hprod.congr_of_eventuallyEq hFB).congr_deriv (by ring)
  -- the derivative is integrable: it is the difference of the two given integrands
  have hDint : MeasureTheory.IntegrableOn
      ((fun z : ℝ => (Work.Spaces.w z) ^ 2 * φ z * (z * deriv ψ z))
        - fun z : ℝ => (Work.Spaces.w z) ^ 2
            * (-(z * deriv φ z) - ((z - 3) / (1 + z)) * φ z) * ψ z) (Set.Ioi 0) :=
    hint1.sub hint2
  -- the flux is continuous on `[0,∞)` at `0` and has limit `0` at `+∞`
  have hcont : ContinuousWithinAt (fun z : ℝ => z * (Work.Spaces.w z) ^ 2 * φ z * ψ z)
      (Set.Ici 0) 0 :=
    continuousWithinAt_Ici_of_tendsto hf0 (by simp)
  -- the fundamental theorem of calculus on `(0,∞)`
  have hFTC := MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto (a := (0:ℝ)) (m := (0:ℝ))
    hcont hderiv hDint hf1
  have hzero : (∫ z in Set.Ioi 0, (Work.Spaces.w z) ^ 2 * φ z * (z * deriv ψ z)
      - (Work.Spaces.w z) ^ 2
          * (-(z * deriv φ z) - ((z - 3) / (1 + z)) * φ z) * ψ z) = 0 := by
    rw [hFTC]
    simp
  have hsplit := MeasureTheory.integral_sub hint1 hint2
  linarith

end Work.FTS.EllipticEst.Prop
