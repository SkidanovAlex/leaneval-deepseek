/-
Copyright: work module for the Elgindi finite-time singularity project.

# The pointwise second-derivative identity for the slice inequality

This file proves the pointwise identity underlying
`Cores.AeStep2Aux.slice_second_trunc` / `slice_second_nonpos`:

  `σ θ * (f θ * f'' θ) = (Phi f)' θ - Psi f θ`

with `σ θ = sin(2θ)^{-η}`, `Phi` the boundary primitive and `Psi ≥ 0` the bulk
term (see `slice_second_defs`).

The proof is a direct computation: `f` is `C²` on an open neighbourhood of `θ`,
so `f` and `deriv f` have (strict) derivatives there; the derivative of `Phi f`
is computed with the product rule and the `rpow` chain rule, and the resulting
expression is rearranged with the elementary `rpow` identities
`s^{-(1+η)} = s^{-η}/s` and `s^{-(2+η)} = s^{-η}/s²`.
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.EllipticEst.Cores.AeStep2Aux.slice_second_defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Cores.AeStep2Aux

set_option autoImplicit false

/-- The exponent identity `sin(2θ)^{-(1+η)} = sin(2θ)^{-η-1}`, matching the
derivative produced by the `rpow` chain rule. -/
private lemma ssi_sig1_eq_rpow (θ : ℝ) :
    sig1 θ = (Real.sin (2 * θ)) ^ (-Work.Spaces.eta - 1) := by
  unfold sig1
  rw [show -(1 + Work.Spaces.eta) = -Work.Spaces.eta - 1 by ring]

/-- The exponent identity `sin(2θ)^{-(2+η)} = sin(2θ)^{-(1+η)-1}`, matching the
derivative produced by the `rpow` chain rule. -/
private lemma ssi_sig2_eq_rpow (θ : ℝ) :
    sig2 θ = (Real.sin (2 * θ)) ^ (-(1 + Work.Spaces.eta) - 1) := by
  unfold sig2
  rw [show -(2 + Work.Spaces.eta) = -(1 + Work.Spaces.eta) - 1 by ring]

/-- `sin(2θ)^{-(1+η)} = sin(2θ)^{-η} / sin(2θ)`. -/
private lemma ssi_sig1_eq_div {θ : ℝ} (hs : 0 < Real.sin (2 * θ)) :
    sig1 θ = sig θ / Real.sin (2 * θ) := by
  unfold sig1 sig
  rw [show -(1 + Work.Spaces.eta) = -Work.Spaces.eta + -1 by ring]
  rw [Real.rpow_add hs, Real.rpow_neg_one]
  ring

/-- `sin(2θ)^{-(2+η)} = sin(2θ)^{-η} / sin(2θ)²`. -/
private lemma ssi_sig2_eq_div {θ : ℝ} (hs : 0 < Real.sin (2 * θ)) :
    sig2 θ = sig θ / (Real.sin (2 * θ)) ^ 2 := by
  unfold sig2 sig
  rw [show -(2 + Work.Spaces.eta) = -Work.Spaces.eta + -1 + -1 by ring]
  rw [Real.rpow_add hs, Real.rpow_add hs, Real.rpow_neg_one]
  ring

theorem slice_second_identity {f : ℝ → ℝ} (hf : ContDiffOn ℝ 2 f (Set.Ioo 0 (Real.pi / 2)))
    {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    Work.FTS.EllipticEst.Cores.AeStep2Aux.sliceIntegrand f θ
      = deriv (Work.FTS.EllipticEst.Cores.AeStep2Aux.Phi f) θ
        - Work.FTS.EllipticEst.Cores.AeStep2Aux.Psi f θ := by
  have hmem : Set.Ioo 0 (Real.pi / 2) ∈ 𝓝 θ := isOpen_Ioo.mem_nhds hθ
  have hf2 : ContDiffAt ℝ 2 f θ := hf.contDiffAt hmem
  have hfd1 : ContDiffAt ℝ 1 (deriv f) θ := hf2.derivWithin (by norm_num)
  have hd1 : HasDerivAt f (deriv f θ) θ := (hf2.hasStrictDerivAt (by norm_num)).hasDerivAt
  have hd2 : HasDerivAt (deriv f) (deriv (deriv f) θ) θ :=
    (hfd1.hasStrictDerivAt (by norm_num)).hasDerivAt
  have hs_pos : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2])
  have hs_ne : Real.sin (2 * θ) ≠ 0 := ne_of_gt hs_pos
  -- derivatives of the elementary factors
  have hlin : HasDerivAt (fun t : ℝ => 2 * t) 2 θ := by
    simpa using (hasDerivAt_id θ).const_mul (2 : ℝ)
  have hSd : HasDerivAt (fun t : ℝ => Real.sin (2 * t)) (2 * Real.cos (2 * θ)) θ := by
    convert hlin.sin using 1
    ring
  have hCd : HasDerivAt (fun t : ℝ => Real.cos (2 * t)) (-(2 * Real.sin (2 * θ))) θ := by
    convert hlin.cos using 1
    ring
  have hsig_raw : HasDerivAt sig
      ((2 * Real.cos (2 * θ)) * (-Work.Spaces.eta)
        * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta - 1)) θ :=
    hSd.rpow_const (p := -Work.Spaces.eta) (Or.inl hs_ne)
  have hsig : HasDerivAt sig (-(2 * Work.Spaces.eta) * Real.cos (2 * θ) * sig1 θ) θ := by
    convert hsig_raw using 1
    rw [ssi_sig1_eq_rpow]
    ring
  have hsig1_raw : HasDerivAt sig1
      ((2 * Real.cos (2 * θ)) * (-(1 + Work.Spaces.eta))
        * (Real.sin (2 * θ)) ^ (-(1 + Work.Spaces.eta) - 1)) θ :=
    hSd.rpow_const (p := -(1 + Work.Spaces.eta)) (Or.inl hs_ne)
  have hsig1 : HasDerivAt sig1 (-(2 * (1 + Work.Spaces.eta)) * Real.cos (2 * θ) * sig2 θ) θ := by
    convert hsig1_raw using 1
    rw [ssi_sig2_eq_rpow]
    ring
  -- the derivative of `Phi`
  have hff' : HasDerivAt (fun t => f t * deriv f t)
      (deriv f θ * deriv f θ + f θ * deriv (deriv f) θ) θ := hd1.mul hd2
  have ht1 : HasDerivAt (fun t => sig t * (f t * deriv f t))
      (-(2 * Work.Spaces.eta) * Real.cos (2 * θ) * sig1 θ * (f θ * deriv f θ)
        + sig θ * (deriv f θ * deriv f θ + f θ * deriv (deriv f) θ)) θ := hsig.mul hff'
  have hsq : HasDerivAt (fun t => (f t) ^ 2) (2 * f θ * deriv f θ) θ := by
    have h := hd1.pow 2
    rw [Pi.pow_def] at h
    simpa using h
  have hcs : HasDerivAt (fun t => Real.cos (2 * t) * sig1 t)
      ((-(2 * Real.sin (2 * θ))) * sig1 θ
        + Real.cos (2 * θ) * (-(2 * (1 + Work.Spaces.eta)) * Real.cos (2 * θ) * sig2 θ)) θ :=
    hCd.mul hsig1
  have ht2 : HasDerivAt (fun t => Real.cos (2 * t) * sig1 t * (f t) ^ 2)
      (((-(2 * Real.sin (2 * θ))) * sig1 θ
        + Real.cos (2 * θ) * (-(2 * (1 + Work.Spaces.eta)) * Real.cos (2 * θ) * sig2 θ))
          * (f θ) ^ 2
        + (Real.cos (2 * θ) * sig1 θ) * (2 * f θ * deriv f θ)) θ := hcs.mul hsq
  have hPhi : HasDerivAt (Phi f)
      ((-(2 * Work.Spaces.eta) * Real.cos (2 * θ) * sig1 θ * (f θ * deriv f θ)
        + sig θ * (deriv f θ * deriv f θ + f θ * deriv (deriv f) θ))
       - (((-(2 * Real.sin (2 * θ))) * sig1 θ
        + Real.cos (2 * θ) * (-(2 * (1 + Work.Spaces.eta)) * Real.cos (2 * θ) * sig2 θ))
          * (f θ) ^ 2
        + (Real.cos (2 * θ) * sig1 θ) * (2 * f θ * deriv f θ))) θ := ht1.sub ht2
  rw [hPhi.deriv]
  -- final algebraic rearrangement
  simp only [sliceIntegrand, Psi, ssi_sig1_eq_div hs_pos, ssi_sig2_eq_div hs_pos]
  field_simp
  ring

end Work.FTS.EllipticEst.Cores.AeStep2Aux
