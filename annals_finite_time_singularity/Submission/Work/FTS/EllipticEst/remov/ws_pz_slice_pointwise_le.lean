/-
Copyright: work module for the Elgindi finite-time singularity project.

# The pointwise slice bound for `∂_zΨ`

This module proves

`Work.FTS.EllipticEst.remov.ws_pz_slice_pointwise_le`

the pointwise bound on the whole `θ`-slice of `∂_zΨ` from the value and the
`θ`-derivative of `∂_zΨ` at the angle `π/4` and one weighted `L²`-energy, namely the
`θ`-energy `thetaE (D_z (∂_θ²Ψ)) s` of the slot `∂_θ²∂_zΨ` rescaled by `1/s²`.

It is a direct consequence of the one-dimensional second-order slice bound
`Work.FTS.EllipticEst.remov.ws_slice_pointwise_le` (proved in `wsAux`) applied to the slice
`θ ↦ ∂_zΨ(s,θ)`: by that estimate,

  `(∂_zΨ(s,θ))² ≤ 2(∂_zΨ(s,π/4))²
      + 4π²(1 + ∫_θ sEta)(1 + (∂_θ∂_zΨ(s,π/4))² + ∫_θ (∂_θ²∂_zΨ(s,·))² sEta)`

and the only two things to identify are

* the second derivative of the slice: `∂_θ²(∂_zΨ(s,·)) = pthIter 2 (pz Ψ) s` (definitional),
  which by Clairaut (`Work.FTS.EllipticEst.remov.pz_pthIter_comm_open`) and `D_z = s ∂_z`
  equals `(1/s)·D_z(∂_θ²Ψ)(s,·)`;
* the resulting energy: `thetaE (pthIter 2 (pz Ψ)) s = (1/s²)·thetaE (DzIter 1 (pthIter 2 Ψ)) s`,

the factor `1/s²` being exactly the one appearing in the statement.  The integrability of that
energy is the `i = 1` slot of `HkMem α k (∂_θ²Ψ)` (`Work.FTS.EllipticEst.remov.ws_slot_slice`),
which is where the hypotheses `1 ≤ k` and `HkMem` are used.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.remov.wsAux
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.EllipticEst.remov.Dz_slice_identities

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.remov

set_option maxHeartbeats 3200000

local notation "Iθ" => Work.Spaces.Iθ
local notation "SS" => Work.FTS.EllipticEst.sEta

/-! ## Two `θ`-identities for the `∂_z`-slice -/

/-- The second `θ`-derivative of the slice `θ ↦ ∂_zΨ(s,θ)` is the iterate
`pthIter 2 (pz Ψ) s`.  This is definitional. -/
theorem pz_slice_second_deriv_eq (Ψ : ℝ → ℝ → ℝ) (s : ℝ) :
    (fun θ => deriv (fun t => deriv (fun θ' => Work.Spaces.pz Ψ s θ') t) θ)
      = fun θ => Work.Spaces.pthIter 2 (Work.Spaces.pz Ψ) s θ := by
  funext θ
  rfl

/-- **Clairaut in the rescaling form needed below**: on the open quadrant the iterate
`∂_θ²∂_zΨ` equals `(1/s)·D_z(∂_θ²Ψ)`. -/
theorem pthIter2_pz_eq_inv_dz {Ψ : ℝ → ℝ → ℝ} (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ)
    {s θ : ℝ} (hs : 0 < s) (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    Work.Spaces.pthIter 2 (Work.Spaces.pz Ψ) s θ
      = (1 / s) * Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 Ψ) s θ := by
  -- Clairaut: `∂_θ²∂_zΨ = ∂_z∂_θ²Ψ`
  have h1 := pz_pthIter_comm_open Ψ hΨ 2 s θ hs hθ.1 hθ.2
  rw [← h1]
  -- and `D_z(∂_θ²Ψ)(s,θ) = s·∂_z(∂_θ²Ψ)(s,θ)`
  show Work.Spaces.pz (Work.Spaces.pthIter 2 Ψ) s θ
      = (1 / s) * (s * Work.Spaces.pz (Work.Spaces.pthIter 2 Ψ) s θ)
  rw [one_div, ← mul_assoc, inv_mul_cancel₀ (ne_of_gt hs), one_mul]

/-- **The `θ`-energy of the `∂_z`-slice is the rescaled energy of the `D_z`-slot**: the
`H^k`-norm controls `∂_θ²∂_zΨ` only through the `D_z = z∂_z` slot, which costs a factor
`1/s²`. -/
theorem thetaE_pthIter2_pz_eq_inv_sq {Ψ : ℝ → ℝ → ℝ} (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ)
    {s : ℝ} (hs : 0 < s) :
    thetaE (Work.Spaces.pthIter 2 (Work.Spaces.pz Ψ)) s
      = (1 / s ^ 2) * thetaE (Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 Ψ)) s := by
  have hae : (fun θ => (Work.Spaces.pthIter 2 (Work.Spaces.pz Ψ) s θ) ^ 2 * SS θ)
      =ᵐ[MeasureTheory.volume.restrict Iθ]
      (fun θ => (1 / s ^ 2)
        * ((Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 Ψ) s θ) ^ 2 * SS θ)) := by
    refine Work.FTS.EllipticEst.ae_restrict_Icc_of_forall_Ioo ?_
    intro θ hθ
    show (Work.Spaces.pthIter 2 (Work.Spaces.pz Ψ) s θ) ^ 2 * SS θ
        = (1 / s ^ 2) * ((Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 Ψ) s θ) ^ 2 * SS θ)
    rw [pthIter2_pz_eq_inv_dz hΨ hs hθ, mul_pow, div_pow, one_pow]
    ring
  rw [thetaE, thetaE,
    MeasureTheory.integral_congr_ae hae, MeasureTheory.integral_const_mul]

/-! ## The pointwise slice bound -/

theorem ws_pz_slice_pointwise_le {α : ℝ} {k : ℕ} {Ψ : ℝ → ℝ → ℝ}
    (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ) (hk : 1 ≤ k)
    (hm : Work.Spaces.HkMem α k (Work.Spaces.pthIter 2 Ψ))
    {s A B : ℝ} (hs : 0 < s)
    (hA : (Work.Spaces.pz Ψ s (Real.pi / 4)) ^ 2 ≤ A)
    (hB : (deriv (fun θ => Work.Spaces.pz Ψ s θ) (Real.pi / 4)) ^ 2 ≤ B) :
    ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      (Work.Spaces.pz Ψ s θ) ^ 2
        ≤ 2 * A + 4 * Real.pi ^ 2 * (1 + ∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.sEta θ)
          * (1 + B + (1 / s ^ 2) * Work.FTS.EllipticEst.remov.thetaE
              (Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 Ψ)) s) := by
  -- the slice `θ ↦ ∂_zΨ(s,θ)` is `C²` on the open angle interval
  have hv : ContDiffOn ℝ 2 (fun θ => Work.Spaces.pz Ψ s θ) (Set.Ioo 0 (Real.pi / 2)) :=
    ws_contDiffOn_slice hΨ.pz hs
  -- the `i = 1` slot of `HkMem α k (∂_θ²Ψ)` is the `θ`-energy, up to `1/s²`
  have hsm2 : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.pthIter 2 Ψ) :=
    SmoothOpen_pthIter_local hΨ 2
  have hslot : IntegrableOn
      (fun θ => (Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 Ψ) s θ) ^ 2 * SS θ) Iθ :=
    ws_slot_slice hsm2 hm 1 hk hs
  -- the integrand of `ws_slice_pointwise_le` is the rescaled slot
  have hae : (fun θ => (1 / s ^ 2)
        * ((Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 Ψ) s θ) ^ 2 * SS θ))
      =ᵐ[MeasureTheory.volume.restrict Iθ]
      (fun θ => (deriv (fun t => deriv (fun θ' => Work.Spaces.pz Ψ s θ') t) θ) ^ 2 * SS θ) := by
    refine Work.FTS.EllipticEst.ae_restrict_Icc_of_forall_Ioo ?_
    intro θ hθ
    have h1 : deriv (fun t => deriv (fun θ' => Work.Spaces.pz Ψ s θ') t) θ
        = Work.Spaces.pthIter 2 (Work.Spaces.pz Ψ) s θ :=
      congrFun (pz_slice_second_deriv_eq Ψ s) θ
    show (1 / s ^ 2)
        * ((Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 Ψ) s θ) ^ 2 * SS θ)
        = (deriv (fun t => deriv (fun θ' => Work.Spaces.pz Ψ s θ') t) θ) ^ 2 * SS θ
    rw [h1, pthIter2_pz_eq_inv_dz hΨ hs hθ, mul_pow, div_pow, one_pow]
    ring
  have hE : IntegrableOn
      (fun θ => (deriv (fun t => deriv (fun θ' => Work.Spaces.pz Ψ s θ') t) θ) ^ 2 * SS θ)
      Iθ :=
    (hslot.const_mul (1 / s ^ 2)).congr hae
  have hpt := ws_slice_pointwise_le (v := fun θ => Work.Spaces.pz Ψ s θ) hv hE
  -- the energy integral equals the rescaled `D_z`-slot energy
  have hEint : (∫ θ in Iθ,
        (deriv (fun t => deriv (fun θ' => Work.Spaces.pz Ψ s θ') t) θ) ^ 2 * SS θ)
      = (1 / s ^ 2) * thetaE (Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 Ψ)) s := by
    rw [MeasureTheory.integral_congr_ae hae.symm, MeasureTheory.integral_const_mul]
    rfl
  intro θ hθ
  have h := hpt θ hθ
  beta_reduce at h
  rw [hEint] at h
  have hS0 : (0 : ℝ) ≤ ∫ θ in Iθ, SS θ := ws_sEta_integral_nonneg
  have hc : (0 : ℝ) ≤ 4 * Real.pi ^ 2 * (1 + ∫ θ in Iθ, SS θ) := by
    have : (0 : ℝ) ≤ 1 + ∫ θ in Iθ, SS θ := by linarith
    positivity
  have hmono : 1 + (deriv (fun θ => Work.Spaces.pz Ψ s θ) (Real.pi / 4)) ^ 2
        + (1 / s ^ 2) * thetaE (Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 Ψ)) s
      ≤ 1 + B + (1 / s ^ 2) * thetaE (Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 Ψ)) s := by
    linarith [hB]
  have hmul := mul_le_mul_of_nonneg_left hmono hc
  linarith [h, hmul, hA]

end Work.FTS.EllipticEst.remov
