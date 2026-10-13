/-
Copyright: work module for the Elgindi finite-time singularity project.

# Honesty of the angular slices `∂_z u`, `∂_z²u` and `Lzero1 (u z ·)` in the `Ae` class

For a datum `Work.FTS.EllipticEst.H2W.Ae.AeData α u G` (the almost-everywhere class of the
level-`0` elliptic estimate) and every `z > 0`, the three angular slices

  `θ ↦ ∂_z u(z,θ) · sinθcos²θ`,   `θ ↦ ∂_z²u(z,θ) · sinθcos²θ`,
  `θ ↦ Lzero1 (u z ·) θ · sinθcos²θ`

are integrable on `Iθ = [0,π/2]`.

## Route

* The three `ℋ⁰`-hypotheses give, slicewise in `z`, the weighted `L²`-bounds
  `∫ (G)²σ < ∞`, `∫ (z²∂_z²u)²σ < ∞` and `∫ (∂_θ²u)²σ < ∞` with `σ = sin(2θ)^{-η}`
  (`remov.ws_slot_slice`), and the elementary absorption
  `|g·sinθcos²θ| ≤ g²σ + 1` (`remov.ws_absMoment`) turns them into the integrability of the
  pairings `G·sinθcos²θ` and `(z²∂_z²u)·sinθcos²θ`; dividing by `z² ≠ 0` gives the second
  conjunct.
* The third conjunct is `Endpt.Lzero1_slice_mul_integrable`, whose hypothesis — boundedness of
  the slice and of its `θ`-derivative — is `Endpt.sliceBdd_of_hmB`, the fundamental-theorem
  bound from the honest weighted energy of `∂_θ²u`.
* The first conjunct is recovered from the equation `bslOp α u = G` on the open quadrant:
  `α(5+α) z ∂_zu = Lzero u - α²z²∂_z²u - G` there, and each of the three summands of the right
  side has just been shown to be integrable against `sinθcos²θ` (for `Lzero u` via the slice
  identity `Lzero u z θ = Lzero1 (u z ·) θ` and the third conjunct).

Everything here is asserted in the weak class of `Ae.Defs`: the equation is used only on the
open quadrant and the `HkMem`-hypotheses only through their angular slices at the fixed `z`.
-/
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.H2W.Ae.Defs
import Submission.Work.FTS.EllipticEst.StraightDefs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.EllipticEst.Cert.SmoothOpen_bslOp
import Submission.Work.FTS.EllipticEst.remov.SmoothOpen_bslOp_of_smoothOpen
import Submission.Work.FTS.EllipticEst.remov.wsAux
import Submission.Work.FTS.EllipticEst.remov.wsMomentId
import Submission.Work.FTS.EllipticEst.ae_restrict_Icc_of_forall_Ioo
import Submission.Work.FTS.EllipticEst.Endpt.sliceBdd_of_hmB
import Submission.Work.FTS.EllipticEst.Endpt.Lzero1_slice_mul_integrable

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.H2W.AeProof

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.unusedVariables false

local notation "Iθ" => Work.Spaces.Iθ
local notation "sg" => Work.Elliptic.sinCos2

/-- `Lzero1` applied to the `θ`-slice is the two-variable `Lzero` of a function with the same
slice (both depend only on the `θ`-slice). -/
private theorem Lzero1_slice_eq (Ψ : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.FTS.EllipticEst.Lzero1 (fun t : ℝ => Ψ z t) θ = Work.Elliptic.Lzero Ψ z θ := by
  simp only [Work.FTS.EllipticEst.Lzero1, Work.Elliptic.Lzero, Work.Spaces.pthIter_succ,
    Work.Spaces.pthIter_zero, Work.Spaces.pth]

/-- Dividing an integrand by a nonzero constant preserves integrability. -/
private theorem integrableOn_of_const_mul {c : ℝ} (hc : c ≠ 0) {f : ℝ → ℝ}
    (h : MeasureTheory.IntegrableOn (fun θ : ℝ => c * f θ) Iθ) :
    MeasureTheory.IntegrableOn f Iθ := by
  have h' : MeasureTheory.IntegrableOn (fun θ : ℝ => c⁻¹ * (c * f θ)) Iθ :=
    h.const_mul c⁻¹
  refine h'.congr (Filter.Eventually.of_forall (fun θ => ?_))
  field_simp

theorem AeSliceMomentFinite (α : ℝ) (u G : ℝ → ℝ → ℝ)
    (h : Work.FTS.EllipticEst.H2W.Ae.AeData α u G) {z : ℝ} (hz : 0 < z) :
    MeasureTheory.IntegrableOn (fun θ : ℝ => Work.Spaces.pz u z θ * Work.Elliptic.sinCos2 θ)
        Work.Spaces.Iθ
    ∧ MeasureTheory.IntegrableOn (fun θ : ℝ => Work.Spaces.pzIter 2 u z θ * Work.Elliptic.sinCos2 θ)
        Work.Spaces.Iθ
    ∧ MeasureTheory.IntegrableOn
        (fun θ : ℝ => Work.FTS.EllipticEst.Lzero1 (fun t : ℝ => u z t) θ
          * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ := by
  have hα : 0 < α := h.hα
  -- the `C^∞`-on-the-open-quadrant structure of `u`, `G` and `z²∂_z²u`
  have hU : Work.FTS.EllipticEst.SmoothOpen u :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  have hG : Work.FTS.EllipticEst.SmoothOpen G :=
    Work.FTS.EllipticEst.Cert.smoothOpen_congr_bsl
      (Work.FTS.EllipticEst.remov.SmoothOpen_bslOp_of_smoothOpen hU)
      (fun z θ hz hθ hθ2 => h.eq z hz θ hθ hθ2)
  have hA : Work.FTS.EllipticEst.SmoothOpen (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 u z θ) :=
    Work.FTS.EllipticEst.remov.ws_smoothOpen_zsq hU
  -- ## the pairings of `G` and of `z²∂_z²u` with the angular profile
  have hGsg : MeasureTheory.IntegrableOn (fun θ : ℝ => G z θ * sg θ) Iθ :=
    (Work.FTS.EllipticEst.remov.ws_absMoment
      (Work.FTS.EllipticEst.remov.ws_aesm_slice hG hz)
      (Work.FTS.EllipticEst.remov.ws_slot_slice hG h.memG 0 (Nat.zero_le 0) hz)).1
  have hAsg : MeasureTheory.IntegrableOn (fun θ : ℝ => (z ^ 2 * Work.Spaces.pzIter 2 u z θ) * sg θ)
      Iθ :=
    (Work.FTS.EllipticEst.remov.ws_absMoment
      (Work.FTS.EllipticEst.remov.ws_aesm_slice hA hz)
      (Work.FTS.EllipticEst.remov.ws_slot_slice hA h.memRad2 0 (Nat.zero_le 0) hz)).1
  -- ## the third conjunct
  have h3 : MeasureTheory.IntegrableOn
      (fun θ : ℝ => Work.FTS.EllipticEst.Lzero1 (fun t : ℝ => u z t) θ * sg θ) Iθ := by
    obtain ⟨C, _hCpos, hC⟩ :=
      Work.FTS.EllipticEst.Endpt.sliceBdd_of_hmB h.smooth h.memAng2 hz
    exact Work.FTS.EllipticEst.Endpt.Lzero1_slice_mul_integrable h.smooth h.memAng2 hz hC
  -- ## the second conjunct (divide the pairing of `z²∂_z²u` by `z²`)
  have h2 : MeasureTheory.IntegrableOn (fun θ : ℝ => Work.Spaces.pzIter 2 u z θ * sg θ) Iθ := by
    have h' : MeasureTheory.IntegrableOn
        (fun θ : ℝ => z ^ 2 * (Work.Spaces.pzIter 2 u z θ * sg θ)) Iθ := by
      refine hAsg.congr (Filter.Eventually.of_forall (fun θ => ?_))
      ring
    exact integrableOn_of_const_mul (pow_ne_zero 2 (ne_of_gt hz)) h'
  -- ## the first conjunct, from the equation
  have hLsg : MeasureTheory.IntegrableOn
      (fun θ : ℝ => Work.Elliptic.Lzero u z θ * sg θ) Iθ := by
    refine h3.congr (Filter.Eventually.of_forall (fun θ => ?_))
    show Work.FTS.EllipticEst.Lzero1 (fun t : ℝ => u z t) θ * sg θ
      = Work.Elliptic.Lzero u z θ * sg θ
    rw [Lzero1_slice_eq u z θ]
  have hRHS : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (Work.Elliptic.Lzero u z θ - α ^ 2 * z ^ 2 * Work.Spaces.pzIter 2 u z θ
        - G z θ) * sg θ) Iθ := by
    have ha : MeasureTheory.IntegrableOn
        (fun θ : ℝ => (α ^ 2 * z ^ 2 * Work.Spaces.pzIter 2 u z θ) * sg θ) Iθ := by
      refine (hAsg.const_mul (α ^ 2)).congr (Filter.Eventually.of_forall (fun θ => ?_))
      ring
    refine ((hLsg.sub ha).sub hGsg).congr (Filter.Eventually.of_forall (fun θ => ?_))
    simp only [Pi.sub_apply]
    ring
  have hae : (fun θ : ℝ => (α * (5 + α) * z)⁻¹ * ((Work.Elliptic.Lzero u z θ
        - α ^ 2 * z ^ 2 * Work.Spaces.pzIter 2 u z θ - G z θ) * sg θ))
      =ᵐ[MeasureTheory.volume.restrict Iθ]
      (fun θ : ℝ => Work.Spaces.pz u z θ * sg θ) := by
    refine Work.FTS.EllipticEst.ae_restrict_Icc_of_forall_Ioo (fun θ hθ => ?_)
    have heq := h.eq z hz θ hθ.1 hθ.2
    rw [Work.Elliptic.bslOp_apply] at heq
    have hden : α * (5 + α) * z ≠ 0 := ne_of_gt (by positivity)
    have hkey : Work.Elliptic.Lzero u z θ - α ^ 2 * z ^ 2 * Work.Spaces.pzIter 2 u z θ
        - G z θ = α * (5 + α) * z * Work.Spaces.pz u z θ := by linarith
    show (α * (5 + α) * z)⁻¹ * ((Work.Elliptic.Lzero u z θ
        - α ^ 2 * z ^ 2 * Work.Spaces.pzIter 2 u z θ - G z θ) * sg θ)
      = Work.Spaces.pz u z θ * sg θ
    rw [hkey]
    field_simp
  exact ⟨(hRHS.const_mul ((α * (5 + α) * z)⁻¹)).congr hae, h2, h3⟩

end Work.FTS.EllipticEst.H2W.AeProof
