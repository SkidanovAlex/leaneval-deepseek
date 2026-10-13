import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS_EllLimOK.PkgRepair
import Submission.Work.FTS_EllLimOK.Pinning.tendsto_cos_mul_of_hkMem_cosDiv
import Submission.Work.FTS_EllLimOK.SlotSup.slot_jets_sup_le
import Submission.Work.FTS.ClassC.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS_EllLimOK.Reconstruct
import Submission.Work.FTS_EllLimOK.L2Mem_of_HkMem_zero
import Submission.Work.FTS.GalFields.RHS.SharpAux.Core
import Submission.Work.FTS.OpenPkg.Basic
import Submission.Work.Spaces.aesm_slice_of_continuousOn_Qd
import Submission.Work.FTS_EllLimOK.Pinning.integrableOn_sq_rpow_of_HkMem
import Submission.Work.FTS_EllLimOK.Pinning.integrableOn_cos_sq_rpow_tail
import Submission.Work.FTS_EllLimOK.Pinning.integrableOn_deriv_cos_mul_sq_rpow
import Submission.Work.FTS_EllLimOK.Pinning.smoothOpen_div_cos
import Submission.Work.FTS_EllLimOK.SliceTrace.tendsto_zero_of_deriv_sq_integrable

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `hpin_of_hasPkgD` — the pinning lemma of the repaired elliptic package

This is the module behind obligation 1 of `FTS_EllLimOK`: from the repaired package
`HasPkgD α Ce E = HasPkg α Ce E ∧ PkgCos α E ∧ PkgDecay α E` one derives the *pinning*

`cos s · Φ̃(z,s) → 0`  (`s → π/2⁻`),  `Φ̃ = PhiTil α g (E g)`,

for every class-`C` source `g` and every `z > 0` (`REPLY_LEAD2.md` §2, §9).

## The argument

Fix `g` (class `C`) and `z > 0`, write `Ψ = PhiTil α g (E g)` and `φ(θ) = cos θ · Ψ z θ`.
Three inputs are used:

* `smoothOpen_PhiTil` (`EllPkgGo`'s regularity of the solution) gives `Ψ` of class `C^∞` on
  the open quadrant, hence `φ` is `C¹` on `(0,π/2)`;
* `EllPkgGo.V` gives `Vop Ψ ∈ ℋ⁴`, hence (extraction of the `D_z⁰`-term of the `ℋ⁰`-integrand,
  `integrableOn_sq_rpow_of_HkMem`) the weighted square `(Vop Ψ z ·)²·sin(2θ)^{-η}` is
  integrable; by `integrableOn_deriv_cos_mul_sq_rpow` — the pointwise identity
  `deriv (cos·θΨ z ·) = cos θ·Vop Ψ z θ` (`cos_mul_Vop_eq`) — this is the weighted square of
  `φ'`, which controls the *oscillation* of `φ` near `π/2`;
* `PkgCos` gives `Ψ/cos ∈ ℋ⁰`, hence `(Ψ z ·/cos ·)²·sin(2θ)^{-η}` is integrable; since
  `sin θ ≥ 1/2` on `(π/6, π/2)`, `integrableOn_cos_sq_rpow_tail` turns this into the
  weighted square `φ²·sin(2θ)^{-(η+4)}` on the tail `(π/6, π/2)`, whose weight is *not*
  integrable at `π/2`: that forces a point `τ` close to `π/2` with `|φ(τ)|` small.

Combining the small value at `τ` with the oscillation bound over a short enough tail gives
`|φ| ≤ ε` on a one-sided neighbourhood of `π/2`, i.e. `φ → 0`: this is
`SliceTrace.tendsto_zero_of_deriv_sq_integrable` (the `C¹` form of
`SliceTrace.deriv_tendsto_zero_at_pi_div_two`), applied with `η = Work.Spaces.eta = 99/100`
and `γ = η + 4 > 1`.

Note that *no* pointwise bound on `Vop Ψ` is needed: only the weighted `L²`-bounds of the
package enter.
-/

namespace Work.FTS_EllLimOK.Pinning

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false

/-- The `θ`-slice `θ ↦ cos θ · Ψ z θ` of a quadrant-smooth `Ψ` is `C¹` on `(0, π/2)`. -/
theorem contDiffOn_one_cos_mul_slice {Ψ : ℝ → ℝ → ℝ} (hsm : Work.FTS.EllipticEst.SmoothOpen Ψ)
    {z : ℝ} (hz : 0 < z) :
    ContDiffOn ℝ 1 (fun s => Real.cos s * Ψ z s) (Set.Ioo 0 (π / 2)) := by
  have hs : ContDiffOn ℝ 1 (fun s => Ψ z s) (Set.Ioo 0 (π / 2)) :=
    (hsm.curry_θ hz).of_le (by simp [Work.Stability.smoothOrder])
  exact ((Real.contDiff_cos (n := 1)).contDiffOn).mul hs

/-- The derivative of the slice `θ ↦ cos θ · Ψ z θ` is `cos θ · Vop Ψ z θ` (the
reconstruction identity `cos θ · Vop Ψ = ∂_θ(cos θ · Ψ)` of `Reconstruct`). -/
theorem deriv_cos_mul_slice {Ψ : ℝ → ℝ → ℝ} (hsm : Work.FTS.EllipticEst.SmoothOpen Ψ)
    {z : ℝ} (hz : 0 < z) {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    deriv (fun s => Real.cos s * Ψ z s) θ = Real.cos θ * Work.Construction.Vop Ψ z θ := by
  have hs : ContDiffOn ℝ 1 (fun s => Ψ z s) (Set.Ioo 0 (π / 2)) :=
    (hsm.curry_θ hz).of_le (by simp [Work.Stability.smoothOrder])
  have hd : HasDerivAt (fun s => Ψ z s) (Work.Spaces.pth Ψ z θ) θ := by
    have h2 : DifferentiableAt ℝ (fun s => Ψ z s) θ :=
      (hs.differentiableOn (by norm_num)).differentiableAt (isOpen_Ioo.mem_nhds hθ)
    simpa only [Work.Spaces.pth] using h2.hasDerivAt
  have h1 : HasDerivAt (fun s => Real.cos s * Ψ z s)
      (-Real.sin θ * Ψ z θ + Real.cos θ * Work.Spaces.pth Ψ z θ) θ :=
    (Real.hasDerivAt_cos θ).mul hd
  rw [h1.deriv]
  have hcc : Real.cos θ * Work.Construction.Vop Ψ z θ
      = Real.cos θ * Work.Spaces.pth Ψ z θ - Real.sin θ * Ψ z θ :=
    Work.FTS_EllLimOK.cos_mul_Vop_eq Ψ hθ
  rw [hcc]; ring

theorem hpin_of_hasPkgD {α Ce : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn}
    (hE : Work.FTS_EllLimOK.HasPkgD α Ce E) :
    ∀ g : Work.FTS.Galerkin.Fn, Work.FTS.ClassC.ClassC α g → ∀ z ∈ Set.Ioi (0 : ℝ),
      Filter.Tendsto (fun s => Real.cos s
        * Work.Construction.PhiTil α g (E g) z s) (𝓝[<] (π / 2)) (𝓝 0) := by
  intro g hg z hz
  obtain ⟨hGo, _hK6⟩ := hE.toHasPkg g hg
  set Ψ : ℝ → ℝ → ℝ := Work.Construction.PhiTil α g (E g) with hΨ
  -- regularity and the two `ℋ`-memberships of the package
  have hsm : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.GalFields.RHS.Sharp.smoothOpen_PhiTil hα hGo
  have hVsm : Work.FTS.EllipticEst.SmoothOpen (Work.Construction.Vop Ψ) := hGo.V.1.1
  have hV4 : Work.Spaces.HkMem α 4 (Work.Construction.Vop Ψ) := hGo.V.1.2
  have hV0 : Work.Spaces.HkMem α 0 (Work.Construction.Vop Ψ) :=
    Work.FTS.OpenPkg.HkMem_mono_open hVsm 0 (by norm_num) hV4
  have hmemCos : Work.Spaces.HkMem α 0 (fun z θ => Ψ z θ / Real.cos θ) := hE.cos g hg
  -- the weighted `L²`-integrals provided by the two packages
  have hVint : MeasureTheory.IntegrableOn
      (fun θ => (Work.Construction.Vop Ψ z θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) Work.Spaces.Iθ :=
    integrableOn_sq_rpow_of_HkMem hVsm hV0 z hz
  have hcint : MeasureTheory.IntegrableOn
      (fun θ => (Ψ z θ / Real.cos θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) Work.Spaces.Iθ :=
    integrableOn_sq_rpow_of_HkMem (smoothOpen_div_cos hsm) hmemCos z hz
  -- the two weighted `L²`-tails of `φ(θ) = cos θ · Ψ z θ`
  have h1 : MeasureTheory.IntegrableOn
      (fun θ => (Real.cos θ * Ψ z θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta + 4)))
      (Set.Ioo (Real.pi / 6) (Real.pi / 2)) :=
    integrableOn_cos_sq_rpow_tail hsm hz hcint
  have h2 : MeasureTheory.IntegrableOn
      (fun θ => (deriv (fun s => Real.cos s * Ψ z s) θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) (Set.Ioo 0 (Real.pi / 2)) :=
    integrableOn_deriv_cos_mul_sq_rpow hsm hz hVint
  have ht : (Real.pi / 6) ∈ Set.Ioo 0 (Real.pi / 2) :=
    ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  have hmain := Work.FTS_EllLimOK.SliceTrace.tendsto_zero_of_deriv_sq_integrable
    (η := Work.Spaces.eta) (γ := Work.Spaces.eta + 4)
    (by norm_num [Work.Spaces.eta]) (by norm_num [Work.Spaces.eta]) ht
    (contDiffOn_one_cos_mul_slice hsm hz) h1 h2
  exact hmain

end Work.FTS_EllLimOK.Pinning
