/-
# Viscosity subsolutions under a linear substitution

If `w` is a viscosity subsolution of `tr (C ∘ D²·) = 0` on `s`, then `y ↦ w (B y)` is a viscosity
subsolution of `tr ((B⁻¹ C B⁻¹) ∘ D²·) = 0` on `B ⁻¹' s`.  With `B` a symmetric square root of
`cofOp N` this turns the limiting operator of Savin's Proposition 4.1 into the Laplacian, so the
harmonic mean value property applies to `w ∘ B`.

The proof is the chain rule for the Hessian (`Submission.Savin.Linear.hessOp_comp_linear`) applied
to the test function `ψ ∘ B⁻¹`, together with the fact that a test function touching `w ∘ B` at
`y` corresponds to a test function touching `w` at `B y`.
-/
import Mathlib
import ChallengeDeps
import Submission.Savin.Spec
import Submission.Commons.Analysis.Calculus.FDeriv.hessianWithin_eq_hessian
import Submission.Viscosity

open Metric MeasureTheory Filter Set
open Commons.Analysis.Calculus.FDeriv
open scoped BigOperators RealInnerProductSpace Topology ENNReal Pointwise

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000

namespace Submission

local notation "ℝ⁴" => EuclideanSpace ℝ (Fin 4)

noncomputable section

/-- `tr (C ∘ (B⁻¹ (M B⁻¹))) = tr ((B⁻¹ C B⁻¹) ∘ M)`: the operator transformation. -/
theorem trOp_conj_three (C Bi M : ℝ⁴ →L[ℝ] ℝ⁴) :
    trOp (C * (Bi * (M * Bi))) = trOp ((Bi * C * Bi) * M) := by
  have h1 : C * (Bi * (M * Bi)) = ((C * Bi * M) * Bi) := by noncomm_ring
  rw [h1, trOp_mul_comm (C * Bi * M) Bi]
  try noncomm_ring

/-- **Viscosity subsolutions under a linear substitution.** -/
theorem isViscSubsolution_comp_linear {B Bi : ℝ⁴ →L[ℝ] ℝ⁴} (hBBi : B * Bi = 1)
    (hBiB : Bi * B = 1) (hBisym : Bi.IsSymmetric) {C : ℝ⁴ →L[ℝ] ℝ⁴} {w : ℝ⁴ → ℝ}
    {s : Set ℝ⁴} (hs : IsOpen s)
    (hsub : IsViscSubsolution (fun M => trOp (C * M)) w s) :
    IsViscSubsolution (fun M => trOp ((Bi * C * Bi) * M)) (fun y => w (B y)) (B ⁻¹' s) := by
  intro ψ hψ y hy hloc
  have hBapp : ∀ z : ℝ⁴, B (Bi z) = z := by
    intro z
    have h := congrFun (congrArg (fun T : ℝ⁴ →L[ℝ] ℝ⁴ => (T : ℝ⁴ → ℝ⁴)) hBBi) z
    simpa only [_root_.mul_apply_eq_comp, _root_.one_apply_eq_self] using h
  have hBiapp : ∀ z : ℝ⁴, Bi (B z) = z := by
    intro z
    have h := congrFun (congrArg (fun T : ℝ⁴ →L[ℝ] ℝ⁴ => (T : ℝ⁴ → ℝ⁴)) hBiB) z
    simpa only [_root_.mul_apply_eq_comp, _root_.one_apply_eq_self] using h
  have hBis : IsOpen (B ⁻¹' s) := hs.preimage B.continuous
  have hBy : B y ∈ s := hy
  have hHy : B ⁻¹' s ∈ 𝓝 y := hBis.mem_nhds hy
  -- the test function `ψ ∘ B⁻¹` touches `w` from above at `B y`
  have hφ : ContDiffOn ℝ 2 (fun ζ => ψ (Bi ζ)) s := by
    have hmap : Set.MapsTo Bi s (B ⁻¹' s) := by
      intro z hz
      show B (Bi z) ∈ s
      rw [hBapp z]; exact hz
    exact hψ.comp Bi.contDiff.contDiffOn hmap
  have hlocφ : ∀ᶠ z in 𝓝[s] (B y), w z - ψ (Bi z) ≤ w (B y) - ψ (Bi (B y)) := by
    rw [nhdsWithin_eq_nhds.mpr (hs.mem_nhds hBy)]
    have hcont : Tendsto Bi (𝓝 (B y)) (𝓝 y) := by
      have h1 : Bi (B y) = y := hBiapp y
      rw [show (𝓝 y : Filter ℝ⁴) = 𝓝 (Bi (B y)) from by rw [h1]]
      exact Bi.continuous.continuousAt
    have hev : ∀ᶠ y' in 𝓝 y, w (B y') - ψ y' ≤ w (B y) - ψ y := by
      have h := hloc
      rwa [nhdsWithin_eq_nhds.mpr hHy] at h
    simpa only [hBapp, hBiapp] using hcont.eventually hev
  have hres := hsub (fun ζ => ψ (Bi ζ)) hφ (B y) hBy hlocφ
  -- rewrite the test-function Hessian
  have hC2 : ContDiffAt ℝ 2 ψ y :=
    hψ.contDiffAt (hBis.mem_nhds hy)
  have hhess1 : HessOp (fun ζ => ψ (Bi ζ)) s (B y) = hessOp (fun ζ => ψ (Bi ζ)) (B y) :=
    hessianWithin_eq_hessian (hs.mem_nhds hBy)
  have hhess2 : hessOp (fun ζ => ψ (Bi ζ)) (B y)
      = Bi.adjoint.comp ((hessOp ψ (Bi (B y))).comp Bi) :=
    hessOp_comp_linear (B := Bi) (w := ψ) (x := B y) (by simpa only [hBiapp] using hC2)
  have hhess3 : HessOp ψ (B ⁻¹' s) y = hessOp ψ y :=
    hessianWithin_eq_hessian (hBis.mem_nhds hy)
  have hexpr : C * HessOp (fun ζ => ψ (Bi ζ)) s (B y) = C * (Bi * (hessOp ψ y * Bi)) := by
    rw [hhess1, hhess2, hBisym.clm_adjoint_eq, hBiapp]
    rfl
  dsimp only at hres
  rw [hexpr, trOp_conj_three C Bi (hessOp ψ y)] at hres
  simpa only [hhess3] using hres

/-- `-(tr (C * (-M))) = tr (C * M)`: the operator `M ↦ tr (C * M)` is odd-symmetric. -/
theorem neg_trOp_neg (C M : ℝ⁴ →L[ℝ] ℝ⁴) : -(trOp (C * (-M))) = trOp (C * M) := by
  have h : C * (-M) = -(C * M) := mul_neg C M
  rw [h]
  have h2 : trOp (-(C * M)) = -trOp (C * M) := by
    unfold trOp
    rw [show ((-(C * M) : ℝ⁴ →L[ℝ] ℝ⁴) : ℝ⁴ →ₗ[ℝ] ℝ⁴)
        = -((C * M : ℝ⁴ →L[ℝ] ℝ⁴) : ℝ⁴ →ₗ[ℝ] ℝ⁴) from rfl, map_neg]
  rw [h2, neg_neg]

/-- **Viscosity supersolutions under a linear substitution.** -/
theorem isViscSupersolution_comp_linear {B Bi : ℝ⁴ →L[ℝ] ℝ⁴} (hBBi : B * Bi = 1)
    (hBiB : Bi * B = 1) (hBisym : Bi.IsSymmetric) {C : ℝ⁴ →L[ℝ] ℝ⁴} {w : ℝ⁴ → ℝ}
    {s : Set ℝ⁴} (hs : IsOpen s)
    (hsup : IsViscSupersolution (fun M => trOp (C * M)) w s) :
    IsViscSupersolution (fun M => trOp ((Bi * C * Bi) * M)) (fun y => w (B y)) (B ⁻¹' s) := by
  have hop : (fun M : ℝ⁴ →L[ℝ] ℝ⁴ => -(trOp (C * (-M)))) = fun M => trOp (C * M) := by
    funext M
    exact neg_trOp_neg C M
  have h1 : IsViscSubsolution (fun M => trOp (C * M)) (fun x => -w x) s := by
    rw [← hop]
    exact (isViscSupersolution_iff hs).mp hsup
  have h2 := isViscSubsolution_comp_linear hBBi hBiB hBisym hs h1
  have hop2 : (fun M : ℝ⁴ →L[ℝ] ℝ⁴ => -(trOp ((Bi * C * Bi) * (-M))))
      = fun M => trOp ((Bi * C * Bi) * M) := by
    funext M
    exact neg_trOp_neg (Bi * C * Bi) M
  rw [isViscSupersolution_iff (hs.preimage B.continuous), hop2]
  exact h2

/-- **The negated (proper) operator.**  Since `M ↦ tr (C ∘ M)` is *increasing*, the operator that
satisfies the proper-ellipticity sign convention is `M ↦ -tr (C ∘ M)`; this is the variant of
`isViscSubsolution_comp_linear` for it (the proof is identical, the sign sitting outside the whole
expression). -/
theorem isViscSubsolution_comp_linear_neg {B Bi : ℝ⁴ →L[ℝ] ℝ⁴} (hBBi : B * Bi = 1)
    (hBiB : Bi * B = 1) (hBisym : Bi.IsSymmetric) {C : ℝ⁴ →L[ℝ] ℝ⁴} {w : ℝ⁴ → ℝ}
    {s : Set ℝ⁴} (hs : IsOpen s)
    (hsub : IsViscSubsolution (fun M => -trOp (C * M)) w s) :
    IsViscSubsolution (fun M => -trOp ((Bi * C * Bi) * M)) (fun y => w (B y)) (B ⁻¹' s) := by
  intro ψ hψ y hy hloc
  have hBapp : ∀ z : ℝ⁴, B (Bi z) = z := by
    intro z
    have h := congrFun (congrArg (fun T : ℝ⁴ →L[ℝ] ℝ⁴ => (T : ℝ⁴ → ℝ⁴)) hBBi) z
    simpa only [_root_.mul_apply_eq_comp, _root_.one_apply_eq_self] using h
  have hBiapp : ∀ z : ℝ⁴, Bi (B z) = z := by
    intro z
    have h := congrFun (congrArg (fun T : ℝ⁴ →L[ℝ] ℝ⁴ => (T : ℝ⁴ → ℝ⁴)) hBiB) z
    simpa only [_root_.mul_apply_eq_comp, _root_.one_apply_eq_self] using h
  have hBis : IsOpen (B ⁻¹' s) := hs.preimage B.continuous
  have hBy : B y ∈ s := hy
  have hHy : B ⁻¹' s ∈ 𝓝 y := hBis.mem_nhds hy
  have hφ : ContDiffOn ℝ 2 (fun ζ => ψ (Bi ζ)) s := by
    have hmap : Set.MapsTo Bi s (B ⁻¹' s) := by
      intro z hz
      show B (Bi z) ∈ s
      rw [hBapp z]; exact hz
    exact hψ.comp Bi.contDiff.contDiffOn hmap
  have hlocφ : ∀ᶠ z in 𝓝[s] (B y), w z - ψ (Bi z) ≤ w (B y) - ψ (Bi (B y)) := by
    rw [nhdsWithin_eq_nhds.mpr (hs.mem_nhds hBy)]
    have hcont : Tendsto Bi (𝓝 (B y)) (𝓝 y) := by
      have h1 : Bi (B y) = y := hBiapp y
      rw [show (𝓝 y : Filter ℝ⁴) = 𝓝 (Bi (B y)) from by rw [h1]]
      exact Bi.continuous.continuousAt
    have hev : ∀ᶠ y' in 𝓝 y, w (B y') - ψ y' ≤ w (B y) - ψ y := by
      have h := hloc
      rwa [nhdsWithin_eq_nhds.mpr hHy] at h
    simpa only [hBapp, hBiapp] using hcont.eventually hev
  have hres := hsub (fun ζ => ψ (Bi ζ)) hφ (B y) hBy hlocφ
  have hC2 : ContDiffAt ℝ 2 ψ y := hψ.contDiffAt (hBis.mem_nhds hy)
  have hhess1 : HessOp (fun ζ => ψ (Bi ζ)) s (B y) = hessOp (fun ζ => ψ (Bi ζ)) (B y) :=
    hessianWithin_eq_hessian (hs.mem_nhds hBy)
  have hhess2 : hessOp (fun ζ => ψ (Bi ζ)) (B y)
      = Bi.adjoint.comp ((hessOp ψ (Bi (B y))).comp Bi) :=
    hessOp_comp_linear (B := Bi) (w := ψ) (x := B y) (by simpa only [hBiapp] using hC2)
  have hhess3 : HessOp ψ (B ⁻¹' s) y = hessOp ψ y :=
    hessianWithin_eq_hessian (hBis.mem_nhds hy)
  have hexpr : C * HessOp (fun ζ => ψ (Bi ζ)) s (B y) = C * (Bi * (hessOp ψ y * Bi)) := by
    rw [hhess1, hhess2, hBisym.clm_adjoint_eq, hBiapp]
    rfl
  dsimp only at hres
  rw [hexpr, trOp_conj_three C Bi (hessOp ψ y)] at hres
  simpa only [hhess3] using hres

/-- **The negated (proper) operator**, supersolution version. -/
theorem isViscSupersolution_comp_linear_neg {B Bi : ℝ⁴ →L[ℝ] ℝ⁴} (hBBi : B * Bi = 1)
    (hBiB : Bi * B = 1) (hBisym : Bi.IsSymmetric) {C : ℝ⁴ →L[ℝ] ℝ⁴} {w : ℝ⁴ → ℝ}
    {s : Set ℝ⁴} (hs : IsOpen s)
    (hsup : IsViscSupersolution (fun M => -trOp (C * M)) w s) :
    IsViscSupersolution (fun M => -trOp ((Bi * C * Bi) * M)) (fun y => w (B y)) (B ⁻¹' s) := by
  intro ψ hψ y hy hloc
  have hBapp : ∀ z : ℝ⁴, B (Bi z) = z := by
    intro z
    have h := congrFun (congrArg (fun T : ℝ⁴ →L[ℝ] ℝ⁴ => (T : ℝ⁴ → ℝ⁴)) hBBi) z
    simpa only [_root_.mul_apply_eq_comp, _root_.one_apply_eq_self] using h
  have hBiapp : ∀ z : ℝ⁴, Bi (B z) = z := by
    intro z
    have h := congrFun (congrArg (fun T : ℝ⁴ →L[ℝ] ℝ⁴ => (T : ℝ⁴ → ℝ⁴)) hBiB) z
    simpa only [_root_.mul_apply_eq_comp, _root_.one_apply_eq_self] using h
  have hBis : IsOpen (B ⁻¹' s) := hs.preimage B.continuous
  have hBy : B y ∈ s := hy
  have hHy : B ⁻¹' s ∈ 𝓝 y := hBis.mem_nhds hy
  have hφ : ContDiffOn ℝ 2 (fun ζ => ψ (Bi ζ)) s := by
    have hmap : Set.MapsTo Bi s (B ⁻¹' s) := by
      intro z hz
      show B (Bi z) ∈ s
      rw [hBapp z]; exact hz
    exact hψ.comp Bi.contDiff.contDiffOn hmap
  have hlocφ : ∀ᶠ z in 𝓝[s] (B y), w z - ψ (Bi z) ≥ w (B y) - ψ (Bi (B y)) := by
    rw [nhdsWithin_eq_nhds.mpr (hs.mem_nhds hBy)]
    have hcont : Tendsto Bi (𝓝 (B y)) (𝓝 y) := by
      have h1 : Bi (B y) = y := hBiapp y
      rw [show (𝓝 y : Filter ℝ⁴) = 𝓝 (Bi (B y)) from by rw [h1]]
      exact Bi.continuous.continuousAt
    have hev : ∀ᶠ y' in 𝓝 y, w (B y') - ψ y' ≥ w (B y) - ψ y := by
      have h := hloc
      rwa [nhdsWithin_eq_nhds.mpr hHy] at h
    simpa only [hBapp, hBiapp] using hcont.eventually hev
  have hres := hsup (fun ζ => ψ (Bi ζ)) hφ (B y) hBy hlocφ
  have hC2 : ContDiffAt ℝ 2 ψ y := hψ.contDiffAt (hBis.mem_nhds hy)
  have hhess1 : HessOp (fun ζ => ψ (Bi ζ)) s (B y) = hessOp (fun ζ => ψ (Bi ζ)) (B y) :=
    hessianWithin_eq_hessian (hs.mem_nhds hBy)
  have hhess2 : hessOp (fun ζ => ψ (Bi ζ)) (B y)
      = Bi.adjoint.comp ((hessOp ψ (Bi (B y))).comp Bi) :=
    hessOp_comp_linear (B := Bi) (w := ψ) (x := B y) (by simpa only [hBiapp] using hC2)
  have hhess3 : HessOp ψ (B ⁻¹' s) y = hessOp ψ y :=
    hessianWithin_eq_hessian (hBis.mem_nhds hy)
  have hexpr : C * HessOp (fun ζ => ψ (Bi ζ)) s (B y) = C * (Bi * (hessOp ψ y * Bi)) := by
    rw [hhess1, hhess2, hBisym.clm_adjoint_eq, hBiapp]
    rfl
  dsimp only at hres
  rw [hexpr, trOp_conj_three C Bi (hessOp ψ y)] at hres
  simpa only [hhess3] using hres

end

end Submission
