/-
Copyright: work module for the Elgindi finite-time singularity project.

# `FourInt` for the logarithmically truncated function `ζ_k · G`

The truncation step of the mixed weighted interpolation estimate replaces a datum `G` (smooth
on the open half-strip `(0,∞) × (-1, π/2+1)`) by the compactly supported `cut φ k G = ζ_k · G`,
where `ζ_k = zc φ k` is the logarithmic cut-off of `IsZCut φ K` (which equals `1` on `(1/k, k)`
and vanishes off `[1/k², k²]`).

This module proves that the truncated function satisfies the four integrability conditions
`FourInt (cut φ k G)`: each of the four slice functions

  `z ↦ w(z)² ∫_θ (F z θ)² sin(2θ)^{-η} dθ`,  `F ∈ {D_z∂_θ(ζ_kG), D_z²(ζ_kG), ∂_θ²(ζ_kG), D_z(ζ_kG)}`,

is supported in the compact interval `[1/k², k²]` (because every one of the four `F` is built
from `ζ_k`, `D_zζ_k = zE`, `D_z²ζ_k = zF` and derivatives of `G`, and all three of the cut-off
factors vanish there) and bounded there (each `F` is `C^∞` on the strip, hence bounded on the
compact box `[1/k², k²] × Iθ`, and the angular weight `sin(2θ)^{-η}` with `η = 99/100 < 1` is
integrable on `Iθ`).

The two ingredients are therefore

* `contDiffOn_uncurry_cut`: `cut φ k G` is `C^n` on the strip for every `n` (product of the
  `C^∞` function `ζ_k` of `z` alone with `G`), together with the workspace lemmas
  `contDiffOn_uncurry_{pth,Dz}_fin` which carry this regularity to the derivatives;
* `..._eq_zero_off_support`: derivatives of a function vanishing off `[δ,R]` vanish there too;
* `integrable_outer_sq_of_support`: the resulting integrability criterion.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Blocks.InterpTruncDefs
import Submission.Work.FTS.EllipticEst.ThetaU.K1Aux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Blocks.InterpTrunc

set_option autoImplicit false

/-! ## Smoothness of the truncated function on the strip -/

/-- `cut φ k G = ζ_k · G` is `C^n` on the open strip `(0,∞) × (-1, π/2+1)` for every `n`,
being the product of the `C^∞` function `ζ_k` of `z` alone with the `C^∞` function `G`. -/
theorem contDiffOn_uncurry_cut {φ : ℝ → ℝ} {K : ℝ} (hφ : Work.FTS.EllipticEst.IsZCut φ K)
    {k : ℕ} (hk : 2 ≤ k) {G : ℝ → ℝ → ℝ} (hG : Work.FTS.EllipticEst.ThetaU.SmoothOpenθ G)
    (n : ℕ) :
    ContDiffOn ℝ n (Function.uncurry (cut φ k G)) (Work.FTS.EllipticEst.ThetaU.OStrip) := by
  have hζ : ContDiffOn ℝ n (zeta φ k) (Set.Ioi 0) :=
    contDiffOn_infty.mp (zeta_contDiffOn_of_isZCut hφ hk) n
  have h1 : ContDiffOn ℝ n (fun p : ℝ × ℝ => zeta φ k p.1)
      (Work.FTS.EllipticEst.ThetaU.OStrip) :=
    hζ.comp contDiff_fst.contDiffOn (fun p hp => hp.1)
  exact h1.mul (hG n)

/-! ## Vanishing of the derivatives off the support in `z` -/

/-- A function which vanishes off `[δ,R]` in the first variable has vanishing `z`-derivative
there: on a neighbourhood of such a point its `θ`-slice is identically zero. -/
theorem Dz_eq_zero_off_support {δ R : ℝ} {H : ℝ → ℝ → ℝ}
    (hsupp : ∀ z, z ∉ Set.Icc δ R → ∀ θ, H z θ = 0) :
    ∀ z, z ∉ Set.Icc δ R → ∀ θ, Work.Spaces.Dz H z θ = 0 := by
  intro z hz θ
  have hn : ∀ᶠ z' in 𝓝 z, z' ∉ Set.Icc δ R := isClosed_Icc.isOpen_compl.mem_nhds hz
  have hev : (fun z' => H z' θ) =ᶠ[𝓝 z] (fun _ => (0 : ℝ)) :=
    hn.mono (fun z' hz' => hsupp z' hz' θ)
  show z * deriv (fun z' => H z' θ) z = 0
  rw [hev.deriv_eq, deriv_const, mul_zero]

/-- A function which vanishes off `[δ,R]` in the first variable has vanishing `θ`-derivative
there (its `θ`-slice is identically zero). -/
theorem pth_eq_zero_off_support {δ R : ℝ} {H : ℝ → ℝ → ℝ}
    (hsupp : ∀ z, z ∉ Set.Icc δ R → ∀ θ, H z θ = 0) :
    ∀ z, z ∉ Set.Icc δ R → ∀ θ, Work.Spaces.pth H z θ = 0 := by
  intro z hz θ
  have h0 : (fun θ' => H z θ') = fun _ => (0 : ℝ) := funext (fun θ' => hsupp z hz θ')
  show deriv (fun θ' => H z θ') θ = 0
  rw [h0, deriv_const]

/-- `D_z∂_θ` of a function vanishing off `[δ,R]` vanishes there as well. -/
theorem Dz_pth_eq_zero_off_support {δ R : ℝ} {H : ℝ → ℝ → ℝ}
    (hsupp : ∀ z, z ∉ Set.Icc δ R → ∀ θ, H z θ = 0) :
    ∀ z, z ∉ Set.Icc δ R → ∀ θ, Work.Spaces.Dz (Work.Spaces.pth H) z θ = 0 :=
  Dz_eq_zero_off_support (pth_eq_zero_off_support hsupp)

/-! ## Integrability of the outer weighted square integral -/

/-- If `F` is `C¹` on the strip `(0,∞) × (-1, π/2+1)` (in particular on a neighbourhood of the
box `[δ,R] × Iθ`) and vanishes for `z ∉ [δ,R]`, then the outer slice integral
`z ↦ w(z)² ∫_θ F(z,θ)² σ(θ) dθ` is integrable on `Iz = [0,∞)`: it is supported in the compact
interval `[δ,R]` and bounded there by the compactness of the box. -/
theorem integrable_outer_sq_of_support {δ R : ℝ} (hδ : 0 < δ) (hδR : δ < R)
    {F : ℝ → ℝ → ℝ}
    (hFsm : ContDiffOn ℝ 1 (Function.uncurry F) (Work.FTS.EllipticEst.ThetaU.OStrip))
    (hF0 : ∀ z, z ∉ Set.Icc δ R → ∀ θ, F z θ = 0) :
    MeasureTheory.Integrable
      (fun z => (Work.Spaces.w z) ^ 2
        * (∫ θ in Work.Spaces.Iθ, (F z θ) ^ 2 * Work.FTS.EllipticEst.thEta θ))
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
  have hcontStrip : ContinuousOn (Function.uncurry (fun z θ => (F z θ) ^ 2))
      Work.FTS.EllipticEst.ThetaU.OStrip := by
    have h1 : ContinuousOn (Function.uncurry F) Work.FTS.EllipticEst.ThetaU.OStrip :=
      hFsm.continuousOn
    have hsq : ContinuousOn (Function.uncurry (fun z θ => F z θ * F z θ))
        Work.FTS.EllipticEst.ThetaU.OStrip := h1.mul h1
    simpa only [pow_two] using hsq
  have hsub : Set.Ioi (0 : ℝ) ×ˢ Set.Ioo 0 (Real.pi / 2)
      ⊆ Work.FTS.EllipticEst.ThetaU.OStrip := by
    intro p hp
    exact ⟨hp.1, ⟨by linarith [hp.2.1], by linarith [hp.2.2, Real.pi_pos]⟩⟩
  have hbox : Set.Icc δ R ×ˢ Work.Spaces.Iθ ⊆ Work.FTS.EllipticEst.ThetaU.OStrip := by
    intro p hp
    exact ⟨lt_of_lt_of_le hδ hp.1.1,
      ⟨by linarith [hp.2.1], by linarith [hp.2.2, Real.pi_pos]⟩⟩
  refine Work.FTS.EllipticEst.ThetaU.integrable_outer_of_bound (δ := δ) (R := R) hδ
    (hcontStrip.mono hsub) ?_ ?_
  · intro z hz θ
    rw [hF0 z hz θ]
    ring
  · obtain ⟨M, _, hM⟩ := Work.FTS.EllipticEst.ThetaU.exists_bound_box hδ hδR
      (f := fun z θ => (F z θ) ^ 2) (hcontStrip.mono hbox)
    exact ⟨M, hM⟩

/-! ## The four integrability conditions of the truncated function -/

theorem fourInt_cut {φ : ℝ → ℝ} {K : ℝ} (hφ : Work.FTS.EllipticEst.IsZCut φ K) {k : ℕ}
    (hk : 2 ≤ k) {G : ℝ → ℝ → ℝ} (hG : Work.FTS.EllipticEst.ThetaU.SmoothOpenθ G) :
    Work.FTS.EllipticEst.FourInt (cut φ k G) := by
  have hk2 : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hk4 : (4 : ℝ) ≤ (k : ℝ) ^ 2 := by nlinarith
  have hδ : (0 : ℝ) < 1 / (k : ℝ) ^ 2 := by positivity
  have hδR : 1 / (k : ℝ) ^ 2 < (k : ℝ) ^ 2 := by
    rw [div_lt_iff₀ (by positivity)]
    nlinarith
  -- the truncated function is smooth on the strip
  have hcut : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry (cut φ k G))
      (Work.FTS.EllipticEst.ThetaU.OStrip) := fun n => contDiffOn_uncurry_cut hφ hk hG n
  -- and vanishes off the compact support `[1/k², k²]` of `ζ_k`
  have hsupp : ∀ z, z ∉ Set.Icc (1 / (k : ℝ) ^ 2) ((k : ℝ) ^ 2) →
      ∀ θ : ℝ, cut φ k G z θ = 0 := by
    intro z hz θ
    simp only [cut, zeta_eq_zero_of_notMem hφ hk hz, zero_mul]
  -- smoothness of the four derived functions on the strip
  have hsm1 : ContDiffOn ℝ 1 (Function.uncurry (Work.Spaces.Dz (Work.Spaces.pth
      (cut φ k G)))) (Work.FTS.EllipticEst.ThetaU.OStrip) :=
    Work.FTS.EllipticEst.ThetaU.contDiffOn_uncurry_Dz_fin (n := 1)
      (Work.FTS.EllipticEst.ThetaU.contDiffOn_uncurry_pth_fin (n := 2) (hcut 3))
  have hsm2 : ContDiffOn ℝ 1 (Function.uncurry (Work.Spaces.Dz (Work.Spaces.Dz
      (cut φ k G)))) (Work.FTS.EllipticEst.ThetaU.OStrip) :=
    Work.FTS.EllipticEst.ThetaU.contDiffOn_uncurry_Dz_fin (n := 1)
      (Work.FTS.EllipticEst.ThetaU.contDiffOn_uncurry_Dz_fin (n := 2) (hcut 3))
  have hsm3 : ContDiffOn ℝ 1 (Function.uncurry (Work.Spaces.pth (Work.Spaces.pth
      (cut φ k G)))) (Work.FTS.EllipticEst.ThetaU.OStrip) :=
    Work.FTS.EllipticEst.ThetaU.contDiffOn_uncurry_pth_fin (n := 1)
      (Work.FTS.EllipticEst.ThetaU.contDiffOn_uncurry_pth_fin (n := 2) (hcut 3))
  have hsm4 : ContDiffOn ℝ 1 (Function.uncurry (Work.Spaces.Dz (cut φ k G)))
      (Work.FTS.EllipticEst.ThetaU.OStrip) :=
    Work.FTS.EllipticEst.ThetaU.contDiffOn_uncurry_Dz_fin (n := 1) (hcut 2)
  -- vanishing of the four derived functions off the support
  have hz1 : ∀ z, z ∉ Set.Icc (1 / (k : ℝ) ^ 2) ((k : ℝ) ^ 2) →
      ∀ θ : ℝ, Work.Spaces.Dz (Work.Spaces.pth (cut φ k G)) z θ = 0 :=
    Dz_pth_eq_zero_off_support hsupp
  have hz2 : ∀ z, z ∉ Set.Icc (1 / (k : ℝ) ^ 2) ((k : ℝ) ^ 2) →
      ∀ θ : ℝ, Work.Spaces.Dz (Work.Spaces.Dz (cut φ k G)) z θ = 0 :=
    Dz_eq_zero_off_support (Dz_eq_zero_off_support hsupp)
  have hz3 : ∀ z, z ∉ Set.Icc (1 / (k : ℝ) ^ 2) ((k : ℝ) ^ 2) →
      ∀ θ : ℝ, Work.Spaces.pth (Work.Spaces.pth (cut φ k G)) z θ = 0 :=
    pth_eq_zero_off_support (pth_eq_zero_off_support hsupp)
  have hz4 : ∀ z, z ∉ Set.Icc (1 / (k : ℝ) ^ 2) ((k : ℝ) ^ 2) →
      ∀ θ : ℝ, Work.Spaces.Dz (cut φ k G) z θ = 0 :=
    Dz_eq_zero_off_support hsupp
  -- the four slice integrals are integrable on `Iz`
  have hI1 := integrable_outer_sq_of_support (δ := 1 / (k : ℝ) ^ 2) (R := (k : ℝ) ^ 2)
    hδ hδR hsm1 hz1
  have hI2 := integrable_outer_sq_of_support (δ := 1 / (k : ℝ) ^ 2) (R := (k : ℝ) ^ 2)
    hδ hδR hsm2 hz2
  have hI3 := integrable_outer_sq_of_support (δ := 1 / (k : ℝ) ^ 2) (R := (k : ℝ) ^ 2)
    hδ hδR hsm3 hz3
  have hI4 := integrable_outer_sq_of_support (δ := 1 / (k : ℝ) ^ 2) (R := (k : ℝ) ^ 2)
    hδ hδR hsm4 hz4
  rw [fourInt_iff]
  exact ⟨hI1, hI2, hI3, hI4⟩

end Work.Blocks.InterpTrunc
