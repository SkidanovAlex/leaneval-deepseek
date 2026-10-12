import ChallengeDeps
import Submission.ProfileEq1D
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Radial 1D weak equation of the scattering solution (Layer 3)

For *radial* `v` and `w` with `w` a weak scattering solution
(`IsScatteringSolution w v`), and for a radial test function
`φ(x) := ψ ‖x‖` with `ψ ∈ C∞c((R₀, ∞))` (`R₀ > 0`, so `φ` is smooth on all
of `ℝ³`), the weak equation

    −∫ w·Δφ = (1/2)∫ v(1−w)·φ

reduces — by the same radial integration as in
`RadialTest.radial_weakHarmonic_1D`, with `ψ := χ/r` — to the clean 1D
statement for `u(r) := r · radialProfile w r` and the radial source profile

    gprof(r) := radialProfile v r · (1 − radialProfile w r) = v(r·u₀)·(1 − w(r·u₀)) :

    ∫ r in Ioi 0, u r · χ''(r) dr = −(1/2) · ∫ r in Ioi 0, r · gprof r · χ r dr

for every `χ ∈ C∞c((R₀, ∞))`.  (Since every `χ ∈ C∞c((0,∞))` has support in
`(R₀, ∞)` for some `R₀ > 0`, the identity holds for every test function with
support away from `0`.)

This is the 1D weak form of `u'' = −(1/2)·r·gprof` on `(0, ∞)` and is the
ingredient of the Gauss/shell identity identifying the exterior constant of
`w` (its scattering length `c = (1/8π)∫_{ℝ³} v(1−w)`, classical formula
`c = (1/2)∫₀^∞ r²·gprof`).
-/

noncomputable section

open _root_.BoseGases
set_option autoImplicit false

namespace Submission.BoseGases

open Filter Metric MeasureTheory Laplacian
open scoped ContDiff Topology Real

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- The radial 1D weak equation for `u(r) := r · radialProfile w r` with the
radial source `gprof(r) := radialProfile v r · (1 − radialProfile w r)`,
obtained by testing the 3D scattering equation with the radial function
`φ(x) := (χ‖x‖)/‖x‖`. -/
theorem scattering_1D_weak_equation {v w : ℝ³ → ℝ} {R₀ : ℝ} (hR₀ : 0 < R₀)
    (hvrad : IsRadial v) (hrad : IsRadial w) (hw : IsScatteringSolution w v) :
    ∀ (χ : ℝ → ℝ), ContDiff ℝ ∞ χ → HasCompactSupport χ →
      (∀ r : ℝ, χ r ≠ 0 → R₀ < r) →
      (∫ r in Set.Ioi (0 : ℝ), (r * radialProfile w r) * deriv (deriv χ) r)
        = -(1 / 2) * (∫ r in Set.Ioi (0 : ℝ),
            r * (radialProfile v r * (1 - radialProfile w r)) * χ r) := by
  intro χ hχ hχcs hχsup
  -- the radial test profile ψ := χ/r (smooth, compactly supported)
  let ψ : ℝ → ℝ := fun r : ℝ => χ r / r
  let φ : ℝ³ → ℝ := fun x : ℝ³ => ψ ‖x‖
  have hψc : ContDiff ℝ ∞ ψ := by
    dsimp [ψ]
    exact contDiff_div_self hR₀ hχ hχsup
  have hψcs : HasCompactSupport ψ := by
    dsimp [ψ]
    exact hasCompactSupport_div_self hχcs
  have hψsup : ∀ r : ℝ, ψ r ≠ 0 → R₀ < r := by
    dsimp [ψ]
    exact support_div_self_gt hχsup
  have hφ : ContDiff ℝ ∞ φ := by
    dsimp [φ]
    exact radialTest_contDiff hR₀ hψc hψsup
  have hφcs : HasCompactSupport φ := by
    dsimp [φ]
    exact radialTest_hasCompactSupport hR₀ hψcs hψsup
  -- the 3D weak scattering equation tested on the radial test function φ
  have heq := hw.eq φ ⟨hφ, hφcs⟩
  -- === Left-hand side: ∫ w·Δφ reduces to 4π·∫ u(r)·χ″(r) dr ===
  let gL : ℝ → ℝ := fun r => radialProfile w r * (deriv (deriv ψ) r + 2 * deriv ψ r / r)
  have hpointL (x : ℝ³) (hx : x ≠ 0) : w x * (Δ φ) x = gL ‖x‖ := by
    have hw' : w x = radialProfile w ‖x‖ := radial_eq_profile hrad x
    have hψ2 : ContDiffAt ℝ 2 ψ ‖x‖ := (contDiff_infty.mp hψc 2).contDiffAt
    have hφx : (Δ φ) x = deriv (deriv ψ) ‖x‖ + 2 * deriv ψ ‖x‖ / ‖x‖ := by
      dsimp [φ]
      exact radialTest_delta (x := x) hx hψ2
    dsimp [gL]
    rw [hw', hφx]
  have h_aeL : (fun x : ℝ³ => w x * (Δ φ) x) =ᵐ[volume] (fun x : ℝ³ => gL ‖x‖) := by
    change ∀ᵐ (x : ℝ³) ∂(volume : Measure ℝ³), w x * (Δ φ) x = gL ‖x‖
    rw [MeasureTheory.ae_iff]
    apply MeasureTheory.measure_mono_null
    · intro x hx
      rw [Set.mem_singleton_iff]
      by_contra hx0
      exact hx (hpointL x hx0)
    · exact MeasureTheory.NullSingletonClass.measure_singleton (x := (0 : ℝ³))
  have hcongL : (∫ x : ℝ³, w x * (Δ φ) x) = (∫ x : ℝ³, gL ‖x‖) :=
    MeasureTheory.integral_congr_ae h_aeL
  have hmainL : (∫ x : ℝ³, w x * (Δ φ) x) =
      4 * π * (∫ r in Set.Ioi (0 : ℝ), r ^ 2 * gL r) := by
    rw [hcongL]
    exact integral_fun_norm_r3 (g := gL)
  have hfunL : (fun r : ℝ => r ^ 2 * gL r) = (fun r : ℝ =>
      r ^ 2 * radialProfile w r * deriv (deriv ψ) r + 2 * r * radialProfile w r * deriv ψ r) := by
    funext r
    by_cases hr : r = 0
    · subst r
      simp [gL]
    · dsimp [gL]
      field_simp [hr]
  have hψ0 : ContDiff ℝ ∞ (fun t : ℝ => χ t / t) := by
    simpa [ψ] using hψc
  have hfunL2 : (fun r : ℝ =>
        r ^ 2 * radialProfile w r * deriv (deriv ψ) r + 2 * r * radialProfile w r * deriv ψ r)
      = (fun r : ℝ => (r * radialProfile w r) * deriv (deriv χ) r) := by
    funext r
    have hsid := snd_identity_div hχ hψ0 r
    dsimp [ψ]
    calc
      r ^ 2 * radialProfile w r * deriv (deriv (fun t : ℝ => χ t / t)) r
          + 2 * r * radialProfile w r * deriv (fun t : ℝ => χ t / t) r
          = radialProfile w r * (r ^ 2 * deriv (deriv (fun t : ℝ => χ t / t)) r
              + 2 * r * deriv (fun t : ℝ => χ t / t) r) := by ring
      _ = radialProfile w r * (r * deriv (deriv χ) r) := by rw [hsid]
      _ = (r * radialProfile w r) * deriv (deriv χ) r := by ring
  have hfunLtot : (fun r : ℝ => r ^ 2 * gL r) =
      (fun r : ℝ => (r * radialProfile w r) * deriv (deriv χ) r) := by
    exact hfunL.trans hfunL2
  have hconvL : (∫ r in Set.Ioi (0 : ℝ), r ^ 2 * gL r) =
      (∫ r in Set.Ioi (0 : ℝ), (r * radialProfile w r) * deriv (deriv χ) r) := by
    exact congrArg (fun h : ℝ → ℝ => ∫ r : ℝ in Set.Ioi (0 : ℝ), h r) hfunLtot
  have hmainL2 : (∫ x : ℝ³, w x * (Δ φ) x) =
      4 * π * (∫ r in Set.Ioi (0 : ℝ), (r * radialProfile w r) * deriv (deriv χ) r) := by
    rw [hmainL, hconvL]
  -- === Right-hand side: ∫ v(1−w)·φ reduces to 4π·∫ r·gprof(r)·χ(r) dr ===
  let gR : ℝ → ℝ := fun r => radialProfile v r * (1 - radialProfile w r) * ψ r
  have hpointR (x : ℝ³) (hx : x ≠ 0) : (v x * (1 - w x)) * φ x = gR ‖x‖ := by
    have hvx : v x = radialProfile v ‖x‖ := radial_eq_profile hvrad x
    have hwx : w x = radialProfile w ‖x‖ := radial_eq_profile hrad x
    dsimp [φ, gR, ψ]
    rw [hvx, hwx]
  have h_aeR : (fun x : ℝ³ => (v x * (1 - w x)) * φ x) =ᵐ[volume] (fun x : ℝ³ => gR ‖x‖) := by
    change ∀ᵐ (x : ℝ³) ∂(volume : Measure ℝ³), (v x * (1 - w x)) * φ x = gR ‖x‖
    rw [MeasureTheory.ae_iff]
    apply MeasureTheory.measure_mono_null
    · intro x hx
      rw [Set.mem_singleton_iff]
      by_contra hx0
      exact hx (hpointR x hx0)
    · exact MeasureTheory.NullSingletonClass.measure_singleton (x := (0 : ℝ³))
  have hcongR : (∫ x : ℝ³, (v x * (1 - w x)) * φ x) = (∫ x : ℝ³, gR ‖x‖) :=
    MeasureTheory.integral_congr_ae h_aeR
  have hmainR : (∫ x : ℝ³, (v x * (1 - w x)) * φ x) =
      4 * π * (∫ r in Set.Ioi (0 : ℝ), r ^ 2 * gR r) := by
    rw [hcongR]
    exact integral_fun_norm_r3 (g := gR)
  have hfunR : (fun r : ℝ => r ^ 2 * gR r) = (fun r : ℝ =>
      r * (radialProfile v r * (1 - radialProfile w r)) * χ r) := by
    funext r
    by_cases hr : r = 0
    · subst r
      simp [gR]
    · dsimp [gR, ψ]
      have hne : r ≠ 0 := hr
      field_simp [hne]
  have hconvR : (∫ r in Set.Ioi (0 : ℝ), r ^ 2 * gR r) =
      (∫ r in Set.Ioi (0 : ℝ), r * (radialProfile v r * (1 - radialProfile w r)) * χ r) := by
    exact congrArg (fun h : ℝ → ℝ => ∫ r : ℝ in Set.Ioi (0 : ℝ), h r) hfunR
  have hmainR2 : (∫ x : ℝ³, v x * (1 - w x) * φ x) =
      4 * π * (∫ r in Set.Ioi (0 : ℝ), r * (radialProfile v r * (1 - radialProfile w r)) * χ r) := by
    rw [hmainR, hconvR]
  -- === Combine: −4π·I₁ = (1/2)·4π·I₂, hence I₁ = −(1/2)·I₂ ===
  have hcore : -(4 * π * (∫ r in Set.Ioi (0 : ℝ), (r * radialProfile w r) * deriv (deriv χ) r))
      = (1 / 2) * (4 * π * (∫ r in Set.Ioi (0 : ℝ),
          r * (radialProfile v r * (1 - radialProfile w r)) * χ r)) := by
    calc
      -(4 * π * (∫ r in Set.Ioi (0 : ℝ), (r * radialProfile w r) * deriv (deriv χ) r))
          = -(∫ x : ℝ³, w x * (Δ φ) x) := by rw [hmainL2]
      _ = (1 / 2) * (∫ x : ℝ³, v x * (1 - w x) * φ x) := heq
      _ = (1 / 2) * (4 * π * (∫ r in Set.Ioi (0 : ℝ),
          r * (radialProfile v r * (1 - radialProfile w r)) * χ r)) := by rw [hmainR2]
  have hfac : (4 * π : ℝ) ≠ 0 :=
    mul_ne_zero (by norm_num : (4 : ℝ) ≠ 0) Real.pi_ne_zero
  have hneg : -(∫ r in Set.Ioi (0 : ℝ), (r * radialProfile w r) * deriv (deriv χ) r)
      = (1 / 2) * (∫ r in Set.Ioi (0 : ℝ),
          r * (radialProfile v r * (1 - radialProfile w r)) * χ r) := by
    apply (mul_left_cancel₀ hfac)
    calc
      4 * π * (-(∫ r in Set.Ioi (0 : ℝ), (r * radialProfile w r) * deriv (deriv χ) r))
          = -(4 * π * (∫ r in Set.Ioi (0 : ℝ), (r * radialProfile w r) * deriv (deriv χ) r)) := by
            ring
      _ = (1 / 2) * (4 * π * (∫ r in Set.Ioi (0 : ℝ),
          r * (radialProfile v r * (1 - radialProfile w r)) * χ r)) := hcore
      _ = 4 * π * ((1 / 2) * (∫ r in Set.Ioi (0 : ℝ),
          r * (radialProfile v r * (1 - radialProfile w r)) * χ r)) := by
            ring
  linarith

end Submission.BoseGases
