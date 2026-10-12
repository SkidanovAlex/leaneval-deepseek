import Mathlib
import ChallengeDeps
import Submission.RadialCutoff
import Submission.ScatExterior
import Submission.ScatteringDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Gauss/shell identity: exterior constant = scattering length (Layer 3)

Let `w` be a scattering solution of a radial-support potential `v`
(`tsupport v ⊆ ball 0 R`) and suppose `w x = c / ‖x‖` a.e. on the exterior
`{x | R ≤ ‖x‖}` (as supplied by `ScatExterior.scattering_solution_exterior_form`).
Testing the scattering equation with a smooth radial cutoff
`θ ≡ 1` on `ball(0,R)`, `θ ≡ 0` outside `ball(0,M)` gives

    (1/2)∫v(1−w) = (1/2)∫v(1−w)·θ = −∫w·Δθ = c·∫(1/‖x‖)·Δθ = 4π·c

where `∫(1/‖x‖)·Δθ = −4π` is the Newtonian identity of
`Submission.RadialCutoff` (`integral_norm_inv_mul_delta_smooth`, via the
radial corollary `radial_delta_norm_inv` below).  Hence

    c = (8π)⁻¹ · ∫ v(1−w),

the classical scattering-length formula.  Combining this with
`ScatteringDefs.a_eq_integral_of_exists` (the defining identity of `a v` for
the *chosen* scattering solution) will give `w₀ = a v / ‖x‖` a.e. on the
exterior for the chosen solution and `∫v(1−w₀) = 8π·a v`.

## Route for `radial_delta_norm_inv`
Let `σ := radialProfile θ`.  `σ` is smooth (`ContDiff.comp` with the linear
map `r ↦ r•radU0`), compactly supported (`θ` radially compactly supported),
`σ 0 = θ 0 = 1`, and `θ = σ∘‖·‖` pointwise (`radial_eq_profile`), so
`integral_norm_inv_mul_delta_smooth` applies verbatim after a congr.

## Route for `scattering_flux`
1. Pick `M > R` and the cutoff `θ` from
   `RadialCutoff.exists_smooth_radial_cutoff` (so `θ` smooth, HCS,
   radial, `θ ≡ 1` on `{‖x‖ ≤ R}`, `θ ≡ 0` on `{M ≤ ‖x‖}`).
2. `hw.eq θ`: `−∫w·Δθ = (1/2)∫v(1−w)·θ`.
3. RHS: pointwise `v(1−w)·θ = v(1−w)` (where `v ≠ 0` we have `‖x‖ < R`).
4. LHS: pointwise `Δθ = 0` off the shell `{R ≤ ‖x‖}` (θ locally constant
   inside the ball and outside the big ball), and on the shell `w = c/‖x‖`
   a.e. (`hform`), so `∫w·Δθ = c·∫(1/‖x‖)·Δθ = c·(−4π)` by
   `radial_delta_norm_inv`.  Then solve for `c`.
-/

noncomputable section

open _root_.BoseGases
set_option autoImplicit false

namespace Submission.BoseGases

open Filter Metric MeasureTheory Laplacian
open scoped ContDiff Topology Real

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- The radial profile of a smooth function is smooth: `radialProfile θ` is
`θ` composed with the smooth linear map `r ↦ r • radU0`. -/
lemma radialProfile_contDiff {θ : ℝ³ → ℝ} (hθ : ContDiff ℝ ∞ θ) :
    ContDiff ℝ ∞ (radialProfile θ) := by
  have hsmul : ContDiff ℝ ∞ (fun r : ℝ => r • radU0) := by
    have hf : ContDiff ℝ ∞ (fun r : ℝ => r) := contDiff_id
    have hg : ContDiff ℝ ∞ (fun _ : ℝ => radU0) := contDiff_const
    convert (ContDiff.smul (𝕜 := ℝ) hf hg) using 1
    all_goals (funext r; rfl)
  unfold radialProfile
  exact hθ.comp hsmul

/-- The radial profile of a compactly supported function is compactly
supported: if `θ (r • radU0) ≠ 0` then `r • radU0 ∈ tsupport θ`, a bounded
set, so `|r|` is bounded. -/
lemma radialProfile_hasCompactSupport {θ : ℝ³ → ℝ} (hθcs : HasCompactSupport θ) :
    HasCompactSupport (radialProfile θ) := by
  let K : Set ℝ³ := tsupport θ
  have hKbdd : Bornology.IsBounded K := IsCompact.isBounded hθcs
  obtain ⟨B, hKsub⟩ := Bornology.IsBounded.subset_closedBall hKbdd (0 : ℝ³)
  let B₀ : ℝ := max B 0
  have hB₀ : 0 ≤ B₀ := le_max_right B 0
  have hKsub₀ : K ⊆ Metric.closedBall (0 : ℝ³) B₀ := by
    have hmono : Metric.closedBall (0 : ℝ³) B ⊆ Metric.closedBall (0 : ℝ³) B₀ :=
      Metric.closedBall_subset_closedBall (le_max_left B 0)
    exact hKsub.trans hmono
  refine HasCompactSupport.intro' (ProperSpace.isCompact_closedBall (0 : ℝ) B₀) isClosed_closedBall ?_
  intro r hrK
  by_contra hne
  have hsupp : r • radU0 ∈ Function.support θ := by
    simpa [Function.support, radialProfile] using hne
  have hmemK : r • radU0 ∈ K := subset_tsupport θ hsupp
  have hball : r • radU0 ∈ Metric.closedBall (0 : ℝ³) B₀ := hKsub₀ hmemK
  have hnorm : ‖r • radU0‖ ≤ B₀ := by
    simpa [Metric.mem_closedBall, dist_zero_right] using hball
  have habs : |r| ≤ B₀ := by
    simpa [norm_smul_radU0] using hnorm
  have hrb : r ∈ Metric.closedBall (0 : ℝ) B₀ := by
    simpa [Metric.mem_closedBall, dist_zero_right] using habs
  exact hrK hrb

/-- If `θ ≡ 1` on the closed ball `{‖x‖ ≤ R}`, then `θ` is constant (equal
to one) in a neighbourhood of every point with `‖x‖ < R`, so its Laplacian
vanishes there. -/
lemma laplacian_eq_zero_of_norm_lt {θ : ℝ³ → ℝ} {R : ℝ}
    (hθone : ∀ x : ℝ³, ‖x‖ ≤ R → θ x = 1) {x : ℝ³} (hx : ‖x‖ < R) : (Δ θ) x = 0 := by
  have hnh : Metric.ball (0 : ℝ³) R ∈ 𝓝 x :=
    Metric.isOpen_ball.mem_nhds (by simpa [Metric.mem_ball, dist_zero_right] using hx)
  have hloc : θ =ᶠ[𝓝 x] (fun _ : ℝ³ => (1 : ℝ)) := by
    filter_upwards [hnh] with y hy
    have hyle : ‖y‖ ≤ R := le_of_lt (by simpa [Metric.mem_ball, dist_zero_right] using hy)
    exact hθone y hyle
  have hcongr := InnerProductSpace.laplacian_congr_nhds (E := ℝ³) (f₁ := θ) (f₂ := (fun _ : ℝ³ => (1 : ℝ))) hloc
  have hval := hcongr.eq_of_nhds
  simpa using hval

/-- Newtonian identity in radial-function form: for a smooth, compactly
supported, radial `θ : ℝ³ → ℝ` with `θ 0 = 1`,
`∫ x, ‖x‖⁻¹ · (Δθ) x = −4π`. -/
theorem radial_delta_norm_inv {θ : ℝ³ → ℝ} (hθ : ContDiff ℝ ∞ θ)
    (hθcs : HasCompactSupport θ) (hradθ : IsRadial θ) (hθ0 : θ 0 = 1) :
    (∫ x : ℝ³, (‖x‖ : ℝ)⁻¹ * ((Δ θ) x)) = -4 * π := by
  let σ : ℝ → ℝ := radialProfile θ
  have hσc : ContDiff ℝ ∞ σ := by
    dsimp [σ]
    exact radialProfile_contDiff hθ
  have hσcs : HasCompactSupport σ := by
    dsimp [σ]
    exact radialProfile_hasCompactSupport hθcs
  have hσ0 : σ 0 = 1 := by
    dsimp [σ]
    simp [radialProfile, hθ0]
  have hθeq : θ = (fun y : ℝ³ => σ ‖y‖) := by
    funext y
    simpa [σ] using (radial_eq_profile hradθ y)
  rw [hθeq]
  exact integral_norm_inv_mul_delta_smooth hσc hσcs hσ0

/-- The exterior constant of a scattering solution is its scattering length:
`w x = c/‖x‖` a.e. on `{x | R ≤ ‖x‖}` forces
`c = (8π)⁻¹ · ∫ v(1−w)`. -/
theorem scattering_flux {v w : ℝ³ → ℝ} {R : ℝ} (hR : 0 < R)
    (hrad : IsRadial w) (hw : IsScatteringSolution w v)
    (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R) {c : ℝ}
    (hform : ∀ᵐ x : ℝ³, R ≤ ‖x‖ → w x = c / ‖x‖) :
    c = (1 / (8 * π)) * (∫ x : ℝ³, v x * (1 - w x)) := by
  obtain ⟨M, hRM⟩ : ∃ M : ℝ, R < M := ⟨R + 1, by linarith⟩
  rcases exists_smooth_radial_cutoff (R := R) (M := M) hR hRM with
    ⟨θ, hθ, hθcs, hθnonneg, hθle1, hθrad, hθone, hθzero⟩
  have hθ0 : θ 0 = 1 := hθone 0 (by simpa using le_of_lt hR)
  -- step 3: on the support of v the cutoff equals one, so θ is inert
  have hrhs : (∫ x : ℝ³, v x * (1 - w x) * θ x) = ∫ x : ℝ³, v x * (1 - w x) := by
    have hpt : (fun x : ℝ³ => v x * (1 - w x) * θ x) = (fun x : ℝ³ => v x * (1 - w x)) := by
      funext x
      by_cases hvx : v x = 0
      · simp [hvx]
      · have hxsupp : x ∈ Function.support v := by simpa [Function.support] using hvx
        have hxt : x ∈ tsupport v := subset_tsupport v hxsupp
        have hxb : x ∈ ball (0 : ℝ³) R := hv_supp hxt
        have hnorm : ‖x‖ < R := by simpa [Metric.mem_ball, dist_zero_right] using hxb
        have hθx : θ x = 1 := hθone x (le_of_lt hnorm)
        rw [hθx]
        ring
    rw [hpt]
  -- step 4: w·Δθ = c·(‖·‖⁻¹·Δθ) a.e. (hform on the shell, Δθ = 0 inside)
  have hae : (fun x : ℝ³ => w x * (Δ θ) x) =ᵐ[volume]
      (fun x : ℝ³ => c * ((‖x‖ : ℝ)⁻¹ * (Δ θ) x)) := by
    filter_upwards [hform] with x hx
    by_cases hRle : R ≤ ‖x‖
    · have hwx : w x = c / ‖x‖ := hx hRle
      rw [hwx]
      rw [div_eq_mul_inv]
      ring
    · have hlt : ‖x‖ < R := lt_of_not_ge hRle
      have hΔ0 : (Δ θ) x = 0 := laplacian_eq_zero_of_norm_lt hθone hlt
      simp [hΔ0]
  have hlhs : (∫ x : ℝ³, w x * (Δ θ) x) = c * (∫ x : ℝ³, (‖x‖ : ℝ)⁻¹ * (Δ θ) x) := by
    calc
      (∫ x : ℝ³, w x * (Δ θ) x)
          = ∫ x : ℝ³, c * ((‖x‖ : ℝ)⁻¹ * (Δ θ) x) := MeasureTheory.integral_congr_ae hae
      _ = c * (∫ x : ℝ³, (‖x‖ : ℝ)⁻¹ * (Δ θ) x) := MeasureTheory.integral_const_mul c _
  -- weak equation for the test function θ
  have weq := hw.eq θ ⟨hθ, hθcs⟩
  have hnewt := radial_delta_norm_inv hθ hθcs hθrad hθ0
  have hwΔ : (∫ x : ℝ³, w x * (Δ θ) x) = -4 * π * c := by
    rw [hlhs, hnewt]
    ring
  have hweq2 : -(-4 * π * c) = (1 / 2) * (∫ x : ℝ³, v x * (1 - w x)) := by
    rw [hwΔ] at weq
    rw [hrhs] at weq
    exact weq
  have hmain : (∫ x : ℝ³, v x * (1 - w x)) = 8 * π * c := by
    linarith
  have h8ne : (8 * π : ℝ) ≠ 0 := mul_ne_zero (by norm_num) Real.pi_ne_zero
  field_simp [h8ne]
  linarith [hmain]

end Submission.BoseGases
