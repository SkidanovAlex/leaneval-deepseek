import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import ChallengeDeps
import Submission.RadialIntegral
import Submission.RadialLaplacian
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Smooth radial cutoffs and the Newtonian identity `∫ ‖x‖⁻¹ · Δθ = −4π`

Two calculus ingredients of the Gauss/shell identity that identifies the
exterior constant of a scattering solution with its scattering length
(`c = (8π)⁻¹·∫v(1−w)`):

1. **Existence of smooth radial cutoffs** (`exists_smooth_radial_cutoff`):
   for `0 < R < M` there is a radial smooth compactly-supported
   `θ : ℝ³ → ℝ` with `0 ≤ θ ≤ 1`, `θ x = 1` whenever `‖x‖ ≤ R` and
   `θ x = 0` whenever `M ≤ ‖x‖`.  Construct it as `θ(x) := σ ‖x‖` where
   `σ : ℝ → ℝ` is smooth with compact support, `σ ≡ 1` on `(-∞, R]`
   (hence even near `0`, so `θ` is smooth at `0`) and `σ ≡ 0` on
   `[M, ∞)`; build `σ` from a smooth monotone transition `τ` with
   `τ = 0` on `(-∞,0]`, `τ = 1` on `[1,∞)` (e.g. from a `ContDiffBump`
   mass-one bump supported in `(0,1)`: `τ(t) := ∫ x in Iic t, ρ x`), via
   `σ(r) := 1 − τ((r − R)/(M − R))`.

2. **Newtonian cutoff identity** (`integral_norm_inv_mul_delta_smooth`):
   for every smooth compactly-supported profile `σ : ℝ → ℝ` with
   `σ 0 = 1`, the radial function `θ(x) := σ‖x‖` satisfies

       ∫ x : ℝ³, (‖x‖)⁻¹ · (Δθ)(x) = −4π

   (i.e. `Δ(1/‖x‖) = −4π·δ₀` integrated against `θ`).  Radial route: on
   `x ≠ 0`, `Δθ x = σ''‖x‖ + 2·σ'‖x‖/‖x‖` (`RadialLaplacian`), and with
   `d(‖x‖) = 4πr²dr` (`RadialIntegral`):
   `∫ (1/r)·[σ''(r) + 2σ'(r)/r]·4πr² dr = 4π∫₀^∞ [r·σ'' + 2σ'] dr
   = 4π∫₀^∞ [(rσ')' + σ'] dr = 4π·(σ(∞) − σ(0)) = −4π`.
-/

noncomputable section

open _root_.BoseGases
set_option autoImplicit false

namespace Submission.BoseGases

open Filter Metric MeasureTheory Laplacian
open scoped ContDiff Topology Real

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- One-dimensional smooth cutoff: for `a < b` there is a smooth `ψ : ℝ → ℝ` with
`0 ≤ ψ ≤ 1`, `ψ ≡ 1` on `(-∞, a]` and `ψ ≡ 0` on `[b, ∞)`.  Built from
`Real.smoothTransition` as `ψ(t) = 1 − τ((t − a)/(b − a))`. -/
lemma one_dim_cutoff {a b : ℝ} (hab : a < b) :
    ∃ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ ∧ (∀ t, 0 ≤ ψ t) ∧ (∀ t, ψ t ≤ 1) ∧
      (∀ t, t ≤ a → ψ t = 1) ∧ (∀ t, b ≤ t → ψ t = 0) := by
  let ψ : ℝ → ℝ := fun t => 1 - Real.smoothTransition ((t - a) / (b - a))
  have hbma : b - a ≠ 0 := sub_ne_zero.mpr (ne_of_gt hab)
  refine ⟨ψ, ?_, ?_, ?_, ?_, ?_⟩
  · have hτc : ContDiff ℝ ∞ Real.smoothTransition := Real.smoothTransition.contDiff
    have hden : ContDiff ℝ ∞ (fun _ : ℝ => b - a) := contDiff_const
    have hnum : ContDiff ℝ ∞ (fun t : ℝ => t - a) := contDiff_id.sub contDiff_const
    have hdiv : ContDiff ℝ ∞ (fun t : ℝ => (t - a) / (b - a)) := ContDiff.div hnum hden (fun _ => hbma)
    have h1 : ContDiff ℝ ∞ (fun t : ℝ => Real.smoothTransition ((t - a) / (b - a))) := hτc.comp hdiv
    simpa [ψ] using contDiff_const.sub h1
  · intro t
    dsimp [ψ]
    linarith [Real.smoothTransition.le_one ((t - a) / (b - a))]
  · intro t
    dsimp [ψ]
    linarith [Real.smoothTransition.nonneg ((t - a) / (b - a))]
  · intro t ht
    dsimp [ψ]
    have hden : 0 < b - a := sub_pos.mpr hab
    have hnumle : t - a ≤ 0 := sub_nonpos.mpr ht
    have harg : (t - a) / (b - a) ≤ 0 := (div_le_iff₀ hden).2 (by simpa using hnumle)
    rw [Real.smoothTransition.zero_of_nonpos harg]
    norm_num
  · intro t ht
    dsimp [ψ]
    have hden : 0 < b - a := sub_pos.mpr hab
    have harg : 1 ≤ (t - a) / (b - a) := by
      rw [one_le_div hden]
      linarith
    rw [Real.smoothTransition.one_of_one_le harg]
    norm_num

/-- Existence of a smooth radial cutoff: `θ ≡ 1` on `{‖x‖ ≤ R}` and
`θ ≡ 0` on `{M ≤ ‖x‖}`, with `0 ≤ θ ≤ 1`, smooth, compactly supported,
radial.  Constructed as `θ(x) = ψ ‖x‖²` with the one-dimensional `ψ`
of `one_dim_cutoff` (composition with the smooth map `x ↦ ‖x‖²` makes
`θ` smooth at the origin without any flatness condition on the profile). -/
theorem exists_smooth_radial_cutoff {R M : ℝ} (hR : 0 < R) (hRM : R < M) :
    ∃ θ : ℝ³ → ℝ,
      ContDiff ℝ ∞ θ ∧ HasCompactSupport θ ∧ (∀ x : ℝ³, 0 ≤ θ x) ∧
      (∀ x : ℝ³, θ x ≤ 1) ∧ IsRadial θ ∧
      (∀ x : ℝ³, ‖x‖ ≤ R → θ x = 1) ∧
      (∀ x : ℝ³, M ≤ ‖x‖ → θ x = 0) := by
  let a : ℝ := R ^ 2
  let b : ℝ := M ^ 2
  have hab : a < b := by
    dsimp [a, b]
    have hMR : 0 < M - R := sub_pos.mpr hRM
    have hsum : 0 < M + R := add_pos (lt_trans hR hRM) hR
    have hdiff : 0 < M ^ 2 - R ^ 2 := by
      rw [sq_sub_sq]
      positivity
    linarith
  obtain ⟨ψ, hψc, hψ0, hψ1, hψle, hψge⟩ := one_dim_cutoff hab
  let θ : ℝ³ → ℝ := fun x => ψ (‖x‖ ^ 2)
  have hθone : ∀ x : ℝ³, ‖x‖ ≤ R → θ x = 1 := by
    intro x hx
    have hmul : ‖x‖ ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ (norm_nonneg x) hx 2
    have : ‖x‖ ^ 2 ≤ a := by simpa [a] using hmul
    dsimp [θ]
    exact hψle (‖x‖ ^ 2) this
  have hθzero : ∀ x : ℝ³, M ≤ ‖x‖ → θ x = 0 := by
    intro x hx
    have hMle : 0 ≤ M := le_of_lt (lt_trans hR hRM)
    have hmul : M ^ 2 ≤ ‖x‖ ^ 2 := pow_le_pow_left₀ hMle hx 2
    have : b ≤ ‖x‖ ^ 2 := by simpa [b] using hmul
    dsimp [θ]
    exact hψge (‖x‖ ^ 2) this
  refine ⟨θ, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hnsq : ContDiff ℝ ∞ (fun x : ℝ³ => ‖x‖ ^ 2) := contDiff_norm_sq ℝ
    exact hψc.comp hnsq
  · refine HasCompactSupport.intro' (ProperSpace.isCompact_closedBall (0 : ℝ³) M) ?_ ?_
    · exact isClosed_closedBall
    · intro x hxK
      have hMx : M < ‖x‖ := by
        have hd : M < dist x 0 := by
          rw [Metric.mem_closedBall] at hxK
          exact not_le.mp hxK
        simpa [dist_eq_norm] using hd
      exact hθzero x (le_of_lt hMx)
  · intro x
    dsimp [θ]
    exact hψ0 (‖x‖ ^ 2)
  · intro x
    dsimp [θ]
    exact hψ1 (‖x‖ ^ 2)
  · intro x y hxy
    dsimp [θ]
    apply congrArg ψ
    rw [hxy]
  · exact hθone
  · exact hθzero

/-- One-dimensional core of the Newtonian identity: for smooth compactly-supported
`σ`, `∫₀^∞ (r σ''(r) + 2σ'(r)) dr = −σ(0)`.  The integrand is the derivative of
`r ↦ rσ'(r) + σ(r)`, whose value at `0` is `σ 0` and which vanishes at infinity. -/
lemma radial_one_dimensional {σ : ℝ → ℝ} (hσ : ContDiff ℝ ∞ σ) (hσcs : HasCompactSupport σ) :
    (∫ r in Set.Ioi (0 : ℝ), (r * deriv (deriv σ) r + 2 * deriv σ r)) = -σ 0 := by
  let F : ℝ → ℝ := fun r => r * deriv σ r + σ r
  have hσd : ContDiff ℝ ∞ (deriv σ) := (contDiff_infty_iff_deriv.mp hσ).2
  have hid : ContDiff ℝ ∞ (fun r : ℝ => r) := contDiff_id
  have hFcTop : ContDiff ℝ ∞ F := by
    have hmul : ContDiff ℝ ∞ (fun r : ℝ => r * deriv σ r) := ContDiff.mul hid hσd
    have hsum : ContDiff ℝ ∞ (fun r : ℝ => r * deriv σ r + σ r) := ContDiff.add hmul hσ
    exact hsum
  have hFc : ContDiff ℝ 1 F := hFcTop.of_le (by norm_num : (1 : ℕ∞ω) ≤ ∞)
  have hFcs : HasCompactSupport F := by
    have hprod : HasCompactSupport (fun r : ℝ => r * deriv σ r) :=
      HasCompactSupport.mul_left (f := fun r : ℝ => r) (HasCompactSupport.deriv hσcs)
    have hsum : HasCompactSupport (fun r : ℝ => r * deriv σ r + σ r) :=
      HasCompactSupport.add hprod hσcs
    exact hsum
  have hFint : (∫ r in Set.Ioi (0 : ℝ), deriv F r) = -F 0 :=
    HasCompactSupport.integral_Ioi_deriv_eq hFc hFcs 0
  have hH : ∀ r : ℝ, HasDerivAt F (r * deriv (deriv σ) r + 2 * deriv σ r) r := by
    intro r
    change HasDerivAt (fun t : ℝ => t * deriv σ t + σ t)
        (r * deriv (deriv σ) r + 2 * deriv σ r) r
    have hder : HasDerivAt (deriv σ) (deriv (deriv σ) r) r := by
      have hdf : DifferentiableAt ℝ (deriv σ) r :=
        (hσd.contDiffAt.of_le (by norm_num : (1 : ℕ∞ω) ≤ ∞)).differentiableAt
          (by norm_num : (1 : ℕ∞ω) ≠ 0)
      exact hdf.hasDerivAt
    have hprod : HasDerivAt (fun t : ℝ => t * deriv σ t) (deriv σ r + r * deriv (deriv σ) r) r := by
      have hmul : HasDerivAt (id * deriv σ) (1 * deriv σ r + id r * deriv (deriv σ) r) r :=
        HasDerivAt.mul (hasDerivAt_id r) hder
      change HasDerivAt (fun t : ℝ => id t * deriv σ t) (1 * deriv σ r + id r * deriv (deriv σ) r) r at hmul
      simpa [id_eq, one_mul] using hmul
    have hσa : HasDerivAt σ (deriv σ r) r := by
      have hdf : DifferentiableAt ℝ σ r :=
        (hσ.contDiffAt.of_le (by norm_num : (1 : ℕ∞ω) ≤ ∞)).differentiableAt
          (by norm_num : (1 : ℕ∞ω) ≠ 0)
      exact hdf.hasDerivAt
    have hsum : HasDerivAt ((fun t : ℝ => t * deriv σ t) + σ)
        (deriv σ r + r * deriv (deriv σ) r + deriv σ r) r :=
      HasDerivAt.add hprod hσa
    convert hsum using 1
    all_goals first | rfl | (ext t; rfl) | ring
  have hdeq : (fun r : ℝ => r * deriv (deriv σ) r + 2 * deriv σ r) = deriv F := by
    funext r
    exact ((hH r).deriv).symm
  calc
    (∫ r in Set.Ioi (0 : ℝ), (r * deriv (deriv σ) r + 2 * deriv σ r))
        = ∫ r in Set.Ioi (0 : ℝ), deriv F r := by
          rw [hdeq]
    _ = -F 0 := hFint
    _ = -σ 0 := by simp [F]

/-- Newtonian identity for smooth radial cutoffs: for a smooth
compactly-supported profile `σ` with `σ 0 = 1`,
`∫ x, ‖x‖⁻¹ · Δ(σ‖·‖) x = −4π`. -/
theorem integral_norm_inv_mul_delta_smooth {σ : ℝ → ℝ} (hσ : ContDiff ℝ ∞ σ)
    (hσcs : HasCompactSupport σ) (hσ0 : σ 0 = 1) :
    (∫ x : ℝ³, (‖x‖ : ℝ)⁻¹ * ((Δ fun y : ℝ³ => σ ‖y‖) x)) = -4 * π := by
  let R : ℝ → ℝ := fun r => r⁻¹ * (deriv (deriv σ) r + 2 * deriv σ r / r)
  have hpt : ∀ x : ℝ³, (‖x‖ : ℝ)⁻¹ * ((Δ fun y : ℝ³ => σ ‖y‖) x) = R ‖x‖ := by
    intro x
    by_cases hx0 : x = 0
    · subst x
      simp [R, inv_zero]
    · have hf2 : ContDiffAt ℝ 2 σ ‖x‖ :=
        (hσ.contDiffAt).of_le (by decide : (2 : ℕ∞ω) ≤ ∞)
      have hlap := laplacian_radial_norm (f := σ) (x := x) hx0 hf2
      rw [hlap]
  calc
    (∫ x : ℝ³, (‖x‖ : ℝ)⁻¹ * ((Δ fun y : ℝ³ => σ ‖y‖) x))
        = ∫ x : ℝ³, R ‖x‖ := by
          congr 1
          funext x
          exact hpt x
    _ = 4 * π * (∫ r in Set.Ioi (0 : ℝ), r ^ 2 * R r) := by
          rw [integral_fun_norm_r3 (g := R)]
    _ = 4 * π * (∫ r in Set.Ioi (0 : ℝ), (r * deriv (deriv σ) r + 2 * deriv σ r)) := by
          congr 1
          refine MeasureTheory.setIntegral_congr_ae measurableSet_Ioi ?_
          refine ae_of_all _ ?_
          intro r hr
          have hrne : r ≠ 0 := ne_of_gt hr
          unfold R
          field_simp [hrne]
    _ = 4 * π * -σ 0 := by rw [radial_one_dimensional hσ hσcs]
    _ = 4 * π * -1 := by rw [hσ0]
    _ = -4 * π := by ring

end Submission.BoseGases
