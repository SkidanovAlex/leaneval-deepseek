import ChallengeDeps
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Algebra.Order.Star.Real
import Submission.ExteriorClassify
import Submission.RadialCutoff
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Radial weakly-harmonic functions on all of `ℝ³` are constant (Layer 3)

The exterior classification `ExteriorClassify.exterior_harmonic_classification`
shows that a radial, locally integrable function that is *weakly harmonic on
the exterior region* `{x | R ≤ ‖x‖}` (and decays at infinity) is of the form
`c/‖x‖` a.e. there.  This module upgrades that result to functions that are
weakly harmonic on **all** of `ℝ³`: then the constant `c` must vanish, because
a `c/‖x‖` singularity at the origin would violate weak harmonicity there
(the distribution `Δ(1/‖x‖) = −4π·δ₀` is detected by the Newtonian cutoff
identity `RadialCutoff.radial_delta_norm_inv`: for a smooth radial cutoff
`θ ≡ 1` near `0` with `θ 0 = 1`, `∫ ‖x‖⁻¹·Δθ = −4π`).

**Theorem** (`radial_weaklyHarmonic_eq_zero`): if `w : ℝ³ → ℝ` is radial,
locally integrable, weakly harmonic on all of `ℝ³` (`∫w·Δφ = 0` for every
smooth compactly supported `φ`, with no support restriction), and decays to
zero at infinity, then `w = 0` almost everywhere.

## Proof route
1. Fix `ε > 0`.  The weak-harmonicity hypothesis restricted to test functions
   with `tsupport φ ⊆ {x | ε ≤ ‖x‖}` gives the hypothesis of
   `exterior_harmonic_classification` with `R := ε`, yielding
   `c_ε : ℝ` with `∀ᵐ x, ε ≤ ‖x‖ → w x = c_ε / ‖x‖`.
2. **The δ-test at the origin.**  Pick `M > ε` and the cutoff
   `θ = exists_smooth_radial_cutoff (R := ε) (M := M)` (smooth, compactly
   supported, radial, `θ ≡ 1` on `{‖x‖ ≤ ε}`, `θ ≡ 0` on `{M ≤ ‖x‖}`); then
   `θ 0 = 1`.  Weak harmonicity gives `∫ w·Δθ = 0`.
   Since `Δθ = 0` for `‖x‖ < ε` (`θ` locally constant `1` there) and for
   `‖x‖ > M`, the integrand `w·Δθ` agrees a.e. with `c_ε·(‖·‖⁻¹·Δθ)` (from
   the a.e. exterior form on the shell where `Δθ` may be nonzero), so
   `0 = ∫w·Δθ = c_ε·∫‖x‖⁻¹·Δθ = c_ε·(−4π)`, whence `c_ε = 0` (`π ≠ 0`).
3. Therefore `∀ᵐ x, ε ≤ ‖x‖ → w x = 0` for every `ε > 0`.  Take the countable
   family `ε_n = 1/(n+1)`: `{x | x ≠ 0} = ⋃ₙ {x | ε_n ≤ ‖x‖}` (each nonzero
   `x` has some `1/(n+1) ≤ ‖x‖`), so `w = 0` a.e. on `{x | x ≠ 0}`; the origin
   is a null set, hence `w =ᵐ[volume] 0` on all of `ℝ³`.
-/

noncomputable section

open _root_.BoseGases
set_option autoImplicit false

namespace Submission.BoseGases

open Filter Metric MeasureTheory Laplacian
open scoped ContDiff Topology Real RealInnerProductSpace

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- The derivative of a function equal to a constant in a neighbourhood of `x`
vanishes at `x`. -/
lemma deriv_eq_zero_of_eventually_eq_const {f : ℝ → ℝ} {x c : ℝ} (h : f =ᶠ[𝓝 x] fun _ : ℝ => c) :
    deriv f x = 0 := by
  have hd : HasDerivAt f 0 x := (hasDerivAt_const x c).congr_of_eventuallyEq h
  exact hd.deriv

/-- First derivative vanishes at points where the function is pointwise
constant on an open interval around the point. -/
lemma deriv_eq_zero_of_const_on_Ioo {σ : ℝ → ℝ} {lo hi c r : ℝ}
    (hσ : ∀ y : ℝ, y ∈ Set.Ioo lo hi → σ y = c) (hr : r ∈ Set.Ioo lo hi) :
    deriv σ r = 0 := by
  apply deriv_eq_zero_of_eventually_eq_const (f := σ) (x := r) (c := c)
  exact eventuallyEq_of_mem (isOpen_Ioo.mem_nhds hr) (by intro y hy; exact hσ y hy)

/-- Second derivative vanishes at points where the function is pointwise
constant on an open interval around the point. -/
lemma deriv_two_eq_zero_of_const_on_Ioo {σ : ℝ → ℝ} {lo hi c r : ℝ}
    (hσ : ∀ y : ℝ, y ∈ Set.Ioo lo hi → σ y = c) (hr : r ∈ Set.Ioo lo hi) :
    deriv (deriv σ) r = 0 := by
  have hder_pt : ∀ y : ℝ, y ∈ Set.Ioo lo hi → deriv σ y = 0 := by
    intro y hy
    exact deriv_eq_zero_of_const_on_Ioo (σ := σ) (lo := lo) (hi := hi) (c := c) hσ hy
  have hder : deriv σ =ᶠ[𝓝 r] (fun _ : ℝ => (0 : ℝ)) := by
    exact eventuallyEq_of_mem (isOpen_Ioo.mem_nhds hr) (by intro y hy; exact hder_pt y hy)
  exact deriv_eq_zero_of_eventually_eq_const (f := deriv σ) (x := r) (c := 0) hder

/-- Per-radius stage of the proof of `radial_weaklyHarmonic_eq_zero`: for any
radius `ε > 0`, a radial weakly harmonic decaying function vanishes almost
everywhere on the exterior `{x | ε ≤ ‖x‖}`.

The proof is the δ-test at the origin: the exterior classification gives
`w x = c / ‖x‖` a.e. on `{ε ≤ ‖x‖}`; testing weak harmonicity against a smooth
compactly supported radial cutoff `θ = σ‖·‖` that equals `1` on the ball of
radius `ε` and `0` outside `{‖x‖ ≤ M}` gives `∫ w·Δθ = 0`; since `Δθ = 0` on
the punctured ball `{0 < ‖x‖ < ε}` (radial Laplacian of the locally constant
`σ`) and `w = c/‖x‖` a.e. on the shell, `∫ w·Δθ = c·∫‖x‖⁻¹·Δθ = −4πc`
(Newtonian identity `integral_norm_inv_mul_delta_smooth`), whence `c = 0`. -/
lemma radial_weaklyHarmonic_exterior_zero {w : ℝ³ → ℝ} (hrad : IsRadial w)
    (hwli : LocallyIntegrable w)
    (hwh : ∀ φ : ℝ³ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → (∫ x : ℝ³, w x * (Δ φ) x) = 0)
    (hwlim : Tendsto w (cocompact ℝ³) (𝓝 0)) {ε : ℝ} (hε : 0 < ε) :
    ∀ᵐ x : ℝ³, ε ≤ ‖x‖ → w x = 0 := by
  -- step 1: exterior classification at radius ε
  rcases exterior_harmonic_classification (w := w) (R := ε) hε hrad hwli
    (by intro φ hφ hφcs _; exact hwh φ hφ hφcs) hwlim with ⟨c, hwc⟩
  -- step 2: δ-test at the origin with the radial cutoff θ = σ‖·‖
  let M : ℝ := ε + 1
  have hεM : ε < M := by dsimp [M]; linarith
  have hab : ε ^ 2 < M ^ 2 := by dsimp [M]; nlinarith [hε]
  obtain ⟨ψ, hψc, _hψ0le, _hψ1le, hψle, hψge⟩ := one_dim_cutoff (a := ε ^ 2) (b := M ^ 2) hab
  let σ : ℝ → ℝ := fun r => ψ (r ^ 2)
  let θ : ℝ³ → ℝ := fun x => σ ‖x‖
  have hσ0 : σ 0 = 1 := by
    simpa [σ] using hψle 0 (sq_nonneg ε)
  have hσext : ∀ r : ℝ, M ≤ |r| → σ r = 0 := by
    intro r hr
    dsimp [σ]
    apply hψge
    have hM0 : 0 ≤ M := le_of_lt (lt_trans hε hεM)
    have hm : M ^ 2 ≤ |r| ^ 2 := pow_le_pow_left₀ hM0 hr 2
    simpa using hm
  have hσone : ∀ r : ℝ, |r| < ε → σ r = 1 := by
    intro r hr
    dsimp [σ]
    apply hψle
    have h : |r| ≤ |ε| := by simpa [abs_of_pos hε] using (le_of_lt hr)
    exact (sq_le_sq).2 h
  have hσc : ContDiff ℝ ∞ σ := by
    dsimp [σ]
    exact hψc.comp (ContDiff.pow contDiff_id 2)
  have hσcs : HasCompactSupport σ := by
    have hKIcc : IsCompact (Set.Icc (-M) M) := isCompact_Icc
    refine HasCompactSupport.intro' hKIcc isClosed_Icc ?_
    intro r hr
    have hMle : M ≤ |r| := by
      by_contra h
      exact hr (abs_le.mp (le_of_lt (lt_of_not_ge h)))
    exact hσext r hMle
  have hθc : ContDiff ℝ ∞ θ := by
    dsimp [θ, σ]
    exact hψc.comp (contDiff_norm_sq ℝ)
  have hθzero : ∀ x : ℝ³, M ≤ ‖x‖ → θ x = 0 := by
    intro x hx
    dsimp [θ]
    exact hσext ‖x‖ (by simpa [abs_of_nonneg (norm_nonneg x)] using hx)
  have hθcs : HasCompactSupport θ := by
    refine HasCompactSupport.intro' (ProperSpace.isCompact_closedBall (0 : ℝ³) M) (isClosed_closedBall) ?_
    intro x hxK
    have hMx : M < ‖x‖ := by
      have hd : M < dist x 0 := by
        rw [Metric.mem_closedBall] at hxK
        exact not_le.mp hxK
      simpa [dist_eq_norm] using hd
    exact hθzero x (le_of_lt hMx)
  -- Δθ = 0 on the punctured ball {0 < ‖x‖ < ε}
  have hdeltazero : ∀ x : ℝ³, x ≠ 0 → ‖x‖ < ε → (Δ θ) x = 0 := by
    intro x hx0 hxε
    have hσ2 : ContDiffAt ℝ 2 σ ‖x‖ := by
      exact (hσc.contDiffAt (x := ‖x‖)).of_le (by decide : (2 : ℕ∞ω) ≤ ∞)
    have hlap := laplacian_radial_norm (f := σ) (x := x) hx0 hσ2
    have hσconst : ∀ y : ℝ, y ∈ Set.Ioo (-ε) ε → σ y = 1 := by
      intro y hy
      exact hσone y ((abs_lt).2 hy)
    have hrI : ‖x‖ ∈ Set.Ioo (-ε) ε := by
      refine ⟨?_, hxε⟩
      have : 0 ≤ ‖x‖ := norm_nonneg x
      linarith
    have hd1 : deriv σ ‖x‖ = 0 := deriv_eq_zero_of_const_on_Ioo (σ := σ) (lo := -ε) (hi := ε) (c := 1) hσconst hrI
    have hd2 : deriv (deriv σ) ‖x‖ = 0 := deriv_two_eq_zero_of_const_on_Ioo (σ := σ) (lo := -ε) (hi := ε) (c := 1) hσconst hrI
    dsimp [θ]
    rw [hlap]
    simp [hd1, hd2]
  -- Newtonian identity ∫ ‖x‖⁻¹·Δθ = −4π
  have hnewt : (∫ x : ℝ³, (‖x‖ : ℝ)⁻¹ * (Δ θ) x) = -4 * π := by
    dsimp [θ]
    exact integral_norm_inv_mul_delta_smooth hσc hσcs hσ0
  -- weak harmonicity applied to θ
  have hwhθ : (∫ x : ℝ³, w x * (Δ θ) x) = 0 := hwh θ hθc hθcs
  -- a.e. comparison of integrands w·Δθ = (c/‖x‖)·Δθ
  let Bad : Set ℝ³ := {x : ℝ³ | ¬ (ε ≤ ‖x‖ → w x = c / ‖x‖)}
  let E : Set ℝ³ := {x : ℝ³ | ‖x‖ < ε ∧ (Δ θ) x ≠ 0}
  have hBadvol0 : (volume : Measure ℝ³) Bad = 0 := by
    dsimp [Bad]
    exact MeasureTheory.ae_iff.mp hwc
  have hEvol0 : (volume : Measure ℝ³) E = 0 := by
    have hEsub : E ⊆ ({0} : Set ℝ³) := by
      intro x hx
      by_cases hx0 : x = 0
      · simpa using hx0
      · exfalso
        exact hx.2 (hdeltazero x hx0 hx.1)
    exact measure_mono_null hEsub (NullSingletonClass.measure_singleton (x := (0 : ℝ³)))
  have hFsub : {x : ℝ³ | w x * (Δ θ) x ≠ (c / ‖x‖) * (Δ θ) x} ⊆ Bad ∪ E := by
    intro x hx
    by_cases hεx : ε ≤ ‖x‖
    · by_cases hw : w x = c / ‖x‖
      · exfalso
        exact hx (by rw [hw])
      · left
        dsimp [Bad]
        exact fun h => hw (h hεx)
    · right
      refine ⟨lt_of_not_ge hεx, ?_⟩
      by_contra hΔ
      exact hx (by simp [hΔ])
  have hFae' : ∀ᵐ (x : ℝ³) ∂(volume : Measure ℝ³),
      w x * (Δ θ) x = (c / ‖x‖) * (Δ θ) x := by
    rw [MeasureTheory.ae_iff]
    refine measure_mono_null ?_ (measure_union_null hBadvol0 hEvol0)
    intro x hx
    exact hFsub hx
  have hFae : (fun x : ℝ³ => w x * (Δ θ) x) =ᵐ[volume]
      (fun x : ℝ³ => (c / ‖x‖) * (Δ θ) x) := hFae'
  have hstep : (∫ x : ℝ³, w x * (Δ θ) x) = (∫ x : ℝ³, (c / ‖x‖) * (Δ θ) x) :=
    MeasureTheory.integral_congr_ae hFae
  have hstep2 : (∫ x : ℝ³, w x * (Δ θ) x) =
      c * (∫ x : ℝ³, (‖x‖ : ℝ)⁻¹ * (Δ θ) x) := by
    calc
      (∫ x : ℝ³, w x * (Δ θ) x) = ∫ x : ℝ³, (c / ‖x‖) * (Δ θ) x := hstep
      _ = ∫ x : ℝ³, c * ((‖x‖ : ℝ)⁻¹ * (Δ θ) x) := by
          refine MeasureTheory.integral_congr_ae ?_
          filter_upwards with x
          rw [div_eq_mul_inv]
          ring
      _ = c * (∫ x : ℝ³, (‖x‖ : ℝ)⁻¹ * (Δ θ) x) := by
          rw [MeasureTheory.integral_const_mul]
  -- 0 = ∫w·Δθ = c·(−4π), whence c = 0
  have hcmul : c * (4 * π) = 0 := by
    have hc4 : c * (-4 * π) = 0 := by
      calc
        c * (-4 * π) = c * (∫ x : ℝ³, (‖x‖ : ℝ)⁻¹ * (Δ θ) x) := by rw [hnewt]
        _ = ∫ x : ℝ³, w x * (Δ θ) x := by rw [hstep2]
        _ = 0 := hwhθ
    nlinarith
  have hc0 : c = 0 :=
    (mul_eq_zero.mp hcmul).resolve_right (mul_ne_zero (by norm_num : (4 : ℝ) ≠ 0) Real.pi_ne_zero)
  filter_upwards [hwc] with x hx hεx
  have hw : w x = c / ‖x‖ := hx hεx
  rw [hc0] at hw
  simpa using hw

/-- For every positive `t` there is `n : ℕ` with `1/(n+1) ≤ t`. -/
lemma exists_nat_inv_le {t : ℝ} (ht : 0 < t) : ∃ n : ℕ, (1 : ℝ) / (n + 1) ≤ t := by
  rcases exists_nat_gt (1 / t) with ⟨n, hn⟩
  refine ⟨n, ?_⟩
  have hn' : 1 / t < (n : ℝ) + 1 := lt_trans hn (by norm_num)
  have h1' : 1 < t * ((n : ℝ) + 1) := (div_lt_iff₀' ht).mp hn'
  have h1 : 1 < ((n : ℝ) + 1) * t := by rwa [mul_comm] at h1'
  have hnp1 : 0 < (n : ℝ) + 1 := by positivity
  have h2 : (1 : ℝ) / ((n : ℝ) + 1) < t := (div_lt_iff₀' hnp1).mpr h1
  exact le_of_lt h2

/-- A radial, locally integrable, weakly harmonic (on all of `ℝ³`) function
that decays to zero at infinity is zero almost everywhere. -/
theorem radial_weaklyHarmonic_eq_zero {w : ℝ³ → ℝ} (hrad : IsRadial w)
    (hwli : LocallyIntegrable w)
    (hwh : ∀ φ : ℝ³ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      (∫ x : ℝ³, w x * (Δ φ) x) = 0)
    (hwlim : Tendsto w (cocompact ℝ³) (𝓝 0)) :
    w =ᵐ[volume] 0 := by
  -- w = 0 a.e. on each exterior {εₙ ≤ ‖x‖} with εₙ = 1/(n+1)
  have hstep (n : ℕ) : ∀ᵐ x : ℝ³, ((1 : ℝ) / (n + 1)) ≤ ‖x‖ → w x = 0 := by
    apply radial_weaklyHarmonic_exterior_zero (w := w) (ε := (1 : ℝ) / (n + 1)) hrad hwli hwh hwlim
    positivity
  let B : ℕ → Set ℝ³ := fun n => {x : ℝ³ | ¬ (((1 : ℝ) / (n + 1)) ≤ ‖x‖ → w x = 0)}
  have hB (n : ℕ) : (volume : Measure ℝ³) (B n) = 0 := by
    dsimp [B]
    exact (MeasureTheory.ae_iff.mp (hstep n))
  -- {w ≠ 0} ⊆ {0} ∪ ⋃ₙ Bₙ : every x ≠ 0 has some εₙ ≤ ‖x‖
  have hcover : {x : ℝ³ | w x ≠ 0} ⊆ ({0} : Set ℝ³) ∪ ⋃ n : ℕ, B n := by
    intro x hx
    by_cases hx0 : x = 0
    · exact Or.inl (by simpa using hx0)
    · right
      rcases exists_nat_inv_le (norm_pos_iff.mpr hx0) with ⟨n, hn⟩
      exact Set.mem_iUnion.mpr ⟨n, by
        intro h
        exact hx (h hn)⟩
  have hzero : (volume : Measure ℝ³) (({0} : Set ℝ³) ∪ ⋃ n : ℕ, B n) = 0 := by
    exact measure_union_null (NullSingletonClass.measure_singleton (x := (0 : ℝ³))) (measure_iUnion_null hB)
  have hvol : (volume : Measure ℝ³) {x : ℝ³ | w x ≠ 0} = 0 :=
    measure_mono_null hcover hzero
  have hvol_ae : ∀ᵐ (x : ℝ³) ∂(volume : Measure ℝ³), w x = 0 := by
    rw [MeasureTheory.ae_iff]
    simpa using hvol
  exact hvol_ae

end Submission.BoseGases
