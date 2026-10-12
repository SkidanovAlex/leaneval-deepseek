import ChallengeDeps
import Mathlib.Tactic.Have
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Algebra.Order.Ring.Star
import Submission.NewtonIdAux
import Submission.OneDimId
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The mean-value (origin) Newton identity

This module must prove the origin case of the Newtonian identity:

    ∫_x (Δφ)(x) · (‖x‖)⁻¹ dx = −4π · φ(0)        (φ smooth, compactly supported)

The module `Submission.NewtonIdAux` (imported above) contains a large toolkit, all machine
verified, that you should reuse:

* `newton_integral_delta_of_zero` — the reduction from a general centre `y` to the origin;
* `integral_delta_laplacian_zero` — the **ball version**: if `ψ` is smooth, compactly supported
  and vanishes on the closed ball `{x | ‖x‖ ≤ R1}` for some `R1 > 0`, then
  `∫ (Δψ)(x)·(‖x‖)⁻¹ dx = 0`;
* `integral_laplacian_mul` (Green's second identity): for smooth HCS `u, v`,
  `∫ (Δu)·v = ∫ u·(Δv)`;
* `smooth_kernel R1 M1 ...`: a smooth HCS function equal to `1/‖x‖` on the annulus
  `R1 ≤ ‖x‖ ≤ 2·M1` and zero near zero and at infinity;
* `radial_delta_norm_inv`: for smooth HCS *radial* `θ` with `θ 0 = 1`,
  `∫ ‖x‖⁻¹·(Δθ) = −4π`;
* translations, `integral_fderiv_eq_zero`, continuity/integrability helpers,
  `continuous_laplacian`, `hasCompactSupport_laplacian`, `integrable_shifted_inv`, etc.

## What remains to be done

The ball version above is not enough directly, because splitting
`φ = φ(0)·θ + ψ` (θ a smooth radial cutoff, `θ ≡ 1` near `0`) leaves a `ψ` with
`ψ(0) = 0` only — `ψ` does **not** vanish on a whole ball.  Prove the origin identity
by one of the classical routes:

**Route A (ε-regularisation of the kernel + dominated convergence).**  Choose the smooth
compactly-supported kernels `kₙ` from `smooth_kernel (1/(n+1)) B ...` (`B` larger than the
support of `φ`; smooth, HCS, `kₙ(x) = 1/‖x‖` for `‖x‖ ≥ 1/(n+1)` and `‖x‖ ≤ 2B`).  Green's
identity gives `∫(Δφ)·kₙ = ∫φ·Δkₙ`.  Use
`MeasureTheory.tendsto_integral_of_dominated_convergence` (sequence version, `n : ℕ`) to pass
`n → ∞`:

   * LHS → `∫(Δφ)(x)·(‖x‖)⁻¹ dx`  (dominated by `|Δφ|/‖x‖`, integrable since `Δφ` is bounded
     with compact support and `1/‖x‖` is locally integrable in ℝ³);
   * RHS → `−4π·φ(0)`: the Laplacian of the kernel is supported near the two transition
     annuli.  On the outer (large-radius) transition `φ = 0`, so only the inner (radius
     `≈ 1/(n+1)`) transition matters, where
     `∫φ·Δkₙ = φ(0)·∫_{inner} Δkₙ + small`.  By the radial (one-dimensional) computation
     `∫ Δkₙ = −4π` on the inner region (the flux through the sphere of radius `1/(n+1)`),
     and the remainder `∫(φ−φ(0))·Δkₙ → 0` (as `|φ(x)−φ(0)| ≤ C‖x‖`).

**Route B (flux through a small sphere).**  For `ε > 0` write, on `{ε ≤ ‖x‖}`,
`(Δφ)/‖x‖ = div(∇φ/‖x‖ + φ·x/‖x‖³)`; integrate over the shell `{ε ≤ ‖x‖ ≤ M}` and use the
divergence theorem on shells (reprove it with spherical-coordinate Fubini if needed, or with
`MeasureTheory.integral_divergence_of_hasFDerivAt_off_countable` after a change of variables)
to get boundary fluxes through the spheres of radii `ε` and `M`; let `ε → 0` and `M → ∞`.

Whatever route you choose, the *only* deliverable of this module is the theorem below.
Do not modify its statement.  You may add helper lemmas above it.
-/

noncomputable section

open _root_.BoseGases
set_option autoImplicit false

namespace Submission.BoseGases

open Filter Metric MeasureTheory Laplacian
open scoped ContDiff Topology Real

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-! ## Helpers added for the proof of `newton_integral_delta_zero` -/

section CalculusHelpers

/-- The Laplacian commutes with addition (smooth case). -/
lemma laplacian_add_smooth (f g : ℝ³ → ℝ) (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) :
    (Δ (fun x : ℝ³ => f x + g x)) = fun x : ℝ³ => (Δ f) x + (Δ g) x := by
  funext x
  exact ContDiffAt.laplacian_add
    ((hf.of_le (by decide : (2 : ℕ∞ω) ≤ ∞)).contDiffAt)
    ((hg.of_le (by decide : (2 : ℕ∞ω) ≤ ∞)).contDiffAt)

/-- The Laplacian commutes with scalar multiplication (smooth case). -/
lemma laplacian_smul_smooth (c : ℝ) (g : ℝ³ → ℝ) (hg : ContDiff ℝ ∞ g) :
    (Δ (fun x : ℝ³ => c * g x)) = fun x : ℝ³ => c * (Δ g) x := by
  funext x
  have hg2 : ContDiffAt ℝ 2 g x := (hg.of_le (by decide : (2 : ℕ∞ω) ≤ ∞)).contDiffAt
  have hsm : (fun x : ℝ³ => c * g x) = c • g := by
    funext x
    simp [smul_eq_mul]
  calc
    (Δ (fun x : ℝ³ => c * g x)) x = Δ (c • g) x := by rw [hsm]
    _ = c • (Δ g) x := InnerProductSpace.laplacian_smul (𝕜 := ℝ) c hg2
    _ = c * (Δ g) x := by simp [smul_eq_mul]

/-- The Laplacian of a smooth function is continuous. -/
lemma continuous_laplacian (g : ℝ³ → ℝ) (hg : ContDiff ℝ ∞ g) : Continuous (Δ g) := by
  have hsum : (Δ g) = fun x : ℝ³ => ∑ i : Fin 3,
      fderiv ℝ (fun z : ℝ³ => fderiv ℝ g z (euclBasis3 i)) x (euclBasis3 i) := by
    funext x
    exact laplacian_basis_sum g hg x
  rw [hsum]
  refine continuous_finset_sum Finset.univ ?_
  intro i hi
  exact continuous_fderiv_apply (u := fun z : ℝ³ => fderiv ℝ g z (euclBasis3 i))
    (contDiff_fderiv_apply g hg (euclBasis3 i)) (euclBasis3 i)

/-- The Laplacian of a compactly supported function has compact support. -/
lemma hasCompactSupport_laplacian (g : ℝ³ → ℝ) (hcs : HasCompactSupport g) :
    HasCompactSupport (Δ g) := by
  refine HasCompactSupport.intro' (K := tsupport g) hcs (isClosed_tsupport g) ?_
  intro x hx
  exact laplacian_eq_zero_of_not_mem_tsupport g hx

/-- `‖x‖⁻¹` is integrable on the open ball of radius `R` in ℝ³. -/
lemma integrableOn_inv_norm_ball (R : ℝ) (hR : 0 ≤ R) :
    IntegrableOn (fun x : ℝ³ => (‖x‖ : ℝ)⁻¹) (Metric.ball (0 : ℝ³) R) := by
  rw [integrable_radial_ball_r3 (f := fun r : ℝ => r⁻¹) R]
  have hcont : Continuous (fun r : ℝ => r) := continuous_id
  have hIcc : IntegrableOn (fun r : ℝ => r) (Set.Icc 0 R) := by
    refine ContinuousOn.integrableOn_compact (K := Set.Icc 0 R) isCompact_Icc ?_
    exact hcont.continuousOn
  have hsub : Set.Ioo 0 R ⊆ Set.Icc 0 R := by
    intro r hr
    exact ⟨le_of_lt hr.1, le_of_lt hr.2⟩
  have hIoo : IntegrableOn (fun r : ℝ => r) (Set.Ioo 0 R) := hIcc.mono_set hsub
  have hpt : ∀ r ∈ Set.Ioo 0 R, r ^ 2 * r⁻¹ = r := by
    intro r hr
    have hrne : r ≠ 0 := ne_of_gt hr.1
    field_simp [hrne]
  have hcongr : (fun r : ℝ => r) =ᵐ[volume.restrict (Set.Ioo 0 R)] (fun r : ℝ => r ^ 2 * r⁻¹) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
    exact (hpt r hr).symm
  exact MeasureTheory.Integrable.congr hIoo hcongr

/-- A continuous compactly supported function divided by `‖x‖` is integrable on ℝ³. -/
lemma integrable_mul_norm_inv {g : ℝ³ → ℝ} (hg : Continuous g) (hcs : HasCompactSupport g) :
    Integrable (fun x : ℝ³ => g x * (‖x‖ : ℝ)⁻¹) := by
  rcases hcs.isBounded.subset_closedBall (0 : ℝ³) with ⟨B₀, hB₀⟩
  let B : ℝ := max B₀ 1
  have hB₀le : B₀ ≤ B := le_max_left B₀ 1
  have hB₁ : 1 ≤ B := le_max_right B₀ 1
  have hB0 : 0 ≤ B := le_trans zero_le_one hB₁
  have hts : tsupport g ⊆ Metric.closedBall (0 : ℝ³) B := by
    intro x hx
    have hx₀ : x ∈ Metric.closedBall (0 : ℝ³) B₀ := hB₀ hx
    exact Metric.closedBall_subset_closedBall hB₀le hx₀
  let K : Set ℝ³ := Metric.closedBall (0 : ℝ³) B
  have hK : IsCompact K := ProperSpace.isCompact_closedBall (0 : ℝ³) B
  have hKne : K.Nonempty := ⟨0, by
    dsimp [K]
    simpa [dist_self] using hB0⟩
  let ψ : ℝ³ → ℝ := fun x => ‖g x‖
  have hψc : ContinuousOn ψ K := by
    dsimp [ψ]
    exact (continuous_norm.comp hg).continuousOn
  rcases IsCompact.exists_isMaxOn hK hKne hψc with ⟨x₀, hx₀, hmax⟩
  let C : ℝ := ψ x₀
  have hC : 0 ≤ C := by
    dsimp [C, ψ]
    exact norm_nonneg (g x₀)
  have hbound : ∀ x, x ∈ K → ‖g x‖ ≤ C := by
    intro x hx
    simpa [ψ, C] using hmax hx
  have hg0 : ∀ x : ℝ³, x ∉ K → g x = 0 := by
    intro x hxK
    by_contra hz
    apply hxK
    exact hts (subset_tsupport g (by simpa [Function.support] using hz))
  have hmeas_inv : Measurable (fun x : ℝ³ => (‖x‖ : ℝ)⁻¹) := by
    change Measurable (fun x : ℝ³ => ((fun r : ℝ => r⁻¹) (‖x‖)))
    exact Measurable.inv (measurable_norm : Measurable (fun x : ℝ³ => ‖x‖))
  have hmeas : Measurable (fun x : ℝ³ => g x * (‖x‖ : ℝ)⁻¹) := by
    exact hg.measurable.mul hmeas_inv
  have hasm : AEStronglyMeasurable (fun x : ℝ³ => g x * (‖x‖ : ℝ)⁻¹) volume := by
    exact hmeas.stronglyMeasurable.aestronglyMeasurable
  let R : ℝ := B + 1
  have hR : 0 ≤ R := by dsimp [R]; linarith
  have hball : IntegrableOn (fun x : ℝ³ => (‖x‖ : ℝ)⁻¹) (Metric.ball (0 : ℝ³) R) :=
    integrableOn_inv_norm_ball R hR
  let D : ℝ³ → ℝ := fun x => C * ((Metric.ball (0 : ℝ³) R).indicator (fun x : ℝ³ => (‖x‖ : ℝ)⁻¹)) x
  have hD : Integrable D := by
    dsimp [D]
    refine MeasureTheory.Integrable.const_mul ?_ C
    exact (MeasureTheory.integrable_indicator_iff (s := Metric.ball (0 : ℝ³) R)
      (f := fun x : ℝ³ => (‖x‖ : ℝ)⁻¹) (hs := measurableSet_ball)).2 hball
  have hbd : ∀ x : ℝ³, ‖g x * (‖x‖ : ℝ)⁻¹‖ ≤ D x := by
    intro x
    by_cases hxK : x ∈ K
    · have hxin : x ∈ Metric.ball (0 : ℝ³) R := by
        have hnorm : ‖x‖ ≤ B := by
          simpa [K, Metric.mem_closedBall, dist_zero_right] using hxK
        have hlt : ‖x‖ < R := by dsimp [R]; linarith
        simpa [Metric.mem_ball, dist_zero_right] using hlt
      have h₁ : ‖g x‖ ≤ C := hbound x hxK
      have h₂ : 0 ≤ (‖x‖ : ℝ)⁻¹ := by
        exact inv_nonneg.mpr (norm_nonneg x)
      have hmul : ‖g x‖ * (‖x‖ : ℝ)⁻¹ ≤ C * (‖x‖ : ℝ)⁻¹ :=
        mul_le_mul_of_nonneg_right h₁ h₂
      calc
        ‖g x * (‖x‖ : ℝ)⁻¹‖ = ‖g x‖ * ‖(‖x‖ : ℝ)⁻¹‖ := by simp
        _ = ‖g x‖ * (‖x‖ : ℝ)⁻¹ := by
              simp [abs_of_nonneg (inv_nonneg.mpr (norm_nonneg x))]
        _ ≤ C * (‖x‖ : ℝ)⁻¹ := hmul
        _ = D x := by
              dsimp [D]
              simp [hxin]
    · have hgx : g x = 0 := hg0 x hxK
      have hDx : 0 ≤ D x := by
        dsimp [D]
        exact mul_nonneg hC (Set.indicator_nonneg
          (fun y hy => inv_nonneg.mpr (norm_nonneg y)) x)
      calc
        ‖g x * (‖x‖ : ℝ)⁻¹‖ = 0 := by simp [hgx]
        _ ≤ D x := hDx
  exact MeasureTheory.Integrable.mono' hD hasm (ae_of_all volume hbd)

end CalculusHelpers

section NewtonKernel

/-- 1-D "rise" profile with scale `R`: `0` for `t ≤ R/2`, `1` for `R ≤ t`, smooth, in `[0,1]`. -/
def riseProfile (R : ℝ) (t : ℝ) : ℝ := Real.smoothTransition (2 * t / R - 1)

/-- 1-D "drop" profile with scale `M`: `1` for `t ≤ 2M`, `0` for `4M ≤ t`, smooth, in `[0,1]`. -/
def dropProfile (M : ℝ) (t : ℝ) : ℝ := 1 - Real.smoothTransition ((t - 2 * M) / (2 * M))

/-- 1-D radial profile of the truncated Newton kernel: `S(t) = rise R t · drop M t · t⁻¹`. -/
def kernelProfile1D (R M : ℝ) (t : ℝ) : ℝ :=
  riseProfile R t * dropProfile M t * t⁻¹

/-- The truncated Newton kernel: smooth, HCS, equal to `‖x‖⁻¹` for `R ≤ ‖x‖ ≤ 2M`, zero for
`‖x‖ ≤ R/2` and for `4M ≤ ‖x‖`. -/
def newtonKernel (R M : ℝ) (x : ℝ³) : ℝ := kernelProfile1D R M ‖x‖

lemma riseProfile_nonneg (R t : ℝ) : 0 ≤ riseProfile R t := by
  dsimp [riseProfile]
  exact Real.smoothTransition.nonneg _

lemma riseProfile_le_one (R t : ℝ) : riseProfile R t ≤ 1 := by
  dsimp [riseProfile]
  exact Real.smoothTransition.le_one _

lemma dropProfile_nonneg (M t : ℝ) : 0 ≤ dropProfile M t := by
  dsimp [dropProfile]
  exact sub_nonneg.mpr (Real.smoothTransition.le_one _)

lemma dropProfile_le_one (M t : ℝ) : dropProfile M t ≤ 1 := by
  dsimp [dropProfile]
  exact sub_le_self _ (Real.smoothTransition.nonneg _)

/-- value of the rise profile on the small side -/
lemma riseProfile_zero_of_le (R : ℝ) (hR : 0 < R) {t : ℝ} (ht : t ≤ R / 2) :
    riseProfile R t = 0 := by
  dsimp [riseProfile]
  have hden : 0 < R := hR
  have hnum : 2 * t / R - 1 ≤ 0 := by
    have h1 : 2 * t / R ≤ 1 := by
      rw [div_le_iff₀ hR]
      linarith [ht]
    linarith
  rw [Real.smoothTransition.zero_of_nonpos hnum]

/-- value of the rise profile on the large side -/
lemma riseProfile_one_of_ge (R : ℝ) (hR : 0 < R) {t : ℝ} (ht : R ≤ t) :
    riseProfile R t = 1 := by
  dsimp [riseProfile]
  have h1 : 1 ≤ 2 * t / R - 1 := by
    have h2 : 2 ≤ 2 * t / R := by
      rw [le_div_iff₀ hR]
      linarith [ht]
    linarith
  rw [Real.smoothTransition.one_of_one_le h1]

/-- value of the drop profile on the small side -/
lemma dropProfile_one_of_le (M : ℝ) (hM : 0 < M) {t : ℝ} (ht : t ≤ 2 * M) :
    dropProfile M t = 1 := by
  dsimp [dropProfile]
  have hden : 0 < 2 * M := by positivity
  have harg : (t - 2 * M) / (2 * M) ≤ 0 := by
    rw [div_le_iff₀ hden]
    linarith [ht]
  rw [Real.smoothTransition.zero_of_nonpos harg]
  norm_num

/-- value of the drop profile on the large side -/
lemma dropProfile_zero_of_ge (M : ℝ) (hM : 0 < M) {t : ℝ} (ht : 4 * M ≤ t) :
    dropProfile M t = 0 := by
  dsimp [dropProfile]
  have hden : 0 < 2 * M := by positivity
  have harg : 1 ≤ (t - 2 * M) / (2 * M) := by
    rw [le_div_iff₀ hden]
    linarith [ht]
  rw [Real.smoothTransition.one_of_one_le harg]
  norm_num

/-- The kernel equals `‖x‖⁻¹` on the annulus. -/
lemma newtonKernel_eq_inv {R M : ℝ} (hR : 0 < R) (hM : 0 < M) {x : ℝ³}
    (h1 : R ≤ ‖x‖) (h2 : ‖x‖ ≤ 2 * M) : newtonKernel R M x = (‖x‖ : ℝ)⁻¹ := by
  dsimp [newtonKernel, kernelProfile1D]
  rw [riseProfile_one_of_ge R hR h1]
  rw [dropProfile_one_of_le M hM h2]
  ring

/-- The kernel vanishes on the closed ball of radius `R/2`. -/
lemma newtonKernel_zero_small {R M : ℝ} (hR : 0 < R) {x : ℝ³} (hx : ‖x‖ ≤ R / 2) :
    newtonKernel R M x = 0 := by
  dsimp [newtonKernel, kernelProfile1D]
  rw [riseProfile_zero_of_le R hR hx]
  ring

/-- The kernel vanishes outside the closed ball of radius `4M`. -/
lemma newtonKernel_zero_big {R M : ℝ} (hM : 0 < M) {x : ℝ³} (hx : 4 * M ≤ ‖x‖) :
    newtonKernel R M x = 0 := by
  dsimp [newtonKernel, kernelProfile1D]
  rw [dropProfile_zero_of_ge M hM hx]
  ring

/-- The kernel lies between `0` and `‖x‖⁻¹`. -/
lemma newtonKernel_nonneg (R M : ℝ) (x : ℝ³) : 0 ≤ newtonKernel R M x := by
  dsimp [newtonKernel, kernelProfile1D]
  exact mul_nonneg (mul_nonneg (riseProfile_nonneg R ‖x‖) (dropProfile_nonneg M ‖x‖))
    (inv_nonneg.mpr (norm_nonneg x))

lemma newtonKernel_le_inv (R M : ℝ) (x : ℝ³) : newtonKernel R M x ≤ (‖x‖ : ℝ)⁻¹ := by
  dsimp [newtonKernel, kernelProfile1D]
  have h₁ : riseProfile R ‖x‖ * dropProfile M ‖x‖ ≤ 1 := by
    calc
      riseProfile R ‖x‖ * dropProfile M ‖x‖
          ≤ riseProfile R ‖x‖ * 1 := by
            exact mul_le_mul_of_nonneg_left (dropProfile_le_one M ‖x‖) (riseProfile_nonneg R ‖x‖)
      _ = riseProfile R ‖x‖ := by ring
      _ ≤ 1 := riseProfile_le_one R ‖x‖
  calc
    riseProfile R ‖x‖ * dropProfile M ‖x‖ * (‖x‖ : ℝ)⁻¹
        ≤ 1 * (‖x‖ : ℝ)⁻¹ := by
          exact mul_le_mul_of_nonneg_right h₁ (inv_nonneg.mpr (norm_nonneg x))
    _ = (‖x‖ : ℝ)⁻¹ := by ring

end NewtonKernel

/-- `Real.smoothTransition` is differentiable everywhere. -/
lemma st_differentiableAt (t : ℝ) : DifferentiableAt ℝ Real.smoothTransition t := by
  exact Real.smoothTransition.contDiffAt.differentiableAt (by norm_num : (∞ : ℕ∞ω) ≠ 0)

/-- First derivative of the rise profile. -/
lemma deriv_riseProfile (R : ℝ) (hR : R ≠ 0) (t : ℝ) :
    deriv (riseProfile R) t = (2 / R) * (deriv Real.smoothTransition) (2 * t / R - 1) := by
  unfold riseProfile
  let h : ℝ → ℝ := (fun s : ℝ => (2 / R) * s) - fun s : ℝ => (1 : ℝ)
  have hdh : HasDerivAt h (2 / R) t := by
    dsimp [h]
    have hm : HasDerivAt (fun s : ℝ => (2 / R) * s) ((2 / R) * 1) t :=
      HasDerivAt.const_mul (2 / R) (hasDerivAt_id t)
    simpa using hm.sub (hasDerivAt_const (x := t) (c := (1 : ℝ)))
  have hdst : HasDerivAt Real.smoothTransition (deriv Real.smoothTransition (h t)) (h t) :=
    (st_differentiableAt (h t)).hasDerivAt
  have hc := HasDerivAt.comp t hdst hdh
  have hmain : HasDerivAt (fun s : ℝ => Real.smoothTransition (2 * s / R - 1))
      (deriv Real.smoothTransition (h t) * (2 / R)) t := by
    have hfun : (fun s : ℝ => Real.smoothTransition (2 * s / R - 1)) =
        Real.smoothTransition ∘ h := by
      funext s
      congr 1
      dsimp [h]
      ring_nf
    rw [hfun]
    exact hc
  rw [hmain.deriv]
  have hh_eq : h t = 2 * t / R - 1 := by
    dsimp [h]
    ring_nf
  rw [hh_eq]
  ring_nf

/-- Second derivative of the rise profile. -/
lemma deriv_two_riseProfile (R : ℝ) (hR : R ≠ 0) (t : ℝ) :
    deriv (deriv (riseProfile R)) t =
      (4 / R ^ 2) * (deriv (deriv Real.smoothTransition)) (2 * t / R - 1) := by
  have hst' : ContDiff ℝ ∞ (deriv Real.smoothTransition) :=
    (contDiff_infty_iff_deriv.mp Real.smoothTransition.contDiff).2
  have hst'df : ∀ y : ℝ, DifferentiableAt ℝ (deriv Real.smoothTransition) y :=
    fun y => hst'.differentiable (by norm_num : (∞ : ℕ∞ω) ≠ 0) y
  have hdw : ∀ y : ℝ, HasDerivAt (deriv Real.smoothTransition)
      (deriv (deriv Real.smoothTransition) y) y := fun y => (hst'df y).hasDerivAt
  have hfun : (deriv (riseProfile R)) =
      fun s : ℝ => (2 / R) * (deriv Real.smoothTransition) (2 * s / R - 1) := by
    funext s
    exact deriv_riseProfile R hR s
  rw [hfun]
  let h : ℝ → ℝ := fun s : ℝ => 2 * s / R - 1
  have hdh : HasDerivAt h (2 / R) t := by
    dsimp [h]
    have hm : HasDerivAt (fun s : ℝ => (2 / R) * s) ((2 / R) * 1) t :=
      HasDerivAt.const_mul (2 / R) (hasDerivAt_id t)
    have hsub := hm.sub (hasDerivAt_const (x := t) (c := (1 : ℝ)))
    have hfun2 : (fun s : ℝ => 2 * s / R - 1) = (fun s : ℝ => (2 / R) * s) - fun s : ℝ => (1 : ℝ) := by
      funext s
      dsimp
      ring_nf
    rw [hfun2]
    simpa using hsub
  have hwcomp : HasDerivAt (fun s : ℝ => (deriv Real.smoothTransition) (h s))
      (deriv (deriv Real.smoothTransition) (h t) * (2 / R)) t := by
    have hc := HasDerivAt.comp t (hdw (h t)) hdh
    change HasDerivAt (fun s : ℝ => (deriv Real.smoothTransition) (h s))
        (deriv (deriv Real.smoothTransition) (h t) * (2 / R)) t
    exact hc
  have hG : HasDerivAt (fun s : ℝ => (2 / R) * (deriv Real.smoothTransition) (h s))
      ((2 / R) * (deriv (deriv Real.smoothTransition) (h t) * (2 / R))) t := by
    exact HasDerivAt.const_mul (2 / R) hwcomp
  rw [hG.deriv]
  have hh_eq : h t = 2 * t / R - 1 := by
    rfl
  rw [hh_eq]
  field_simp [hR]
  ring


/-- Second derivatives agree for functions equal on an open neighbourhood. -/
lemma deriv_two_eq_of_eventuallyEq_open {f g : ℝ → ℝ} {r : ℝ} (U : Set ℝ)
    (hUo : IsOpen U) (hUr : r ∈ U) (hfg : ∀ s ∈ U, f s = g s) :
    deriv (deriv f) r = deriv (deriv g) r := by
  have hderPt : ∀ s ∈ U, deriv f s = deriv g s := by
    intro s hs
    have hmem : U ∈ 𝓝 s := hUo.mem_nhds hs
    have hev : f =ᶠ[𝓝 s] g := by
      refine eventuallyEq_of_mem hmem ?_
      intro y hy
      exact hfg y hy
    exact hev.deriv_eq
  have hderEv : (deriv f) =ᶠ[𝓝 r] (deriv g) := by
    refine eventuallyEq_of_mem (hUo.mem_nhds hUr) ?_
    intro s hs
    exact hderPt s hs
  exact hderEv.deriv_eq

/-- The drop profile is constantly `1` below `2M`. -/
lemma dropProfile_one_of_lt {M : ℝ} (hM : 0 < M) {t : ℝ} (ht : t < 2 * M) :
    dropProfile M t = 1 := by
  exact dropProfile_one_of_le M hM (le_of_lt ht)

/-- The first derivative of the drop profile vanishes below `2M`. -/
lemma deriv_dropProfile_eq_zero {M : ℝ} (hM : 0 < M) {t : ℝ} (ht : t < 2 * M) :
    deriv (dropProfile M) t = 0 := by
  have hev : dropProfile M =ᶠ[𝓝 t] (fun _ : ℝ => 1) := by
    refine eventuallyEq_of_mem (Metric.ball_mem_nhds t (sub_pos.mpr ht)) ?_
    intro s hs
    have hs' : |s - t| < 2 * M - t := by
      simpa [Real.dist_eq, dist_eq_norm, dist_zero_right] using hs
    have hs2 : s ≤ 2 * M := by
      have hb := (abs_le.mp (le_of_lt hs')).2
      linarith
    exact dropProfile_one_of_le M hM hs2
  calc
    deriv (dropProfile M) t = deriv (fun _ : ℝ => 1) t := hev.deriv_eq
    _ = 0 := by simp

/-- The second derivative of the drop profile vanishes below `2M`. -/
lemma deriv_two_dropProfile_eq_zero {M : ℝ} (hM : 0 < M) {t : ℝ} (ht : t < 2 * M) :
    deriv (deriv (dropProfile M)) t = 0 := by
  have hderPt : ∀ s : ℝ, s ∈ Set.Iio (2 * M) → deriv (dropProfile M) s = 0 := by
    intro s hs
    exact deriv_dropProfile_eq_zero hM hs
  have hderEv : (deriv (dropProfile M)) =ᶠ[𝓝 t] (fun _ : ℝ => 0) := by
    have hmem : Set.Iio (2 * M) ∈ 𝓝 t :=
      (isOpen_Iio (a := 2 * M)).mem_nhds (by simpa [Set.mem_Iio] using ht)
    refine eventuallyEq_of_mem hmem ?_
    intro s hs
    exact hderPt s hs
  calc
    deriv (deriv (dropProfile M)) t = deriv (fun _ : ℝ => 0) t := hderEv.deriv_eq
    _ = 0 := by simp


/-- Integral over a closed annulus of a radial function reduces to a 1-D integral. -/
lemma integral_annulus_radial {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (G : ℝ → ℝ) :
    (∫ x : ℝ³ in {x : ℝ³ | a ≤ ‖x‖ ∧ ‖x‖ ≤ b}, G ‖x‖) =
      4 * π * (∫ r in Set.Icc a b, r ^ 2 * G r) := by
  let A : Set ℝ³ := {x : ℝ³ | a ≤ ‖x‖ ∧ ‖x‖ ≤ b}
  have hAmeas : MeasurableSet A := by
    dsimp [A]
    exact (measurableSet_Icc.preimage measurable_norm)
  let g : ℝ → ℝ := (Set.Icc a b).indicator (fun r : ℝ => G r)
  have hpt : (fun x : ℝ³ => A.indicator (fun x : ℝ³ => G ‖x‖) x) = fun x : ℝ³ => g ‖x‖ := by
    funext x
    by_cases hx : x ∈ A
    · have hx' : ‖x‖ ∈ Set.Icc a b := by
        dsimp [A] at hx
        exact ⟨hx.1, hx.2⟩
      simp [hx, hx', g]
    · have hx' : ‖x‖ ∉ Set.Icc a b := by
        intro h
        apply hx
        dsimp [A]
        exact ⟨h.1, h.2⟩
      simp [hx, hx', g]
  have hIoi : Set.Ioi (0 : ℝ) ∩ Set.Icc a b = Set.Icc a b := by
    ext r
    constructor
    · intro hr
      exact hr.2
    · intro hr
      constructor
      · exact lt_of_lt_of_le ha hr.1
      · exact hr
  calc
    (∫ x : ℝ³ in A, G ‖x‖) = ∫ x : ℝ³, A.indicator (fun x : ℝ³ => G ‖x‖) x := by
          rw [integral_indicator (s := A) (f := fun x : ℝ³ => G ‖x‖) (μ := (volume : Measure ℝ³)) hAmeas]
    _ = ∫ x : ℝ³, g ‖x‖ := by rw [hpt]
    _ = 4 * π * (∫ r in Set.Ioi (0 : ℝ), r ^ 2 * g r) := integral_fun_norm_r3 (g := g)
    _ = 4 * π * (∫ r in Set.Icc a b, r ^ 2 * G r) := by
          congr 1
          have hfun : (fun r : ℝ => r ^ 2 * g r) = (Set.Icc a b).indicator (fun r : ℝ => r ^ 2 * G r) := by
            funext r
            by_cases hr : r ∈ Set.Icc a b
            · simp [g, hr]
            · simp [g, hr]
          calc
            (∫ r in Set.Ioi (0 : ℝ), r ^ 2 * g r)
                = ∫ r in Set.Ioi (0 : ℝ), (Set.Icc a b).indicator (fun r : ℝ => r ^ 2 * G r) r := by rw [hfun]
            _ = ∫ r in Set.Ioi (0 : ℝ) ∩ Set.Icc a b, (fun r : ℝ => r ^ 2 * G r) r := by
                  rw [setIntegral_indicator (s := Set.Ioi (0 : ℝ)) (t := Set.Icc a b)
                    (f := fun r : ℝ => r ^ 2 * G r) (μ := (volume : Measure ℝ)) (by measurability)]
            _ = ∫ r in Set.Icc a b, r ^ 2 * G r := by rw [hIoi]

/-- Laplacian of the kernel vanishes on the inner open ball. -/
lemma laplacian_newtonKernel_zero_inner {ε M : ℝ} (hε : 0 < ε) (hM : 0 < M) {x : ℝ³}
    (hx : ‖x‖ < ε / 2) : (Δ (newtonKernel ε M)) x = 0 := by
  exact mv_laplacian_eq_zero_of_norm_lt (g := newtonKernel ε M) (R := ε / 2)
    (fun y hy => newtonKernel_zero_small hε hy) hx

/-- Laplacian of the kernel vanishes on the open annulus. -/
lemma laplacian_newtonKernel_zero_middle {ε M : ℝ} (hε : 0 < ε) (hM : 0 < M) {x : ℝ³}
    (hx1 : ε < ‖x‖) (hx2 : ‖x‖ < 2 * M) : (Δ (newtonKernel ε M)) x = 0 := by
  have hxnz : x ≠ 0 := by
    intro hz
    rw [hz] at hx1
    have : ε < (0 : ℝ) := by simpa using hx1
    linarith
  have hloc : newtonKernel ε M =ᶠ[𝓝 x] (fun y : ℝ³ => (‖y‖ : ℝ)⁻¹) := by
    let U : Set ℝ³ := {y : ℝ³ | ε < ‖y‖ ∧ ‖y‖ < 2 * M}
    have hUo : IsOpen U := by
      dsimp [U]
      exact (isOpen_Ioi.preimage continuous_norm).inter (isOpen_Iio.preimage continuous_norm)
    have hxU : x ∈ U := ⟨hx1, hx2⟩
    filter_upwards [hUo.mem_nhds hxU] with y hy
    exact newtonKernel_eq_inv hε hM (le_of_lt hy.1) (le_of_lt hy.2)
  have hΔ : (Δ (newtonKernel ε M)) =ᶠ[𝓝 x] (Δ fun y : ℝ³ => (‖y‖ : ℝ)⁻¹) := by
    exact InnerProductSpace.laplacian_congr_nhds (E := ℝ³) (f₁ := newtonKernel ε M)
      (f₂ := fun y : ℝ³ => (‖y‖ : ℝ)⁻¹) hloc
  have hz : (Δ fun y : ℝ³ => (‖y‖ : ℝ)⁻¹) x = 0 := laplacian_inv_norm_eq_zero hxnz
  simpa [hz] using (Filter.EventuallyEq.eq_of_nhds hΔ)

-- ℝ³ radial Laplacian of `V(‖·‖)/‖·‖`
lemma laplacian_div_norm_identity (V : ℝ → ℝ) (hV : ContDiff ℝ 2 V) {x : ℝ³} (hx : x ≠ 0) :
    (Δ fun y : ℝ³ => V ‖y‖ * (‖y‖ : ℝ)⁻¹) x = deriv (deriv V) ‖x‖ * (‖x‖ : ℝ)⁻¹ := by
  have hx0 : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have hfun : (fun y : ℝ³ => V ‖y‖ * (‖y‖ : ℝ)⁻¹) = fun y : ℝ³ => (fun t : ℝ => V t * t⁻¹) ‖y‖ := by
    funext y
    rfl
  rw [hfun]
  have hf2 : ContDiffAt ℝ 2 (fun t : ℝ => V t * t⁻¹) ‖x‖ := by
    have hV2 : ContDiffAt ℝ 2 V ‖x‖ := hV.contDiffAt
    have hinv : ContDiffAt ℝ 2 (fun t : ℝ => t⁻¹) ‖x‖ :=
      contDiffAt_inv (𝕜 := ℝ) (n := (2 : ℕ∞ω)) hx0
    exact hV2.mul hinv
  have hlap := laplacian_radial_norm (f := fun t : ℝ => V t * t⁻¹) hx hf2
  rw [hlap]
  have hid := one_dim_div_identity V hV (r := ‖x‖) hx0
  simpa using hid


/-- The first derivative of the smooth transition is bounded on `[0,1]`. -/
lemma exists_bound_smoothTransition_deriv :
    ∃ Md : ℝ, 0 ≤ Md ∧ ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ‖deriv Real.smoothTransition s‖ ≤ Md := by
  have hcont : Continuous (fun s : ℝ => ‖deriv Real.smoothTransition s‖) := by
    have hc := ContDiff.continuous_deriv (Real.smoothTransition.contDiff)
      (by norm_num : (1 : ℕ∞ω) ≤ ∞)
    exact hc.norm
  rcases IsCompact.exists_isMaxOn isCompact_Icc (by simp : (Set.Icc (0 : ℝ) 1).Nonempty)
    hcont.continuousOn with ⟨x₀, hx₀, hmax⟩
  refine ⟨‖deriv Real.smoothTransition x₀‖, norm_nonneg _, ?_⟩
  intro s hs
  simpa using hmax hs

/-- The second derivative of the smooth transition is bounded on `[0,1]`. -/
lemma exists_bound_smoothTransition_deriv_two :
    ∃ M2 : ℝ, 0 ≤ M2 ∧
      ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ‖deriv (deriv Real.smoothTransition) s‖ ≤ M2 := by
  have hst' : ContDiff ℝ ∞ (deriv Real.smoothTransition) :=
    (contDiff_infty_iff_deriv.mp Real.smoothTransition.contDiff).2
  have hcont : Continuous (fun s : ℝ => ‖deriv (deriv Real.smoothTransition) s‖) := by
    have hc := ContDiff.continuous_deriv hst' (by norm_num : (1 : ℕ∞ω) ≤ ∞)
    exact hc.norm
  rcases IsCompact.exists_isMaxOn isCompact_Icc (by simp : (Set.Icc (0 : ℝ) 1).Nonempty)
    hcont.continuousOn with ⟨x₀, hx₀, hmax⟩
  refine ⟨‖deriv (deriv Real.smoothTransition) x₀‖, norm_nonneg _, ?_⟩
  intro s hs
  simpa using hmax hs



/-- The rise profile is smooth (when `R ≠ 0`). -/
lemma contDiff_riseProfile (R : ℝ) (hR : R ≠ 0) : ContDiff ℝ ∞ (riseProfile R) := by
  change ContDiff ℝ ∞ (fun t : ℝ => Real.smoothTransition (2 * t / R - 1))
  have haff : ContDiff ℝ ∞ (fun t : ℝ => 2 * t / R - 1) := by
    have hnum : ContDiff ℝ ∞ (fun t : ℝ => (2 : ℝ) * t) :=
      (contDiff_const : ContDiff ℝ ∞ fun _ : ℝ => (2 : ℝ)).mul contDiff_id
    have hden : ContDiff ℝ ∞ (fun _ : ℝ => R) := contDiff_const
    have hdiv : ContDiff ℝ ∞ (fun t : ℝ => (2 * t) / R) :=
      ContDiff.div hnum hden (fun _ => hR)
    exact hdiv.sub contDiff_const
  change ContDiff ℝ ∞ (Real.smoothTransition ∘ (fun t : ℝ => 2 * t / R - 1))
  exact Real.smoothTransition.contDiff.comp haff

/-- The drop profile is smooth (when `M ≠ 0`). -/
lemma contDiff_dropProfile (M : ℝ) (hM : M ≠ 0) : ContDiff ℝ ∞ (dropProfile M) := by
  change ContDiff ℝ ∞ (fun t : ℝ => 1 - Real.smoothTransition ((t - 2 * M) / (2 * M)))
  have hden : ContDiff ℝ ∞ (fun _ : ℝ => 2 * M) := contDiff_const
  have hnum : ContDiff ℝ ∞ (fun t : ℝ => t - 2 * M) := contDiff_id.sub contDiff_const
  have hdiv : ContDiff ℝ ∞ (fun t : ℝ => (t - 2 * M) / (2 * M)) :=
    ContDiff.div hnum hden (fun _ => mul_ne_zero two_ne_zero hM)
  change ContDiff ℝ ∞ (fun t : ℝ => 1 - Real.smoothTransition ((t - 2 * M) / (2 * M)))
  exact contDiff_const.sub (Real.smoothTransition.contDiff.comp hdiv)

/-- The 1-D kernel profile is smooth. -/
lemma contDiff_kernelProfile1D (R M : ℝ) (hR : 0 < R) (hM : 0 < M) :
    ContDiff ℝ ∞ (kernelProfile1D R M) := by
  rw [contDiff_iff_contDiffAt]
  intro t
  by_cases ht : t = 0
  · subst t
    apply ContDiffAt.congr_of_eventuallyEq (n := ∞)
    · exact contDiffAt_const (x := (0 : ℝ)) (c := (0 : ℝ))
    · have hhalf : 0 < R / 2 := by positivity
      filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hhalf] with y hy
      have hyle : y ≤ R / 2 := by
        have hlt : |y| < R / 2 := by simpa [Metric.mem_ball, dist_zero_right] using hy
        linarith [abs_le.mp (le_of_lt hlt)]
      dsimp [kernelProfile1D]
      rw [riseProfile_zero_of_le R hR hyle]
      ring
  · have hI : ContDiffAt ℝ ∞ (riseProfile R) t :=
      (contDiff_riseProfile R (ne_of_gt hR)).contDiffAt
    have hO : ContDiffAt ℝ ∞ (dropProfile M) t :=
      (contDiff_dropProfile M (ne_of_gt hM)).contDiffAt
    have hinv : ContDiffAt ℝ ∞ (fun s : ℝ => s⁻¹) t :=
      contDiffAt_inv (𝕜 := ℝ) (n := ∞) ht
    change ContDiffAt ℝ ∞ (fun s : ℝ => riseProfile R s * dropProfile M s * s⁻¹) t
    exact (hI.mul hO).mul hinv

/-- The truncated Newton kernel is smooth. -/
lemma contDiff_newtonKernel (R M : ℝ) (hR : 0 < R) (hM : 0 < M) :
    ContDiff ℝ ∞ (newtonKernel R M) := by
  change ContDiff ℝ ∞ (fun x : ℝ³ => kernelProfile1D R M ‖x‖)
  have hhalf : 0 < R / 2 := by positivity
  have hS0 : ∀ t : ℝ, |t| < R / 2 → kernelProfile1D R M t = 0 := by
    intro t ht
    have hle : t ≤ R / 2 := by
      have hlt : t < R / 2 := (abs_lt.mp ht).2
      exact le_of_lt hlt
    change riseProfile R t * dropProfile M t * t⁻¹ = 0
    rw [riseProfile_zero_of_le R hR hle]
    ring
  exact contDiff_norm_comp_of_zero_near (contDiff_kernelProfile1D R M hR hM) hhalf hS0

/-- The truncated Newton kernel has compact support. -/
lemma hasCompactSupport_newtonKernel (R M : ℝ) (hM : 0 < M) :
    HasCompactSupport (newtonKernel R M) := by
  change HasCompactSupport (fun x : ℝ³ => kernelProfile1D R M ‖x‖)
  refine HasCompactSupport.intro' (K := Metric.closedBall (0 : ℝ³) (4 * M)) ?_ ?_ ?_
  · exact ProperSpace.isCompact_closedBall (0 : ℝ³) (4 * M)
  · exact isClosed_closedBall
  · intro x hx
    have hMx : 4 * M < ‖x‖ := by
      have hd : ¬ dist x 0 ≤ 4 * M := hx
      simpa [dist_eq_norm, dist_zero_right] using (not_le.mp hd)
    have hge : 4 * M ≤ ‖x‖ := le_of_lt hMx
    dsimp [kernelProfile1D]
    rw [dropProfile_zero_of_ge M hM hge]
    ring





/-- The Laplacian of the truncated kernel is `≤ 8·M2/ε³` on the inner annulus `ε/2 ≤ ‖x‖ ≤ ε`. -/
lemma kernel_laplacian_bound_annulus (M2 : ℝ) (hM2 : 0 ≤ M2)
    (hbnd2 : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ‖deriv (deriv Real.smoothTransition) s‖ ≤ M2)
    {ε M : ℝ} (hε : 0 < ε) (hM : 0 < M) (hεM : ε < 2 * M) :
    ∀ x : ℝ³, ε / 2 ≤ ‖x‖ → ‖x‖ ≤ ε → ‖(Δ (newtonKernel ε M)) x‖ ≤ (8 * M2) / ε ^ 3 := by
  intro x hlo hhi
  have hxpos : 0 < ‖x‖ := lt_of_lt_of_le (by positivity : 0 < ε / 2) hlo
  have hx : x ≠ 0 := norm_ne_zero_iff.mp (ne_of_gt hxpos)
  let V : ℝ → ℝ := fun t => riseProfile ε t * dropProfile M t
  have hker : (newtonKernel ε M) = fun y : ℝ³ => V ‖y‖ * (‖y‖ : ℝ)⁻¹ := by
    funext y
    dsimp [newtonKernel, kernelProfile1D, V]
  have hV2 : ContDiff ℝ 2 V := by
    dsimp [V]
    exact ((contDiff_riseProfile ε (ne_of_gt hε)).mul
      (contDiff_dropProfile M (ne_of_gt hM))).of_le (by decide : (2 : ℕ∞ω) ≤ ∞)
  have hmain := laplacian_div_norm_identity V hV2 hx
  have hΔeq : (Δ (newtonKernel ε M)) x = deriv (deriv V) ‖x‖ * (‖x‖ : ℝ)⁻¹ := by
    calc
      (Δ (newtonKernel ε M)) x = (Δ fun y : ℝ³ => V ‖y‖ * (‖y‖ : ℝ)⁻¹) x := by rw [hker]
      _ = deriv (deriv V) ‖x‖ * (‖x‖ : ℝ)⁻¹ := hmain
  have hV2b : ‖deriv (deriv V) ‖x‖‖ ≤ 4 * M2 / ε ^ 2 := by
    let U : Set ℝ := Set.Ioo 0 (2 * M)
    have hUo : IsOpen U := isOpen_Ioo
    have hUr : ‖x‖ ∈ U := by
      dsimp [U]
      exact ⟨hxpos, lt_of_le_of_lt hhi hεM⟩
    have hVeq : ∀ s ∈ U, V s = riseProfile ε s := by
      intro s hs
      dsimp [V]
      rw [dropProfile_one_of_le M hM (le_of_lt hs.2)]
      ring
    have hder2eq : deriv (deriv V) ‖x‖ = deriv (deriv (riseProfile ε)) ‖x‖ :=
      deriv_two_eq_of_eventuallyEq_open (f := V) (g := riseProfile ε) (r := ‖x‖) U hUo hUr hVeq
    have hder2u := deriv_two_riseProfile ε (ne_of_gt hε) ‖x‖
    have harg : 2 * ‖x‖ / ε - 1 ∈ Set.Icc (0 : ℝ) 1 := by
      constructor
      · have h1 : 1 ≤ 2 * ‖x‖ / ε := by
          rw [le_div_iff₀ hε]
          linarith [hlo]
        linarith
      · have h2 : 2 * ‖x‖ / ε ≤ 2 := by
          rw [div_le_iff₀ hε]
          linarith [hhi]
        linarith
    have hbnd := hbnd2 (2 * ‖x‖ / ε - 1) harg
    have hpos4 : 0 ≤ 4 / ε ^ 2 := by positivity
    calc
      ‖deriv (deriv V) ‖x‖‖ = ‖deriv (deriv (riseProfile ε)) ‖x‖‖ := by rw [hder2eq]
      _ = ‖(4 / ε ^ 2) * (deriv (deriv Real.smoothTransition)) (2 * ‖x‖ / ε - 1)‖ := by rw [hder2u]
      _ = (4 / ε ^ 2) * ‖(deriv (deriv Real.smoothTransition)) (2 * ‖x‖ / ε - 1)‖ := by
            simp [abs_of_nonneg hpos4]
      _ ≤ (4 / ε ^ 2) * M2 := by
            exact mul_le_mul_of_nonneg_left hbnd hpos4
      _ = 4 * M2 / ε ^ 2 := by ring
  have hle1 : ‖(Δ (newtonKernel ε M)) x‖ = ‖deriv (deriv V) ‖x‖ * (‖x‖ : ℝ)⁻¹‖ := by rw [hΔeq]
  have hle2 : ‖deriv (deriv V) ‖x‖ * (‖x‖ : ℝ)⁻¹‖ ≤ (4 * M2 / ε ^ 2) * (2 / ε) := by
    calc
      ‖deriv (deriv V) ‖x‖ * (‖x‖ : ℝ)⁻¹‖ = ‖deriv (deriv V) ‖x‖‖ * ‖(‖x‖ : ℝ)⁻¹‖ := by simp
      _ ≤ (4 * M2 / ε ^ 2) * (2 / ε) := by
            have hinvle : (‖x‖ : ℝ)⁻¹ ≤ (ε / 2)⁻¹ :=
              (inv_le_inv₀ hxpos (by positivity : 0 < ε / 2)).2 hlo
            have h3 : (ε / 2)⁻¹ = 2 / ε := by field_simp
            have hn : ‖(‖x‖ : ℝ)⁻¹‖ = (‖x‖ : ℝ)⁻¹ := by
              exact abs_of_nonneg (inv_nonneg.mpr (norm_nonneg x))
            have h1 : ‖(‖x‖ : ℝ)⁻¹‖ ≤ 2 / ε := by
              rw [hn, ← h3]
              exact hinvle
            exact mul_le_mul hV2b h1 (norm_nonneg ((‖x‖ : ℝ)⁻¹)) (by positivity : 0 ≤ 4 * M2 / ε ^ 2)
  have hfinal : (4 * M2 / ε ^ 2) * (2 / ε) = (8 * M2) / ε ^ 3 := by
    field_simp [hε]
    ring
  calc
    ‖(Δ (newtonKernel ε M)) x‖ = ‖deriv (deriv V) ‖x‖ * (‖x‖ : ℝ)⁻¹‖ := hle1
    _ ≤ (4 * M2 / ε ^ 2) * (2 / ε) := hle2
    _ = (8 * M2) / ε ^ 3 := hfinal
    _ ≤ (8 * M2) / ε ^ 3 := le_rfl


/-- The Laplacian of the truncated kernel is bounded by `C/ε³` on the ball of radius `ε`. -/
lemma kernel_laplacian_bound_ball (M2 : ℝ) (hM2 : 0 ≤ M2)
    (hbnd2 : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ‖deriv (deriv Real.smoothTransition) s‖ ≤ M2)
    {ε M : ℝ} (hε : 0 < ε) (hM : 0 < M) (hεM : ε < 2 * M) :
    ∀ x : ℝ³, ‖x‖ ≤ ε → ‖(Δ (newtonKernel ε M)) x‖ ≤ (8 * M2) / ε ^ 3 := by
  intro x hx
  by_cases hsmall : ‖x‖ < ε / 2
  · have hz : (Δ (newtonKernel ε M)) x = 0 := laplacian_newtonKernel_zero_inner hε hM hsmall
    rw [hz]
    simpa using div_nonneg (mul_nonneg (by norm_num : 0 ≤ (8 : ℝ)) hM2) (pow_nonneg (le_of_lt hε) 3)
  · have hlo : ε / 2 ≤ ‖x‖ := le_of_not_gt hsmall
    exact kernel_laplacian_bound_annulus M2 hM2 hbnd2 hε hM hεM x hlo hx


/-- A constant multiple of a compactly supported function has compact support. -/
lemma hasCompactSupport_const_mul_fun (c : ℝ) (g : ℝ³ → ℝ) (hcs : HasCompactSupport g) :
    HasCompactSupport (fun x : ℝ³ => c * g x) := by
  refine HasCompactSupport.intro' (K := tsupport g) hcs (isClosed_tsupport g) ?_
  intro x hx
  by_cases hz : g x = 0
  · simp [hz]
  · exfalso
    apply hx
    exact subset_tsupport g (by simpa [Function.support] using hz)

/-! ## ε-sequence helpers -/

/-- `ε n = 1/(n+2)`, used as the inner cutoff radius of the truncated kernel. -/
def epsN (n : ℕ) : ℝ := (((n + 2 : ℕ) : ℝ)⁻¹)

lemma epsN_pos (n : ℕ) : 0 < epsN n := by
  dsimp [epsN]
  positivity

lemma epsN_nonneg (n : ℕ) : 0 ≤ epsN n := le_of_lt (epsN_pos n)

lemma epsN_le_one (n : ℕ) : epsN n ≤ 1 := by
  dsimp [epsN]
  have h1n : (1 : ℕ) ≤ n + 2 := by omega
  have hc : (1 : ℝ) ≤ ((n + 2 : ℕ) : ℝ) := by exact_mod_cast h1n
  exact inv_le_one_of_one_le₀ hc

lemma tendsto_epsN : Tendsto (fun n : ℕ => epsN n) atTop (𝓝 (0 : ℝ)) := by
  have hb : Tendsto (fun n : ℕ => ((n : ℕ) : ℝ)⁻¹) atTop (𝓝 (0 : ℝ)) :=
    tendsto_inv_atTop_nhds_zero_nat
  have hshift : Tendsto (fun n : ℕ => n + 2) atTop atTop := by
    exact tendsto_atTop_atTop.2 (fun b => ⟨b, fun a ha => by omega⟩)
  convert hb.comp hshift using 1
  ext n
  norm_num [epsN]

/-- Inside the ball of radius `2M`, the truncated kernels converge pointwise to `‖x‖⁻¹`. -/
lemma kernel_tendsto_inv {M : ℝ} (hM : 0 < M) {x : ℝ³} (hx : ‖x‖ ≤ 2 * M) :
    Tendsto (fun n : ℕ => newtonKernel (epsN n) M x) atTop (𝓝 ((‖x‖ : ℝ)⁻¹)) := by
  by_cases hx0 : x = 0
  · subst x
    have hzero : ∀ n : ℕ, newtonKernel (epsN n) M (0 : ℝ³) = 0 := by
      intro n
      exact newtonKernel_zero_small (epsN_pos n) (by
        rw [norm_zero]
        exact div_nonneg (epsN_nonneg n) (by norm_num))
    have htgt : ((‖(0 : ℝ³)‖ : ℝ)⁻¹) = 0 := by simp
    rw [htgt]
    exact tendsto_const_nhds.congr'
      (Eventually.of_forall (fun n : ℕ => (hzero n).symm) :
        (fun _ : ℕ => (0 : ℝ)) =ᶠ[atTop] (fun n : ℕ => newtonKernel (epsN n) M (0 : ℝ³)))
  · have hrpos : 0 < ‖x‖ := norm_pos_iff.mpr hx0
    have hev : ∀ᶠ n : ℕ in atTop, epsN n ≤ ‖x‖ := by
      have hmem : Metric.ball (0 : ℝ) ‖x‖ ∈ 𝓝 (0 : ℝ) := Metric.ball_mem_nhds (0 : ℝ) hrpos
      filter_upwards [tendsto_epsN hmem] with n hn
      have hlt : epsN n < ‖x‖ := by
        have habs : |epsN n| < ‖x‖ := by simpa [Real.dist_eq] using hn
        exact (abs_lt.mp habs).2
      exact le_of_lt hlt
    have hev_eq : (fun n : ℕ => newtonKernel (epsN n) M x) =ᶠ[atTop] (fun _ : ℕ => (‖x‖ : ℝ)⁻¹) := by
      filter_upwards [hev] with n hn
      exact newtonKernel_eq_inv (epsN_pos n) hM hn hx
    exact (tendsto_const_nhds.congr' hev_eq.symm)

/-! ## Bound for the Green-RHS integrals `∫ ψ·Δkₙ` -/

/-- `∫ψ·Δkₙ` is concentrated on the ball of radius `ε n`, where it is bounded by
`(8M2/ε³)·(Lε)·(4π/3·ε³)`. -/
lemma rhs_integral_bound {ψ : ℝ³ → ℝ} {L M M2 : ℝ} (hL0 : 0 ≤ L) (hM20 : 0 ≤ M2)
    (hM2b : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ‖deriv (deriv Real.smoothTransition) s‖ ≤ M2)
    (hLipb : ∀ x : ℝ³, ‖x‖ ≤ 1 → ‖ψ x‖ ≤ L * ‖x‖)
    (hM : 0 < M) (h2M : (1 : ℝ) < 2 * M)
    (hψbig : ∀ x : ℝ³, 2 * M ≤ ‖x‖ → ψ x = 0) :
    ∀ n : ℕ, ‖∫ x : ℝ³, ψ x * (Δ (newtonKernel (epsN n) M)) x‖ ≤
      (((8 * M2) / (epsN n) ^ 3) * (L * epsN n)) * (((4 / 3) * π) * (epsN n) ^ 3) := by
  intro n
  let S : Set ℝ³ := Metric.closedBall (0 : ℝ³) (epsN n)
  let g : ℝ³ → ℝ := fun x => ψ x * (Δ (newtonKernel (epsN n) M)) x
  have hzero_out : ∀ x : ℝ³, x ∉ S → g x = 0 := by
    intro x hxS
    dsimp [g]
    have hgt : epsN n < ‖x‖ := by
      have hle : ¬ ‖x‖ ≤ epsN n := by
        intro hxle
        apply hxS
        simpa [S, Metric.mem_closedBall, dist_zero_right] using hxle
      exact lt_of_not_ge hle
    by_cases h2 : ‖x‖ < 2 * M
    · have hΔ0 : (Δ (newtonKernel (epsN n) M)) x = 0 :=
        laplacian_newtonKernel_zero_middle (epsN_pos n) hM hgt h2
      simp [hΔ0]
    · have hge : 2 * M ≤ ‖x‖ := le_of_not_gt h2
      have hψ0 : ψ x = 0 := hψbig x hge
      simp [hψ0]
  have hind : g = S.indicator g := by
    funext x
    by_cases hx : x ∈ S
    · simp [hx]
    · simp [hx, hzero_out x hx]
  have hmeasS : MeasurableSet S := by dsimp [S]; exact measurableSet_closedBall
  have heq : (∫ x : ℝ³, g x) = ∫ x in S, g x := by
    calc
      (∫ x : ℝ³, g x) = ∫ x : ℝ³, S.indicator g x := by
            exact congrArg (fun h : ℝ³ → ℝ => ∫ x : ℝ³, h x) hind
      _ = ∫ x in S, g x := integral_indicator hmeasS
  have hfin : (volume : Measure ℝ³) S < ⊤ := by
    dsimp [S]
    rw [volume_ball_r3 (epsN n) (epsN_nonneg n)]
    exact lt_top_iff_ne_top.mpr ENNReal.ofReal_ne_top
  have hεM : epsN n < 2 * M := lt_of_le_of_lt (epsN_le_one n) h2M
  have hbnd : ∀ x ∈ S, ‖g x‖ ≤ (((8 * M2) / (epsN n) ^ 3) * (L * epsN n)) := by
    intro x hx
    dsimp [g]
    have hxnorm : ‖x‖ ≤ epsN n := by simpa [S, Metric.mem_closedBall, dist_zero_right] using hx
    have hΔb : ‖(Δ (newtonKernel (epsN n) M)) x‖ ≤ (8 * M2) / (epsN n) ^ 3 :=
      kernel_laplacian_bound_ball M2 hM20 hM2b (epsN_pos n) hM hεM x hxnorm
    have hLb : ‖ψ x‖ ≤ L * epsN n := by
      have hx1 : ‖x‖ ≤ 1 := le_trans hxnorm (epsN_le_one n)
      have hb1 := hLipb x hx1
      exact le_trans hb1 (mul_le_mul_of_nonneg_left hxnorm hL0)
    have hΔ0' : 0 ≤ ‖(Δ (newtonKernel (epsN n) M)) x‖ := norm_nonneg _
    have hLM0 : 0 ≤ L * epsN n := mul_nonneg hL0 (epsN_nonneg n)
    have hb2 := mul_le_mul hLb hΔb hΔ0' hLM0
    calc
      ‖ψ x * (Δ (newtonKernel (epsN n) M)) x‖ ≤ ‖ψ x‖ * ‖(Δ (newtonKernel (epsN n) M)) x‖ := norm_mul_le _ _
      _ ≤ (L * epsN n) * ((8 * M2) / (epsN n) ^ 3) := hb2
      _ = ((8 * M2) / (epsN n) ^ 3) * (L * epsN n) := by ring
  have hbnd' := norm_setIntegral_le_of_norm_le_const (s := S) (f := g) (μ := (volume : Measure ℝ³)) hfin hbnd
  calc
    ‖∫ x : ℝ³, ψ x * (Δ (newtonKernel (epsN n) M)) x‖ = ‖∫ x in S, g x‖ := by rw [heq]
    _ ≤ (((8 * M2) / (epsN n) ^ 3) * (L * epsN n)) * (volume : Measure ℝ³).real S := hbnd'
    _ ≤ (((8 * M2) / (epsN n) ^ 3) * (L * epsN n)) * (((4 / 3) * π) * (epsN n) ^ 3) := by
          have hvol : (volume : Measure ℝ³).real S = ((4 / 3) * π) * (epsN n) ^ 3 := by
            dsimp [S]
            rw [measureReal_def]
            rw [volume_ball_r3 (epsN n) (epsN_nonneg n)]
            have h43 : (0 : ℝ) ≤ (4 / 3) * π := by positivity
            exact ENNReal.toReal_ofReal (mul_nonneg h43 (pow_nonneg (epsN_nonneg n) 3))
          rw [hvol]

/-- The Green-RHS integrals `∫ ψ·Δkₙ` tend to zero. -/
lemma rhs_integral_seq_tendsto_zero {ψ : ℝ³ → ℝ} {L M : ℝ} (hL0 : 0 ≤ L)
    (hLipb : ∀ x : ℝ³, ‖x‖ ≤ 1 → ‖ψ x‖ ≤ L * ‖x‖)
    (hM : 0 < M) (h2M : (1 : ℝ) < 2 * M)
    (hψbig : ∀ x : ℝ³, 2 * M ≤ ‖x‖ → ψ x = 0) :
    Tendsto (fun n : ℕ => ∫ x : ℝ³, ψ x * (Δ (newtonKernel (epsN n) M)) x) atTop (𝓝 0) := by
  rcases exists_bound_smoothTransition_deriv_two with ⟨M2, hM20, hM2b⟩
  let C : ℝ := (32 : ℝ) / 3 * π * L * M2
  have hb : ∀ n : ℕ, ‖∫ x : ℝ³, ψ x * (Δ (newtonKernel (epsN n) M)) x‖ ≤ C * epsN n := by
    intro n
    have h1 := rhs_integral_bound (ψ := ψ) (L := L) (M := M) (M2 := M2) hL0 hM20 hM2b hLipb hM h2M hψbig n
    have hε : epsN n ≠ 0 := ne_of_gt (epsN_pos n)
    calc
      ‖∫ x : ℝ³, ψ x * (Δ (newtonKernel (epsN n) M)) x‖
          ≤ (((8 * M2) / (epsN n) ^ 3) * (L * epsN n)) * (((4 / 3) * π) * (epsN n) ^ 3) := h1
      _ = (32 / 3 * π * L * M2) * epsN n := by
            field_simp [hε]
            ring
      _ = C * epsN n := by rfl
  let J : ℕ → ℝ := fun n => ∫ x : ℝ³, ψ x * (Δ (newtonKernel (epsN n) M)) x
  have hlimC : Tendsto (fun n : ℕ => C * epsN n) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds (x := C)).mul tendsto_epsN
  have hlimlo : Tendsto (fun n : ℕ => -(C * epsN n)) atTop (𝓝 0) := by
    simpa using hlimC.neg
  have hlo : ∀ᶠ n : ℕ in atTop, -(C * epsN n) ≤ J n := by
    apply Eventually.of_forall
    intro n
    have h := hb n
    have habs : |J n| ≤ C * epsN n := by simpa [J] using h
    exact (abs_le.mp habs).1
  have hhi : ∀ᶠ n : ℕ in atTop, J n ≤ C * epsN n := by
    apply Eventually.of_forall
    intro n
    have h := hb n
    have habs : |J n| ≤ C * epsN n := by simpa [J] using h
    exact (abs_le.mp habs).2
  simpa [J] using (Filter.Tendsto.squeeze' hlimlo hlimC hlo hhi)

/-! ## The main zero-integral identity -/

/-- Remainder Newton identity for `ψ` vanishing to first order at the origin. -/
lemma zero_integral_lipschitz {ψ : ℝ³ → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hψcs : HasCompactSupport ψ)
    (hLip : ∃ L : ℝ, 0 ≤ L ∧ ∀ x : ℝ³, ‖x‖ ≤ 1 → ‖ψ x‖ ≤ L * ‖x‖) :
    (∫ x : ℝ³, (Δ ψ) x * (‖x‖ : ℝ)⁻¹) = 0 := by
  rcases hLip with ⟨L, hL0, hLipb⟩
  -- pick a large positive radius M whose double contains the support of ψ
  rcases hψcs.isBounded.subset_closedBall (0 : ℝ³) with ⟨B₀, hBts⟩
  let B : ℝ := max B₀ 1
  let M : ℝ := B + 1
  have hB0 : 0 ≤ B := by dsimp [B]; exact le_trans zero_le_one (le_max_right B₀ 1)
  have hB0le : B₀ ≤ B := by dsimp [B]; exact le_max_left B₀ 1
  have hM : 0 < M := by dsimp [M]; linarith
  have h2Mbig : (1 : ℝ) < 2 * M := by dsimp [M]; linarith
  have hB2M : B < 2 * M := by dsimp [M]; linarith
  have htsB : tsupport ψ ⊆ Metric.closedBall (0 : ℝ³) B := by
    intro x hx
    exact Metric.closedBall_subset_closedBall hB0le (hBts hx)
  -- ψ vanishes outside the closed ball of radius B (hence outside the ball of radius 2M)
  have hψout : ∀ x : ℝ³, B < ‖x‖ → ψ x = 0 := by
    intro x hxB
    by_contra hz
    have hxsupp : x ∈ Function.support ψ := by simpa [Function.support] using hz
    have hxB' : x ∈ Metric.closedBall (0 : ℝ³) B := htsB (subset_tsupport ψ hxsupp)
    have hxle : ‖x‖ ≤ B := by simpa [Metric.mem_closedBall, dist_zero_right] using hxB'
    linarith
  have hψbig : ∀ x : ℝ³, 2 * M ≤ ‖x‖ → ψ x = 0 := by
    intro x hx
    exact hψout x (lt_of_lt_of_le hB2M hx)
  -- Green-RHS limit
  have hJlim : Tendsto (fun n : ℕ => ∫ x : ℝ³, ψ x * (Δ (newtonKernel (epsN n) M)) x) atTop (𝓝 0) :=
    rhs_integral_seq_tendsto_zero (ψ := ψ) (L := L) hL0 hLipb hM h2Mbig hψbig
  -- dominated convergence for the Green-LHS
  let F : ℕ → ℝ³ → ℝ := fun n x => (Δ ψ) x * newtonKernel (epsN n) M x
  let f : ℝ³ → ℝ := fun x => (Δ ψ) x * (‖x‖ : ℝ)⁻¹
  let bound : ℝ³ → ℝ := fun x => ‖(Δ ψ) x * (‖x‖ : ℝ)⁻¹‖
  have hFcont : ∀ n : ℕ, Continuous (fun x : ℝ³ => F n x) := by
    intro n
    dsimp [F]
    exact (continuous_laplacian ψ hψ).mul
      (ContDiff.continuous (contDiff_newtonKernel (epsN n) M (epsN_pos n) hM))
  have hFmeas : ∀ n : ℕ, AEStronglyMeasurable (F n) volume := by
    intro n
    exact Continuous.aestronglyMeasurable (hFcont n)
  have hboundInt : Integrable bound volume := by
    dsimp [bound]
    have hgi : Integrable (fun x : ℝ³ => (Δ ψ) x * (‖x‖ : ℝ)⁻¹) :=
      integrable_mul_norm_inv (continuous_laplacian ψ hψ) (hasCompactSupport_laplacian ψ hψcs)
    exact hgi.norm
  have hbnd : ∀ n : ℕ, ∀ᵐ x : ℝ³ ∂volume, ‖F n x‖ ≤ bound x := by
    intro n
    refine ae_of_all volume ?_
    intro x
    dsimp [F, bound]
    have hk0 : 0 ≤ newtonKernel (epsN n) M x := newtonKernel_nonneg (epsN n) M x
    calc
      ‖(Δ ψ) x * newtonKernel (epsN n) M x‖
          ≤ ‖(Δ ψ) x‖ * ‖newtonKernel (epsN n) M x‖ := norm_mul_le _ _
      _ = ‖(Δ ψ) x‖ * newtonKernel (epsN n) M x := by simp [abs_of_nonneg hk0]
      _ ≤ ‖(Δ ψ) x‖ * (‖x‖ : ℝ)⁻¹ := mul_le_mul_of_nonneg_left (newtonKernel_le_inv (epsN n) M x) (norm_nonneg _)
      _ = ‖(Δ ψ) x * (‖x‖ : ℝ)⁻¹‖ := by simp
  -- pointwise convergence of the integrand
  have hpt : ∀ x : ℝ³, Tendsto (fun n : ℕ => F n x) atTop (𝓝 (f x)) := by
    intro x
    by_cases hle : ‖x‖ ≤ 2 * M
    · have hk : Tendsto (fun n : ℕ => newtonKernel (epsN n) M x) atTop (𝓝 ((‖x‖ : ℝ)⁻¹)) :=
        kernel_tendsto_inv hM hle
      have hc : Tendsto (fun _ : ℕ => (Δ ψ) x) atTop (𝓝 ((Δ ψ) x)) := tendsto_const_nhds
      simpa [F, f] using hc.mul hk
    · have hgt : 2 * M < ‖x‖ := not_le.mp hle
      have hΔ0 : (Δ ψ) x = 0 := by
        apply laplacian_eq_zero_of_not_mem_tsupport ψ
        intro hxmem
        have hxB' : x ∈ Metric.closedBall (0 : ℝ³) B := htsB hxmem
        have hxle : ‖x‖ ≤ B := by simpa [Metric.mem_closedBall, dist_zero_right] using hxB'
        linarith
      have hF0 : ∀ n : ℕ, F n x = 0 := by
        intro n
        dsimp [F]
        simp [hΔ0]
      have hfx : f x = 0 := by dsimp [f]; simp [hΔ0]
      rw [hfx]
      exact tendsto_const_nhds.congr'
        (Eventually.of_forall (fun n : ℕ => (hF0 n).symm) : (fun _ : ℕ => (0 : ℝ)) =ᶠ[atTop] (fun n : ℕ => F n x))
  have hlim : ∀ᵐ x : ℝ³ ∂volume, Tendsto (fun n : ℕ => F n x) atTop (𝓝 (f x)) := by
    exact ae_of_all volume hpt
  have hdc : Tendsto (fun n : ℕ => ∫ x : ℝ³, F n x) atTop (𝓝 (∫ x : ℝ³, f x)) :=
    MeasureTheory.tendsto_integral_of_dominated_convergence (F := F) (f := f) bound hFmeas hboundInt hbnd hlim
  -- Green's identity connects the two sequences
  have hgreen : ∀ n : ℕ, (∫ x : ℝ³, F n x) =
      ∫ x : ℝ³, ψ x * (Δ (newtonKernel (epsN n) M)) x := by
    intro n
    dsimp [F]
    exact integral_laplacian_mul hψ (contDiff_newtonKernel (epsN n) M (epsN_pos n) hM) hψcs
      (hasCompactSupport_newtonKernel (epsN n) M hM)
  have hIJ : (fun n : ℕ => ∫ x : ℝ³, F n x) =
      fun n : ℕ => ∫ x : ℝ³, ψ x * (Δ (newtonKernel (epsN n) M)) x := by
    funext n
    exact hgreen n
  have hdc0 : Tendsto (fun n : ℕ => ∫ x : ℝ³, F n x) atTop (𝓝 0) := by
    simpa [hIJ] using hJlim
  have hmain : (∫ x : ℝ³, f x) = 0 := tendsto_nhds_unique hdc hdc0
  simpa [f] using hmain



/-- A smooth function is Lipschitz on the unit ball: `|φ(x)−φ(0)| ≤ C·‖x‖`. -/
lemma smooth_lipschitz_at_zero (φ : ℝ³ → ℝ) (hφ : ContDiff ℝ ∞ φ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ³, ‖x‖ ≤ 1 → ‖φ x - φ 0‖ ≤ C * ‖x‖ := by
  let K : Set ℝ³ := Metric.closedBall (0 : ℝ³) 1
  have hK : IsCompact K := ProperSpace.isCompact_closedBall (0 : ℝ³) 1
  have hKne : K.Nonempty := ⟨0, by simp [K]⟩
  have hfderivCont : ContinuousOn (fun x : ℝ³ => ‖fderiv ℝ φ x‖) K := by
    have hcont : Continuous (fun x : ℝ³ => (fderiv ℝ φ x : ℝ³ →L[ℝ] ℝ)) :=
      ContDiff.continuous_fderiv hφ (by norm_num : (∞ : ℕ∞ω) ≠ 0)
    exact hcont.norm.continuousOn
  rcases IsCompact.exists_isMaxOn hK hKne hfderivCont with ⟨x₀, hx₀, hmax⟩
  let C : ℝ := ‖fderiv ℝ φ x₀‖
  have hC : 0 ≤ C := by
    dsimp [C]
    exact norm_nonneg _
  refine ⟨C, hC, ?_⟩
  intro x hx
  have hxK : x ∈ K := by
    dsimp [K]
    simpa [dist_eq_norm, dist_zero_right] using hx
  have h0K : (0 : ℝ³) ∈ K := by simp [K]
  have hdiff : ∀ y ∈ K, DifferentiableAt ℝ φ y := by
    intro y hy
    exact hφ.differentiable (by norm_num : (∞ : ℕ∞ω) ≠ 0) y
  have hbound : ∀ y ∈ K, ‖fderiv ℝ φ y‖ ≤ C := by
    intro y hy
    simpa [C] using hmax hy
  have him := Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ) hdiff hbound
    (convex_closedBall (0 : ℝ³) 1) h0K hxK
  simpa using him

/-- Newton identity at the origin: `∫ (Δφ)(x)/‖x‖ dx = −4π·φ(0)`. -/
theorem newton_integral_delta_zero (φ : ℝ³ → ℝ) (hφ : ContDiff ℝ ∞ φ)
    (hφcs : HasCompactSupport φ) :
    (∫ x : ℝ³, (Δ φ) x * (‖x‖ : ℝ)⁻¹) = -4 * π * φ 0 := by
  obtain ⟨θ, hθc, hθcs, _hθ0le, _hθ1, hθrad, hθone, _hθzero⟩ :=
    exists_smooth_radial_cutoff (R := 1) (M := 2) (by norm_num) (by norm_num)
  let c : ℝ := φ 0
  let ψ : ℝ³ → ℝ := fun x => φ x - c * θ x
  have hθ0 : θ 0 = 1 := hθone 0 (by simp)
  have hψc : ContDiff ℝ ∞ ψ := by
    dsimp [ψ]
    exact hφ.sub ((contDiff_const : ContDiff ℝ ∞ fun _ : ℝ³ => c).mul hθc)
  have hψcs : HasCompactSupport ψ := by
    dsimp [ψ]
    exact hφcs.sub (hasCompactSupport_const_mul_fun c θ hθcs)
  rcases smooth_lipschitz_at_zero φ hφ with ⟨C, hC0, hC⟩
  have hLipψ : ∃ L : ℝ, 0 ≤ L ∧ ∀ x : ℝ³, ‖x‖ ≤ 1 → ‖ψ x‖ ≤ L * ‖x‖ := by
    refine ⟨C, hC0, ?_⟩
    intro x hx
    have hθ1 : θ x = 1 := hθone x hx
    have hcalc : ψ x = φ x - φ 0 := by
      dsimp [ψ, c]
      rw [hθ1]
      ring
    rw [hcalc]
    exact hC x hx
  have hfψ_int : Integrable (fun x : ℝ³ => (Δ ψ) x * (‖x‖ : ℝ)⁻¹) :=
    integrable_mul_norm_inv (continuous_laplacian ψ hψc) (hasCompactSupport_laplacian ψ hψcs)
  have hfθ_int : Integrable (fun x : ℝ³ => (Δ θ) x * (‖x‖ : ℝ)⁻¹) :=
    integrable_mul_norm_inv (continuous_laplacian θ hθc) (hasCompactSupport_laplacian θ hθcs)
  let fψ : ℝ³ → ℝ := fun x => (Δ ψ) x * (‖x‖ : ℝ)⁻¹
  let fθ : ℝ³ → ℝ := fun x => (Δ θ) x * (‖x‖ : ℝ)⁻¹
  let cfθ : ℝ³ → ℝ := fun x => c * fθ x
  have hcfθ_int : Integrable cfθ := by
    dsimp [cfθ, fθ]
    exact MeasureTheory.Integrable.const_mul hfθ_int c
  -- Δφ = Δψ + c·Δθ pointwise
  have hΔφ : (fun x : ℝ³ => (Δ φ) x) = fun x : ℝ³ => (Δ ψ) x + c * (Δ θ) x := by
    funext x
    have hφeq : φ = fun y : ℝ³ => ψ y + c * θ y := by
      funext y
      dsimp [ψ, c]
      ring
    have hΔ1 : (Δ φ) x = (Δ (fun y : ℝ³ => ψ y + c * θ y)) x := by
      exact congrFun (congrArg (fun g : ℝ³ → ℝ => (Δ g)) hφeq) x
    calc
      (Δ φ) x = (Δ (fun y : ℝ³ => ψ y + c * θ y)) x := hΔ1
      _ = (Δ ψ) x + (Δ (fun y : ℝ³ => c * θ y)) x := by
            rw [laplacian_add_smooth ψ (fun y : ℝ³ => c * θ y) hψc
              ((contDiff_const : ContDiff ℝ ∞ fun _ : ℝ³ => c).mul hθc)]
      _ = (Δ ψ) x + c * (Δ θ) x := by
            rw [laplacian_smul_smooth c θ hθc]
  have hsum_eq : (fun x : ℝ³ => ((Δ ψ) x + c * (Δ θ) x) * (‖x‖ : ℝ)⁻¹) =
      fun x : ℝ³ => fψ x + cfθ x := by
    funext x
    dsimp [fψ, fθ, cfθ]
    ring
  have hψ0int : (∫ x : ℝ³, fψ x) = 0 := by
    dsimp [fψ]
    exact zero_integral_lipschitz hψc hψcs hLipψ
  have hθdelta : (∫ x : ℝ³, fθ x) = -4 * π := by
    dsimp [fθ]
    have hr := radial_delta_norm_inv hθc hθcs hθrad hθ0
    -- hr : ∫ x, ‖x‖⁻¹·(Δθ)x = -4π
    calc
      (∫ x : ℝ³, (Δ θ) x * (‖x‖ : ℝ)⁻¹)
          = ∫ x : ℝ³, (‖x‖ : ℝ)⁻¹ * (Δ θ) x := by
            congr 1
            funext x
            ring
      _ = -4 * π := hr
  have hcθ : (∫ x : ℝ³, cfθ x) = c * -4 * π := by
    calc
      (∫ x : ℝ³, cfθ x) = ∫ x : ℝ³, c * fθ x := by rfl
      _ = c * (∫ x : ℝ³, fθ x) := by
            exact MeasureTheory.integral_const_mul c fθ
      _ = c * (-4 * π) := by rw [hθdelta]
      _ = c * -4 * π := by ring
  calc
    (∫ x : ℝ³, (Δ φ) x * (‖x‖ : ℝ)⁻¹)
        = ∫ x : ℝ³, ((Δ ψ) x + c * (Δ θ) x) * (‖x‖ : ℝ)⁻¹ := by
          congr 1
          funext x
          rw [congrFun hΔφ x]
    _ = ∫ x : ℝ³, fψ x + cfθ x := by
          rw [hsum_eq]
    _ = (∫ x : ℝ³, fψ x) + ∫ x : ℝ³, cfθ x := by
          exact MeasureTheory.integral_add hfψ_int hcfθ_int
    _ = 0 + ∫ x : ℝ³, cfθ x := by rw [hψ0int]
    _ = 0 + c * -4 * π := by rw [hcθ]
    _ = -4 * π * φ 0 := by
          dsimp [c]
          ring

end Submission.BoseGases
