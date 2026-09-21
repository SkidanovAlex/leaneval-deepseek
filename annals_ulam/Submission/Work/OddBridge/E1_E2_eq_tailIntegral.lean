import Mathlib
import Submission.Work.OddVolterra.Defs
import Submission.Work.OddVolterra.RowIdentity.contDiff_trunc_pow_sqrt

/-!
# The tail-integral form of the odd inhomogeneities `E₁`, `E₂`

Ryabogin's odd-dimensional transition-slope argument differentiates the two
moment equations of the *perturbed* body.  The two inhomogeneities `E₁`, `E₂`
are the corresponding derivatives of the moment integrands of the *ball*
semicircle, integrated over the fixed interval `(-x₀(1), x₀(1))`,
`x₀ = profileX`.

The point of this file is that, on the transition window `[1 - 2τ, 1]` adopted by
the paper, the perturbation `h` of the cutting line *vanishes identically* on
`[1 - τ, ∞)` (this is the content of the hypothesis `htail`).  Hence, near every
slope `s ∈ [99/100, 1]`, the radicand

`ψ_s(t) = f(t)² - (s t + h s)²`

of the perturbed moment integrand agrees with the ball radicand

`B(s,t) = 1 - t²(1 + s²) = 1 - t² - s² t²`,

and therefore both `E₁` and `E₂` re-assemble into the *ball* integrals that the
paper uses as the tail data of its row identities `(t1)` and `(t2)`.

The two ingredients are
* the germ invariance of `iteratedDeriv` (`Filter.EventuallyEq.iteratedDeriv_eq`),
  which lets us replace the perturbed integrand by the ball integrand near `s`;
* the identity `z ^ n * √z = z ^ (n + 1/2)` of `Real.rpow`
  (`pow_mul_sqrt_eq_rpow`), which converts the truncated powers into the
  half-integer powers of the paper.
-/

namespace Work.OddBridge

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval
open Commons.Geometry.Ulam

noncomputable section

/-! ## The vanishing of the perturbation on the transition window -/

/-- The hypothesis `htail` of the transition window, in germ form: on a
neighbourhood of every slope `s ∈ [99/100, 1]` the perturbation `h` is zero. -/
lemma h_eventually_zero {h : ℝ → ℝ}
    (htail : ∀ s : ℝ, 1 - Work.OddVolterra.tau ≤ s → h s = 0)
    {s : ℝ} (hs : 99 / 100 ≤ s) : ∀ᶠ u in 𝓝 s, h u = 0 := by
  have hlt : 1 - Work.OddVolterra.tau < s := by
    unfold Work.OddVolterra.tau; linarith
  filter_upwards [isOpen_Ioi.mem_nhds hlt] with u hu
  exact htail u (le_of_lt hu)

/-- On the transition window the perturbation is *locally constant* (equal to
`0`), hence its derivative vanishes. -/
lemma deriv_h_eq_zero_of_tail {h : ℝ → ℝ}
    (htail : ∀ s : ℝ, 1 - Work.OddVolterra.tau ≤ s → h s = 0) {u : ℝ}
    (hu : 1 - Work.OddVolterra.tau < u) : deriv h u = 0 := by
  have heq : h =ᶠ[𝓝 u] (fun _ : ℝ => 0) := by
    filter_upwards [isOpen_Ioi.mem_nhds hu] with v hv
    exact htail v (le_of_lt hv)
  rw [heq.deriv_eq]
  simp

/-- Germ form of `deriv_h_eq_zero_of_tail`. -/
lemma deriv_h_eventually_zero {h : ℝ → ℝ}
    (htail : ∀ s : ℝ, 1 - Work.OddVolterra.tau ≤ s → h s = 0)
    {s : ℝ} (hs : 99 / 100 ≤ s) : ∀ᶠ u in 𝓝 s, deriv h u = 0 := by
  have hlt : 1 - Work.OddVolterra.tau < s := by
    unfold Work.OddVolterra.tau; linarith
  filter_upwards [isOpen_Ioi.mem_nhds hlt] with u hu
  exact deriv_h_eq_zero_of_tail htail hu

/-! ## The radicand of the ball on the section -/

/-- On the transition window the radicand of the perturbed moment integrand, with
the ball `semicircle` as profile and with the perturbation `h` vanishing, is the
ball radicand `1 - t² - u² t²`. -/
lemma psi_semicircle_of_h_eq_zero {h : ℝ → ℝ} {u t : ℝ} (hu : h u = 0)
    (ht : t ∈ Set.Icc (-1 : ℝ) 1) :
    Work.OddVolterra.psi h semicircle u t = 1 - t ^ 2 - u ^ 2 * t ^ 2 := by
  have hsemi : semicircle t ^ 2 = 1 - t ^ 2 := semicircle_sq_of_mem_Icc ht
  unfold Work.OddVolterra.psi Work.OddVolterra.line
  rw [hsemi, hu]
  ring

/-! ## The two integrands -/

/-- Pointwise (in `t`) form of the first row: the `(n+1)`-st derivative of the
perturbed first-moment integrand is the ball expression of the paper. -/
lemma iteratedDeriv_E1_integrand_eq (n : ℕ) {h : ℝ → ℝ}
    (htail : ∀ s : ℝ, 1 - Work.OddVolterra.tau ≤ s → h s = 0)
    {s : ℝ} (hs : 99 / 100 ≤ s) {t : ℝ} (ht : t ∈ Set.Icc (-1 : ℝ) 1) :
    iteratedDeriv (n + 1)
        (fun u : ℝ => Work.OddVolterra.psi h semicircle u t ^ n *
          Real.sqrt (Work.OddVolterra.psi h semicircle u t)) s =
      iteratedDeriv (n + 1)
        (fun u : ℝ => (1 - t ^ 2 - u ^ 2 * t ^ 2) ^ ((n : ℝ) + 1 / 2)) s := by
  refine Filter.EventuallyEq.iteratedDeriv_eq _ ?_
  filter_upwards [h_eventually_zero htail hs] with u hu
  rw [psi_semicircle_of_h_eq_zero hu ht,
    Work.OddVolterra.RowIdentity.pow_mul_sqrt_eq_rpow]

/-- Pointwise (in `t`) form of the second row: the `n`-th derivative of the
perturbed centroid integrand is `t` times the ball expression of the paper. -/
lemma iteratedDeriv_E2_integrand_eq (n : ℕ) (hn : 1 ≤ n) {h : ℝ → ℝ}
    (htail : ∀ s : ℝ, 1 - Work.OddVolterra.tau ≤ s → h s = 0)
    {s : ℝ} (hs : 99 / 100 ≤ s) {t : ℝ} (ht : t ∈ Set.Icc (-1 : ℝ) 1) :
    iteratedDeriv n
        (fun u : ℝ => Work.OddVolterra.psi h semicircle u t ^ (n - 1) *
          Real.sqrt (Work.OddVolterra.psi h semicircle u t) *
          Work.OddVolterra.lineSlope h u t) s =
      t * iteratedDeriv n
        (fun u : ℝ => (1 - t ^ 2 - u ^ 2 * t ^ 2) ^ ((n : ℝ) - 1 / 2)) s := by
  have hev : (fun u : ℝ => Work.OddVolterra.psi h semicircle u t ^ (n - 1) *
        Real.sqrt (Work.OddVolterra.psi h semicircle u t) *
        Work.OddVolterra.lineSlope h u t)
      =ᶠ[𝓝 s]
      (fun u : ℝ => t * (1 - t ^ 2 - u ^ 2 * t ^ 2) ^ ((n : ℝ) - 1 / 2)) := by
    filter_upwards [h_eventually_zero htail hs, deriv_h_eventually_zero htail hs]
      with u hu hdu
    have hpsi := psi_semicircle_of_h_eq_zero hu ht
    have hls : Work.OddVolterra.lineSlope h u t = t := by
      unfold Work.OddVolterra.lineSlope
      rw [hdu]; ring
    rw [hpsi, hls, Work.OddVolterra.RowIdentity.pow_mul_sqrt_eq_rpow (n - 1)]
    have hexp : (((n - 1 : ℕ) : ℝ) + 1 / 2) = (n : ℝ) - 1 / 2 := by
      have hcast : (((n - 1 : ℕ)) : ℝ) = (n : ℝ) - 1 := by
        rw [Nat.cast_sub hn]; norm_num
      rw [hcast]; ring
    rw [hexp]
    ring
  rw [Filter.EventuallyEq.iteratedDeriv_eq n hev, iteratedDeriv_const_mul_field]

/-! ## The tail-integral form of `E₁` and `E₂` -/

theorem E1_E2_eq_tailIntegral (n : ℕ) (hn : 1 ≤ n) {h : ℝ → ℝ}
    (htail : ∀ s : ℝ, 1 - Work.OddVolterra.tau ≤ s → h s = 0)
    {s : ℝ} (hs : 99/100 ≤ s) (hs1 : s ≤ 1) :
    Work.OddVolterra.E1 n h s =
        (∫ t in (-(Commons.Geometry.Ulam.profileX 1))..(Commons.Geometry.Ulam.profileX 1),
          iteratedDeriv (n + 1) (fun u : ℝ => (1 - t ^ 2 - u ^ 2 * t ^ 2) ^ ((n : ℝ) + 1 / 2)) s) ∧
      Work.OddVolterra.E2 n h s =
        (∫ t in (-(Commons.Geometry.Ulam.profileX 1))..(Commons.Geometry.Ulam.profileX 1),
          t * iteratedDeriv n (fun u : ℝ => (1 - t ^ 2 - u ^ 2 * t ^ 2) ^ ((n : ℝ) - 1 / 2)) s) := by
  have hx0pos : 0 < profileX 1 := profileX_pos 1 (by norm_num)
  have hx0sq : (profileX 1) ^ 2 = (1 : ℝ) / 2 := by rw [profileX_sq]; norm_num
  have hx0lt : profileX 1 < 1 := by nlinarith [hx0sq, hx0pos]
  have hle : -(profileX 1) ≤ profileX 1 := by linarith
  constructor
  · rw [Work.OddVolterra.E1]
    apply intervalIntegral.integral_congr
    intro t ht
    have ht' : t ∈ Set.Icc (-(profileX 1)) (profileX 1) := by
      rwa [Set.uIcc_of_le hle] at ht
    exact iteratedDeriv_E1_integrand_eq n htail hs
      ⟨by linarith [ht'.1], by linarith [ht'.2]⟩
  · rw [Work.OddVolterra.E2]
    apply intervalIntegral.integral_congr
    intro t ht
    have ht' : t ∈ Set.Icc (-(profileX 1)) (profileX 1) := by
      rwa [Set.uIcc_of_le hle] at ht
    exact iteratedDeriv_E2_integrand_eq n hn htail hs
      ⟨by linarith [ht'.1], by linarith [ht'.2]⟩

end

end Work.OddBridge
