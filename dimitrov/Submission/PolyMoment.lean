import Mathlib
import Submission.PolyaShell
import Submission.E0Complex

/-!
# E2a completion: polynomial-weighted circle moments (the E2c bridge)

`Submission.PolyaShell.circleIntegral_moment_laurent` records the *monomial*
circle moments of the Laurent branch `g` (with `g X = f (X⁻¹)`, `f` analytic
on `ball 0 ρ₀`, Taylor coefficients `a : ℕ → ℂ`): for every `m : ℕ` and
`0 < ρ` with `ρ⁻¹ < ρ₀`,

    ∮_{|z| = ρ} z^m · g z  =  2πi · a (m+1).

The Pólya/Hankel shell (E2c) must bound the entries of the *complex moment
matrix* `Submission.E0Complex.cMomentMatrix k a p i j =
∑_{r<k} (∑_{s<k} (p i).coeff s · a (s+r)) · (p j).coeff r` (for monic `pᵢ`
of degree `i < k`), and the entry is a *polynomial-weighted* circle moment:

    cMomentMatrix k a p i j  =  (2πi)⁻¹ · ∮_{|z|=ρ} g z · (p i).eval z
                                        · (p j).eval z · z⁻¹ dz .

This module supplies that identity.  Two ingredients beyond
`circleIntegral_moment_laurent`:

1. **The negative-power moment** (`circleIntegral_inv_laurent`):
   `∮_{|z|=ρ} g z · z⁻¹ = 2πi · a 0`.  This is the `k = 0` term of the
   Laurent data `g(z) = Σ a_k z⁻ᵏ` (`∮ z⁻¹⁻ᵏ = 2πi·δ_{k,0}`); it is NOT
   covered by the `m : ℕ`-indexed monomial lemma (whose exponent `m ≥ 0`
   reads off `a (m+1)`).  Proof: copy the proof of
   `circleIntegral_moment_laurent` (uniform convergence of the partial sums
   on the circle, `TendstoUniformlyOn.tendsto_circleIntegral_of_continuousOn`,
   then the *finite* sum at level N: `∮ S_N(z) · z⁻¹ = 2πi · a 0`, using the
   elementary fact `∮ z⁻¹⁻ᵏ = 0` for `k ≥ 1` and `= 2πi` for `k = 0` —
   cf. `PolyaShell.circleIntegral_mul_inv_pow_zero` /
   `PolyaShell.circleIntegral_mul_inv_pow_crit` which handle
   `z^m · (z⁻¹)^k` for natural exponents `m`, `k`; the `z⁻¹` factor is
   `(z⁻¹)^1`; verify carefully which exponent lemma covers `∮ z⁻¹` itself
   (this is `m = 0, k = 1` in the notation `z^m·(z⁻¹)^k` when `z^m = 1`)).
   NOTE on notation: `z⁻¹` in Lean is `z⁻¹` (involution on `ℂ`), NOT
   `(z⁻¹ : ℂ[X])`; `(z⁻¹) ^ k` in PolyaShell is the k-th power of the
   complex inverse.

2. **Linearity over the polynomial factor** (`circleIntegral_poly_moment`):
   expand `W.eval z · z⁻¹ = ∑_{t ≤ W.natDegree} (W.coeff t) · z^(t-1)` —
   careful: the `t = 0` term is `(W.coeff 0) · z⁻¹` (handled by ingredient 1
   with `a 0`), and each `t ≥ 1` term is `(W.coeff t) · z^(t-1)` (handled by
   the monomial lemma with `m := t - 1`, giving `a ((t-1)+1) = a t`); pull
   the *finite* sums out of the circle integral
   (`circleIntegral.integral_fun_sum`, as in PolyaShell), then simplify
   `t - 1 + 1 = t` and `t = 0 → t - 1 = 0` cases with `omega`.

3. **The moment-matrix identity** (`cMomentMatrix_eq_circleIntegral`):
   instantiate with `W := (p i) * (p j)` and rewrite the coefficient
   convolution `(p i * p j).coeff t = ∑_{s ≤ t} (p i).coeff s · (p j).coeff (t-s)`
   (`Polynomial.coeff_mul`) — with `(p i).natDegree = i.val < k` all the
   `s`, `r` indices involved are `< k`, matching the definition of
   `cMomentMatrix` (reindex `r := t - s`; finite sums over `ℕ` ranges).

No sorries may remain.  All statements below are correct as written (they
were derived from the verified monomial lemma and the definition of
`cMomentMatrix`); do not weaken hypotheses.
-/

noncomputable section

open scoped Polynomial Real Topology Complex
open Polynomial Filter

namespace Submission.PolyMoment

open Submission.SqrtTaylor
open Submission.E0Complex
open Submission.PolyaShell


/-- The truncated Laurent summands with an extra `z⁻¹` factor are continuous on
the circle (in the `(z⁻¹)^(k+1)` grouped form). -/
lemma inv_term_continuous (a : ℕ → ℂ) {ρ : ℝ} (hρ : 0 < ρ) (k : ℕ) :
    ContinuousOn (fun z : ℂ => (a k) * (z⁻¹) ^ (k + 1)) (Metric.sphere (0 : ℂ) ρ) := by
  have hcont_inv : ContinuousOn (fun z : ℂ => z⁻¹) (Metric.sphere (0 : ℂ) ρ) :=
    continuousOn_id.inv₀ (fun z hz => ne_zero_of_mem_sphere_zero hρ hz)
  exact (continuousOn_const.mul (hcont_inv.pow (k + 1)))

/-- **Negative-power moments (finite sums).**  For the truncated Laurent data
`S_N(z) := Σ_{k=0}^{N} (a k) z⁻ᵏ`, `∮ S_N(z)·z⁻¹ = 2πi·a 0` for every `N`. -/
lemma circleIntegral_inv_fin (a : ℕ → ℂ) {ρ : ℝ} (hρ : 0 < ρ) (N : ℕ) :
    (∮ z in C((0 : ℂ), ρ),
        (∑ k ∈ Finset.range (N + 1), (a k) * (z⁻¹) ^ k) * z⁻¹) =
      2 * π * Complex.I * a 0 := by
  classical
  have hdist : (fun z : ℂ => (∑ k ∈ Finset.range (N + 1), (a k) * (z⁻¹) ^ k) * z⁻¹)
      = fun z : ℂ => ∑ k ∈ Finset.range (N + 1), (a k) * (z⁻¹) ^ (k + 1) := by
    funext z
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k hk
    calc (a k * (z⁻¹) ^ k) * z⁻¹ = (a k) * ((z⁻¹) ^ k * z⁻¹) := by ring
      _ = (a k) * (z⁻¹) ^ (k + 1) := by rw [← pow_succ]
  rw [hdist]
  have hsum : (∮ z in C((0 : ℂ), ρ), ∑ k ∈ Finset.range (N + 1), (a k) * (z⁻¹) ^ (k + 1))
      = ∑ k ∈ Finset.range (N + 1),
          ∮ z in C((0 : ℂ), ρ), (a k) * (z⁻¹) ^ (k + 1) := by
    exact circleIntegral.integral_fun_sum (s := Finset.range (N + 1))
      (f := fun (k : ℕ) (z : ℂ) => (a k) * (z⁻¹) ^ (k + 1)) (c := (0 : ℂ)) (R := ρ)
        (by intro k hk; exact (ContinuousOn.circleIntegrable hρ.le (inv_term_continuous a hρ k)))
  rw [hsum]
  have hsingle : (∑ k ∈ Finset.range (N + 1),
        (∮ z in C((0 : ℂ), ρ), (a k) * (z⁻¹) ^ (k + 1))) =
      (∮ z in C((0 : ℂ), ρ), (a 0) * (z⁻¹) ^ (0 + 1)) := by
    apply Finset.sum_eq_single 0
    · intro k hk hkne
      rw [circleIntegral.integral_const_mul]
      have h0 : (∮ z in C((0 : ℂ), ρ), (z⁻¹) ^ (k + 1)) = 0 := by
        simpa using (circleIntegral_mul_inv_pow_zero hρ (m := 0) (k := k + 1) (by omega))
      rw [h0]
      ring
    · intro hknot
      exfalso
      exact hknot (Finset.mem_range.mpr (by omega))
  rw [hsingle]
  rw [circleIntegral.integral_const_mul]
  have hcrit1 : (∮ z in C((0 : ℂ), ρ), (z⁻¹) ^ (0 + 1)) = 2 * π * Complex.I := by
    simpa using (circleIntegral_mul_inv_pow_crit hρ 0)
  rw [hcrit1]
  ring

/-- Multiplication by `z⁻¹` preserves uniform convergence on the circle
`|z| = ρ` (multiplier applied on the right). -/
lemma mul_inv_tendstoUniformlyOn_sphere {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ} {ρ : ℝ}
    (hρpos : 0 < ρ) (hF : TendstoUniformlyOn F f atTop (Metric.sphere (0 : ℂ) ρ)) :
    TendstoUniformlyOn (fun n z => F n z * z⁻¹) (fun z => f z * z⁻¹) atTop
      (Metric.sphere (0 : ℂ) ρ) := by
  rw [Metric.tendstoUniformlyOn_iff] at hF ⊢
  intro ε hε
  have hden : 0 < ρ⁻¹ + 1 := by positivity
  have hF' : ∀ᶠ n in atTop, ∀ x ∈ Metric.sphere (0 : ℂ) ρ,
      dist (f x) (F n x) < ε / (2 * (ρ⁻¹ + 1)) :=
    hF (ε / (2 * (ρ⁻¹ + 1))) (by positivity)
  filter_upwards [hF'] with n hn z hz
  have hnorm : ‖z‖ = ρ := (mem_sphere_zero_iff_norm.mp hz)
  have hzinv : ‖z⁻¹‖ = ρ⁻¹ := by rw [norm_inv, hnorm]
  have hdiv : ρ⁻¹ / (ρ⁻¹ + 1) ≤ 1 := by
    rw [div_le_iff₀ hden]
    linarith
  calc
    dist (f z * z⁻¹) (F n z * z⁻¹) = ‖f z * z⁻¹ - F n z * z⁻¹‖ := by rw [dist_eq_norm]
    _ = ‖(f z - F n z) * z⁻¹‖ := by congr 1; ring
    _ = ‖f z - F n z‖ * ‖z⁻¹‖ := by rw [norm_mul]
    _ ≤ (ε / (2 * (ρ⁻¹ + 1))) * ρ⁻¹ := by
      exact mul_le_mul (by simpa [dist_eq_norm] using (le_of_lt (hn z hz)))
        (le_of_eq hzinv) (norm_nonneg _) (by positivity)
    _ ≤ ε / 2 := by
      calc
        (ε / (2 * (ρ⁻¹ + 1))) * ρ⁻¹ = (ε / 2) * (ρ⁻¹ / (ρ⁻¹ + 1)) := by
          field_simp [hden.ne']
        _ ≤ (ε / 2) * 1 := mul_le_mul_of_nonneg_left hdiv (by positivity)
        _ = ε / 2 := by ring
    _ < ε := by linarith

/-- **Negative-power moments (given uniform convergence).**  If the truncated
Laurent sums `S_N(z) = Σ_{k=0}^{N} (a k) z⁻ᵏ` times `z⁻¹` converge uniformly
on the circle `|z| = ρ` to `g z · z⁻¹`, then `∮ g z·z⁻¹ = 2πi·a 0`. -/
lemma circleIntegral_inv_of_uniform {a : ℕ → ℂ} {g : ℂ → ℂ} {ρ : ℝ}
    (hρ : 0 < ρ)
    (hcont : ∀ᶠ N in atTop, ContinuousOn
        (fun z : ℂ => (∑ k ∈ Finset.range (N + 1), (a k) * (z⁻¹) ^ k) * z⁻¹)
        (Metric.sphere (0 : ℂ) ρ))
    (huni : TendstoUniformlyOn
        (fun (N : ℕ) (z : ℂ) => (∑ k ∈ Finset.range (N + 1), (a k) * (z⁻¹) ^ k) * z⁻¹)
        (fun z : ℂ => g z * z⁻¹) atTop (Metric.sphere (0 : ℂ) ρ)) :
    (∮ z in C((0 : ℂ), ρ), g z * z⁻¹) = 2 * π * Complex.I * a 0 := by
  classical
  have hT : Tendsto (fun N : ℕ =>
        (∮ z in C((0 : ℂ), ρ),
          (∑ k ∈ Finset.range (N + 1), (a k) * (z⁻¹) ^ k) * z⁻¹))
      atTop (𝓝 (∮ z in C((0 : ℂ), ρ), g z * z⁻¹)) := by
    simpa using (TendstoUniformlyOn.tendsto_circleIntegral_of_continuousOn
      (f := fun (N : ℕ) (z : ℂ) => (∑ k ∈ Finset.range (N + 1), (a k) * (z⁻¹) ^ k) * z⁻¹)
      (g := fun z : ℂ => g z * z⁻¹) (c := (0 : ℂ)) (R := ρ) hρ.le hcont huni)
  have hconst : (fun N : ℕ =>
        (∮ z in C((0 : ℂ), ρ),
          (∑ k ∈ Finset.range (N + 1), (a k) * (z⁻¹) ^ k) * z⁻¹))
      =ᶠ[atTop] fun _ : ℕ => 2 * π * Complex.I * a 0 := by
    rw [Filter.EventuallyEq, Filter.eventually_atTop]
    refine ⟨0, ?_⟩
    intro N hN
    exact circleIntegral_inv_fin a hρ N
  have hT2 : Tendsto (fun _ : ℕ => 2 * π * Complex.I * a 0)
      atTop (𝓝 (∮ z in C((0 : ℂ), ρ), g z * z⁻¹)) := hT.congr' hconst
  have hT3 : Tendsto (fun _ : ℕ => 2 * π * Complex.I * a 0)
      atTop (𝓝 (2 * π * Complex.I * a 0)) := tendsto_const_nhds
  exact tendsto_nhds_unique hT2 hT3

/-- The negative-power Laurent circle moment: `∮ g z·z⁻¹ = 2πi·a 0`. -/
lemma circleIntegral_inv_laurent {a : ℕ → ℂ} {f g : ℂ → ℂ} {ρ₀ : ℝ}
    (hf : DifferentiableOn ℂ f (Metric.ball (0 : ℂ) ρ₀))
    (ha : ∀ k : ℕ, taylorCoeff f k = a k)
    (hg : ∀ X : ℂ, X ≠ 0 → g X = f (X⁻¹)) {ρ : ℝ} (hρpos : 0 < ρ) (hρ : ρ⁻¹ < ρ₀) :
    (∮ z in C((0 : ℂ), ρ), g z * (z⁻¹)) = 2 * π * Complex.I * a 0 := by
  have hU : TendstoUniformlyOn
      (fun (N : ℕ) (z : ℂ) => (∑ k ∈ Finset.range (N + 1), (a k) * (z⁻¹) ^ k) * z⁻¹)
      (fun z : ℂ => g z * z⁻¹) atTop (Metric.sphere (0 : ℂ) ρ) :=
    mul_inv_tendstoUniformlyOn_sphere hρpos
      (laurentSums_tendstoUniformlyOn_sphere (a := a) (f := f) (g := g) hf ha hg hρpos hρ)
  have hcont : ∀ᶠ N in atTop, ContinuousOn
      (fun z : ℂ => (∑ k ∈ Finset.range (N + 1), (a k) * (z⁻¹) ^ k) * z⁻¹)
      (Metric.sphere (0 : ℂ) ρ) := by
    filter_upwards with N
    have hterm : ∀ k ∈ Finset.range (N + 1),
        ContinuousOn (fun z : ℂ => (a k) * (z⁻¹) ^ k * z⁻¹) (Metric.sphere (0 : ℂ) ρ) := by
      intro k hk
      have hcont_inv : ContinuousOn (fun z : ℂ => z⁻¹) (Metric.sphere (0 : ℂ) ρ) :=
        continuousOn_id.inv₀ (fun z hz => ne_zero_of_mem_sphere_zero hρpos hz)
      exact (continuousOn_const.mul (hcont_inv.pow k)).mul hcont_inv
    have hsumcont : ContinuousOn
        (fun z : ℂ => ∑ k ∈ Finset.range (N + 1), (a k) * (z⁻¹) ^ k * z⁻¹)
        (Metric.sphere (0 : ℂ) ρ) := continuousOn_finsetSum (Finset.range (N + 1)) hterm
    have hEq : (fun z : ℂ => (∑ k ∈ Finset.range (N + 1), (a k) * (z⁻¹) ^ k) * z⁻¹)
        = fun z : ℂ => ∑ k ∈ Finset.range (N + 1), (a k) * (z⁻¹) ^ k * z⁻¹ := by
      funext z
      rw [Finset.sum_mul]
    rw [hEq]
    exact hsumcont
  exact circleIntegral_inv_of_uniform hρpos hcont hU

/-- `g` is continuous on the circle `|z| = ρ`: `g X = f (X⁻¹)`, `f` is
continuous on `ball 0 ρ₀`, and inversion is continuous away from `0`
(`ρ⁻¹ < ρ₀` puts the inverted circle inside the ball). -/
lemma g_continuousOn_sphere {f g : ℂ → ℂ} {ρ₀ : ℝ}
    (hf : DifferentiableOn ℂ f (Metric.ball (0 : ℂ) ρ₀))
    (hg : ∀ X : ℂ, X ≠ 0 → g X = f (X⁻¹)) {ρ : ℝ} (hρpos : 0 < ρ) (hρ : ρ⁻¹ < ρ₀) :
    ContinuousOn g (Metric.sphere (0 : ℂ) ρ) := by
  have hfcont : ContinuousOn f (Metric.ball (0 : ℂ) ρ₀) := hf.continuousOn
  have hinvc : ContinuousOn (fun z : ℂ => z⁻¹) (Metric.sphere (0 : ℂ) ρ) := by
    exact continuousOn_id.inv₀ (fun z hz => ne_zero_of_mem_sphere_zero hρpos hz)
  have hmaps : Set.MapsTo (fun z : ℂ => z⁻¹) (Metric.sphere (0 : ℂ) ρ)
      (Metric.ball (0 : ℂ) ρ₀) := by
    intro z hz
    rw [Metric.mem_ball, dist_eq_norm, sub_zero]
    have hnorm : ‖z‖ = ρ := (mem_sphere_zero_iff_norm.mp hz)
    rw [norm_inv, hnorm]
    exact hρ
  have hcomp : ContinuousOn (f ∘ (fun z : ℂ => z⁻¹)) (Metric.sphere (0 : ℂ) ρ) :=
    ContinuousOn.comp hfcont hinvc hmaps
  have hEqOn : Set.EqOn g (f ∘ (fun z : ℂ => z⁻¹)) (Metric.sphere (0 : ℂ) ρ) := by
    intro z hz
    change g z = f (z⁻¹)
    exact hg z (ne_zero_of_mem_sphere_zero hρpos hz)
  exact ContinuousOn.congr hcomp hEqOn

/-- For every power `t : ℕ`, `∮ g z·z^t·z⁻¹ = 2πi·a t`: `t = 0` is the
negative-power moment (`a 0`), and `t ≥ 1` is the monomial moment
`z^m·g z` with `m := t - 1` (since `z^t·z⁻¹ = z^(t-1)` on the contour). -/
lemma circleIntegral_g_mul_pow_mul_inv {a : ℕ → ℂ} {f g : ℂ → ℂ} {ρ₀ : ℝ}
    (hf : DifferentiableOn ℂ f (Metric.ball (0 : ℂ) ρ₀))
    (ha : ∀ k : ℕ, taylorCoeff f k = a k)
    (hg : ∀ X : ℂ, X ≠ 0 → g X = f (X⁻¹)) {ρ : ℝ} (hρpos : 0 < ρ) (hρ : ρ⁻¹ < ρ₀)
    (t : ℕ) :
    (∮ z in C((0 : ℂ), ρ), g z * z ^ t * z⁻¹) = 2 * π * Complex.I * a t := by
  by_cases ht : t = 0
  · subst t
    have hEq : Set.EqOn (fun z : ℂ => g z * z ^ 0 * z⁻¹) (fun z : ℂ => g z * z⁻¹)
        (Metric.sphere (0 : ℂ) ρ) := by
      intro z hz
      simp
    calc
      (∮ z in C((0 : ℂ), ρ), g z * z ^ 0 * z⁻¹)
          = ∮ z in C((0 : ℂ), ρ), g z * z⁻¹ := circleIntegral.integral_congr hρpos.le hEq
      _ = 2 * π * Complex.I * a 0 := circleIntegral_inv_laurent hf ha hg hρpos hρ
  · have htpos : 1 ≤ t := by omega
    have hEq : Set.EqOn (fun z : ℂ => g z * z ^ t * z⁻¹) (fun z : ℂ => z ^ (t - 1) * g z)
        (Metric.sphere (0 : ℂ) ρ) := by
      intro z hz
      have hzne : z ≠ 0 := ne_zero_of_mem_sphere_zero hρpos hz
      have hzt : z ^ t * z⁻¹ = z ^ (t - 1) := by
        rw [show t = (t - 1) + 1 by omega]
        rw [pow_succ]
        have hz1 : z * z⁻¹ = 1 := mul_inv_cancel₀ hzne
        calc (z ^ (t - 1) * z) * z⁻¹ = z ^ (t - 1) * (z * z⁻¹) := by ring
          _ = z ^ (t - 1) * 1 := by rw [hz1]
          _ = z ^ (t - 1) := by rw [mul_one]
      calc
        g z * z ^ t * z⁻¹ = g z * (z ^ t * z⁻¹) := by ring
        _ = g z * z ^ (t - 1) := by rw [hzt]
        _ = z ^ (t - 1) * g z := by ring
    calc
      (∮ z in C((0 : ℂ), ρ), g z * z ^ t * z⁻¹)
          = ∮ z in C((0 : ℂ), ρ), z ^ (t - 1) * g z := circleIntegral.integral_congr hρpos.le hEq
      _ = 2 * π * Complex.I * a ((t - 1) + 1) := circleIntegral_moment_laurent hf ha hg hρpos hρ (t - 1)
      _ = 2 * π * Complex.I * a t := by
        rw [show (t - 1) + 1 = t by omega]
/-- Polynomial-weighted circle moment:
`∮ g z · (W.eval z) · z⁻¹ = 2πi · ∑_{t ≤ W.natDegree} (W.coeff t) · a t`. -/

lemma circleIntegral_poly_moment {a : ℕ → ℂ} {f g : ℂ → ℂ} {ρ₀ : ℝ}
    (hf : DifferentiableOn ℂ f (Metric.ball (0 : ℂ) ρ₀))
    (ha : ∀ k : ℕ, taylorCoeff f k = a k)
    (hg : ∀ X : ℂ, X ≠ 0 → g X = f (X⁻¹)) {ρ : ℝ} (hρpos : 0 < ρ) (hρ : ρ⁻¹ < ρ₀)
    (W : ℂ[X]) :
    (∮ z in C((0 : ℂ), ρ), g z * (W.eval z) * (z⁻¹)) =
      2 * π * Complex.I * (∑ t ∈ Finset.range (W.natDegree + 1), (W.coeff t) * a t) := by
  classical
  have hgcont : ContinuousOn g (Metric.sphere (0 : ℂ) ρ) := g_continuousOn_sphere hf hg hρpos hρ
  have hEq : Set.EqOn (fun z : ℂ => g z * (W.eval z) * z⁻¹)
      (fun z : ℂ => ∑ t ∈ Finset.range (W.natDegree + 1),
        (W.coeff t) * (g z * z ^ t * z⁻¹))
      (Metric.sphere (0 : ℂ) ρ) := by
    intro z hz
    calc
      g z * (W.eval z) * z⁻¹ = g z * (W.eval z * z⁻¹) := by ring
      _ = g z * ((∑ t ∈ Finset.range (W.natDegree + 1), (W.coeff t) * z ^ t) * z⁻¹) := by
        rw [Polynomial.eval_eq_sum_range]
      _ = ∑ t ∈ Finset.range (W.natDegree + 1), (W.coeff t) * (g z * z ^ t * z⁻¹) := by
        rw [Finset.sum_mul]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro t ht
        ring
  calc
    (∮ z in C((0 : ℂ), ρ), g z * (W.eval z) * z⁻¹)
        = ∮ z in C((0 : ℂ), ρ),
            ∑ t ∈ Finset.range (W.natDegree + 1), (W.coeff t) * (g z * z ^ t * z⁻¹) :=
          circleIntegral.integral_congr hρpos.le hEq
    _ = ∑ t ∈ Finset.range (W.natDegree + 1),
          ∮ z in C((0 : ℂ), ρ), (W.coeff t) * (g z * z ^ t * z⁻¹) := by
        refine circleIntegral.integral_fun_sum (s := Finset.range (W.natDegree + 1))
          (f := fun (t : ℕ) (z : ℂ) => (W.coeff t) * (g z * z ^ t * z⁻¹))
          (c := (0 : ℂ)) (R := ρ) ?_
        intro t ht
        exact ContinuousOn.circleIntegrable hρpos.le
          (by
            have hcont_id : ContinuousOn (fun z : ℂ => z) (Metric.sphere (0 : ℂ) ρ) := continuousOn_id
            have hcont_inv : ContinuousOn (fun z : ℂ => z⁻¹) (Metric.sphere (0 : ℂ) ρ) :=
              hcont_id.inv₀ (fun z hz => ne_zero_of_mem_sphere_zero hρpos hz)
            have hc : ContinuousOn (fun z : ℂ => g z * z ^ t * z⁻¹) (Metric.sphere (0 : ℂ) ρ) :=
              (hgcont.mul (hcont_id.pow t)).mul hcont_inv
            exact hc.const_mul (W.coeff t))
    _ = ∑ t ∈ Finset.range (W.natDegree + 1), (W.coeff t) * (2 * π * Complex.I * a t) := by
        apply Finset.sum_congr rfl
        intro t ht
        rw [circleIntegral.integral_const_mul]
        rw [circleIntegral_g_mul_pow_mul_inv hf ha hg hρpos hρ t]
    _ = 2 * π * Complex.I * (∑ t ∈ Finset.range (W.natDegree + 1), (W.coeff t) * a t) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro t ht
        ring

/-- Linearity over one polynomial factor (continuous `h` on the contour):
`∮ h z·(q.eval z)·z⁻¹ = Σ_{t ≤ q.natDegree} q.coeff t · ∮ h z·z^t·z⁻¹`. -/
lemma circleIntegral_mul_eval_linear {h : ℂ → ℂ} {ρ : ℝ}
    (hρpos : 0 < ρ) (hh : ContinuousOn h (Metric.sphere (0 : ℂ) ρ)) (q : ℂ[X]) :
    (∮ z in C((0 : ℂ), ρ), h z * (q.eval z) * z⁻¹) =
      ∑ t ∈ Finset.range (q.natDegree + 1),
        (q.coeff t) * (∮ z in C((0 : ℂ), ρ), h z * z ^ t * z⁻¹) := by
  classical
  have hEq : Set.EqOn (fun z : ℂ => h z * (q.eval z) * z⁻¹)
      (fun z : ℂ => ∑ t ∈ Finset.range (q.natDegree + 1),
        (q.coeff t) * (h z * z ^ t * z⁻¹))
      (Metric.sphere (0 : ℂ) ρ) := by
    intro z hz
    calc
      h z * (q.eval z) * z⁻¹ = h z * (q.eval z * z⁻¹) := by ring
      _ = h z * ((∑ t ∈ Finset.range (q.natDegree + 1), (q.coeff t) * z ^ t) * z⁻¹) := by
        rw [Polynomial.eval_eq_sum_range]
      _ = ∑ t ∈ Finset.range (q.natDegree + 1), (q.coeff t) * (h z * z ^ t * z⁻¹) := by
        rw [Finset.sum_mul]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro t ht
        ring
  calc
    (∮ z in C((0 : ℂ), ρ), h z * (q.eval z) * z⁻¹)
        = ∮ z in C((0 : ℂ), ρ),
            ∑ t ∈ Finset.range (q.natDegree + 1), (q.coeff t) * (h z * z ^ t * z⁻¹) :=
          circleIntegral.integral_congr hρpos.le hEq
    _ = ∑ t ∈ Finset.range (q.natDegree + 1),
          ∮ z in C((0 : ℂ), ρ), (q.coeff t) * (h z * z ^ t * z⁻¹) := by
        refine circleIntegral.integral_fun_sum (s := Finset.range (q.natDegree + 1))
          (f := fun (t : ℕ) (z : ℂ) => (q.coeff t) * (h z * z ^ t * z⁻¹))
          (c := (0 : ℂ)) (R := ρ) ?_
        intro t ht
        exact ContinuousOn.circleIntegrable hρpos.le
          (by
            have hcont_id : ContinuousOn (fun z : ℂ => z) (Metric.sphere (0 : ℂ) ρ) := continuousOn_id
            have hcont_inv : ContinuousOn (fun z : ℂ => z⁻¹) (Metric.sphere (0 : ℂ) ρ) :=
              hcont_id.inv₀ (fun z hz => ne_zero_of_mem_sphere_zero hρpos hz)
            have hc : ContinuousOn (fun z : ℂ => h z * z ^ t * z⁻¹) (Metric.sphere (0 : ℂ) ρ) :=
              (hh.mul (hcont_id.pow t)).mul hcont_inv
            exact hc.const_mul (q.coeff t))
    _ = ∑ t ∈ Finset.range (q.natDegree + 1),
          (q.coeff t) * (∮ z in C((0 : ℂ), ρ), h z * z ^ t * z⁻¹) := by
        apply Finset.sum_congr rfl
        intro t ht
        rw [circleIntegral.integral_const_mul]

/-- The complex moment-matrix entry equals the finitely-supported double sum of
coefficient products: only `s ≤ i.val`, `r ≤ j.val` survive. -/
lemma cMomentMatrix_eq_double_sum (k : ℕ) (a : ℕ → ℂ) (p : Fin k → ℂ[X])
    (hdeg : ∀ i : Fin k, (p i).natDegree = i.val) (i j : Fin k) :
    cMomentMatrix k a p i j =
      ∑ s ∈ Finset.range (i.val + 1), ∑ r ∈ Finset.range (j.val + 1),
        (p i).coeff s * (p j).coeff r * a (s + r) := by
  classical
  have hik : i.val + 1 ≤ k := by have := i.isLt; omega
  have hjk : j.val + 1 ≤ k := by have := j.isLt; omega
  have hsubi : Finset.range (i.val + 1) ⊆ Finset.range k := by
    intro x hx
    have hxl : x < i.val + 1 := Finset.mem_range.mp hx
    exact Finset.mem_range.mpr (by omega)
  have hsubj : Finset.range (j.val + 1) ⊆ Finset.range k := by
    intro x hx
    have hxl : x < j.val + 1 := Finset.mem_range.mp hx
    exact Finset.mem_range.mpr (by omega)
  calc
    cMomentMatrix k a p i j
        = ∑ r ∈ Finset.range k, (∑ s ∈ Finset.range k, (p i).coeff s * a (s + r)) * (p j).coeff r := by
          unfold cMomentMatrix
          calc
            (∑ r : Fin k, (∑ s : Fin k, (p i).coeff s.val * a (s.val + r.val)) * (p j).coeff r.val)
                = ∑ r ∈ Finset.range k, (∑ s : Fin k, (p i).coeff s.val * a (s.val + r)) * (p j).coeff r := by
                  simpa using (Fin.sum_univ_eq_sum_range (f := fun r0 : ℕ =>
                    (∑ s : Fin k, (p i).coeff s.val * a (s.val + r0)) * (p j).coeff r0) k)
            _ = ∑ r ∈ Finset.range k, (∑ s ∈ Finset.range k, (p i).coeff s * a (s + r)) * (p j).coeff r := by
                  apply Finset.sum_congr rfl
                  intro r hr
                  have hInner : (∑ s : Fin k, (p i).coeff s.val * a (s.val + r)) =
                      (∑ s ∈ Finset.range k, (p i).coeff s * a (s + r)) := by
                    simpa using (Fin.sum_univ_eq_sum_range (f := fun s0 : ℕ => (p i).coeff s0 * a (s0 + r)) k)
                  rw [hInner]
    _ = ∑ r ∈ Finset.range k,
          (∑ s ∈ Finset.range (i.val + 1), (p i).coeff s * a (s + r)) * (p j).coeff r := by
          apply Finset.sum_congr rfl
          intro r hr
          have hIn : (∑ s ∈ Finset.range (i.val + 1), (p i).coeff s * a (s + r)) =
              (∑ s ∈ Finset.range k, (p i).coeff s * a (s + r)) := by
            exact Finset.sum_subset hsubi (by
              intro x hxk hxnot
              have hxge : ¬ x < i.val + 1 := by simpa using hxnot
              have hgt : i.val < x := by omega
              have hc : (p i).coeff x = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hdeg i]; exact hgt)
              simp [hc])
          rw [hIn]
    _ = ∑ r ∈ Finset.range (j.val + 1),
          (∑ s ∈ Finset.range (i.val + 1), (p i).coeff s * a (s + r)) * (p j).coeff r := by
          exact (Finset.sum_subset hsubj (by
            intro r hrk hrnot
            have hxge : ¬ r < j.val + 1 := by simpa using hrnot
            have hgt : j.val < r := by omega
            have hc : (p j).coeff r = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hdeg j]; exact hgt)
            simp [hc])).symm
    _ = ∑ s ∈ Finset.range (i.val + 1), ∑ r ∈ Finset.range (j.val + 1),
          (p i).coeff s * (p j).coeff r * a (s + r) := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro s hs
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro r hr
          ring

/-- The circle moment of `g·(p i)·(p j)·z⁻¹` is the coefficient-weighted
double sum `Σ_{s≤i.val} Σ_{r≤j.val} (p i).coeff s·(p j).coeff r·(2πi·a(s+r))`. -/
lemma circleIntegral_poly_pair_moment {a : ℕ → ℂ} {f g : ℂ → ℂ} {ρ₀ : ℝ}
    (hf : DifferentiableOn ℂ f (Metric.ball (0 : ℂ) ρ₀))
    (ha : ∀ k : ℕ, taylorCoeff f k = a k)
    (hg : ∀ X : ℂ, X ≠ 0 → g X = f (X⁻¹)) {ρ : ℝ} (hρpos : 0 < ρ) (hρ : ρ⁻¹ < ρ₀)
    (k : ℕ) (p : Fin k → ℂ[X])
    (hdeg : ∀ i : Fin k, (p i).natDegree = i.val) (i j : Fin k) :
    (∮ z in C((0 : ℂ), ρ), g z * ((p i).eval z) * ((p j).eval z) * (z⁻¹)) =
      ∑ s ∈ Finset.range (i.val + 1), ∑ r ∈ Finset.range (j.val + 1),
        (p i).coeff s * (p j).coeff r * (2 * π * Complex.I * a (s + r)) := by
  classical
  have hgcont : ContinuousOn g (Metric.sphere (0 : ℂ) ρ) := g_continuousOn_sphere hf hg hρpos hρ
  have h0cont : ContinuousOn (fun z : ℂ => g z * ((p j).eval z)) (Metric.sphere (0 : ℂ) ρ) :=
    hgcont.mul (Polynomial.continuousOn (p j))
  have hEq0 : Set.EqOn (fun z : ℂ => g z * ((p i).eval z) * ((p j).eval z) * z⁻¹)
      (fun z : ℂ => (g z * ((p j).eval z)) * ((p i).eval z) * z⁻¹)
      (Metric.sphere (0 : ℂ) ρ) := by
    intro z hz
    ring
  have hstep1 : (∮ z in C((0 : ℂ), ρ), g z * ((p i).eval z) * ((p j).eval z) * z⁻¹) =
      ∑ s ∈ Finset.range (i.val + 1),
        (p i).coeff s * (∮ z in C((0 : ℂ), ρ), (g z * ((p j).eval z)) * z ^ s * z⁻¹) := by
    calc
      (∮ z in C((0 : ℂ), ρ), g z * ((p i).eval z) * ((p j).eval z) * z⁻¹)
          = ∮ z in C((0 : ℂ), ρ), (g z * ((p j).eval z)) * ((p i).eval z) * z⁻¹ :=
            circleIntegral.integral_congr hρpos.le hEq0
      _ = ∑ s ∈ Finset.range ((p i).natDegree + 1),
            (p i).coeff s * (∮ z in C((0 : ℂ), ρ), (g z * ((p j).eval z)) * z ^ s * z⁻¹) :=
            circleIntegral_mul_eval_linear hρpos h0cont (p i)
      _ = ∑ s ∈ Finset.range (i.val + 1),
            (p i).coeff s * (∮ z in C((0 : ℂ), ρ), (g z * ((p j).eval z)) * z ^ s * z⁻¹) := by
            rw [hdeg i]
  have hstep2 : ∀ s : ℕ,
      (∮ z in C((0 : ℂ), ρ), (g z * ((p j).eval z)) * z ^ s * z⁻¹) =
        ∑ r ∈ Finset.range (j.val + 1),
          (p j).coeff r * (∮ z in C((0 : ℂ), ρ), (g z * z ^ s) * z ^ r * z⁻¹) := by
    intro s
    have hcont_id : ContinuousOn (fun z : ℂ => z) (Metric.sphere (0 : ℂ) ρ) := continuousOn_id
    have h1cont : ContinuousOn (fun z : ℂ => g z * z ^ s) (Metric.sphere (0 : ℂ) ρ) :=
      hgcont.mul (hcont_id.pow s)
    have hEqs : Set.EqOn (fun z : ℂ => (g z * ((p j).eval z)) * z ^ s * z⁻¹)
        (fun z : ℂ => (g z * z ^ s) * ((p j).eval z) * z⁻¹)
        (Metric.sphere (0 : ℂ) ρ) := by
      intro z hz
      ring
    calc
      (∮ z in C((0 : ℂ), ρ), (g z * ((p j).eval z)) * z ^ s * z⁻¹)
          = ∮ z in C((0 : ℂ), ρ), (g z * z ^ s) * ((p j).eval z) * z⁻¹ :=
            circleIntegral.integral_congr hρpos.le hEqs
      _ = ∑ r ∈ Finset.range ((p j).natDegree + 1),
            (p j).coeff r * (∮ z in C((0 : ℂ), ρ), (g z * z ^ s) * z ^ r * z⁻¹) :=
            circleIntegral_mul_eval_linear hρpos h1cont (p j)
      _ = ∑ r ∈ Finset.range (j.val + 1),
            (p j).coeff r * (∮ z in C((0 : ℂ), ρ), (g z * z ^ s) * z ^ r * z⁻¹) := by
            rw [hdeg j]
  have hinner_moment : ∀ s r : ℕ,
      (∮ z in C((0 : ℂ), ρ), (g z * z ^ s) * z ^ r * z⁻¹) = 2 * π * Complex.I * a (s + r) := by
    intro s r
    have hEq : Set.EqOn (fun z : ℂ => (g z * z ^ s) * z ^ r * z⁻¹)
        (fun z : ℂ => g z * z ^ (s + r) * z⁻¹)
        (Metric.sphere (0 : ℂ) ρ) := by
      intro z hz
      calc
        (g z * z ^ s) * z ^ r * z⁻¹ = g z * (z ^ s * z ^ r) * z⁻¹ := by ring
        _ = g z * z ^ (s + r) * z⁻¹ := by rw [← pow_add]
    calc
      (∮ z in C((0 : ℂ), ρ), (g z * z ^ s) * z ^ r * z⁻¹)
          = ∮ z in C((0 : ℂ), ρ), g z * z ^ (s + r) * z⁻¹ :=
            circleIntegral.integral_congr hρpos.le hEq
      _ = 2 * π * Complex.I * a (s + r) := circleIntegral_g_mul_pow_mul_inv hf ha hg hρpos hρ (s + r)
  calc
    (∮ z in C((0 : ℂ), ρ), g z * ((p i).eval z) * ((p j).eval z) * z⁻¹)
        = ∑ s ∈ Finset.range (i.val + 1),
            (p i).coeff s * (∮ z in C((0 : ℂ), ρ), (g z * ((p j).eval z)) * z ^ s * z⁻¹) := hstep1
    _ = ∑ s ∈ Finset.range (i.val + 1),
          (p i).coeff s * (∑ r ∈ Finset.range (j.val + 1),
            (p j).coeff r * (∮ z in C((0 : ℂ), ρ), (g z * z ^ s) * z ^ r * z⁻¹)) := by
          apply Finset.sum_congr rfl
          intro s hs
          rw [hstep2 s]
    _ = ∑ s ∈ Finset.range (i.val + 1), ∑ r ∈ Finset.range (j.val + 1),
          (p i).coeff s * (p j).coeff r * (∮ z in C((0 : ℂ), ρ), (g z * z ^ s) * z ^ r * z⁻¹) := by
          apply Finset.sum_congr rfl
          intro s hs
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro r hr
          ring
    _ = ∑ s ∈ Finset.range (i.val + 1), ∑ r ∈ Finset.range (j.val + 1),
          (p i).coeff s * (p j).coeff r * (2 * π * Complex.I * a (s + r)) := by
          apply Finset.sum_congr rfl
          intro s hs
          apply Finset.sum_congr rfl
          intro r hr
          rw [hinner_moment s r]

/-- Moment-matrix entries are polynomial-weighted circle moments: for monic
`pᵢ` of degree `i.val < k`, `(2πi)⁻¹ ∮ g·(p i)·(p j)·z⁻¹` equals the
`(i,j)`-entry of the complex moment matrix of `a`. -/
lemma cMomentMatrix_eq_circleIntegral {a : ℕ → ℂ} {f g : ℂ → ℂ} {ρ₀ : ℝ}
    (hf : DifferentiableOn ℂ f (Metric.ball (0 : ℂ) ρ₀))
    (ha : ∀ k : ℕ, taylorCoeff f k = a k)
    (hg : ∀ X : ℂ, X ≠ 0 → g X = f (X⁻¹)) {ρ : ℝ} (hρpos : 0 < ρ) (hρ : ρ⁻¹ < ρ₀)
    (k : ℕ) (p : Fin k → ℂ[X])
    (hdeg : ∀ i : Fin k, (p i).natDegree = i.val) (i j : Fin k) :
    cMomentMatrix k a p i j =
      ((2 * π * Complex.I)⁻¹) * (∮ z in C((0 : ℂ), ρ),
        g z * ((p i).eval z) * ((p j).eval z) * (z⁻¹)) := by
  classical
  let D : ℂ := ∑ s ∈ Finset.range (i.val + 1), ∑ r ∈ Finset.range (j.val + 1),
      (p i).coeff s * (p j).coeff r * a (s + r)
  let B : ℂ := ∑ s ∈ Finset.range (i.val + 1), ∑ r ∈ Finset.range (j.val + 1),
      (p i).coeff s * (p j).coeff r * (2 * π * Complex.I * a (s + r))
  have hMM : cMomentMatrix k a p i j = D := by
    simpa [D] using (cMomentMatrix_eq_double_sum k a p hdeg i j)
  have hInt : B = (∮ z in C((0 : ℂ), ρ),
      g z * ((p i).eval z) * ((p j).eval z) * (z⁻¹)) := by
    simpa [B] using (circleIntegral_poly_pair_moment hf ha hg hρpos hρ k p hdeg i j).symm
  have hB : 2 * π * Complex.I * D = B := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s hs
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r hr
    ring
  calc
    cMomentMatrix k a p i j = D := hMM
    _ = (2 * π * Complex.I)⁻¹ * (2 * π * Complex.I * D) := by
        rw [← mul_assoc, inv_mul_cancel₀ Complex.two_pi_I_ne_zero, one_mul]
    _ = (2 * π * Complex.I)⁻¹ * B := by rw [hB]
    _ = (2 * π * Complex.I)⁻¹ * (∮ z in C((0 : ℂ), ρ),
          g z * ((p i).eval z) * ((p j).eval z) * (z⁻¹)) := by rw [hInt]

end Submission.PolyMoment

end
