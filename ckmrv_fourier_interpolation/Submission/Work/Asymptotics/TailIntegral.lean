/-
# The tail integral `∫_{t ≥ 1} g t · e^{-πλt} dt`: smoothness and growth bounds

CKMRV's decomposition (5.2)--(5.3) of the layer `F₂` splits the contour integral into a
`low` piece over `(0,1]`, a `trunc` piece over `[1,∞)` with the non-decaying part of the kernel
subtracted, and an explicit `high` piece.  The `trunc` piece is

`∫_{t ≥ 1} (K(τ,it) - 𝒢(τ,it)) · e^{-πλt} dt` with `λ = r²`,

and the only analytic input is the exponential decay of the tail amplitude
`h(t) = K(τ,it) - 𝒢(τ,it)` for `t ≥ 1` (a.e. in `t`).  This file develops the parametric-integral
engine for such tails, for an arbitrary amplitude `g` satisfying an a.e. bound
`‖g t‖ ≤ C · t^M · e^{-πt}`:

* `tailIntegral g λ = ∫_{t ≥ 1} g t · e^{-πλt} dt`;
* `tailIntegral_hasDerivAt`: `λ ↦ tailIntegral g λ` is differentiable for `λ > -1`, with
  derivative `tailIntegral (fun t ↦ g t · (-πt)) λ` (differentiation under the integral sign);
* `tailIntegral_iteratedDeriv`: the `m`-th derivative is `∫_{t ≥ 1} g t (-πt)^m e^{-πλt} dt`;
* `tailIntegral_contDiffOn`: `λ ↦ tailIntegral g λ` is smooth on `(-1, ∞)`;
* `tailIntegral_iteratedDeriv_bound`: on `λ ≥ 0` the `m`-th derivative is bounded by
  `C π^m e^{-πλ} ∫_{t ≥ 1} t^{M+m} e^{-πt} dt`.

Two elementary estimates used by the assembly live here as well:
`norm_iteratedDeriv_two_sub_two_cos` (every iterated derivative of the regularising factor
`2 - 2 cos (πλ)` is bounded by `4π^j`) and `integrableOn_rpow_mul_exp_neg` (a polynomial times a
decaying exponential is integrable on `[1,∞)`).
-/
import Mathlib

noncomputable section

open MeasureTheory Filter Topology
open scoped Topology ContDiff

namespace Work.Asymptotics

/-! ## The iterated derivative of `x ↦ (x : ℂ)` and of `x ↦ |x| ^ k` -/

/-- The canonical `ℂ`-valued derivative helpers: `‖(r : ℂ)‖ = |r|`. -/
lemma norm_ofReal_eq_abs (r : ℝ) : ‖(r : ℂ)‖ = |r| := by
  rw [Complex.norm_real, Real.norm_eq_abs]

/-! ## The iterated derivatives of the regularising factor `2 - 2 cos (πlam)` -/

/-- All iterated derivatives of `x ↦ 2 - 2 cos (π x)` are bounded by `4 π^j`:  the `j`-th
derivative is `±2π^j cos (πx)` or `±2π^j sin (πx)` (`j ≥ 1`), and `j = 0` gives `≤ 4`. -/
theorem norm_iteratedDeriv_two_sub_two_cos (j : ℕ) (x : ℝ) :
    ‖iteratedDeriv j (fun x : ℝ => (2 - 2 * Real.cos (Real.pi * x) : ℂ)) x‖ ≤ 4 * Real.pi ^ j := by
  have hinner : ∀ y : ℝ, HasDerivAt (fun z : ℝ => Real.pi * z) Real.pi y := by
    intro y
    simpa using (hasDerivAt_id y).const_mul Real.pi
  have hcosd : ∀ y : ℝ, HasDerivAt (fun z : ℝ => (Real.cos (Real.pi * z) : ℂ))
      (-(Real.pi : ℂ) * (Real.sin (Real.pi * y) : ℂ)) y := by
    intro y
    have h1 : HasDerivAt (fun z : ℝ => Real.cos (Real.pi * z))
        (-(Real.sin (Real.pi * y)) * Real.pi) y :=
      (Real.hasDerivAt_cos (Real.pi * y)).comp y (hinner y)
    have h2 := h1.ofReal_comp
    have heq : ((↑(-(Real.sin (Real.pi * y)) * Real.pi) : ℂ))
        = (-(Real.pi : ℂ)) * (↑(Real.sin (Real.pi * y)) : ℂ) := by push_cast; ring
    rwa [heq] at h2
  have hsind : ∀ y : ℝ, HasDerivAt (fun z : ℝ => (Real.sin (Real.pi * z) : ℂ))
      ((Real.pi : ℂ) * (Real.cos (Real.pi * y) : ℂ)) y := by
    intro y
    have h1 : HasDerivAt (fun z : ℝ => Real.sin (Real.pi * z))
        (Real.cos (Real.pi * y) * Real.pi) y :=
      (Real.hasDerivAt_sin (Real.pi * y)).comp y (hinner y)
    have h2 := h1.ofReal_comp
    have heq : ((↑(Real.cos (Real.pi * y) * Real.pi) : ℂ))
        = (Real.pi : ℂ) * (↑(Real.cos (Real.pi * y)) : ℂ) := by push_cast; ring
    rwa [heq] at h2
  have key : ∀ j : ℕ, ∃ A a b : ℂ, ‖A‖ + ‖a‖ + ‖b‖ ≤ 4 * Real.pi ^ j ∧
      iteratedDeriv j (fun x : ℝ => (2 - 2 * Real.cos (Real.pi * x) : ℂ))
        = fun x : ℝ => a * (Real.cos (Real.pi * x) : ℂ)
            + b * (Real.sin (Real.pi * x) : ℂ) + A := by
    intro j
    induction j with
    | zero =>
        refine ⟨2, -2, 0, ?_, ?_⟩
        · norm_num
        · funext y; rw [iteratedDeriv_zero]; ring
    | succ k ih =>
        obtain ⟨A, a, b, hbnd, hfun⟩ := ih
        refine ⟨0, b * (Real.pi : ℂ), -(a * (Real.pi : ℂ)), ?_, ?_⟩
        · have hπ : ‖(Real.pi : ℂ)‖ = Real.pi := Complex.norm_of_nonneg Real.pi_pos.le
          have h1 : ‖b * (Real.pi : ℂ)‖ + ‖-(a * (Real.pi : ℂ))‖
              = (‖a‖ + ‖b‖) * Real.pi := by
            simp only [norm_mul, norm_neg, hπ]
            ring
          have h2 : ‖a‖ + ‖b‖ ≤ 4 * Real.pi ^ k := by
            have := norm_nonneg A; linarith
          rw [norm_zero, zero_add, h1]
          calc (‖a‖ + ‖b‖) * Real.pi ≤ (4 * Real.pi ^ k) * Real.pi :=
                mul_le_mul_of_nonneg_right h2 Real.pi_pos.le
            _ = 4 * Real.pi ^ (k + 1) := by rw [pow_succ]; ring
        · rw [iteratedDeriv_succ, hfun]
          funext y
          have hd : HasDerivAt
              (fun z : ℝ => a * (Real.cos (Real.pi * z) : ℂ)
                + b * (Real.sin (Real.pi * z) : ℂ) + A)
              (a * (-(Real.pi : ℂ) * (Real.sin (Real.pi * y) : ℂ))
                + b * ((Real.pi : ℂ) * (Real.cos (Real.pi * y) : ℂ))) y :=
            (((hcosd y).const_mul a).add ((hsind y).const_mul b)).add_const A
          rw [hd.deriv]
          ring
  obtain ⟨A, a, b, hbnd, hfun⟩ := key j
  rw [hfun]
  have hc : ‖(Real.cos (Real.pi * x) : ℂ)‖ ≤ 1 := by
    rw [norm_ofReal_eq_abs]
    exact abs_le.mpr ⟨Real.neg_one_le_cos (Real.pi * x), Real.cos_le_one (Real.pi * x)⟩
  have hs : ‖(Real.sin (Real.pi * x) : ℂ)‖ ≤ 1 := by
    rw [norm_ofReal_eq_abs]
    exact abs_le.mpr ⟨Real.neg_one_le_sin (Real.pi * x), Real.sin_le_one (Real.pi * x)⟩
  calc ‖a * (Real.cos (Real.pi * x) : ℂ) + b * (Real.sin (Real.pi * x) : ℂ) + A‖
      ≤ ‖a * (Real.cos (Real.pi * x) : ℂ) + b * (Real.sin (Real.pi * x) : ℂ)‖ + ‖A‖ :=
        norm_add_le _ _
    _ ≤ (‖a * (Real.cos (Real.pi * x) : ℂ)‖ + ‖b * (Real.sin (Real.pi * x) : ℂ)‖) + ‖A‖ := by
        gcongr
        exact norm_add_le _ _
    _ ≤ (‖a‖ * 1 + ‖b‖ * 1) + ‖A‖ := by
        gcongr
        · rw [norm_mul]; exact mul_le_mul_of_nonneg_left hc (norm_nonneg a)
        · rw [norm_mul]; exact mul_le_mul_of_nonneg_left hs (norm_nonneg b)
    _ ≤ 4 * Real.pi ^ j := by linarith

/-! ## Integrability of a polynomial times a decaying exponential on `[1,∞)` -/

/-- `t ↦ t^A e^{-ct}` is integrable on `[1,∞)` for `A ≥ 0`, `c > 0`. -/
theorem integrableOn_rpow_mul_exp_neg (A c : ℝ) (hA : 0 ≤ A) (hc : 0 < c) :
    IntegrableOn (fun t : ℝ => t ^ A * Real.exp (-(c * t))) (Set.Ici 1) := by
  have h0 : IntegrableOn (fun t : ℝ => t ^ A * Real.exp (-(c * t))) (Set.Ioi (0 : ℝ)) := by
    have h := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := A) (b := c)
      (by linarith) one_pos hc
    simpa [Real.rpow_one] using h
  refine h0.mono_set (fun t ht => ?_)
  rw [Set.mem_Ioi]
  exact lt_of_lt_of_le zero_lt_one (Set.mem_Ici.mp ht)


/-! ## The tail integral and its basic properties -/

/-- The tail integral `∫_{t ≥ 1} g t · e^{-π λ t} dt`, as a function of the parameter `λ`.  For
`λ > -1` this converges; for `λ ≤ -1` the integrand is no longer integrable and Lean's Bochner
integral takes the junk value `0` there. -/
def tailIntegral (g : ℝ → ℂ) (lam : ℝ) : ℂ :=
  ∫ t in Set.Ici (1 : ℝ), g t * (Real.exp (-(Real.pi * lam * t)) : ℂ)

/-- The decay constant `∫_{t ≥ 1} t ^ (M + m) e^{-πt} dt` of the tail estimates. -/
def tailDecay (M : ℝ) (m : ℕ) : ℝ :=
  ∫ t in Set.Ici (1 : ℝ), t ^ (M + (m : ℝ)) * Real.exp (-(Real.pi * t))

lemma tailDecay_nonneg (M : ℝ) (m : ℕ) : 0 ≤ tailDecay M m := by
  rw [tailDecay]
  refine setIntegral_nonneg measurableSet_Ici (fun t ht => ?_)
  exact mul_nonneg (Real.rpow_nonneg (le_of_lt (lt_of_lt_of_le zero_lt_one (Set.mem_Ici.mp ht))) _)
    (Real.exp_pos _).le

lemma tailDecay_mono {M : ℝ} (hM : 0 ≤ M) {m m' : ℕ} (h : m ≤ m') :
    tailDecay M m ≤ tailDecay M m' := by
  have hint1 : IntegrableOn (fun t : ℝ => t ^ (M + (m : ℝ)) * Real.exp (-(Real.pi * t)))
      (Set.Ici (1 : ℝ)) := integrableOn_rpow_mul_exp_neg (M + m) Real.pi (by positivity) Real.pi_pos
  have hint2 : IntegrableOn (fun t : ℝ => t ^ (M + (m' : ℝ)) * Real.exp (-(Real.pi * t)))
      (Set.Ici (1 : ℝ)) := integrableOn_rpow_mul_exp_neg (M + m') Real.pi (by positivity) Real.pi_pos
  rw [tailDecay, tailDecay]
  refine integral_mono_ae hint1 hint2 ?_
  filter_upwards [ae_restrict_mem measurableSet_Ici] with t ht
  have ht1 : (1 : ℝ) ≤ t := Set.mem_Ici.mp ht
  refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
  have hexp : M + (m : ℝ) ≤ M + (m' : ℝ) := by
    have h1 : (m : ℝ) ≤ (m' : ℝ) := by exact_mod_cast h
    linarith
  exact Real.rpow_le_rpow_of_exponent_le ht1 hexp

/-- The a.e. bound for the amplitude `t ↦ g t · (-πt)^m` obtained from that for `g`. -/
lemma tailIntegral_amp_ae_bound (g : ℝ → ℂ) {C M : ℝ}
    (hb : ∀ᵐ t ∂(volume.restrict (Set.Ici (1 : ℝ))),
      ‖g t‖ ≤ C * t ^ M * Real.exp (-(Real.pi * t))) (m : ℕ) :
    ∀ᵐ t ∂(volume.restrict (Set.Ici (1 : ℝ))),
      ‖g t * (((-(Real.pi * t) : ℝ)) : ℂ) ^ m‖
        ≤ C * Real.pi ^ m * t ^ (M + (m : ℝ)) * Real.exp (-(Real.pi * t)) := by
  filter_upwards [hb, ae_restrict_mem measurableSet_Ici] with t hb ht
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one (Set.mem_Ici.mp ht)
  have hπt : (0 : ℝ) < Real.pi * t := mul_pos Real.pi_pos ht0
  have hfac : ‖((( -(Real.pi * t)) : ℝ) : ℂ)‖ = Real.pi * t := by
    rw [norm_ofReal_eq_abs, abs_of_neg (by linarith)]
    ring
  have htM : t ^ (M + (m : ℝ)) = t ^ M * t ^ (m : ℝ) := Real.rpow_add ht0 M _
  have htm : t ^ (m : ℝ) = t ^ m := Real.rpow_natCast t m
  calc ‖g t * (((-(Real.pi * t) : ℝ)) : ℂ) ^ m‖
      = ‖g t‖ * (Real.pi * t) ^ m := by rw [norm_mul, norm_pow, hfac]
    _ ≤ (C * t ^ M * Real.exp (-(Real.pi * t))) * (Real.pi * t) ^ m :=
        mul_le_mul_of_nonneg_right hb (by positivity)
    _ = C * Real.pi ^ m * t ^ (M + (m : ℝ)) * Real.exp (-(Real.pi * t)) := by
        rw [mul_pow, htM, htm]
        ring

/-- **Integrability of the tail integrand** for `lam > -1`. -/
lemma integrableOn_tailIntegral (g : ℝ → ℂ)
    (hmeas : AEStronglyMeasurable g (volume.restrict (Set.Ici (1 : ℝ))))
    {C M : ℝ} (hC : 0 ≤ C) (hM : 0 ≤ M)
    (hb : ∀ᵐ t ∂(volume.restrict (Set.Ici (1 : ℝ))),
      ‖g t‖ ≤ C * t ^ M * Real.exp (-(Real.pi * t)))
    {lam : ℝ} (hlam : -1 < lam) :
    IntegrableOn (fun t : ℝ => g t * (Real.exp (-(Real.pi * lam * t)) : ℂ)) (Set.Ici (1 : ℝ)) := by
  have hcpos : 0 < Real.pi * (lam + 1) := mul_pos Real.pi_pos (by linarith)
  have hmaj : Integrable (fun t : ℝ => C * t ^ M * Real.exp (-(Real.pi * (lam + 1) * t)))
      (volume.restrict (Set.Ici (1 : ℝ))) := by
    have h1 := integrableOn_rpow_mul_exp_neg M (Real.pi * (lam + 1)) hM hcpos
    simpa only [mul_assoc] using h1.const_mul C
  refine MeasureTheory.Integrable.mono'
    (f := fun t : ℝ => g t * (Real.exp (-(Real.pi * lam * t)) : ℂ))
    (g := fun t : ℝ => C * t ^ M * Real.exp (-(Real.pi * (lam + 1) * t))) hmaj ?_ ?_
  · exact hmeas.mul (by fun_prop : Continuous fun t : ℝ =>
      (Real.exp (-(Real.pi * lam * t)) : ℂ)).aestronglyMeasurable
  · filter_upwards [hb] with t hb
    have hexp : Real.exp (-(Real.pi * t)) * Real.exp (-(Real.pi * lam * t))
        = Real.exp (-(Real.pi * (lam + 1) * t)) := by
      rw [← Real.exp_add]; congr 1; ring
    calc ‖g t * (Real.exp (-(Real.pi * lam * t)) : ℂ)‖
        = ‖g t‖ * Real.exp (-(Real.pi * lam * t)) := by
          rw [norm_mul, norm_ofReal_eq_abs, abs_of_pos (Real.exp_pos _)]
      _ ≤ (C * t ^ M * Real.exp (-(Real.pi * t))) * Real.exp (-(Real.pi * lam * t)) :=
          mul_le_mul_of_nonneg_right hb (Real.exp_pos _).le
      _ = C * t ^ M * (Real.exp (-(Real.pi * t)) * Real.exp (-(Real.pi * lam * t))) := by ring
      _ = C * t ^ M * Real.exp (-(Real.pi * (lam + 1) * t)) := by rw [hexp]

/-- **Differentiation under the integral sign**: for `λ > -1` the tail integral is differentiable
with derivative the tail integral of the `lam`-derivative `t ↦ g t · (-πt)` of the amplitude. -/
lemma tailIntegral_hasDerivAt (g : ℝ → ℂ)
    (hmeas : AEStronglyMeasurable g (volume.restrict (Set.Ici (1 : ℝ))))
    {C M : ℝ} (hC : 0 ≤ C) (hM : 0 ≤ M)
    (hb : ∀ᵐ t ∂(volume.restrict (Set.Ici (1 : ℝ))),
      ‖g t‖ ≤ C * t ^ M * Real.exp (-(Real.pi * t)))
    {lam : ℝ} (hlam : -1 < lam) :
    HasDerivAt (tailIntegral g)
      (tailIntegral (fun t => g t * (((-(Real.pi * t) : ℝ)) : ℂ)) lam) lam := by
  set r : ℝ := (lam + 1) / 2 with hrdef
  have hr : 0 < r := by rw [hrdef]; linarith
  have hcpos : 0 < Real.pi * (lam - r + 1) := mul_pos Real.pi_pos (by rw [hrdef]; linarith)
  have hmajor_int : Integrable
      (fun t : ℝ => C * Real.pi * t ^ (M + 1) * Real.exp (-(Real.pi * (lam - r + 1) * t)))
      (volume.restrict (Set.Ici (1 : ℝ))) := by
    have h1 := integrableOn_rpow_mul_exp_neg (M + 1) (Real.pi * (lam - r + 1)) (by linarith) hcpos
    simpa only [mul_assoc] using h1.const_mul (C * Real.pi)
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Set.Ici (1 : ℝ)))
    (F := fun x (t : ℝ) => g t * (Real.exp (-(Real.pi * x * t)) : ℂ))
    (F' := fun x (t : ℝ) =>
      g t * (((-(Real.pi * t) : ℝ)) : ℂ) * (Real.exp (-(Real.pi * x * t)) : ℂ))
    (x₀ := lam) (s := Metric.ball lam r)
    (bound := fun t : ℝ => C * Real.pi * t ^ (M + 1) * Real.exp (-(Real.pi * (lam - r + 1) * t)))
    (Metric.ball_mem_nhds lam hr) ?_ ?_ ?_ ?_ hmajor_int ?_).2
  · refine Filter.Eventually.of_forall (fun x => hmeas.mul ?_)
    exact (by fun_prop : Continuous fun t : ℝ =>
      (Real.exp (-(Real.pi * x * t)) : ℂ)).aestronglyMeasurable
  · exact integrableOn_tailIntegral g hmeas hC hM hb hlam
  · have h1 : AEStronglyMeasurable (fun t : ℝ => g t * (((-(Real.pi * t) : ℝ)) : ℂ))
        (volume.restrict (Set.Ici (1 : ℝ))) :=
      hmeas.mul (by fun_prop : Continuous fun t : ℝ =>
        (((-(Real.pi * t) : ℝ)) : ℂ)).aestronglyMeasurable
    exact h1.mul (by fun_prop : Continuous fun t : ℝ =>
      (Real.exp (-(Real.pi * lam * t)) : ℂ)).aestronglyMeasurable
  · filter_upwards [hb, ae_restrict_mem measurableSet_Ici] with t hb ht x hx
    have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one (Set.mem_Ici.mp ht)
    have hxd : |x - lam| < r := by simpa [Real.dist_eq] using Metric.mem_ball.mp hx
    have hxr : lam - r < x := by have h' := (abs_lt.mp hxd).1; linarith
    have hexple : Real.exp (-(Real.pi * x * t)) ≤ Real.exp (-(Real.pi * (lam - r) * t)) := by
      apply Real.exp_le_exp.mpr
      have h1 : Real.pi * (lam - r) * t ≤ Real.pi * x * t := by
        apply mul_le_mul_of_nonneg_right _ ht0.le
        exact mul_le_mul_of_nonneg_left hxr.le Real.pi_pos.le
      linarith
    have hfac : ‖(((-(Real.pi * t)) : ℝ) : ℂ)‖ = Real.pi * t := by
      rw [norm_ofReal_eq_abs, abs_of_neg (by have := mul_pos Real.pi_pos ht0; linarith)]
      ring
    have hexpnorm : ‖(Real.exp (-(Real.pi * x * t)) : ℂ)‖ = Real.exp (-(Real.pi * x * t)) := by
      rw [norm_ofReal_eq_abs, abs_of_pos (Real.exp_pos _)]
    have htM : t ^ (M + 1) = t ^ M * t ^ (1 : ℝ) := Real.rpow_add ht0 M 1
    have ht1 : t ^ (1 : ℝ) = t := Real.rpow_one t
    calc ‖g t * (((-(Real.pi * t) : ℝ)) : ℂ) * (Real.exp (-(Real.pi * x * t)) : ℂ)‖
        = ‖g t‖ * (Real.pi * t) * Real.exp (-(Real.pi * x * t)) := by
          rw [norm_mul, norm_mul, hfac, hexpnorm]
      _ ≤ (C * t ^ M * Real.exp (-(Real.pi * t))) * (Real.pi * t)
            * Real.exp (-(Real.pi * (lam - r) * t)) := by
          have h1 : ‖g t‖ * (Real.pi * t) ≤ (C * t ^ M * Real.exp (-(Real.pi * t))) * (Real.pi * t) :=
            mul_le_mul_of_nonneg_right hb (by positivity)
          exact mul_le_mul h1 hexple (Real.exp_pos _).le (by positivity)
      _ = C * Real.pi * t ^ (M + 1) * Real.exp (-(Real.pi * (lam - r + 1) * t)) := by
          rw [htM, ht1]
          have hexp : Real.exp (-(Real.pi * t)) * Real.exp (-(Real.pi * (lam - r) * t))
              = Real.exp (-(Real.pi * (lam - r + 1) * t)) := by
            rw [← Real.exp_add]; congr 1; ring
          calc C * t ^ M * Real.exp (-(Real.pi * t)) * (Real.pi * t)
                * Real.exp (-(Real.pi * (lam - r) * t))
              = C * Real.pi * (t ^ M * t) * (Real.exp (-(Real.pi * t))
                * Real.exp (-(Real.pi * (lam - r) * t))) := by ring
            _ = C * Real.pi * (t ^ M * t) * Real.exp (-(Real.pi * (lam - r + 1) * t)) := by rw [hexp]
  · refine Filter.Eventually.of_forall (fun t x _ => ?_)
    have h1 : HasDerivAt (fun y : ℝ => Real.exp (-(Real.pi * y * t)))
        (Real.exp (-(Real.pi * x * t)) * (-(Real.pi * t))) x := by
      have h2 : HasDerivAt (fun y : ℝ => -(Real.pi * y * t)) (-(Real.pi * t)) x := by
        have h3 : (fun y : ℝ => -(Real.pi * y * t)) = fun y : ℝ => (-(Real.pi * t)) * y := by
          funext y; ring
        rw [h3]
        simpa using (hasDerivAt_id x).const_mul (-(Real.pi * t))
      simpa using h2.exp
    have h5 := (h1.ofReal_comp).const_mul (g t)
    have heq : g t * (↑(Real.exp (-(Real.pi * x * t)) * (-(Real.pi * t))))
        = g t * (((-(Real.pi * t) : ℝ)) : ℂ) * (Real.exp (-(Real.pi * x * t)) : ℂ) := by
      push_cast; ring
    rwa [heq] at h5

/-- **The iterated derivative of the tail integral**: differentiating `m` times under the integral
sign multiplies the amplitude by `(-πt)^m`. -/
lemma tailIntegral_iteratedDeriv (g : ℝ → ℂ)
    (hmeas : AEStronglyMeasurable g (volume.restrict (Set.Ici (1 : ℝ))))
    {C M : ℝ} (hC : 0 ≤ C) (hM : 0 ≤ M)
    (hb : ∀ᵐ t ∂(volume.restrict (Set.Ici (1 : ℝ))),
      ‖g t‖ ≤ C * t ^ M * Real.exp (-(Real.pi * t))) (m : ℕ) :
    ∀ lam : ℝ, -1 < lam → iteratedDeriv m (tailIntegral g) lam
      = tailIntegral (fun t : ℝ => g t * (((-(Real.pi * t) : ℝ)) : ℂ) ^ m) lam := by
  induction m with
  | zero =>
      intro lam _
      simp [tailIntegral]
  | succ k ih =>
      intro lam hlam
      set G : ℝ → ℂ := fun t => g t * (((-(Real.pi * t) : ℝ)) : ℂ) ^ k with hG
      have hGmeas : AEStronglyMeasurable G (volume.restrict (Set.Ici (1 : ℝ))) :=
        hmeas.mul (by fun_prop : Continuous fun t : ℝ =>
          (((-(Real.pi * t) : ℝ)) : ℂ) ^ k).aestronglyMeasurable
      have hGbound := tailIntegral_amp_ae_bound g hb k
      have hev : iteratedDeriv k (tailIntegral g) =ᶠ[𝓝 lam] tailIntegral G :=
        Filter.eventually_of_mem (isOpen_Ioi.mem_nhds hlam) (fun y hy => ih y hy)
      rw [iteratedDeriv_succ, hev.deriv_eq,
        (tailIntegral_hasDerivAt G hGmeas (by positivity) (by positivity) hGbound hlam).deriv]
      congr 1
      funext t
      simp only [hG]
      rw [pow_succ]
      ring

/-- `‖iteratedDerivWithin n f s x‖ = ‖iteratedDeriv n f x‖` for `s` open and `x ∈ s`. -/
lemma norm_iteratedDerivWithin_eq_of_isOpen {s : Set ℝ} (hs : IsOpen s) {x : ℝ} (hx : x ∈ s)
    (n : ℕ) (f : ℝ → ℂ) :
    ‖iteratedDerivWithin n f s x‖ = ‖iteratedDeriv n f x‖ := by
  rw [← norm_iteratedFDerivWithin_eq_norm_iteratedDerivWithin (s := s) (x := x),
    ← norm_iteratedFDeriv_eq_norm_iteratedDeriv (x := x)]
  exact congrArg norm (iteratedFDerivWithin_of_isOpen n hs hx)

/-- **Smoothness of the tail integral** on `(-1, ∞)`:  on the open set `(-1,∞)` the `m`-th
derivative of `tailIntegral g` is the tail integral of `t ↦ g t (-πt)^m`, which is differentiable,
hence continuous; the characterization of `ContDiffOn` through the one-sided iterated derivatives
therefore applies without any further input. -/
lemma tailIntegral_contDiffOn (n : ℕ) (g : ℝ → ℂ)
    (hmeas : AEStronglyMeasurable g (volume.restrict (Set.Ici (1 : ℝ))))
    {C M : ℝ} (hC : 0 ≤ C) (hM : 0 ≤ M)
    (hb : ∀ᵐ t ∂(volume.restrict (Set.Ici (1 : ℝ))),
      ‖g t‖ ≤ C * t ^ M * Real.exp (-(Real.pi * t))) :
    ContDiffOn ℝ (n : ℕ∞ω) (tailIntegral g) (Set.Ioi (-1)) := by
  refine contDiffOn_of_continuousOn_differentiableOn_deriv (n := (n : ℕ∞)) ?_ ?_
  · intro m hm
    have hmn : m ≤ n := by exact_mod_cast hm
    set G : ℝ → ℂ := fun t => g t * (((-(Real.pi * t) : ℝ)) : ℂ) ^ m with hG
    have hGmeas : AEStronglyMeasurable G (volume.restrict (Set.Ici (1 : ℝ))) :=
      hmeas.mul (by fun_prop : Continuous fun t : ℝ =>
        (((-(Real.pi * t) : ℝ)) : ℂ) ^ m).aestronglyMeasurable
    have hGbound := tailIntegral_amp_ae_bound g hb m
    have hGdiff : DifferentiableOn ℝ (tailIntegral G) (Set.Ioi (-1)) := fun lam hlam =>
      (tailIntegral_hasDerivAt G hGmeas (by positivity) (by positivity) hGbound hlam).differentiableAt.differentiableWithinAt
    refine hGdiff.continuousOn.congr ?_
    intro x hx
    show iteratedDerivWithin m (tailIntegral g) (Set.Ioi (-1)) x = tailIntegral G x
    rw [iteratedDerivWithin_of_isOpen (n := m) (f := tailIntegral g) isOpen_Ioi hx, hG,
      tailIntegral_iteratedDeriv g hmeas hC hM hb m x hx]
  · intro m hm
    have hmn : m < n := by exact_mod_cast hm
    set G : ℝ → ℂ := fun t => g t * (((-(Real.pi * t) : ℝ)) : ℂ) ^ m with hG
    have hGmeas : AEStronglyMeasurable G (volume.restrict (Set.Ici (1 : ℝ))) :=
      hmeas.mul (by fun_prop : Continuous fun t : ℝ =>
        (((-(Real.pi * t) : ℝ)) : ℂ) ^ m).aestronglyMeasurable
    have hGbound := tailIntegral_amp_ae_bound g hb m
    have hGdiff : DifferentiableOn ℝ (tailIntegral G) (Set.Ioi (-1)) := fun lam hlam =>
      (tailIntegral_hasDerivAt G hGmeas (by positivity) (by positivity) hGbound hlam).differentiableAt.differentiableWithinAt
    refine hGdiff.congr fun x hx => ?_
    show iteratedDerivWithin m (tailIntegral g) (Set.Ioi (-1)) x = tailIntegral G x
    rw [iteratedDerivWithin_of_isOpen (n := m) (f := tailIntegral g) isOpen_Ioi hx, hG,
      tailIntegral_iteratedDeriv g hmeas hC hM hb m x hx]

/-- **Growth bound for the iterated derivatives of the tail integral** on `lam ≥ 0`. -/
lemma tailIntegral_iteratedDeriv_bound (g : ℝ → ℂ)
    (hmeas : AEStronglyMeasurable g (volume.restrict (Set.Ici (1 : ℝ))))
    {C M : ℝ} (hC : 0 ≤ C) (hM : 0 ≤ M)
    (hb : ∀ᵐ t ∂(volume.restrict (Set.Ici (1 : ℝ))),
      ‖g t‖ ≤ C * t ^ M * Real.exp (-(Real.pi * t)))
    (m : ℕ) {lam : ℝ} (hlam : 0 ≤ lam) :
    ‖iteratedDeriv m (tailIntegral g) lam‖
      ≤ C * Real.pi ^ m * tailDecay M m * Real.exp (-(Real.pi * lam)) := by
  set G : ℝ → ℂ := fun t => g t * (((-(Real.pi * t) : ℝ)) : ℂ) ^ m with hG
  have hmaj : Integrable (fun t : ℝ => C * Real.pi ^ m * Real.exp (-(Real.pi * lam))
      * (t ^ (M + (m : ℝ)) * Real.exp (-(Real.pi * t)))) (volume.restrict (Set.Ici (1 : ℝ))) := by
    have h1 := integrableOn_rpow_mul_exp_neg (M + m) Real.pi (by positivity) Real.pi_pos
    simpa only [mul_assoc] using h1.const_mul (C * Real.pi ^ m * Real.exp (-(Real.pi * lam)))
  have hpoint : ∀ᵐ t ∂(volume.restrict (Set.Ici (1 : ℝ))),
      ‖G t * (Real.exp (-(Real.pi * lam * t)) : ℂ)‖
        ≤ C * Real.pi ^ m * Real.exp (-(Real.pi * lam))
          * (t ^ (M + (m : ℝ)) * Real.exp (-(Real.pi * t))) := by
    filter_upwards [tailIntegral_amp_ae_bound g hb m, ae_restrict_mem measurableSet_Ici]
      with t ht ht1
    have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one (Set.mem_Ici.mp ht1)
    have hexp : Real.exp (-(Real.pi * lam * t)) ≤ Real.exp (-(Real.pi * lam)) := by
      apply Real.exp_le_exp.mpr
      have h1 : Real.pi * lam ≤ Real.pi * lam * t := by
        have := mul_le_mul_of_nonneg_left (Set.mem_Ici.mp ht1) (mul_nonneg Real.pi_pos.le hlam)
        simpa using this
      linarith
    calc ‖G t * (Real.exp (-(Real.pi * lam * t)) : ℂ)‖
        = ‖G t‖ * Real.exp (-(Real.pi * lam * t)) := by
          rw [norm_mul, norm_ofReal_eq_abs, abs_of_pos (Real.exp_pos _)]
      _ ≤ (C * Real.pi ^ m * t ^ (M + (m : ℝ)) * Real.exp (-(Real.pi * t)))
            * Real.exp (-(Real.pi * lam)) := by gcongr
      _ = C * Real.pi ^ m * Real.exp (-(Real.pi * lam))
            * (t ^ (M + (m : ℝ)) * Real.exp (-(Real.pi * t))) := by ring
  have hnorm_int : IntegrableOn
      (fun t : ℝ => ‖G t * (Real.exp (-(Real.pi * lam * t)) : ℂ)‖) (Set.Ici (1 : ℝ)) := by
    refine MeasureTheory.Integrable.mono'
      (f := fun t : ℝ => ‖G t * (Real.exp (-(Real.pi * lam * t)) : ℂ)‖)
      (g := fun t : ℝ => C * Real.pi ^ m * Real.exp (-(Real.pi * lam))
        * (t ^ (M + (m : ℝ)) * Real.exp (-(Real.pi * t)))) hmaj ?_ ?_
    · have h1 : AEStronglyMeasurable (fun t : ℝ => G t * (Real.exp (-(Real.pi * lam * t)) : ℂ))
          (volume.restrict (Set.Ici (1 : ℝ))) :=
        (hmeas.mul (by fun_prop : Continuous fun t : ℝ =>
          (((-(Real.pi * t) : ℝ)) : ℂ) ^ m).aestronglyMeasurable).mul
          (by fun_prop : Continuous fun t : ℝ =>
            (Real.exp (-(Real.pi * lam * t)) : ℂ)).aestronglyMeasurable
      simpa only [hG] using h1.norm
    · filter_upwards [hpoint] with t ht
      rwa [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
  rw [tailIntegral_iteratedDeriv g hmeas hC hM hb m lam (by linarith)]
  calc ‖tailIntegral G lam‖
      ≤ ∫ t in Set.Ici (1 : ℝ), ‖G t * (Real.exp (-(Real.pi * lam * t)) : ℂ)‖ := by
        rw [tailIntegral]
        exact MeasureTheory.norm_integral_le_integral_norm _
    _ ≤ ∫ t in Set.Ici (1 : ℝ), C * Real.pi ^ m * Real.exp (-(Real.pi * lam))
          * (t ^ (M + (m : ℝ)) * Real.exp (-(Real.pi * t))) := by
        exact integral_mono_ae hnorm_int hmaj hpoint
    _ = C * Real.pi ^ m * tailDecay M m * Real.exp (-(Real.pi * lam)) := by
        rw [tailDecay, MeasureTheory.integral_const_mul]
        ring

end Work.Asymptotics
