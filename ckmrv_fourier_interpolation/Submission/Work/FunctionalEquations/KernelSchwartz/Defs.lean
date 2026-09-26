import Mathlib
import Submission.Work.Analysis.ParamIntegral.iteratedDeriv_intervalIntegral_of_cont
import Submission.Work.FunctionalEquations.Basic
import Submission.Work.RadialSpace.EvenRadial

/-!
# The `m`-th contour integral of the interpolation kernel

CKMRV Theorem 3.1 obtains the coefficient functions of the interpolation basis as the
contour integrals

`a_m(x) = ∫_0^1 K(u + i y) x · e^{-2π i m (u + i y)} du`,

the value being independent of the height `y > 0` (the integrand is holomorphic in `τ`).
This file sets up the *normalised* version of this integral that is used for the Schwartz
and growth estimates: the height is taken to be `y_m = 1/(m+1)`, so that

* the exponential factor `e^{-2π i m (u + i y_m)}` has modulus `e^{2π m y_m} ≤ e^{2π}`,
  a constant, and
* the weight `(Im τ)^{-1} = m + 1` appearing in the growth hypothesis grows only
  polynomially in `m`.

The main objects are

* `Work.FunctionalEquations.KernelSchwartz.tauM m u = u + i / (m+1)`;
* `Work.FunctionalEquations.KernelSchwartz.expM m u = e^{-2π i m (u + i/(m+1))}`;
* `Work.FunctionalEquations.KernelSchwartz.psi N c m t = c m ∫_0^1 N (τ_m u) (t e₁) e^{...} du`,
  the profile of the `m`-th coefficient, as a function of one variable.

The lemmas proved here are the elementary ones: the basic bounds on `y_m`, `τ_m` and
`expM`, the transfer of the radial-derivative growth hypothesis to a bound for the
iterated derivatives of the *profile* `r ↦ N τ (r e₁)` on all of `ℝ` (the profile is
even, since `N τ` is radial), and the evenness of `psi`.
-/

namespace Work.FunctionalEquations.KernelSchwartz

open LeanEval.Analysis.CKMRVInterpolation Work.Core Work.FE Filter Topology
open scoped FourierTransform SchwartzMap

noncomputable section

variable {n : ℕ} [NeZero n]

/-! ### The height `y_m = 1/(m+1)` -/

/-- The height `y_m = 1/(m+1)` at which the `m`-th contour integral is computed. -/
def ym (m : Set.Ici (1:ℕ)) : ℝ := ((m.1 : ℝ) + 1)⁻¹

lemma ym_pos (m : Set.Ici (1:ℕ)) : 0 < ym m := by
  have : (0 : ℝ) < (m.1 : ℝ) + 1 := by positivity
  rw [ym]; positivity

lemma ym_nonneg (m : Set.Ici (1:ℕ)) : 0 ≤ ym m := (ym_pos m).le

lemma ym_inv (m : Set.Ici (1:ℕ)) : (ym m)⁻¹ = (m.1 : ℝ) + 1 := by
  rw [ym, inv_inv]

lemma ym_le_one (m : Set.Ici (1:ℕ)) : ym m ≤ 1 := by
  rw [ym, inv_le_one₀ (by positivity)]
  have : (0 : ℝ) ≤ (m.1 : ℝ) := Nat.cast_nonneg _
  linarith

/-- The point `u + i y_m` of the upper half plane. -/
def tauM (m : Set.Ici (1:ℕ)) (u : ℝ) : ℂ := (u : ℂ) + (ym m : ℂ) * Complex.I

lemma tauM_im (m : Set.Ici (1:ℕ)) (u : ℝ) : (tauM m u).im = ym m := by
  simp [tauM]

lemma tauM_im_pos (m : Set.Ici (1:ℕ)) (u : ℝ) : 0 < (tauM m u).im := by
  rw [tauM_im]; exact ym_pos m

lemma tauM_norm_le (m : Set.Ici (1:ℕ)) {u : ℝ} (hu : u ∈ Set.Icc (0:ℝ) 1) :
    ‖tauM m u‖ ≤ 2 := by
  calc ‖tauM m u‖ ≤ ‖(u : ℂ)‖ + ‖(ym m : ℂ) * Complex.I‖ := by
        rw [tauM]; exact norm_add_le _ _
    _ = |u| + ym m := by
        rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
          Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (ym_nonneg m)]
    _ ≤ 1 + 1 := by
        have hu1 : |u| ≤ 1 := abs_le.mpr ⟨by linarith [hu.1], hu.2⟩
        linarith [ym_le_one m]
    _ = 2 := by norm_num

@[simp] lemma tauM_zero_im (m : Set.Ici (1:ℕ)) : (tauM m 0).im = ym m := tauM_im m 0

/-- The exponential factor `e^{-2π i m (u + i y_m)}`. -/
def expM (m : Set.Ici (1:ℕ)) (u : ℝ) : ℂ :=
  Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (m.1 : ℂ) * tauM m u))

lemma expM_arg_re (m : Set.Ici (1:ℕ)) (u : ℝ) :
    (-(2 * (Real.pi : ℂ) * Complex.I * (m.1 : ℂ) * tauM m u)).re
      = 2 * Real.pi * (m.1 : ℝ) * ym m := by
  simp only [tauM, Complex.neg_re, Complex.mul_re, Complex.mul_im, Complex.add_re,
    Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    Complex.natCast_re, Complex.natCast_im, Complex.re_ofNat, Complex.im_ofNat]
  ring

lemma expM_norm (m : Set.Ici (1:ℕ)) (u : ℝ) :
    ‖expM m u‖ = Real.exp (2 * Real.pi * (m.1 : ℝ) * ym m) := by
  rw [expM, Complex.norm_exp, expM_arg_re]

/-- The exponential factor is bounded by the constant `e^{2π}`, uniformly in `m` and `u`. -/
lemma expM_norm_le (m : Set.Ici (1:ℕ)) (u : ℝ) : ‖expM m u‖ ≤ Real.exp (2 * Real.pi) := by
  rw [expM_norm]
  refine Real.exp_le_exp.mpr ?_
  have hm1 : (1 : ℝ) ≤ (m.1 : ℝ) := by exact_mod_cast m.2
  have hlt : (m.1 : ℝ) * ym m ≤ 1 := by
    rw [ym, mul_inv_le_iff₀ (by positivity : (0:ℝ) < (m.1:ℝ) + 1)]
    linarith
  nlinarith [Real.pi_pos, hm1, hlt]

/-! ### The profile of the `m`-th coefficient -/

/-- The profile of the `m`-th contour integral: the function of one variable
`t ↦ c m ∫_0^1 N (u + i y_m) (t e₁) e^{-2π i m (u + i y_m)} du`. -/
def psi (N : ℂ → E n → ℂ) (c : Set.Ici (1:ℕ) → ℂ) (m : Set.Ici (1:ℕ)) (t : ℝ) : ℂ :=
  c m * ∫ u in (0:ℝ)..1, N (tauM m u) (realIncl (n := n) t) * expM m u

lemma psi_apply (N : ℂ → E n → ℂ) (c : Set.Ici (1:ℕ) → ℂ) (m : Set.Ici (1:ℕ))
    (t : ℝ) :
    psi N c m t = c m * ∫ u in (0:ℝ)..1, N (tauM m u) (realIncl (n := n) t) * expM m u :=
  rfl

/-! ### Evenness of the profile and the transfer of the growth hypothesis -/

/-- The profile `r ↦ N τ (r e₁)` of a radial function is even. -/
lemma profile_even_of_radial (N : ℂ → E n → ℂ)
    (hN_radial : ∀ τ : ℂ, Radial (fun x : E n => N τ x)) (τ : ℂ) :
    Function.Even (fun r : ℝ => N τ (realIncl (n := n) r)) := by
  intro r
  exact hN_radial τ _ _ (by
    rw [Work.Sampling.realIncl_norm, Work.Sampling.realIncl_norm, abs_neg])

/-- For an even function, the norms of the iterated derivatives at `-t` and at `t` agree. -/
lemma norm_iteratedDeriv_neg_of_even {f : ℝ → ℂ} (hf : Function.Even f) (ℓ : ℕ) (t : ℝ) :
    ‖iteratedDeriv ℓ f (-t)‖ = ‖iteratedDeriv ℓ f t‖ := by
  have h1 : iteratedDeriv ℓ f t = (-1 : ℝ) ^ ℓ • iteratedDeriv ℓ f (-t) := by
    have h := iteratedDeriv_comp_neg (𝕜 := ℝ) ℓ f t
    rw [show (fun x : ℝ => f (-x)) = f from funext hf] at h
    exact h
  rw [h1, norm_smul, Real.norm_eq_abs, abs_pow, abs_neg, abs_one, one_pow, one_mul]

/-- **The radial-derivative growth bound along the coordinate axis.**  The growth
hypothesis for the radial derivatives of `N τ` on `E n` gives the same bound for the
iterated derivatives of the profile `r ↦ N τ (r e₁)` at *every* real `t`, because the
profile is even. -/
lemma profile_iteratedDeriv_bound (N : ℂ → E n → ℂ)
    (hN_radial : ∀ τ : ℂ, Radial (fun x : E n => N τ x))
    (hN_growth : ∀ k ℓ : ℕ, ∃ C : ℝ, ∃ N' : ℝ, 0 ≤ C ∧ 0 ≤ N' ∧
      ∀ (τ : ℂ) (x : E n), 0 < τ.im →
        ‖x‖ ^ k * ‖radialDeriv ℓ (fun y : E n => N τ y) x‖
          ≤ C * (1 + (τ.im)⁻¹ + ‖τ‖) ^ N') :
    ∀ k ℓ : ℕ, ∃ C : ℝ, ∃ N' : ℝ, 0 ≤ C ∧ 0 ≤ N' ∧
      ∀ (τ : ℂ), 0 < τ.im → ∀ t : ℝ,
        |t| ^ k * ‖iteratedDeriv ℓ (fun r : ℝ => N τ (realIncl (n := n) r)) t‖
          ≤ C * (1 + (τ.im)⁻¹ + ‖τ‖) ^ N' := by
  intro k ℓ
  obtain ⟨C, N', hC, hN', hb⟩ := hN_growth k ℓ
  refine ⟨C, N', hC, hN', fun τ hτ t => ?_⟩
  set g : ℝ → ℂ := fun r : ℝ => N τ (realIncl (n := n) r) with hg
  have heven : Function.Even g := profile_even_of_radial N hN_radial τ
  have h1 := hb τ (realIncl (n := n) |t|) hτ
  rw [Work.Sampling.realIncl_norm, abs_of_nonneg (abs_nonneg t)] at h1
  have h2 : radialDeriv ℓ (fun y : E n => N τ y) (realIncl (n := n) |t|)
      = iteratedDeriv ℓ g |t| := by
    rw [radialDeriv, Work.Sampling.realIncl_norm, abs_of_nonneg (abs_nonneg t)]
  rw [h2] at h1
  rcases le_total 0 t with ht | ht
  · rw [abs_of_nonneg ht] at h1 ⊢
    exact h1
  · have ht' : |t| = -t := abs_of_nonpos ht
    rw [ht', norm_iteratedDeriv_neg_of_even heven ℓ t] at h1
    rw [ht']; exact h1

/-- The profile of the `m`-th coefficient is even. -/
lemma psi_even (N : ℂ → E n → ℂ) (c : Set.Ici (1:ℕ) → ℂ)
    (hN_radial : ∀ τ : ℂ, Radial (fun x : E n => N τ x)) (m : Set.Ici (1:ℕ)) :
    Function.Even (psi N c m) := by
  intro t
  rw [psi_apply, psi_apply]
  congr 1
  refine intervalIntegral.integral_congr (fun u _ => ?_)
  have h : N (tauM m u) (realIncl (n := n) (-t))
      = N (tauM m u) (realIncl (n := n) t) :=
    hN_radial (tauM m u) _ _ (by
      rw [Work.Sampling.realIncl_norm, Work.Sampling.realIncl_norm, abs_neg])
  rw [h]

/-! ### Continuity and smoothness of the integrand -/

omit [NeZero n] in
lemma continuous_tauM (m : Set.Ici (1:ℕ)) : Continuous (tauM m) :=
  Complex.continuous_ofReal.add continuous_const

omit [NeZero n] in
lemma continuous_expM (m : Set.Ici (1:ℕ)) : Continuous (expM m) := by
  change Continuous (fun u : ℝ => Complex.exp
    (-(2 * (Real.pi : ℂ) * Complex.I * (m.1 : ℂ) * tauM m u)))
  refine Complex.continuous_exp.comp ?_
  have hfun : (fun u : ℝ => -(2 * (Real.pi : ℂ) * Complex.I * (m.1 : ℂ) * tauM m u))
      = fun u : ℝ => (-(2 * (Real.pi : ℂ) * Complex.I * (m.1 : ℂ))) * tauM m u := by
    funext u; ring
  rw [hfun]
  exact continuous_const.mul (continuous_tauM m)

/-- Continuity in `u` of `u ↦ N (u + i y_m) x`. -/
lemma continuousOn_tauM_apply (N : ℂ → E n → ℂ)
    (hN_cont : ∀ x : E n, ContinuousOn (fun τ : ℂ => N τ x) {τ : ℂ | 0 < τ.im})
    (m : Set.Ici (1:ℕ)) (x : E n) : Continuous (fun u : ℝ => N (tauM m u) x) :=
  (hN_cont x).comp_continuous (continuous_tauM m) (fun u => tauM_im_pos m u)

/-- Continuity in `u` of the integrand of `psi`. -/
lemma continuous_integrand (N : ℂ → E n → ℂ)
    (hN_cont : ∀ x : E n, ContinuousOn (fun τ : ℂ => N τ x) {τ : ℂ | 0 < τ.im})
    (m : Set.Ici (1:ℕ)) (r : ℝ) :
    Continuous (fun u : ℝ => N (tauM m u) (realIncl (n := n) r) * expM m u) :=
  (continuousOn_tauM_apply N hN_cont m _).mul (continuous_expM m)

lemma contDiff_realIncl : ContDiff ℝ ⊤ (realIncl (n := n)) := by
  have h2 : (realIncl (n := n)) = fun s : ℝ => s • realIncl (n := n) 1 :=
    funext (fun s => Work.Sampling.realIncl_eq_smul (n := n) s)
  rw [h2]
  exact contDiff_id.smul contDiff_const

/-- Smoothness in `r` of the integrand of `psi`. -/
lemma contDiff_integrand (N : ℂ → E n → ℂ)
    (hN_smooth : ∀ τ : ℂ, ContDiff ℝ ⊤ (fun x : E n => N τ x))
    (m : Set.Ici (1:ℕ)) (u : ℝ) :
    ContDiff ℝ ⊤ (fun r : ℝ => N (tauM m u) (realIncl (n := n) r) * expM m u) :=
  ((hN_smooth (tauM m u)).comp contDiff_realIncl).mul contDiff_const

end

end Work.FunctionalEquations.KernelSchwartz
