import Mathlib
import Submission.Work.FunctionalEquations.DensityAux.composite_seminorm_smooth
import Submission.Work.Radial.gaussian_profile_schwartz

/-!
# Schwartz seminorm bound for a Gaussian times a shifted compactly supported profile

Let `h : 𝓢(ℝ, ℂ)` vanish for `|t| ≥ R` and let `y > 0`.  For every `a : ℝ` the function

  `x ↦ exp (-π y ‖x‖²) * h (‖x‖² - a)`

is a Schwartz function on `ℝⁿ` (it is a Gaussian times the compactly supported profile
`t ↦ h (t - a)`), and its `(k, l)` Schwartz seminorm is bounded by

  `C * exp (-π y (|a| - R)) * (1 + |a| + R) ^ (k + 2l)`.

The exponential factor is the crucial one: the profile can only be nonzero where
`|‖x‖² - a| < R`, i.e. where `‖x‖² ≈ a`, and there the Gaussian contributes
`exp (-π y (|a| - R))`.

The proof proceeds by the Faà di Bruno/Taylor-composition bound
`Work.FunctionalEquations.DensityAux.composite_seminorm_smooth` applied to the
one-variable profile `Ψ (s) = exp (-π y s) h (s - a)`: away from the support region
`Ψ` is identically zero near the point in question, while on the support region its
`j`-th derivative is bounded by the Leibniz rule and the Schwartz seminorms of `h`.

## Main results

* `Work.FunctionalEquations.DensityAux.shift_weightedDerivBound`: the weighted
  one-variable derivative bound.
* `Work.FunctionalEquations.DensityAux.shiftedProfileSeminorm`: the seminorm bound.
-/

open scoped SchwartzMap ContDiff
open Filter Topology

namespace Work.FunctionalEquations.DensityAux

/-- Every natural number, viewed in `ℕ∞ω`, is at most `∞` (`C^∞`). -/
lemma shift_natCast_le_infinity (j : ℕ) : (j : ℕ∞ω) ≤ ∞ := WithTop.coe_le_coe.mpr le_top

/-- On `[0, ∞)` the derivative within `[0, ∞)` of a globally smooth function is the
ordinary derivative. -/
lemma shift_iteratedDerivWithin_Ici_eq (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (j : ℕ) (s : ℝ)
    (hs : 0 ≤ s) : iteratedDerivWithin j f (Set.Ici (0:ℝ)) s = iteratedDeriv j f s :=
  iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Ici 0)
    ((hf.of_le (shift_natCast_le_infinity j)).contDiffAt) hs

/-- Leibniz' rule for the iterated derivative of a product. -/
lemma shift_iteratedDeriv_mul_eq_sum {f g : ℝ → ℂ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (j : ℕ) (x : ℝ) :
    iteratedDeriv j (fun s : ℝ => f s * g s) x =
      ∑ i ∈ Finset.range (j + 1),
        (j.choose i : ℂ) * iteratedDeriv i f x * iteratedDeriv (j - i) g x := by
  have h := iteratedDerivWithin_mul (𝕜 := ℝ) (s := Set.univ) (x := x) (n := j) (Set.mem_univ x)
    uniqueDiffOn_univ (f := f) (g := g) ((hf.of_le (shift_natCast_le_infinity j)).contDiffWithinAt)
    ((hg.of_le (shift_natCast_le_infinity j)).contDiffWithinAt)
  simp only [iteratedDerivWithin_univ] at h
  have h2 : (fun s : ℝ => f s * g s) = f * g := by funext s; rfl
  rw [h2]
  exact h

/-- The iterated derivatives of the zero function vanish. -/
lemma shift_iteratedDeriv_zero_fun (j : ℕ) : iteratedDeriv j (0 : ℝ → ℂ) = 0 := by
  induction j with
  | zero => ext t; simp
  | succ i ih => rw [iteratedDeriv_succ, ih]; ext t; simp

/-- The binomial theorem in the form used for the Leibniz bound. -/
lemma shift_sum_choose_mul_pow (x : ℝ) (j : ℕ) :
    ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * x ^ i = (1 + x) ^ j := by
  rw [add_comm 1 x, add_pow]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [one_pow, mul_one]
  ring

/-- The iterated derivative of `t ↦ exp (z t)` along the real axis. -/
lemma shift_iteratedDeriv_cexp_mul_ofReal (z : ℂ) (i : ℕ) :
    iteratedDeriv i (fun t : ℝ => Complex.exp (z * (t : ℂ))) =
      fun t : ℝ => z^i * Complex.exp (z * (t : ℂ)) := by
  induction i with
  | zero => funext t; simp
  | succ i ih =>
    rw [iteratedDeriv_succ, ih]
    funext t
    have hz : HasDerivAt (fun t : ℝ => z * (t : ℂ)) z t := by
      simpa using (Complex.ofRealCLM.hasDerivAt (x := t)).const_mul z
    have h4 := (hz.cexp).const_mul (z^i)
    rw [h4.deriv]
    ring

/-- Norm of the iterated derivative of `t ↦ exp (z t)`. -/
lemma shift_norm_iteratedDeriv_cexp_mul_ofReal (z : ℂ) (i : ℕ) (t : ℝ) :
    ‖iteratedDeriv i (fun t : ℝ => Complex.exp (z * (t : ℂ))) t‖
      = ‖z‖^i * Real.exp ((z * (t : ℂ)).re) := by
  rw [shift_iteratedDeriv_cexp_mul_ofReal, norm_mul, norm_pow, Complex.norm_exp]

/-- The exponential of a negative real multiple, in the two forms used below. -/
lemma shift_cexp_arg_eq (c : ℝ) :
    (fun t : ℝ => Complex.exp (↑(-(c * t)))) =
      (fun t : ℝ => Complex.exp ((-(↑c) : ℂ) * (t : ℂ))) := by
  funext t
  congr 1
  push_cast
  ring

/-- **The weighted derivative bound.**  For `h : 𝓢(ℝ, ℂ)` vanishing for `|t| ≥ R` and
`a : ℝ`, the profile `Ψ (s) = exp (-π y s) h (s - a)` satisfies

  `(1 + s) ^ (k + 2l) * ‖Ψ^(j) (s)‖
     ≤ (∑ i ≤ l ‖h‖_{0,i}) * (1 + π y) ^ l * exp (-π y (|a| - R)) * (1 + |a| + R) ^ (k + 2l)`

for all `j ≤ l` and `s ≥ 0`. -/
lemma shift_weightedDerivBound {y : ℝ} (hy : 0 < y) (h : SchwartzMap ℝ ℂ) {R : ℝ}
    (hRpos : 0 < R) (hR : ∀ t : ℝ, R ≤ |t| → (h : ℝ → ℂ) t = 0) (a : ℝ) (k l : ℕ) :
    ∀ j : ℕ, j ≤ l → ∀ s : ℝ, 0 ≤ s →
      (1 + s) ^ (k + 2 * l) *
        ‖iteratedDerivWithin j
          (fun s : ℝ => Complex.exp (↑(-(Real.pi * y * s))) * (h : ℝ → ℂ) (s - a))
          (Set.Ici (0:ℝ)) s‖
        ≤ (∑ i ∈ Finset.range (l + 1), (SchwartzMap.seminorm ℂ 0 i) h)
            * (1 + Real.pi * y) ^ l
            * Real.exp (-(Real.pi * y * (|a| - R)))
            * (1 + |a| + R) ^ (k + 2 * l) := by
  intro j hj s hs
  set S : ℝ := ∑ i ∈ Finset.range (l + 1), (SchwartzMap.seminorm ℂ 0 i) h with hSdef
  have hSnn : 0 ≤ S := by
    rw [hSdef]
    exact Finset.sum_nonneg (fun i _ => by positivity)
  set E : ℝ → ℂ := fun t => Complex.exp ((-(↑(Real.pi * y)) : ℂ) * (t : ℂ)) with hEdef
  set H : ℝ → ℂ := fun t => (h : ℝ → ℂ) (t - a) with hHdef
  have hEsm : ContDiff ℝ ∞ E := by
    rw [hEdef]
    exact Complex.contDiff_exp.comp (contDiff_const.mul Complex.ofRealCLM.contDiff)
  have hHsm : ContDiff ℝ ∞ H := by
    rw [hHdef]
    exact (h.smooth ⊤).comp (by fun_prop)
  have hPsm : ContDiff ℝ ∞ (fun s : ℝ => E s * H s) := hEsm.mul hHsm
  have hfun : (fun s : ℝ => Complex.exp (↑(-(Real.pi * y * s))) * (h : ℝ → ℂ) (s - a))
      = fun s : ℝ => E s * H s := by
    funext t
    rw [hEdef, hHdef]
    congr 1
    exact congrFun (shift_cexp_arg_eq (Real.pi * y)) t
  rw [hfun]
  have hstep : iteratedDerivWithin j (fun s : ℝ => E s * H s) (Set.Ici (0:ℝ)) s
      = iteratedDeriv j (fun s : ℝ => E s * H s) s :=
    shift_iteratedDerivWithin_Ici_eq _ hPsm j s hs
  rw [hstep]
  by_cases hcase : |s - a| ≤ R
  · -- ## inside the support region
    have hleib := shift_iteratedDeriv_mul_eq_sum hEsm hHsm j s
    rw [hleib]
    -- ## bound on the summands
    have hterm : ∀ i ∈ Finset.range (j + 1),
        ‖(j.choose i : ℂ) * iteratedDeriv i E s * iteratedDeriv (j - i) H s‖
          ≤ ((j.choose i : ℝ) * (Real.pi * y)^i) * (Real.exp (-(Real.pi * y * s)) * S) := by
      intro i hi
      have hij : i ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      have hji : j - i ≤ l := by omega
      have hE' : ‖iteratedDeriv i E s‖ = (Real.pi * y)^i * Real.exp (-(Real.pi * y * s)) := by
        rw [hEdef, shift_norm_iteratedDeriv_cexp_mul_ofReal]
        have h1 : ((-(↑(Real.pi * y)) : ℂ) * (s : ℂ)).re = -(Real.pi * y * s) := by
          simp only [Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.ofReal_re,
            Complex.ofReal_im]
          ring
        rw [h1]
        have h2 : ‖(-(↑(Real.pi * y)) : ℂ)‖ = Real.pi * y := by
          calc ‖(-(↑(Real.pi * y)) : ℂ)‖ = ‖(↑(Real.pi * y) : ℂ)‖ := norm_neg _
            _ = |Real.pi * y| := RCLike.norm_ofReal _
            _ = Real.pi * y := abs_of_nonneg (by positivity)
        rw [h2]
      have hH' : ‖iteratedDeriv (j - i) H s‖ ≤ S := by
        rw [hHdef]
        have h3 : iteratedDeriv (j - i) (fun t : ℝ => (h : ℝ → ℂ) (t - a)) s
            = iteratedDeriv (j - i) (⇑h) (s - a) := by
          rw [iteratedDeriv_comp_sub_const]
        rw [h3, ← norm_iteratedFDeriv_eq_norm_iteratedDeriv]
        refine le_trans (SchwartzMap.norm_iteratedFDeriv_le_seminorm ℂ h (j - i) (s - a)) ?_
        rw [hSdef]
        exact Finset.single_le_sum (f := fun i => (SchwartzMap.seminorm ℂ 0 i) h)
          (fun i _ => by positivity) (Finset.mem_range.mpr (Nat.lt_succ_of_le hji))
      calc ‖(j.choose i : ℂ) * iteratedDeriv i E s * iteratedDeriv (j - i) H s‖
          = ‖(j.choose i : ℂ)‖ * ‖iteratedDeriv i E s‖ * ‖iteratedDeriv (j - i) H s‖ := by
            rw [norm_mul, norm_mul]
        _ ≤ (j.choose i : ℝ) * ((Real.pi * y)^i * Real.exp (-(Real.pi * y * s))) * S := by
            refine mul_le_mul (mul_le_mul ?_ ?_ (by positivity) (by positivity)) hH'
              (norm_nonneg _) (by positivity)
            · rw [Complex.norm_natCast]
            · exact le_of_eq hE'
        _ = ((j.choose i : ℝ) * (Real.pi * y)^i) * (Real.exp (-(Real.pi * y * s)) * S) := by
            ring
    -- ## the sum
    have hsum_le : ‖∑ i ∈ Finset.range (j + 1),
          (j.choose i : ℂ) * iteratedDeriv i E s * iteratedDeriv (j - i) H s‖
        ≤ (1 + Real.pi * y)^l * (Real.exp (-(Real.pi * y * s)) * S) := by
      refine le_trans (norm_sum_le _ _) ?_
      have h2 : ∑ i ∈ Finset.range (j + 1),
            ((j.choose i : ℝ) * (Real.pi * y)^i) * (Real.exp (-(Real.pi * y * s)) * S)
          = (∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * (Real.pi * y)^i)
            * (Real.exp (-(Real.pi * y * s)) * S) := (Finset.sum_mul ..).symm
      have h3 : ∑ i ∈ Finset.range (j + 1), ‖(j.choose i : ℂ) * iteratedDeriv i E s
            * iteratedDeriv (j - i) H s‖ ≤ (1 + Real.pi * y)^j
              * (Real.exp (-(Real.pi * y * s)) * S) := by
        refine le_trans (Finset.sum_le_sum hterm) ?_
        rw [h2, shift_sum_choose_mul_pow]
      exact le_trans h3 (mul_le_mul_of_nonneg_right
        (pow_le_pow_right₀ (by nlinarith [Real.pi_pos, hy]) hj) (by positivity))
    -- ## the two numerical inequalities on the support region
    have habs_le : |a| - R ≤ s := by
      have h1 : -R ≤ s - a ∧ s - a ≤ R := abs_le.mp hcase
      rcases le_total 0 a with ha | ha
      · rw [abs_of_nonneg ha]; linarith [h1.1]
      · rw [abs_of_nonpos ha]; linarith [h1.2, hs]
    have hexp_le : Real.exp (-(Real.pi * y * s)) ≤ Real.exp (-(Real.pi * y * (|a| - R))) := by
      apply Real.exp_le_exp.mpr
      have h := mul_le_mul_of_nonneg_left habs_le (by positivity : (0:ℝ) ≤ Real.pi * y)
      linarith
    have hpow_le : (1 + s) ^ (k + 2 * l) ≤ (1 + |a| + R) ^ (k + 2 * l) := by
      have h1 : s - a ≤ R := (abs_le.mp hcase).2
      have h2 : s ≤ |a| + R := by linarith [le_abs_self a]
      exact pow_le_pow_left₀ (by linarith) (by linarith) _
    calc (1 + s) ^ (k + 2 * l) * ‖∑ i ∈ Finset.range (j + 1),
            (j.choose i : ℂ) * iteratedDeriv i E s * iteratedDeriv (j - i) H s‖
        ≤ (1 + s) ^ (k + 2 * l)
            * ((1 + Real.pi * y)^l * (Real.exp (-(Real.pi * y * s)) * S)) := by
          exact mul_le_mul_of_nonneg_left hsum_le (by positivity)
      _ = ((1 + s) ^ (k + 2 * l) * Real.exp (-(Real.pi * y * s)))
            * ((1 + Real.pi * y)^l * S) := by ring
      _ ≤ ((1 + |a| + R) ^ (k + 2 * l) * Real.exp (-(Real.pi * y * (|a| - R))))
            * ((1 + Real.pi * y)^l * S) := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          exact mul_le_mul hpow_le hexp_le (by positivity) (by positivity)
      _ = S * (1 + Real.pi * y)^l * Real.exp (-(Real.pi * y * (|a| - R)))
            * (1 + |a| + R) ^ (k + 2 * l) := by ring
  · -- ## outside the support region the profile vanishes near `s`
    simp only [not_le] at hcase
    have hev : (fun s : ℝ => E s * H s) =ᶠ[𝓝 s] 0 := by
      have hpos : 0 < |s - a| - R := sub_pos.mpr hcase
      filter_upwards [Metric.ball_mem_nhds s (half_pos hpos)] with u hu
      rw [Metric.mem_ball, dist_eq_norm, Real.norm_eq_abs] at hu
      have h2 : |s - a| - |u - s| ≤ |u - a| := by
        have h5 : |s - a| ≤ |u - a| + |u - s| := by
          have h6 : s - a = (u - a) + (s - u) := by ring
          calc |s - a| = |(u - a) + (s - u)| := by rw [h6]
            _ ≤ |u - a| + |s - u| := abs_add_le _ _
            _ = |u - a| + |u - s| := by rw [abs_sub_comm s u]
        linarith
      have hRs : R ≤ |u - a| := by linarith
      have hzero : H u = 0 := by
        rw [hHdef]
        exact hR (u - a) hRs
      show E u * H u = 0
      rw [hzero, mul_zero]
    have hLnn : 0 ≤ S * (1 + Real.pi * y)^l * Real.exp (-(Real.pi * y * (|a| - R)))
        * (1 + |a| + R) ^ (k + 2 * l) := by
      have h2 : 0 < 1 + |a| + R := by linarith [abs_nonneg a]
      positivity
    rw [hev.iteratedDeriv_eq]
    simp only [shift_iteratedDeriv_zero_fun, Pi.zero_apply, norm_zero, mul_zero]
    exact hLnn

/-- **The Schwartz seminorm of a Gaussian times a shifted compactly supported profile.**

There is a constant `C ≥ 0` such that for all `N ≥ 1` and nonzero `m : ℤ`, the function

  `x ↦ exp (-π y ‖x‖²) * h (‖x‖² - 2 N m)`

is a Schwartz function on `ℝⁿ` whose `(k, l)` seminorm is bounded by

  `C * exp (-π y (2 N |m| - R)) * (1 + 2 N |m| + R) ^ (k + 2l)`. -/
theorem shiftedProfileSeminorm (n : ℕ) [NeZero n] {y : ℝ} (hy : 0 < y)
    (h : SchwartzMap ℝ ℂ) {R : ℝ} (hR : ∀ t : ℝ, R ≤ |t| → h t = 0) (k l : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ) (m : ℤ), 1 ≤ N → m ≠ 0 →
      ∃ T : SchwartzMap (EuclideanSpace ℝ (Fin n)) ℂ,
        (∀ x, T x = Complex.exp (-(Real.pi * y * (‖x‖ ^ 2 : ℝ))) *
            h ((‖x‖ ^ 2) - 2 * (N : ℝ) * (m : ℝ))) ∧
        (SchwartzMap.seminorm ℂ k l) T
          ≤ C * Real.exp (-(Real.pi * y * (2 * (N : ℝ) * |(m : ℝ)| - R)))
              * (1 + 2 * (N : ℝ) * |(m : ℝ)| + R) ^ (k + 2 * l) := by
  obtain ⟨C₀, hC₀nn, hC₀⟩ := composite_seminorm_smooth n k l
  by_cases hR0 : R ≤ 0
  · -- `h` vanishes identically, so the zero function works
    refine ⟨0, le_refl 0, ?_⟩
    intro N m hN hm
    refine ⟨0, ?_, ?_⟩
    · intro x
      have hz : (h : ℝ → ℂ) ((‖x‖ ^ 2) - 2 * (N : ℝ) * (m : ℝ)) = 0 :=
        hR _ (le_trans hR0 (abs_nonneg _))
      rw [hz]; simp
    · simp
  · simp only [not_le] at hR0
    set S : ℝ := ∑ i ∈ Finset.range (l + 1), (SchwartzMap.seminorm ℂ 0 i) h with hSdef
    refine ⟨C₀ * S * (1 + Real.pi * y) ^ l, ?_, ?_⟩
    · have h1 : 0 < 1 + Real.pi * y := by nlinarith [Real.pi_pos, hy]
      have h2 : 0 ≤ S := by rw [hSdef]; exact Finset.sum_nonneg (fun i _ => by positivity)
      positivity
    · intro N m hN hm
      set a : ℝ := 2 * (N : ℝ) * (m : ℝ) with hadef
      have habs : |a| = 2 * (N : ℝ) * |(m : ℝ)| := by
        rw [hadef, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2),
          abs_of_nonneg (Nat.cast_nonneg N)]
      -- the shifted profile is smooth with compact support
      have hhsm : ContDiff ℝ ∞ (fun t : ℝ => (h : ℝ → ℂ) (t - a)) :=
        (h.smooth ⊤).comp (by fun_prop)
      have hsupp : ∃ R' : ℝ, ∀ t : ℝ, R' ≤ |t| → (h : ℝ → ℂ) (t - a) = 0 := by
        refine ⟨|a| + R, ?_⟩
        intro t ht
        refine hR (t - a) ?_
        have h1 : |t| - |a| ≤ |t - a| := abs_sub_abs_le_abs_sub t a
        have h2 : |a| ≤ |t| := by linarith
        linarith
      obtain ⟨T, hT⟩ := Work.Radial.gaussian_profile_schwartz (n := n) y hhsm hsupp
      have hTval : ∀ x, T x = Complex.exp (-(Real.pi * y * (‖x‖ ^ 2 : ℝ))) *
          (h : ℝ → ℂ) ((‖x‖ ^ 2) - a) := by
        intro x
        rw [hT x, Work.Radial.gaussianTimesProfile, Work.Radial.gaussianWeight]
      refine ⟨T, ?_, ?_⟩
      · intro x
        rw [hTval x]
      · set L : ℝ := S * (1 + Real.pi * y)^l * Real.exp (-(Real.pi * y * (|a| - R)))
            * (1 + |a| + R)^(k + 2*l) with hLdef
        have hLnn : 0 ≤ L := by
          rw [hLdef]
          have h1 : 0 < 1 + |a| + R := by linarith [abs_nonneg a]
          have h2 : 0 < 1 + Real.pi * y := by nlinarith [Real.pi_pos, hy]
          have h3 : 0 ≤ S := by rw [hSdef]; exact Finset.sum_nonneg (fun i _ => by positivity)
          positivity
        -- the one-variable profile and its weighted derivative bound
        have hPsi_sm : ContDiffOn ℝ ∞ (fun s : ℝ =>
            Complex.exp (↑(-(Real.pi * y * s))) * (h : ℝ → ℂ) (s - a)) (Set.Ici (0:ℝ)) := by
          have h1 : ContDiff ℝ ∞ (fun s : ℝ => Complex.exp (↑(-(Real.pi * y * s)))) :=
            Complex.contDiff_exp.comp
              (Complex.ofRealCLM.contDiff.comp (contDiff_const.mul contDiff_id).neg)
          exact (h1.mul ((h.smooth ⊤).comp (by fun_prop))).contDiffOn
        have hw := shift_weightedDerivBound hy h hR0 hR a k l
        have hfun : (⇑T : EuclideanSpace ℝ (Fin n) → ℂ)
            = fun x => Complex.exp (↑(-(Real.pi * y * ‖x‖ ^ 2))) * (h : ℝ → ℂ) (‖x‖ ^ 2 - a) := by
          funext z
          rw [hTval z]
          congr 1
          simp only [Complex.ofReal_neg, Complex.ofReal_mul]
        have hgoal : ∀ x : EuclideanSpace ℝ (Fin n),
            ‖x‖ ^ k * ‖iteratedFDeriv ℝ l (⇑T) x‖ ≤ C₀ * L := by
          intro x
          rw [hfun]
          exact hC₀ _ L hPsi_sm hw x
        refine le_trans (SchwartzMap.seminorm_le_bound ℂ k l T ?_ hgoal) ?_
        · exact mul_nonneg hC₀nn hLnn
        · rw [hLdef, habs]
          apply le_of_eq
          ring_nf

end Work.FunctionalEquations.DensityAux
