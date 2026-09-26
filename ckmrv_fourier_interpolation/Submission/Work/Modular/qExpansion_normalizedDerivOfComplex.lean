import Mathlib
import Submission.Work.Modular.Basic

/-!
# The `q`-expansion of the normalized derivative `D = (2πi)⁻¹ d/dτ`

For a holomorphic, `1`-periodic function `f : ℍ → ℂ` which is bounded at `i∞`, the
`q`-expansion of `Derivative.normalizedDerivOfComplex f` is obtained from the
`q`-expansion of `f` by multiplying the `n`-th coefficient by `n`.

The proof goes through the `cuspFunction` `C q = f(τ)` with `q = exp (2πi τ)`:

* the chain rule along `τ ↦ q = exp (2πiτ)` gives, for every `τ : ℍ`,
  `D f τ = q · C'(q)`;
* consequently the value of `D f` at `q ≠ 0` is `q · C'(q)`, and the cusp function of
  `D f` agrees with `q ↦ q · C'(q)` near `0` (the value at `0` is forced by continuity,
  both sides being `0` there);
* since `C` is analytic at `0`, `iteratedDeriv n (q ↦ q C'(q)) 0 = n · iteratedDeriv n C 0`
  by Leibniz's rule, and `qExpansion` is the Taylor development of the cusp function.
-/

namespace Work.Modular

open UpperHalfPlane ModularForm Filter
open scoped Manifold MatrixGroups ModularForm Topology

/-- The derivative of the `q`-parameter `𝕢 1 z = exp (2πi z)` is `2πi 𝕢 1 z`. -/
lemma deriv_qParam_one (z : ℂ) :
    deriv (Function.Periodic.qParam 1) z = 2 * Real.pi * Complex.I * Function.Periodic.qParam 1 z := by
  have h1 : HasDerivAt (fun y : ℂ => (2 * Real.pi * Complex.I) * y) (2 * Real.pi * Complex.I) z := by
    simpa using (hasDerivAt_id z).const_mul (2 * Real.pi * Complex.I)
  have h2 : HasDerivAt (fun y : ℂ => Complex.exp ((2 * Real.pi * Complex.I) * y))
      (Complex.exp ((2 * Real.pi * Complex.I) * z) * (2 * Real.pi * Complex.I)) z := h1.cexp
  have h3 : Function.Periodic.qParam 1 =
      fun y : ℂ => Complex.exp ((2 * Real.pi * Complex.I) * y) := by
    ext y; simp [Function.Periodic.qParam, mul_assoc]
  rw [h3]
  convert h2.deriv using 1
  ring

/-- Chain rule for the normalized derivative along the `q`-parameter: if `f` is
`1`-periodic and holomorphic, then `D f τ = 𝕢 1 τ · C'(𝕢 1 τ)`, where `C` is the
`cuspFunction` of `f`. -/
lemma normalizedDeriv_eq_qParam_mul_deriv_cuspFunction {f : ℍ → ℂ}
    (hper : Function.Periodic (f ∘ UpperHalfPlane.ofComplex) 1) (hhol : MDiff f) (τ : ℍ) :
    Derivative.normalizedDerivOfComplex f τ =
      Function.Periodic.qParam 1 (τ : ℂ) *
        deriv (UpperHalfPlane.cuspFunction 1 f) (Function.Periodic.qParam 1 (τ : ℂ)) := by
  have hφdiff : DifferentiableAt ℂ (f ∘ UpperHalfPlane.ofComplex) (τ : ℂ) :=
    UpperHalfPlane.mdifferentiableAt_iff.mp (hhol τ)
  have hCd : DifferentiableAt ℂ (UpperHalfPlane.cuspFunction 1 f)
      (Function.Periodic.qParam 1 (τ : ℂ)) :=
    Function.Periodic.differentiableAt_cuspFunction (h := (1 : ℝ)) one_ne_zero hper hφdiff
  have hφeq : f ∘ UpperHalfPlane.ofComplex =
      UpperHalfPlane.cuspFunction 1 f ∘ (Function.Periodic.qParam 1) := by
    funext z
    exact (Function.Periodic.eq_cuspFunction one_ne_zero hper z).symm
  have hder : deriv (f ∘ UpperHalfPlane.ofComplex) (τ : ℂ) =
      deriv (UpperHalfPlane.cuspFunction 1 f) (Function.Periodic.qParam 1 (τ : ℂ)) *
        deriv (Function.Periodic.qParam 1) (τ : ℂ) := by
    rw [hφeq, deriv_comp (τ : ℂ) hCd (Function.Periodic.differentiable_qParam (τ : ℂ))]
  rw [Derivative.normalizedDerivOfComplex, hder, deriv_qParam_one]
  rw [inv_mul_eq_iff_eq_mul₀ Complex.two_pi_I_ne_zero]
  ring

/-- Leibniz's rule in the special case `q ↦ q · C'(q)`: for `C` analytic at `0`,
the `n`-th iterated derivative at `0` of `q ↦ q C'(q)` is `n` times that of `C`. -/
lemma iteratedDeriv_mul_deriv_self (C : ℂ → ℂ) (hC : AnalyticAt ℂ C 0) (n : ℕ) :
    iteratedDeriv n (fun q => q * deriv C q) 0 = (n : ℂ) * iteratedDeriv n C 0 := by
  have hid : ContDiffAt ℂ (n : WithTop ℕ∞) (id : ℂ → ℂ) 0 := contDiffAt_id
  have hdc : ContDiffAt ℂ (n : WithTop ℕ∞) (deriv C) 0 := hC.deriv.contDiffAt
  have hfun : (fun q : ℂ => q * deriv C q) = id * deriv C := rfl
  rw [hfun, iteratedDeriv_mul hid hdc]
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; simp
  · have hsub : iteratedDeriv (n - 1) (deriv C) 0 = iteratedDeriv n C 0 := by
      rw [← iteratedDeriv_succ' (n := n - 1) (f := C), show n - 1 + 1 = n by omega]
    rw [Finset.sum_eq_single 1]
    · rw [hsub, iteratedDeriv_id]
      simp [Nat.choose_one_right]
    · intro i _ hi1
      rw [iteratedDeriv_id]
      have h0 : (if i = 0 then (0 : ℂ) else if i = 1 then 1 else 0) = 0 := by
        rcases eq_or_ne i 0 with rfl | hi0
        · simp
        · simp [hi0, hi1]
      rw [h0, mul_zero, zero_mul]
    · intro h1; exact absurd (Finset.mem_range.mpr (by omega)) h1

/-- The normalized derivative `D = (2πi)⁻¹ d/dτ` acts on `q`-expansions by `q ↦ q d/dq`:
if `f` is holomorphic, periodic of period `1` and bounded at `i∞`, then the `q`-expansion of
`D f` is obtained from that of `f` by multiplying the `n`-th coefficient by `n`. -/
theorem qExpansion_normalizedDerivOfComplex {f : ℍ → ℂ}
    (hper : Function.Periodic (f ∘ UpperHalfPlane.ofComplex) 1) (hhol : MDiff f)
    (hbdd : IsBoundedAtImInfty f) (n : ℕ) :
    (UpperHalfPlane.qExpansion 1 (Derivative.normalizedDerivOfComplex f)).coeff n =
      (n : ℂ) * (UpperHalfPlane.qExpansion 1 f).coeff n := by
  have hC_analytic : AnalyticAt ℂ (UpperHalfPlane.cuspFunction 1 f) 0 :=
    UpperHalfPlane.analyticAt_cuspFunction_zero one_pos hper hhol hbdd
  -- On the punctured unit disc the cusp function of `D f` is `q ↦ q C'(q)`.
  have hnonzero : ∀ q : ℂ, q ≠ 0 → ‖q‖ < 1 →
      UpperHalfPlane.cuspFunction 1 (Derivative.normalizedDerivOfComplex f) q =
        q * deriv (UpperHalfPlane.cuspFunction 1 f) q := by
    intro q hqne hq
    have hw : 0 < (Function.Periodic.invQParam 1 q).im :=
      Function.Periodic.im_invQParam_pos_of_norm_lt_one one_pos hq hqne
    have h1 : UpperHalfPlane.cuspFunction 1 (Derivative.normalizedDerivOfComplex f) q =
        Derivative.normalizedDerivOfComplex f
          (UpperHalfPlane.ofComplex (Function.Periodic.invQParam 1 q)) :=
      Function.Periodic.cuspFunction_eq_of_nonzero 1 _ hqne
    have h2 : Derivative.normalizedDerivOfComplex f
          (UpperHalfPlane.ofComplex (Function.Periodic.invQParam 1 q)) =
        Function.Periodic.qParam 1 (Function.Periodic.invQParam 1 q) *
          deriv (UpperHalfPlane.cuspFunction 1 f)
            (Function.Periodic.qParam 1 (Function.Periodic.invQParam 1 q)) := by
      simpa [UpperHalfPlane.ofComplex_apply_of_im_pos hw] using
        normalizedDeriv_eq_qParam_mul_deriv_cuspFunction hper hhol
          ⟨Function.Periodic.invQParam 1 q, hw⟩
    rw [h1, h2, Function.Periodic.qParam_right_inv one_ne_zero hqne]
  -- Value at `q = 0`: both sides vanish, the left one by continuity at `0`.
  have h0eq : UpperHalfPlane.cuspFunction 1 (Derivative.normalizedDerivOfComplex f) 0 = 0 := by
    change Function.Periodic.cuspFunction 1
      ((Derivative.normalizedDerivOfComplex f) ∘ UpperHalfPlane.ofComplex) 0 = 0
    have hGcont : ContinuousAt
        (fun q : ℂ => q * deriv (UpperHalfPlane.cuspFunction 1 f) q) 0 :=
      (analyticAt_id.mul hC_analytic.deriv).continuousAt
    have hlim : Tendsto (fun q : ℂ => q * deriv (UpperHalfPlane.cuspFunction 1 f) q)
        (𝓝[≠] (0 : ℂ)) (𝓝 (0 : ℂ)) := by
      have h := hGcont.tendsto.mono_left (nhdsWithin_le_nhds (a := (0 : ℂ)) (s := {0}ᶜ))
      simpa using h
    have hloc : Function.Periodic.cuspFunction 1
          ((Derivative.normalizedDerivOfComplex f) ∘ UpperHalfPlane.ofComplex) =ᶠ[𝓝[≠] (0 : ℂ)]
        (fun q : ℂ => q * deriv (UpperHalfPlane.cuspFunction 1 f) q) := by
      change ∀ᶠ q in 𝓝[≠] (0 : ℂ), Function.Periodic.cuspFunction 1
          ((Derivative.normalizedDerivOfComplex f) ∘ UpperHalfPlane.ofComplex) q =
            (fun q : ℂ => q * deriv (UpperHalfPlane.cuspFunction 1 f) q) q
      rw [eventually_nhdsWithin_iff]
      filter_upwards [Metric.ball_mem_nhds (0 : ℂ) zero_lt_one] with q hq hqne
      exact hnonzero q hqne (by simpa using hq)
    have htend : Tendsto (Function.Periodic.cuspFunction 1
        ((Derivative.normalizedDerivOfComplex f) ∘ UpperHalfPlane.ofComplex))
        (𝓝[≠] (0 : ℂ)) (𝓝 (0 : ℂ)) := Filter.Tendsto.congr' hloc.symm hlim
    rw [Function.Periodic.cuspFunction_zero_eq_limUnder_nhds_ne, htend.limUnder_eq]
  have hgoal : ∀ q : ℂ, ‖q‖ < 1 →
      UpperHalfPlane.cuspFunction 1 (Derivative.normalizedDerivOfComplex f) q =
        q * deriv (UpperHalfPlane.cuspFunction 1 f) q := by
    intro q hq
    rcases eq_or_ne q 0 with rfl | hqne
    · simpa using h0eq
    · exact hnonzero q hqne hq
  have hcusp : UpperHalfPlane.cuspFunction 1 (Derivative.normalizedDerivOfComplex f) =ᶠ[𝓝 0]
      fun q => q * deriv (UpperHalfPlane.cuspFunction 1 f) q := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) zero_lt_one] with q hq
    exact hgoal q (by simpa using hq)
  have hiter : iteratedDeriv n
        (UpperHalfPlane.cuspFunction 1 (Derivative.normalizedDerivOfComplex f)) 0
      = (n : ℂ) * iteratedDeriv n (UpperHalfPlane.cuspFunction 1 f) 0 := by
    have h1 := (Filter.EventuallyEq.iteratedDeriv hcusp n).eq_of_nhds
    rw [h1, iteratedDeriv_mul_deriv_self _ hC_analytic n]
  rw [UpperHalfPlane.qExpansion_coeff, UpperHalfPlane.qExpansion_coeff, hiter]
  ring

end Work.Modular
