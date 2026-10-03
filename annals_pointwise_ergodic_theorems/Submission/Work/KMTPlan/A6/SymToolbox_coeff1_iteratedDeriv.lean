import Mathlib
import Submission.Work.KMTPlan.A6.SymToolbox

/-!
# Fourier coefficients of the iterated derivatives of a periodic function

For a function `f : ℝ → ℂ` of period `1` which is `C^m`, the `j`-th Fourier coefficient
`coeff1 f j = ∫₀¹ f(x) e(-j x) dx` of its `m`-th derivative is `(2πij)^m` times that of `f`:

  `coeff1 (iteratedDeriv m f) j = (2πij)^m * coeff1 f j`.

The proof is the classical integration by parts against the character `x ↦ e(-j x)`.  For a
`1`-periodic differentiable `g` whose derivative is continuous the boundary terms
`g(1) e(-j) - g(0) e(0)` vanish (periodicity of `g`, and `e(-j) = e(0) = 1`), whence

  `coeff1 (deriv g) j = (2πij) * coeff1 g j`   (`coeff1_deriv` below),

and the general statement follows by induction on `m`: the intermediate derivatives
`iteratedDeriv n f` (`n ≤ m`) stay `1`-periodic (`iteratedDeriv_periodic_one`) and are
differentiable with continuous derivative because `f` is `C^m`.
-/

namespace Work.KMTPlan.A6

/-- The iterated derivatives of a function of period `1` again have period `1`.  No smoothness
hypothesis is needed (`deriv` is total). -/
theorem iteratedDeriv_periodic_one (f : ℝ → ℂ) (hper : ∀ x : ℝ, f (x + 1) = f x) (k : ℕ) :
    ∀ x : ℝ, iteratedDeriv k f (x + 1) = iteratedDeriv k f x := by
  have h1 : (fun z : ℝ => f (z + 1)) = f := funext hper
  intro x
  have h2 := congr_fun (iteratedDeriv_comp_add_const (𝕜 := ℝ) (F := ℂ) k f 1) x
  rw [h1] at h2
  exact h2.symm

/-- Integration by parts for the Fourier coefficients of a periodic function: for `g` of period
`1`, differentiable, with continuous derivative,

  `coeff1 (deriv g) j = (2πij) * coeff1 g j`.

(The boundary terms `g 1 * e(-j) - g 0 * e(0)` vanish: `g 1 = g 0` and `e(-j) = 1 = e(0)`.) -/
theorem coeff1_deriv (g : ℝ → ℂ) (j : ℤ) (hper : ∀ x : ℝ, g (x + 1) = g x)
    (hd : Differentiable ℝ g) (hcont : Continuous (deriv g)) :
    coeff1 (deriv g) j = (2 * (Real.pi : ℂ) * Complex.I * (j : ℂ)) * coeff1 g j := by
  -- the derivative of the character `y ↦ e(-j y)`
  have hVderiv : ∀ x : ℝ, HasDerivAt (fun y : ℝ => eeC (-(j : ℝ) * y))
      (-(2 * (Real.pi : ℂ) * Complex.I * (j : ℂ)) * eeC (-(j : ℝ) * x)) x := by
    intro x
    have hfun : (fun y : ℝ => eeC (-(j : ℝ) * y))
        = fun y : ℝ => Complex.exp ((-(2 * (Real.pi : ℂ) * Complex.I * (j : ℂ))) * (y : ℂ)) := by
      funext y
      simp only [eeC]
      congr 1
      push_cast
      ring
    have hval : eeC (-(j : ℝ) * x)
        = Complex.exp ((-(2 * (Real.pi : ℂ) * Complex.I * (j : ℂ))) * (x : ℂ)) := congr_fun hfun x
    rw [hfun, hval]
    have hlin : HasDerivAt (fun y : ℝ => (-(2 * (Real.pi : ℂ) * Complex.I * (j : ℂ))) * (y : ℂ))
        (-(2 * (Real.pi : ℂ) * Complex.I * (j : ℂ))) x := by
      simpa using ((hasDerivAt_id x).ofReal_comp).const_mul (-(2 * (Real.pi : ℂ) * Complex.I * (j : ℂ)))
    have hcomp := (Complex.hasDerivAt_exp ((-(2 * (Real.pi : ℂ) * Complex.I * (j : ℂ))) * (x : ℂ))).comp x hlin
    have hthis : HasDerivAt (fun y : ℝ => Complex.exp ((-(2 * (Real.pi : ℂ) * Complex.I * (j : ℂ))) * (y : ℂ)))
        (Complex.exp ((-(2 * (Real.pi : ℂ) * Complex.I * (j : ℂ))) * (x : ℂ)) * (-(2 * (Real.pi : ℂ) * Complex.I * (j : ℂ)))) x := hcomp
    have heq : Complex.exp ((-(2 * (Real.pi : ℂ) * Complex.I * (j : ℂ))) * (x : ℂ)) * (-(2 * (Real.pi : ℂ) * Complex.I * (j : ℂ)))
        = (-(2 * (Real.pi : ℂ) * Complex.I * (j : ℂ))) * Complex.exp ((-(2 * (Real.pi : ℂ) * Complex.I * (j : ℂ))) * (x : ℂ)) := by ring
    rw [heq] at hthis
    exact hthis
  have hV1 : eeC (-(j : ℝ) * 1) = 1 := by
    rw [mul_one, eeC]
    have : (-(j:ℂ)) * (2 * (Real.pi:ℂ) * Complex.I) = ((2:ℂ) * (Real.pi:ℂ) * Complex.I * (-(j:ℝ) : ℝ))
    · push_cast; ring
    rw [← this]
    simpa using Complex.exp_int_mul_two_pi_mul_I (-j)
  have hV0 : eeC (-(j : ℝ) * 0) = 1 := by
    simp [eeC]
  have hcontV : Continuous (fun x : ℝ => eeC (-(j : ℝ) * x)) := by
    unfold eeC
    fun_prop
  have hper01 : g 1 = g 0 := by simpa using hper 0
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul
      (a := (0:ℝ)) (b := 1)
      (u := g) (v := fun y : ℝ => eeC (-(j : ℝ) * y))
      (u' := deriv g) (v' := fun x : ℝ => -(2 * (Real.pi : ℂ) * Complex.I * (j : ℂ)) * eeC (-(j : ℝ) * x))
      (fun x _ => hd.differentiableAt.hasDerivAt) (fun x _ => hVderiv x)
      (hcont.intervalIntegrable 0 1) ((continuous_const.mul hcontV).intervalIntegrable 0 1)
  rw [hV1, hV0, mul_one, mul_one, hper01, sub_self, zero_sub] at hibp
  have hleft : (∫ x in (0:ℝ)..1, g x * (-(2 * (Real.pi : ℂ) * Complex.I * (j : ℂ)) * eeC (-(j : ℝ) * x)))
      = (-(2 * (Real.pi : ℂ) * Complex.I * (j : ℂ))) * (∫ x in (0:ℝ)..1, g x * eeC (-(j : ℝ) * x)) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x _
    ring
  rw [hleft] at hibp
  have h2 : (2 * (Real.pi : ℂ) * Complex.I * (j : ℂ)) * (∫ x in (0:ℝ)..1, g x * eeC (-(j : ℝ) * x))
      = ∫ x in (0:ℝ)..1, deriv g x * eeC (-(j : ℝ) * x) := by
    have := hibp
    rw [neg_mul] at this
    exact neg_inj.mp this
  simpa only [coeff1] using h2.symm

theorem SymToolbox_coeff1_iteratedDeriv (f : ℝ → ℂ) (m : ℕ) (j : ℤ)
    (hper : ∀ x : ℝ, f (x + 1) = f x) (hsm : ContDiff ℝ m f) :
    Work.KMTPlan.A6.coeff1 (iteratedDeriv m f) j
      = (2 * (Real.pi : ℂ) * Complex.I * (j : ℂ)) ^ m * Work.KMTPlan.A6.coeff1 f j := by
  have hcd := contDiff_nat_iff_iteratedDeriv.mp hsm
  have main : ∀ n ≤ m, coeff1 (iteratedDeriv n f) j
      = (2 * (Real.pi : ℂ) * Complex.I * (j : ℂ)) ^ n * coeff1 f j := by
    intro n
    induction n with
    | zero => intro _; simp
    | succ n ih =>
      intro hn
      have hn' : n ≤ m := le_trans (Nat.le_succ n) hn
      have hdiff : Differentiable ℝ (iteratedDeriv n f) := hcd.2 n (Nat.lt_of_succ_le hn)
      have hcont : Continuous (deriv (iteratedDeriv n f)) := by
        rw [← iteratedDeriv_succ]
        exact hcd.1 (n+1) hn
      have hperg : ∀ x : ℝ, iteratedDeriv n f (x + 1) = iteratedDeriv n f x :=
        iteratedDeriv_periodic_one f hper n
      rw [iteratedDeriv_succ]
      rw [coeff1_deriv (iteratedDeriv n f) j hperg hdiff hcont]
      rw [ih hn']
      ring
  exact main m le_rfl

end Work.KMTPlan.A6
