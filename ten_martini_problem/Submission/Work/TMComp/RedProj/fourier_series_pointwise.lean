import Mathlib

/-!
# Pointwise convergence of the Fourier series of a periodic function

For a continuous `1`-periodic function `φ : ℝ → ℂ` whose Fourier coefficients
(`fourierCoeffOn (0 < 1) φ`, i.e. the coefficients computed by integrating over one period
`[0,1]`) form a summable family, the Fourier series converges pointwise at every `x : ℝ` to
`φ x`.

The work is a translation between the "function on `ℝ`" picture and Mathlib's Fourier theory on
the additive circle `AddCircle 1 = ℝ ⧸ ℤ`: a periodic function on `ℝ` descends to the circle,
where Mathlib's `has_pointwise_sum_fourier_series_of_summable` applies; the Fourier coefficients of
the descended function are exactly the `fourierCoeffOn` coefficients of the original function.
-/

namespace Work.TMComp.RedProj

/-- The Fourier coefficients `fourierCoeffOn (0 < 1) f` of a function on `ℝ` are the Fourier
coefficients of its `Ioc`-lift `AddCircle.liftIoc 1 0 f` to the circle.  (This is
`fourierCoeff_liftIoc_eq` specialised to `T = 1`, `a = 0`; the two sides differ only by the
trivial rewriting `0 + 1 = 1`.) -/
theorem fourierCoeff_liftIoc_one (f : ℝ → ℂ) (n : ℤ) :
    fourierCoeff (AddCircle.liftIoc (1 : ℝ) 0 f) n
      = fourierCoeffOn (show (0 : ℝ) < 1 by norm_num) f n := by
  simpa only [zero_add] using (fourierCoeff_liftIoc_eq (T := (1 : ℝ)) (a := (0 : ℝ)) f n)

/-- **Pointwise convergence of the Fourier series.**  If `φ : ℝ → ℂ` is continuous and
`1`-periodic and its Fourier coefficients are summable, then for every `x` the series
`∑_k ĉ_k e^{2πikx}` converges to `φ x`. -/
theorem fourier_series_pointwise (φ : ℝ → ℂ) (hφ : Continuous φ) (hper : ∀ x, φ (x + 1) = φ x)
    (hsum : Summable (fourierCoeffOn (show (0 : ℝ) < 1 by norm_num) φ)) (x : ℝ) :
    HasSum (fun k : ℤ => fourierCoeffOn (show (0 : ℝ) < 1 by norm_num) φ k *
      Complex.exp (2 * Real.pi * Complex.I * (k : ℂ) * (x : ℂ))) (φ x) := by
  -- `φ` descends to the additive circle `AddCircle 1`.
  have hper' : Function.Periodic φ 1 := hper
  -- the `Ioc`-lift and the descent through the quotient agree
  have hlift_eq : hper'.lift = AddCircle.liftIoc (1 : ℝ) 0 φ := by
    funext y
    obtain ⟨t, ht, hty⟩ := AddCircle.eq_coe_Ioc y
    rw [← hty, Function.Periodic.lift_coe, AddCircle.liftIoc_zero_coe_apply ht]
  have hlift_cont : Continuous (AddCircle.liftIoc (1 : ℝ) 0 φ) :=
    AddCircle.liftIoc_continuous (by simpa using (hper 0).symm) hφ.continuousOn
  let F : C(AddCircle (1 : ℝ), ℂ) := ⟨AddCircle.liftIoc (1 : ℝ) 0 φ, hlift_cont⟩
  -- its Fourier coefficients are those of `φ` on `[0,1]`
  have hcoeff : ∀ k, fourierCoeff (⇑F) k
      = fourierCoeffOn (show (0 : ℝ) < 1 by norm_num) φ k := by
    intro k
    show fourierCoeff (AddCircle.liftIoc (1 : ℝ) 0 φ) k = _
    exact fourierCoeff_liftIoc_one φ k
  have hsumF : Summable (fourierCoeff (⇑F)) :=
    hsum.congr (fun k => (hcoeff k).symm)
  -- Mathlib's pointwise convergence theorem on the circle
  have H := has_pointwise_sum_fourier_series_of_summable (f := F) hsumF (x : AddCircle (1 : ℝ))
  have hFval : F (x : AddCircle (1 : ℝ)) = φ x := by
    show AddCircle.liftIoc (1 : ℝ) 0 φ (x : AddCircle (1 : ℝ)) = φ x
    rw [← hlift_eq, Function.Periodic.lift_coe]
  -- identify the `k`-th summand
  have hfun : (fun k : ℤ => fourierCoeffOn (show (0 : ℝ) < 1 by norm_num) φ k *
      Complex.exp (2 * Real.pi * Complex.I * (k : ℂ) * (x : ℂ)))
      = (fun k : ℤ => fourierCoeff (⇑F) k • fourier k (x : AddCircle (1 : ℝ))) := by
    funext k
    rw [← hcoeff k, smul_eq_mul, fourier_coe_apply (T := (1 : ℝ)) (n := k) (x := x)]
    congr 1
    rw [Complex.ofReal_one, div_one]
  exact (by simpa only [← hfun, hFval] using H)

end Work.TMComp.RedProj
