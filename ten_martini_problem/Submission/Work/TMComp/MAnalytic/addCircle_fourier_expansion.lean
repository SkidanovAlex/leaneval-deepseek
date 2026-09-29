import Mathlib

namespace Work.TMComp.MAnalytic

/-- The `n`-th Fourier exponential on the unit circle is the expected complex exponential:
`fourier (-n) x = exp (-(2 π i n x))`. -/
lemma fourier_neg_one_eq (n : ℤ) (x : ℝ) :
    @fourier 1 (-n) ((x : ℝ) : AddCircle (1:ℝ))
      = Complex.exp (-(2 * Real.pi * Complex.I * (n:ℂ) * (x:ℂ))) := by
  rw [fourier_coe_apply]
  congr 1
  push_cast
  ring

/-- `fourier n x = exp (2 π i n x)` on the unit circle. -/
lemma fourier_one_eq (n : ℤ) (x : ℝ) :
    @fourier 1 n ((x : ℝ) : AddCircle (1:ℝ))
      = Complex.exp (2 * Real.pi * Complex.I * (n:ℂ) * (x:ℂ)) := by
  rw [fourier_coe_apply]
  congr 1
  push_cast
  ring

/-- For a `1`-periodic function `g`, the lift `AddCircle.liftIco 1 0 g` takes the value `g t`
at the image of any real `t`. -/
lemma liftIco_one_eq {g : ℝ → ℂ} (hper : ∀ x, g (x + 1) = g x) (t : ℝ) :
    AddCircle.liftIco (1:ℝ) 0 g ((t : ℝ) : AddCircle (1:ℝ)) = g t := by
  have hp : Function.Periodic g (1:ℝ) := hper
  have h := (hp.int_mul ⌊t⌋) (Int.fract t)
  rw [mul_one] at h
  have hfr : g (Int.fract t) = g t := by rw [← h, Int.fract_add_floor]
  rw [← AddCircle.coe_fract t]
  rw [AddCircle.liftIco_coe_apply (x := Int.fract t)
    ⟨Int.fract_nonneg t, by simpa using Int.fract_lt_one t⟩]
  exact hfr

/-- The Fourier coefficients of `AddCircle.liftIco 1 0 g` are given by the interval integral
appearing in the statement. -/
lemma fourierCoeff_liftIco_one {g : ℝ → ℂ} (k : ℤ) :
    fourierCoeff (AddCircle.liftIco (1:ℝ) 0 g) k
      = ∫ s in (0:ℝ)..1, g s * Complex.exp (-(2 * Real.pi * Complex.I * (k:ℂ) * (s:ℂ))) := by
  rw [fourierCoeff_eq_intervalIntegral (a := 0)]
  simp only [one_div, inv_one, one_smul, zero_add]
  refine intervalIntegral.integral_congr_Ioo_of_le (by norm_num) (fun x hx => ?_)
  rw [AddCircle.liftIco_coe_apply (x := x) (show x ∈ Set.Ico (0:ℝ) (0+1) from
        ⟨hx.1.le, by simpa using hx.2⟩)]
  rw [fourier_neg_one_eq k x, smul_eq_mul, mul_comm]

theorem addCircle_fourier_expansion {g : ℝ → ℂ} (hg : Continuous g) (hper : ∀ x, g (x + 1) = g x)
    (hsum : Summable (fun k : ℤ =>
      ∫ s in (0 : ℝ)..1, g s * Complex.exp (-(2 * Real.pi * Complex.I * (k : ℂ) * (s : ℂ))))) :
    ∀ t : ℝ, g t = ∑' k : ℤ,
        (∫ s in (0 : ℝ)..1, g s * Complex.exp (-(2 * Real.pi * Complex.I * (k : ℂ) * (s : ℂ))))
          * Complex.exp (2 * Real.pi * Complex.I * (k : ℂ) * (t : ℂ)) := by
  have hcont : Continuous (AddCircle.liftIco (1:ℝ) 0 g) :=
    AddCircle.liftIco_zero_continuous (p := (1:ℝ)) (by simpa using (hper 0).symm) hg.continuousOn
  let F : C(AddCircle (1:ℝ), ℂ) := ⟨AddCircle.liftIco (1:ℝ) 0 g, hcont⟩
  have hF : ∀ t : ℝ, (F : AddCircle (1:ℝ) → ℂ) ((t : ℝ) : AddCircle (1:ℝ)) = g t := by
    intro t
    exact liftIco_one_eq hper t
  have hcoeff : ∀ k : ℤ, fourierCoeff (F : AddCircle (1:ℝ) → ℂ) k
      = ∫ s in (0:ℝ)..1, g s * Complex.exp (-(2 * Real.pi * Complex.I * (k:ℂ) * (s:ℂ))) := by
    intro k
    exact fourierCoeff_liftIco_one k
  have hsumF : Summable (fourierCoeff (F : AddCircle (1:ℝ) → ℂ)) := by
    rw [funext hcoeff]; exact hsum
  intro t
  have h := has_pointwise_sum_fourier_series_of_summable hsumF ((t:ℝ) : AddCircle (1:ℝ))
  have hsummand : (fun k : ℤ => fourierCoeff (F : AddCircle (1:ℝ) → ℂ) k
        • fourier k ((t:ℝ) : AddCircle (1:ℝ)))
      = (fun k : ℤ => (∫ s in (0:ℝ)..1, g s * Complex.exp (-(2 * Real.pi * Complex.I * (k:ℂ) * (s:ℂ))))
          * Complex.exp (2 * Real.pi * Complex.I * (k:ℂ) * (t:ℂ))) := by
    funext k
    rw [hcoeff k, smul_eq_mul, fourier_one_eq k t]
  rw [hsummand] at h
  rw [hF t] at h
  exact h.tsum_eq.symm

end Work.TMComp.MAnalytic
