import Mathlib
import Submission.Work.ZeroDensity.Montgomery.zeroDetAltPerronAux
import Submission.Work.LinnikAreas.Density4.mellin_kernel_exp

namespace Work.ZeroDensity.Montgomery

open MeasureTheory

/-- For a natural base `n`, a positive real `Y` and a complex exponent `w`, the complex powers
combine as `n^{-w} · Y^{w} = (n/Y)^{-w}`.  (The hypotheses are exactly what is needed: for
`n = 0` both sides are handled by Mathlib's convention `0^z = 0` for `z ≠ 0`, `0^0 = 1`.) -/
lemma cpow_mul_cpow_of_pos {n : ℕ} {Y : ℝ} (hY : 0 < Y) (w : ℂ) :
    (n : ℂ) ^ (-w) * (Y : ℂ) ^ w = (((n : ℝ) / Y : ℝ) : ℂ) ^ (-w) := by
  rw [← Complex.ofReal_natCast n, Complex.ofReal_div]
  rw [Complex.div_cpow_ofReal_nonneg (Nat.cast_nonneg n) hY.le]
  rw [Complex.cpow_neg, Complex.cpow_neg, div_inv_eq_mul]

/-- Mellin inversion for the exponential kernel on a vertical line, in the multiplicative form
used for the Perron term: for `c > 0` and `y > 0`, `∫_ℝ y^{-(c+iu)} Γ(c+iu) du = 2π e^{-y}`. -/
lemma integral_gamma_line_exp (c : ℝ) (hc : 0 < c) (y : ℝ) (hy : 0 < y) :
    (∫ u : ℝ, (y : ℂ) ^ (-((c : ℂ) + (u : ℂ) * Complex.I)) *
        Complex.Gamma ((c : ℂ) + (u : ℂ) * Complex.I))
      = 2 * Real.pi * ((Real.exp (-y) : ℝ) : ℂ) := by
  have hk := Work.LinnikAreas.Density4.mellin_kernel_exp c hc y hy
  have h2 : (2 * (Real.pi : ℂ)) ≠ 0 := by
    apply mul_ne_zero two_ne_zero
    exact_mod_cast Real.pi_ne_zero
  calc (∫ u : ℝ, (y : ℂ) ^ (-((c : ℂ) + (u : ℂ) * Complex.I)) *
        Complex.Gamma ((c : ℂ) + (u : ℂ) * Complex.I))
      = (2 * (Real.pi : ℂ)) * ((1 / (2 * Real.pi)) *
          ∫ u : ℝ, (y : ℂ) ^ (-((c : ℂ) + (u : ℂ) * Complex.I)) *
            Complex.Gamma ((c : ℂ) + (u : ℂ) * Complex.I)) := by
        rw [← mul_assoc, mul_one_div_cancel h2, one_mul]
    _ = (2 * (Real.pi : ℂ)) * ((Real.exp (-y) : ℝ) : ℂ) := by rw [hk]
    _ = 2 * Real.pi * ((Real.exp (-y) : ℝ) : ℂ) := by ring

/-- The individual term of the Perron/Mellin inversion: integrating the `n`-th summand of the
Dirichlet series `Σ_n mCoef X n χ(n) n^{-s}` against the inverse Mellin kernel
`Γ(w) Y^{w}` along the line `w = c + iu` produces `2π · mCoef X n χ(n) n^{-ρ} e^{-n/Y}`. -/
theorem integral_perronTerm {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (ρ : ℂ)
    (X Y c : ℝ) (hc : 0 < c) (hY : 0 < Y) {n : ℕ} (hn : n ≠ 0) :
    (∫ u : ℝ, mCoef X n * χ (n : ZMod q) * (n : ℂ) ^ (-(ρ + ((c : ℂ) + (u : ℂ) * Complex.I)))
        * Complex.Gamma ((c : ℂ) + (u : ℂ) * Complex.I)
        * (Y : ℂ) ^ ((c : ℂ) + (u : ℂ) * Complex.I))
      = 2 * Real.pi * (mCoef X n * χ (n : ZMod q) * (n : ℂ) ^ (-ρ)
          * Complex.exp (-(n : ℂ) / (Y : ℂ))) := by
  classical
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hratio : 0 < (n : ℝ) / Y := div_pos hnpos hY
  have hne : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  -- Pointwise factorisation of the integrand: split `n^{-(ρ+w)}` and combine `n^{-w} Y^w`.
  have hpt : ∀ u : ℝ,
      mCoef X n * χ (n : ZMod q) * (n : ℂ) ^ (-(ρ + ((c : ℂ) + (u : ℂ) * Complex.I)))
          * Complex.Gamma ((c : ℂ) + (u : ℂ) * Complex.I)
          * (Y : ℂ) ^ ((c : ℂ) + (u : ℂ) * Complex.I)
        = (mCoef X n * χ (n : ZMod q) * (n : ℂ) ^ (-ρ))
          * (((((n : ℝ) / Y : ℝ) : ℂ) ^ (-((c : ℂ) + (u : ℂ) * Complex.I)))
              * Complex.Gamma ((c : ℂ) + (u : ℂ) * Complex.I)) := by
    intro u
    calc mCoef X n * χ (n : ZMod q) * (n : ℂ) ^ (-(ρ + ((c : ℂ) + (u : ℂ) * Complex.I)))
          * Complex.Gamma ((c : ℂ) + (u : ℂ) * Complex.I)
          * (Y : ℂ) ^ ((c : ℂ) + (u : ℂ) * Complex.I)
        = mCoef X n * χ (n : ZMod q) * (n : ℂ) ^ (-ρ) *
            ((n : ℂ) ^ (-((c : ℂ) + (u : ℂ) * Complex.I)) *
              (Y : ℂ) ^ ((c : ℂ) + (u : ℂ) * Complex.I)) *
            Complex.Gamma ((c : ℂ) + (u : ℂ) * Complex.I) := by
          rw [show -(ρ + ((c : ℂ) + (u : ℂ) * Complex.I))
                = -ρ + (-((c : ℂ) + (u : ℂ) * Complex.I)) by ring,
              Complex.cpow_add _ _ hne]
          ring
      _ = mCoef X n * χ (n : ZMod q) * (n : ℂ) ^ (-ρ) *
            ((((n : ℝ) / Y : ℝ) : ℂ) ^ (-((c : ℂ) + (u : ℂ) * Complex.I))) *
            Complex.Gamma ((c : ℂ) + (u : ℂ) * Complex.I) := by
          rw [cpow_mul_cpow_of_pos hY ((c : ℂ) + (u : ℂ) * Complex.I)]
      _ = (mCoef X n * χ (n : ZMod q) * (n : ℂ) ^ (-ρ))
          * (((((n : ℝ) / Y : ℝ) : ℂ) ^ (-((c : ℂ) + (u : ℂ) * Complex.I)))
              * Complex.Gamma ((c : ℂ) + (u : ℂ) * Complex.I)) := by ring
  -- Evaluation of the remaining Mellin integral.
  have hmain := integral_gamma_line_exp c hc ((n : ℝ) / Y) hratio
  have hexp : ((Real.exp (-((n : ℝ) / Y)) : ℝ) : ℂ) = Complex.exp (-(n : ℂ) / (Y : ℂ)) := by
    rw [Complex.ofReal_exp]
    congr 1
    push_cast
    ring
  calc (∫ u : ℝ, mCoef X n * χ (n : ZMod q) *
            (n : ℂ) ^ (-(ρ + ((c : ℂ) + (u : ℂ) * Complex.I)))
          * Complex.Gamma ((c : ℂ) + (u : ℂ) * Complex.I)
          * (Y : ℂ) ^ ((c : ℂ) + (u : ℂ) * Complex.I))
      = ∫ u : ℝ, (mCoef X n * χ (n : ZMod q) * (n : ℂ) ^ (-ρ)) *
            (((((n : ℝ) / Y : ℝ) : ℂ) ^ (-((c : ℂ) + (u : ℂ) * Complex.I)))
              * Complex.Gamma ((c : ℂ) + (u : ℂ) * Complex.I)) := by
          apply integral_congr_ae
          filter_upwards with u
          exact hpt u
    _ = (mCoef X n * χ (n : ZMod q) * (n : ℂ) ^ (-ρ)) *
          ∫ u : ℝ, ((((n : ℝ) / Y : ℝ) : ℂ) ^ (-((c : ℂ) + (u : ℂ) * Complex.I)))
              * Complex.Gamma ((c : ℂ) + (u : ℂ) * Complex.I) := by
          rw [integral_const_mul]
    _ = (mCoef X n * χ (n : ZMod q) * (n : ℂ) ^ (-ρ)) *
          (2 * Real.pi * ((Real.exp (-((n : ℝ) / Y)) : ℝ) : ℂ)) := by
          rw [hmain]
    _ = 2 * Real.pi * (mCoef X n * χ (n : ZMod q) * (n : ℂ) ^ (-ρ)
          * Complex.exp (-(n : ℂ) / (Y : ℂ))) := by
          rw [hexp]
          ring

end Work.ZeroDensity.Montgomery
