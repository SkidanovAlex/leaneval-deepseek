import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF

/-- **The exponential/cpower identity for the pair correlation.**  For positive natural
numbers `A, B` and real `s`,
`exp (i s (log B − log A)) = B^{i s} * star (A^{i s})`,

where `^` is `Complex.cpow` and `star` is complex conjugation.  Indeed
`B^{is} = exp(is log B)` and `star (A^{is}) = exp(star(is log A)) = exp(-is log A)` since
`log A, log B` are real and `star (i s) = -i s`.  This converts the Fourier kernel
`e^{2πiξN log(B/A)}` into the multiplicative form `(∏v₂)^{is} conj((∏v₁)^{is})` that the
Dirichlet-character sum factorizes. -/
theorem n4_exp_log_cpow (A B : ℕ) (hA : 0 < A) (hB : 0 < B) (s : ℝ) :
    Complex.exp (Complex.I * (s : ℂ) * ((((Real.log B : ℝ)) : ℂ) - (((Real.log A : ℝ)) : ℂ)))
      = (B : ℂ) ^ (Complex.I * (s : ℂ)) * star (((A : ℂ) ^ (Complex.I * (s : ℂ)))) := by
  have hAne : (A : ℂ) ≠ 0 := by exact_mod_cast hA.ne'
  have hBne : (B : ℂ) ≠ 0 := by exact_mod_cast hB.ne'
  have hlogA : Complex.log (A : ℂ) = (((Real.log A : ℝ)) : ℂ) :=
    (Complex.ofReal_log (le_of_lt (by exact_mod_cast hA : (0:ℝ) < A))).symm
  have hlogB : Complex.log (B : ℂ) = (((Real.log B : ℝ)) : ℂ) :=
    (Complex.ofReal_log (le_of_lt (by exact_mod_cast hB : (0:ℝ) < B))).symm
  -- Rewrite each `cpow` as an exponential using `z ^ w = exp (log z * w)`.
  have hAexp : (A : ℂ) ^ (Complex.I * (s : ℂ))
      = Complex.exp ((((Real.log A : ℝ)) : ℂ) * (Complex.I * (s : ℂ))) := by
    rw [Complex.cpow_def_of_ne_zero hAne, hlogA]
  have hBexp : (B : ℂ) ^ (Complex.I * (s : ℂ))
      = Complex.exp ((((Real.log B : ℝ)) : ℂ) * (Complex.I * (s : ℂ))) := by
    rw [Complex.cpow_def_of_ne_zero hBne, hlogB]
  -- Conjugate the exponential of `A`: `star (exp z) = exp (star z)` and `star` is real
  -- on `log A`, `star i = -i`.
  have hstarexp : star (Complex.exp ((((Real.log A : ℝ)) : ℂ) * (Complex.I * (s : ℂ))))
      = Complex.exp ((((Real.log A : ℝ)) : ℂ) * (-(Complex.I * (s : ℂ)))) := by
    rw [Complex.star_def, ← Complex.exp_conj, ← Complex.star_def]
    congr 1
    rw [Complex.star_def, map_mul (starRingEnd ℂ), map_mul (starRingEnd ℂ),
        Complex.conj_ofReal, Complex.conj_ofReal, Complex.conj_I]
    ring
  rw [hAexp, hBexp, hstarexp, ← Complex.exp_add]
  congr 1
  ring

end Work.BMF
