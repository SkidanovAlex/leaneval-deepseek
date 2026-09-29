import Mathlib
import Submission.Work.CNum.Basic
import Submission.Work.CNum.C2_setup
import Submission.Work.CNum.C2_sqrt_Ra
import Submission.Work.CNum.C2_T_eq
import Submission.Work.CNum.C2_ratio_eq
import Submission.Work.CNum.C2_Psi_antitone
import Submission.Work.CNum.C2_Psi_mem

/-!
# `Work.CNum.C2_clockwise`

`Vof θ` is the normalised parametrisation of the circle `C₂`; on the arc
`θ ∈ (alpR, 2π - alpR)` it is a point of the unit circle travelled **clockwise**:
for `θ₁ < θ₂` on the arc the quotient `Vof θ₂ / Vof θ₁` has negative imaginary part.

The proof is completely explicit.  With `t = θ/2`, `s = sin t`, `σ = C2σ = sin(α/2)`
and `w = C2w θ = √(s² - σ²)`,

* `C2_Vof_explicit` : `Vof θ = -((C2u θ) + (C2v θ)·I)/C`, where
  `C2u θ = cos²t + s w`, `C2v θ = (s - w) cos t`, `C = C2C = cos(α/2)`;
* `C2_ratio_eq`     : `((C2u θ) + (C2v θ)·I)/C = exp(I · C2Psi(θ/2))`;
* `C2_Psi_antitone` : `C2Psi` is strictly antitone on `(α/2, π - α/2)`;
* `C2_Psi_mem`      : `C2Psi` maps `(α/2, π - α/2)` into `(-π/2, π/2)`.

Hence `Vof θ = -exp (I · C2Psi (θ/2))`, the quotient of two such values is
`exp (I · (Ψ₂ - Ψ₁))` with `Ψ₂ - Ψ₁ ∈ (-π, 0)`, whose imaginary part is `sin (Ψ₂ - Ψ₁) < 0`.
-/

namespace Work.CNum

open Complex

/-- `e^{ix} - 1 = 2i sin(x/2) e^{ix/2}`. -/
private lemma exp_I_sub_one (x : ℝ) : Complex.exp (Complex.I * (x : ℂ)) - 1 =
    2 * Complex.I * (Real.sin (x / 2) : ℂ) * Complex.exp (Complex.I * ((x / 2 : ℝ) : ℂ)) := by
  have hx : Complex.exp (Complex.I * (x : ℂ)) =
      (Real.cos x : ℂ) + (Real.sin x : ℂ) * Complex.I := by
    rw [mul_comm Complex.I (x : ℂ), Complex.exp_ofReal_mul_I]
  have hhalf : Complex.exp (Complex.I * ((x / 2 : ℝ) : ℂ)) =
      (Real.cos (x / 2) : ℂ) + (Real.sin (x / 2) : ℂ) * Complex.I := by
    rw [mul_comm Complex.I ((x / 2 : ℝ) : ℂ), Complex.exp_ofReal_mul_I]
  rw [hx, hhalf]
  have hc : Real.cos x = 2 * Real.cos (x / 2) ^ 2 - 1 := by
    have := Real.cos_two_mul (x / 2); rw [show 2 * (x / 2) = x by ring] at this; linarith
  have hs : Real.sin x = 2 * Real.sin (x / 2) * Real.cos (x / 2) := by
    have := Real.sin_two_mul (x / 2); rw [show 2 * (x / 2) = x by ring] at this; linarith
  rw [hc, hs]
  simp only [Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_ofNat,
    Complex.ofReal_one]
  have hcsC : ((Real.cos (x / 2)) ^ 2 : ℂ) + ((Real.sin (x / 2)) ^ 2 : ℂ) = 1 := by
    rw [← Complex.ofReal_pow, ← Complex.ofReal_pow, ← Complex.ofReal_add,
      Real.cos_sq_add_sin_sq, Complex.ofReal_one]
  ring_nf at hcsC ⊢
  rw [Complex.I_sq]
  linear_combination 2 * hcsC

/-- `c₂ = 3(1+c²)/(2d)`. -/
private lemma cenC2_eq_alt : cenC2 = 3 * (1 + cR ^ 2) / (2 * dR) := by
  simp only [cenC2, aR, bR, kR, dR, cR]; norm_num

/-- Explicit value of `Vof` on the `C₂` arc: `Vof θ = -((C2u θ) + (C2v θ)·I)/C2C`. -/
theorem C2_Vof_explicit {θ : ℝ} (h : θ ∈ Set.Ioo alpR (2 * Real.pi - alpR)) :
    Vof θ = -(((C2u θ : ℂ) + (C2v θ : ℂ) * Complex.I) / (C2C : ℂ)) := by
  set e : ℂ := Complex.exp (Complex.I * ((θ / 2 : ℝ) : ℂ)) with he
  have hexp2 : Complex.exp (Complex.I * (θ : ℂ)) = e ^ 2 := by
    have h2 : Complex.I * (θ : ℂ) = ((2 : ℕ) : ℂ) * (Complex.I * ((θ / 2 : ℝ) : ℂ)) := by
      push_cast; ring
    rw [h2, Complex.exp_nat_mul, ← he]
  have h2 : e ^ 2 - 1 = 2 * Complex.I * (Real.sin (θ / 2) : ℂ) * e := by
    rw [← hexp2, he]; exact exp_I_sub_one θ
  have hsqt : Complex.sqrt (Ra (e ^ 2)) = -(Complex.I * (C2T θ : ℂ)) * e := by
    have hsr := C2_sqrt_Ra h
    rw [show ((θ : ℂ)) / 2 = ((θ / 2 : ℝ) : ℂ) by push_cast; ring] at hsr
    rw [← hexp2, hsr, he]
  have hA : (3 / 4 : ℂ) * Wfun (e ^ 2) =
      -(Complex.I * (cenC2 : ℂ) * (((Real.sin (θ / 2) - C2w θ : ℝ)) : ℂ)) * e := by
    rw [Wfun, h2, hsqt, C2_T_eq h, cenC2_eq_alt]
    simp only [dR, cR]
    push_cast
    ring_nf
  have hlin : 1 + Complex.I * (((Real.sin (θ / 2) - C2w θ : ℝ)) : ℂ) * e =
      (C2u θ : ℂ) + (C2v θ : ℂ) * Complex.I := by
    rw [he]
    rw [show Complex.exp (Complex.I * ((θ / 2 : ℝ) : ℂ)) =
        (Real.cos (θ / 2) : ℂ) + (Real.sin (θ / 2) : ℂ) * Complex.I by
      rw [mul_comm, Complex.exp_ofReal_mul_I]]
    simp only [C2u, C2v, Complex.ofReal_sub, Complex.ofReal_add, Complex.ofReal_mul,
      Complex.ofReal_pow]
    ring_nf
    rw [Complex.I_sq]
    have hcs : ((Real.cos (θ / 2)) ^ 2 : ℂ) + ((Real.sin (θ / 2)) ^ 2 : ℂ) = 1 := by
      rw [← Complex.ofReal_pow, ← Complex.ofReal_pow, ← Complex.ofReal_add,
        Real.cos_sq_add_sin_sq, Complex.ofReal_one]
    ring_nf at hcs ⊢
    linear_combination (-1) * hcs
  have hfac : -(Complex.I * (cenC2 : ℂ) * (((Real.sin (θ / 2) - C2w θ : ℝ)) : ℂ)) * e
      - (cenC2 : ℂ) =
      -(cenC2 : ℂ) * (1 + Complex.I * (((Real.sin (θ / 2) - C2w θ : ℝ)) : ℂ) * e) := by ring
  have hsqrtC : (Real.sqrt rho2sq : ℂ) = (cenC2 : ℂ) * (C2C : ℂ) := by
    rw [sqrt_rho2sq, ← Complex.ofReal_mul]
    congr 1
    simp only [cenC2_eq, C2C]; norm_num
  have h1 : (cenC2 : ℂ) ≠ 0 := by
    rw [← Complex.ofReal_zero, Ne, Complex.ofReal_inj, cenC2_eq]; norm_num
  have h2C : (C2C : ℂ) ≠ 0 := by exact_mod_cast C2C_ne_zero
  rw [Vof, hexp2, hA, hfac, hlin, hsqrtC]
  field_simp

theorem C2_clockwise {θ₁ θ₂ : ℝ} (h1 : alpR < θ₁) (h2 : θ₂ < 2 * Real.pi - alpR) (hlt : θ₁ < θ₂) :
    (Vof θ₂ / Vof θ₁).im < 0 := by
  have hθ₁ : θ₁ ∈ Set.Ioo alpR (2 * Real.pi - alpR) := ⟨h1, lt_trans hlt h2⟩
  have hθ₂ : θ₂ ∈ Set.Ioo alpR (2 * Real.pi - alpR) := ⟨lt_trans h1 hlt, h2⟩
  have hV₁ : Vof θ₁ = -Complex.exp (Complex.I * (C2Psi (θ₁ / 2) : ℂ)) := by
    rw [C2_Vof_explicit hθ₁, C2_ratio_eq hθ₁]
  have hV₂ : Vof θ₂ = -Complex.exp (Complex.I * (C2Psi (θ₂ / 2) : ℂ)) := by
    rw [C2_Vof_explicit hθ₂, C2_ratio_eq hθ₂]
  rw [hV₁, hV₂]
  rw [neg_div_neg_eq, ← Complex.exp_sub]
  have hI : Complex.I * (C2Psi (θ₂ / 2) : ℂ) - Complex.I * (C2Psi (θ₁ / 2) : ℂ)
      = ((C2Psi (θ₂ / 2) - C2Psi (θ₁ / 2) : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [hI, Complex.exp_ofReal_mul_I_im]
  have hm₁ := C2_Psi_mem (half_mem hθ₁)
  have hm₂ := C2_Psi_mem (half_mem hθ₂)
  have hanti : C2Psi (θ₂ / 2) < C2Psi (θ₁ / 2) :=
    C2_Psi_antitone (half_mem hθ₁) (half_mem hθ₂) (by linarith)
  exact Real.sin_neg_of_neg_of_neg_pi_lt (by linarith [hanti])
    (by linarith [hm₂.1, hm₁.2])

end Work.CNum
