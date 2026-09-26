import Mathlib
import Submission.Work.CKFinal.LineDecay.Defs

namespace Work.CKFinal.LineDecay

open MeasureTheory

/-- The exponential factor `e^{iπr²(x+i)} = e^{-πr²}e^{iπr²x}` has modulus `e^{-πr²} ≤ 1`
(for `c ≥ 0`; here `c = π r²`). -/
lemma norm_exp_factor_le_one (c x : ℝ) (hc : 0 ≤ c) :
    ‖Complex.exp (Complex.I * (c : ℂ) * ((x : ℂ) + Complex.I))‖ ≤ 1 := by
  rw [Complex.norm_exp, Real.exp_le_one_iff]
  have h : (Complex.I * (c : ℂ) * ((x : ℂ) + Complex.I)).re = -c := by
    simp [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
  rw [h]; linarith

/-- The horizontal pieces `P₂` of the shifted representation are bounded by twice a bound for the
kernel on the segment `{Im z = 1, |Re z| ≤ 1}`: the two integrals run over intervals of length
`1` and the exponential factor `e^{iπr²(x+i)} = e^{-πr²}e^{iπr²x}` has modulus `e^{-πr²} ≤ 1`. -/
theorem P2_norm_segment (K : UpperHalfPlane → UpperHalfPlane → ℂ) (τ : UpperHalfPlane)
    (r M : ℝ) (hM : ∀ x : ℝ, |x| ≤ 1 → ‖Work.CKFinal.Kax K τ x 1‖ ≤ M) :
    ‖Work.CKFinal.P2 K r τ‖ ≤ 2 * M := by
  have hMnn : 0 ≤ M := le_trans (norm_nonneg _) (hM 0 (by norm_num))
  have hπ : (0:ℝ) ≤ Real.pi * r ^ 2 := by positivity
  have hexp : ∀ x : ℝ,
      ‖Complex.exp (Complex.I * ((Real.pi * r ^ 2 : ℝ) : ℂ) * ((x : ℂ) + Complex.I))‖ ≤ 1 :=
    fun x => norm_exp_factor_le_one (Real.pi * r ^ 2) x hπ
  have hpoint : ∀ a b : ℝ, |a| ≤ 1 →
      ‖Work.CKFinal.Kax K τ a 1
        * Complex.exp (Complex.I * ((Real.pi * r ^ 2 : ℝ) : ℂ) * ((b : ℂ) + Complex.I))‖ ≤ M := by
    intro a b ha
    rw [norm_mul]
    exact le_trans (mul_le_mul (hM a ha) (hexp b) (norm_nonneg _) hMnn) (le_of_eq (mul_one M))
  have hA : ‖∫ x in (0:ℝ)..1, Work.CKFinal.Kax K τ (x - 1) 1
      * Complex.exp (Complex.I * ((Real.pi * r ^ 2 : ℝ) : ℂ) * ((x : ℂ) + Complex.I))‖ ≤ M := by
    refine le_trans (intervalIntegral.norm_integral_le_of_norm_le_const (C := M)
      (a := (0:ℝ)) (b := 1) (f := fun x : ℝ => Work.CKFinal.Kax K τ (x - 1) 1
        * Complex.exp (Complex.I * ((Real.pi * r ^ 2 : ℝ) : ℂ) * ((x : ℂ) + Complex.I))) ?_)
      (le_of_eq (by norm_num))
    intro x hx
    rw [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hx
    rw [Set.mem_Ioc] at hx
    obtain ⟨hx1, hx2⟩ := hx
    exact hpoint (x - 1) x (by rw [abs_le]; constructor <;> linarith)
  have hB : ‖∫ x in (-1:ℝ)..0, Work.CKFinal.Kax K τ (x + 1) 1
      * Complex.exp (Complex.I * ((Real.pi * r ^ 2 : ℝ) : ℂ) * ((x : ℂ) + Complex.I))‖ ≤ M := by
    refine le_trans (intervalIntegral.norm_integral_le_of_norm_le_const (C := M)
      (a := (-1:ℝ)) (b := 0) (f := fun x : ℝ => Work.CKFinal.Kax K τ (x + 1) 1
        * Complex.exp (Complex.I * ((Real.pi * r ^ 2 : ℝ) : ℂ) * ((x : ℂ) + Complex.I))) ?_)
      (le_of_eq (by norm_num))
    intro x hx
    rw [Set.uIoc_of_le (by norm_num : (-1:ℝ) ≤ 0)] at hx
    rw [Set.mem_Ioc] at hx
    obtain ⟨hx1, hx2⟩ := hx
    exact hpoint (x + 1) x (by rw [abs_le]; constructor <;> linarith)
  have hsplit : Work.CKFinal.P2 K r τ
      = -Complex.I * (∫ x in (0:ℝ)..1, Work.CKFinal.Kax K τ (x - 1) 1
          * Complex.exp (Complex.I * ((Real.pi * r ^ 2 : ℝ) : ℂ) * ((x : ℂ) + Complex.I)))
        + Complex.I * (∫ x in (-1:ℝ)..0, Work.CKFinal.Kax K τ (x + 1) 1
          * Complex.exp (Complex.I * ((Real.pi * r ^ 2 : ℝ) : ℂ) * ((x : ℂ) + Complex.I))) := by
    rw [Work.CKFinal.P2, Work.CKFinal.hsplit]
    simp only [Complex.ofReal_one, one_mul]
  rw [hsplit]
  have h1 : ‖-Complex.I * (∫ x in (0:ℝ)..1, Work.CKFinal.Kax K τ (x - 1) 1
      * Complex.exp (Complex.I * ((Real.pi * r ^ 2 : ℝ) : ℂ) * ((x : ℂ) + Complex.I)))‖
      = ‖∫ x in (0:ℝ)..1, Work.CKFinal.Kax K τ (x - 1) 1
      * Complex.exp (Complex.I * ((Real.pi * r ^ 2 : ℝ) : ℂ) * ((x : ℂ) + Complex.I))‖ := by
    rw [norm_mul, norm_neg, Complex.norm_I, one_mul]
  have h2 : ‖Complex.I * (∫ x in (-1:ℝ)..0, Work.CKFinal.Kax K τ (x + 1) 1
      * Complex.exp (Complex.I * ((Real.pi * r ^ 2 : ℝ) : ℂ) * ((x : ℂ) + Complex.I)))‖
      = ‖∫ x in (-1:ℝ)..0, Work.CKFinal.Kax K τ (x + 1) 1
      * Complex.exp (Complex.I * ((Real.pi * r ^ 2 : ℝ) : ℂ) * ((x : ℂ) + Complex.I))‖ := by
    rw [norm_mul, Complex.norm_I, one_mul]
  calc ‖-Complex.I * (∫ x in (0:ℝ)..1, Work.CKFinal.Kax K τ (x - 1) 1
          * Complex.exp (Complex.I * ((Real.pi * r ^ 2 : ℝ) : ℂ) * ((x : ℂ) + Complex.I)))
        + Complex.I * (∫ x in (-1:ℝ)..0, Work.CKFinal.Kax K τ (x + 1) 1
          * Complex.exp (Complex.I * ((Real.pi * r ^ 2 : ℝ) : ℂ) * ((x : ℂ) + Complex.I)))‖
      ≤ ‖-Complex.I * (∫ x in (0:ℝ)..1, Work.CKFinal.Kax K τ (x - 1) 1
          * Complex.exp (Complex.I * ((Real.pi * r ^ 2 : ℝ) : ℂ) * ((x : ℂ) + Complex.I)))‖
        + ‖Complex.I * (∫ x in (-1:ℝ)..0, Work.CKFinal.Kax K τ (x + 1) 1
          * Complex.exp (Complex.I * ((Real.pi * r ^ 2 : ℝ) : ℂ) * ((x : ℂ) + Complex.I)))‖ :=
        norm_add_le _ _
    _ ≤ M + M := by rw [h1, h2]; exact add_le_add hA hB
    _ = 2 * M := by ring

end Work.CKFinal.LineDecay
