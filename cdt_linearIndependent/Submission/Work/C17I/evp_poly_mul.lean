import Mathlib
import Submission.Work.CPull.defs
import Submission.Work.C17I.evp_poly
import Submission.Work.CPull.evp_aux

namespace Work.C17I

/-- The coefficient series (weighted by `z ^ n`) of a polynomial, viewed in `ℚ⟦X⟧`, is
absolutely summable: it vanishes off the finite support of the polynomial. -/
lemma summable_abs_coeff_poly_mul (p : Polynomial ℚ) (z : ℂ) :
    Summable (fun n : ℕ => ‖((PowerSeries.coeff n (p : PowerSeries ℚ) : ℚ) : ℂ) * z ^ n‖) := by
  refine summable_of_ne_finset_zero (s := p.support) (fun n hn => ?_)
  have h0 : p.coeff n = 0 := Polynomial.notMem_support_iff.mp hn
  simp [Polynomial.coeff_coe, h0]

theorem evp_poly_mul (p : Polynomial ℚ) (f : PowerSeries ℚ) (z : ℂ)
    (hf : Summable fun n : ℕ => ((PowerSeries.coeff n f : ℚ) : ℂ) * z ^ n) :
    Summable (fun n : ℕ => ((PowerSeries.coeff n ((p : PowerSeries ℚ) * f) : ℚ) : ℂ) * z ^ n) ∧
      p.eval₂ (algebraMap ℚ ℂ) z * (∑' n : ℕ, ((PowerSeries.coeff n f : ℚ) : ℂ) * z ^ n)
        = ∑' n : ℕ, ((PowerSeries.coeff n ((p : PowerSeries ℚ) * f) : ℚ) : ℂ) * z ^ n := by
  have hg := summable_abs_coeff_poly_mul p z
  have hh : Summable (fun n : ℕ => ‖((PowerSeries.coeff n f : ℚ) : ℂ) * z ^ n‖) := hf.norm
  obtain ⟨-, -, hsum, hval⟩ := Work.CPull.evpMul (p : PowerSeries ℚ) f z hg hh
  refine ⟨hsum, ?_⟩
  have e1 : (∑' n : ℕ, ((PowerSeries.coeff n f : ℚ) : ℂ) * z ^ n)
      = Work.CPull.evp f z := rfl
  have e2 : (∑' n : ℕ, ((PowerSeries.coeff n ((p : PowerSeries ℚ) * f) : ℚ) : ℂ) * z ^ n)
      = Work.CPull.evp ((p : PowerSeries ℚ) * f) z := rfl
  rw [e1, e2, hval, Work.C17I.evp_poly]

end Work.C17I
