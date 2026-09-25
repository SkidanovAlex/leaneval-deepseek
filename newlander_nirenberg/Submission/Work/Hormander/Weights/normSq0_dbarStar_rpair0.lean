/-
Copyright: none.  Part of the `Newlander-Nirenberg` formalisation project.

# `‖∂̄*_φ f‖²_{L²_φ}` as a double sum of the *real* pairings `rpair0`

`Work.Hormander.Weights.normSq0_dbarStar` writes `‖∂̄*_φ f‖²_{L²_φ}` as the real
part of the double sum of the Hermitian pairings `pairing0` of the coefficients
`g_j = ∂_j f_j - f_j ∂_j φ`.  Taking real parts one by one (the sum is finite,
and each pairing is the complexification of a real integral) turns that into the
double sum of the *real* pairings `rpair0`.  This is the form used in the
Kohn–Morrey identity, where everything is real.
-/
import Mathlib
import Submission.Work.Hormander.Weights.normSq0_dbarStar
import Submission.Work.Hormander.Weights.Rint

noncomputable section

open MeasureTheory Set
open scoped Topology ContDiff

namespace Work.Hormander.Weights

theorem normSq0_dbarStar_rpair0 {n : ℕ} (φ : Cn n → ℝ) (f : Form1 n) (hφ : ContDiff ℝ 1 φ)
    (hf : ∀ j, ContDiff ℝ 1 (f j)) (hfs : ∀ j, HasCompactSupport (f j)) :
    normSq0 φ (dbarStar φ f)
      = ∑ j, ∑ k, rpair0 φ
          (fun z => dCoord n j (f j) z - f j z * dPhi n j φ z)
          (fun z => dCoord n k (f k) z - f k z * dPhi n k φ z) := by
  rw [normSq0_dbarStar φ f hφ hf hfs]
  have hcont : ∀ j, Continuous (fun z => dCoord n j (f j) z - f j z * dPhi n j φ z) := by
    intro j
    exact (continuous_dCoord (hf j) j).sub
      (((hf j).continuous).mul (continuous_dCoord (contDiff_ofReal_comp hφ) j))
  have hcs : ∀ j, HasCompactSupport (fun z => dCoord n j (f j) z - f j z * dPhi n j φ z) := by
    intro j
    exact (hasCompactSupport_dCoord (hfs j) j).sub
      ((hfs j).mul_right (f' := fun z => dPhi n j φ z))
  have hint : ∀ j k, Integrable (fun z => (dCoord n j (f j) z - f j z * dPhi n j φ z)
      * star (dCoord n k (f k) z - f k z * dPhi n k φ z) * (wn n φ z : ℂ)) := by
    intro j k
    exact integrable_mul_wn hφ ((hcont j).mul (continuous_star.comp (hcont k)))
      ((hcs j).mul_right)
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  exact rpair0_eq_re_pairing (hint j k)

end Work.Hormander.Weights
