import Mathlib
import Submission.Work.GM.Trace.Defs

namespace Work.GM.Trace

open Complex Finset Matrix
open scoped BigOperators
open Submission.GM Submission.LargeValues

/-- For any matrix `M` with rows indexed by `W ⊆ ℝ` and columns by `Fin (N+1)`,
`tr (M M*) = ∑_{t∈W} ∑_j ‖M_{t,j}‖²`. -/
lemma trace_mul_conjTranspose_aux (N : ℕ) (W : Finset ℝ) (M : Matrix W (Fin (N+1)) ℂ) :
    Matrix.trace (M * M.conjTranspose)
      = ∑ t : W, ∑ j : Fin (N+1), ((‖M t j‖^2 : ℝ) : ℂ) := by
  rw [Matrix.trace]
  simp [Matrix.diag_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.mul_conj']

/-- The modulus of the `(t, j)` entry of `M_W`: the phase `(N+j)^{it}` has modulus one
(and when `N + j = 0` the weight vanishes anyway). -/
lemma norm_MWmat_entry (N : ℕ) (W : Finset ℝ) (t : W) (j : Fin (N+1)) :
    ‖MWmat N W t j‖ = bumpW (((N + (j : ℕ) : ℕ) : ℝ) / (N : ℝ)) := by
  rw [MWmat]
  simp only [Nat.cast_add]
  rw [Complex.norm_mul, norm_real, Real.norm_eq_abs, abs_of_nonneg (bumpW_nonneg _)]
  by_cases hx : ((N:ℝ) + (j:ℝ)) = 0
  · have hu : (((N:ℝ) + (j:ℝ)) / (N:ℝ)) = 0 := by rw [hx, zero_div]
    rw [hu, bumpW_eq_zero_of_notMem (by norm_num [Set.mem_Icc])]
    simp
  · have hpos : 0 < ((N:ℝ)+(j:ℝ)) := by
      have h0 : (0:ℝ) ≤ (N:ℝ) + (j:ℝ) := by positivity
      exact lt_of_le_of_ne' h0 hx
    rw [show ((↑N : ℂ) + ↑↑j) = (((↑N : ℝ) + ↑↑j : ℝ) : ℂ) from by push_cast; ring]
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hpos]
    have hre : (I * ((t:ℝ):ℂ)).re = 0 := by simp
    rw [hre, Real.rpow_zero, mul_one]

-- GM 4.4, exact form: `tr(M_W M_W*) = |W| · Σ_{n ∈ [N,2N]} h_0(n/N)`, where `h_0 = w²`.
-- `(M_W M_W*)_tt = Σ_j |w((N+j)/N) (N+j)^{it}|² = Σ_j w((N+j)/N)²` (the phase has modulus one for
-- `N+j ≥ 1`; for `N = 0` the weight vanishes), and
-- `Σ_{n∈Icc N (2N)} hfun 0 (n/N) = Σ_{j : Fin (N+1)} w((N+j)/N)²` by
-- `Submission.LargeValues.sum_Icc_eq_sum_fin` together with `Work.GM.Trace.hfun_zero`.
theorem trace_two_identity (N : ℕ) (W : Finset ℝ) :
    Matrix.trace (Submission.LargeValues.MWmat N W *
        (Submission.LargeValues.MWmat N W).conjTranspose)
      = (W.card : ℂ) * ∑ n ∈ Finset.Icc N (2 * N),
          Submission.GM.hfun 0 ((n : ℝ) / (N : ℝ)) := by
  have hterm : ∀ (t : W) (j : Fin (N+1)),
      ((‖MWmat N W t j‖^2 : ℝ) : ℂ) = hfun 0 (((N + (j:ℕ) : ℕ) : ℝ)/(N:ℝ)) := by
    intro t j
    rw [norm_MWmat_entry, hfun_zero]
  rw [trace_mul_conjTranspose_aux]
  rw [Submission.LargeValues.sum_Icc_eq_sum_fin N
      (fun n => Submission.GM.hfun 0 ((n : ℝ)/(N:ℝ)))]
  rw [Finset.sum_congr rfl (fun t _ => Finset.sum_congr rfl (fun j _ => hterm t j))]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul]

end Work.GM.Trace
