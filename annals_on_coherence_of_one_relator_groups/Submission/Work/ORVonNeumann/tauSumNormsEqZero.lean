import Mathlib
import Submission.Work.ORVonNeumann.VonNeumannAlgebra

namespace Work.ORVonNeumann

/-- A sum of "squares" `∑ j, b j * star (b j)` in `N(G)` vanishes only if every term
does: the trace is faithful and positive on self-adjoint squares. -/
theorem tauSumNormsEqZero {G : Type*} [Group G] (D : Work.ORVonNeumann.GroupVonNeumannAlgebra G)
    {n : ℕ} (b : Fin n → D.N) (h : ∑ j, b j * star (b j) = 0) : ∀ j, b j = 0 := by
  -- Apply the trace to the vanishing sum.
  have hsum : ∑ j, D.τ (b j * star (b j)) = 0 := by
    rw [← map_sum, h, map_zero]
  -- The real parts add up to zero ...
  have hre : ∑ j, (D.τ (b j * star (b j))).re = 0 := by
    have := congrArg Complex.re hsum
    simpa [Complex.re_sum] using this
  -- ... and each real part is non-negative, so each vanishes.
  have hterm : ∀ j, (D.τ (b j * star (b j))).re = 0 := by
    intro j
    refine (Finset.sum_eq_zero_iff_of_nonneg (s := Finset.univ)
      (f := fun j => (D.τ (b j * star (b j))).re) ?_).mp hre j (Finset.mem_univ j)
    intro i _
    have := D.tau_star_mul_self_re_nonneg (star (b i))
    simpa using this
  -- The imaginary parts vanish for self-adjoint arguments.
  have him : ∀ j, (D.τ (b j * star (b j))).im = 0 := by
    intro j
    have := D.tau_star_mul_self_im (star (b j))
    simpa using this
  -- Hence the trace of each term is zero, and faithfulness finishes.
  intro j
  have hzero : D.τ (b j * star (b j)) = 0 := Complex.ext (hterm j) (him j)
  have hb : star (b j) = 0 := D.τ_faithful (star (b j)) (by simpa using hzero)
  simpa using hb

end Work.ORVonNeumann
