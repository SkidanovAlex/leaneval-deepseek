import Mathlib
import Submission.Work.TMC16Core.Defs

/-!
# `pd_upper`: the locally uniform upper bound for the continuants (AJ (9.7))

`pd α lam θ E (n+1)` is the `(0,0)` entry of the `n`-fold transfer product
`iterC α lam E n θ` (both satisfying the second-order recursion
`u_{k+1} = (E - v_k) u_k - u_{k-1}` with `u_0 = 0`, `u_1 = 1`), hence it is bounded by
the Frobenius norm of that product.  Part (2) of `P_LEBasics` says exactly that this
Frobenius norm grows at most like `exp (n (lyap α lam E + ε))` for `n` large, uniformly
in the phase `x`, and locally uniformly in the energy.  Taking the energy to be `E`
itself (`‖E - E‖ = 0 < r`) and exponentiating the logarithm gives the claim.
-/

namespace Work.TMC16Core.Basic

open Work.TMC16Core

theorem frob_nonneg (A : Matrix (Fin 2) (Fin 2) ℂ) : 0 ≤ frob A := by
  rw [frob]; positivity

/-- Every entry of a `2 × 2` complex matrix has modulus at most its Frobenius norm. -/
theorem norm_entry_le_frob (A : Matrix (Fin 2) (Fin 2) ℂ) (i j : Fin 2) :
    ‖A i j‖ ≤ frob A := by
  have hsq : ‖A i j‖ ^ 2 ≤ ‖A 0 0‖ ^ 2 + ‖A 0 1‖ ^ 2 + ‖A 1 0‖ ^ 2 + ‖A 1 1‖ ^ 2 := by
    fin_cases i <;> fin_cases j <;> simp only [Fin.zero_eta, Fin.mk_one] <;>
      nlinarith [norm_nonneg (A 0 0), norm_nonneg (A 0 1), norm_nonneg (A 1 0),
        norm_nonneg (A 1 1)]
  calc ‖A i j‖ = Real.sqrt (‖A i j‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt (‖A 0 0‖ ^ 2 + ‖A 0 1‖ ^ 2 + ‖A 1 0‖ ^ 2 + ‖A 1 1‖ ^ 2) :=
        Real.sqrt_le_sqrt hsq
    _ = frob A := by rw [frob]

/-- The `(0,0)` and `(1,0)` entries of the transfer product `iterC n x` are the
continuants `pd x (n+1)` and `pd x n`. -/
theorem iterC_entries (α lam : ℝ) (E : ℂ) (n : ℕ) (x : ℝ) :
    (iterC α lam E n x) 0 0 = pd α lam x E (n + 1) ∧
      (iterC α lam E n x) 1 0 = pd α lam x E n := by
  induction n with
  | zero =>
    constructor <;> simp [iterC, pd]
  | succ n ih =>
    obtain ⟨h0, h1⟩ := ih
    have hA : (tmC lam E (x + (n : ℝ) * α)) 0 0
        = E - ((amoPot α lam x (n : ℤ) : ℝ) : ℂ) := by
      simp [tmC, amoPot]
    have hB : (tmC lam E (x + (n : ℝ) * α)) 0 1 = -1 := by
      simp [tmC]
    constructor
    · rw [iterC]
      rw [Matrix.mul_apply, Fin.sum_univ_two]
      rw [h0, h1, hA, hB, pd]
      ring
    · rw [iterC]
      rw [Matrix.mul_apply, Fin.sum_univ_two]
      rw [h0, h1]
      simp only [tmC, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.empty_val']
      ring

/-- `pd α lam x E (n+1)` is the `(0,0)` entry of `iterC α lam E n x`. -/
theorem pd_eq_iterC_zero_zero (α lam : ℝ) (E : ℂ) (n : ℕ) (x : ℝ) :
    pd α lam x E (n + 1) = (iterC α lam E n x) 0 0 :=
  (iterC_entries α lam E n x).1.symm

/-- Norm form of the entry bound: the continuant is dominated by the Frobenius norm of
the transfer product. -/
theorem pd_le_frob' (α lam : ℝ) (E : ℂ) (n : ℕ) (x : ℝ) :
    ‖pd α lam x E (n + 1)‖ ≤ frob (iterC α lam E n x) := by
  rw [pd_eq_iterC_zero_zero]
  exact norm_entry_le_frob _ 0 0

theorem pd_upper (h4 : Work.TMC16Core.P_LEBasics) {α lam : ℝ} (hα : Irrational α) (E : ℂ)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∀ θ : ℝ,
      ‖Work.TMC16Core.pd α lam θ E (n + 1)‖ ≤
        Real.exp ((n : ℝ) * (Work.TMC16Core.lyap α lam E + ε)) := by
  obtain ⟨-, hupper⟩ := h4
  obtain ⟨r, hr, n₀, hn⟩ := hupper α lam hα E ε hε
  refine ⟨n₀, fun n hn' θ => ?_⟩
  have hlog : Real.log (frob (iterC α lam E n θ)) ≤ (n : ℝ) * (lyap α lam E + ε) :=
    hn n hn' E (by simpa using hr) θ
  have hfrob : frob (iterC α lam E n θ) ≤ Real.exp ((n : ℝ) * (lyap α lam E + ε)) := by
    by_cases hpos : 0 < frob (iterC α lam E n θ)
    · exact (Real.log_le_iff_le_exp hpos).mp hlog
    · have hzero : frob (iterC α lam E n θ) = 0 :=
        le_antisymm (not_lt.mp hpos) (frob_nonneg _)
      rw [hzero]
      exact (Real.exp_pos _).le
  calc ‖pd α lam θ E (n + 1)‖ ≤ frob (iterC α lam E n θ) := pd_le_frob' α lam E n θ
    _ ≤ Real.exp ((n : ℝ) * (lyap α lam E + ε)) := hfrob

end Work.TMC16Core.Basic
