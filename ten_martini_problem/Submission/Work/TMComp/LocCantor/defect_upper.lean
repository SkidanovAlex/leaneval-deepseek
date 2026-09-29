import Mathlib
import Submission.Work.TMC7Core.Cocycle
import Submission.Work.TMC7Core.Rat
import Submission.Work.TMC7Core.Scale.frob_map_ofReal_sq
import Submission.Work.TMComp.LocCantor.trace_pow_abs_le_rhoSL
import Submission.Work.TMComp.LocCantor.frob_sq_sq_of_det_one

/-!
# The "defect" upper bound for powers of a real `SL₂` matrix

For a real `2 × 2` matrix `A` with `det A = 1` and every `m ≥ 1`,

`log ‖(A^m)²‖_F − log ‖A^m‖_F − m · log (rhoSL (tr A)) ≤ log 2`,

where `‖·‖_F` is the Frobenius norm (`Work.TMC7Core.frob`) and `rhoSL τ` is the spectral
radius of an `SL(2,ℝ)`-matrix with trace `τ` (`Work.TMC7Core.rhoSL`).

This is the classical doubling estimate.  Write `B = A^m` (still unimodular).  By
Cayley–Hamilton `B² = (tr B)·B − 1`, so with `F = ‖B‖_F² = b₀₀²+b₀₁²+b₁₀²+b₁₁²` and
`t = tr B`,

`‖B²‖_F² = (t·b₀₀−1)² + (t·b₀₁)² + (t·b₁₀)² + (t·b₁₁−1)² = 2 + (F−2)·t²`
(`frob_sq_sq_of_det_one`), while `F ≥ 2`
(`two_le_sum_sq_of_det_one`, from `b₀₀²+b₁₁² ≥ 2b₀₀b₁₁`, `b₀₁²+b₁₀² ≥ −2b₀₁b₁₀` and
`det B = 1`).

The eigenvalues of `B` are the `m`-th powers of those of `A`, and by
`max_norm_roots_eq_rhoSL` the two eigenvalues `λ, μ` of `A` satisfy
`max ‖λ‖ ‖μ‖ = rhoSL (tr A)`; hence `|tr B| ≤ 2·rhoSL(tr A)^m`
(the delegated lemma `trace_pow_abs_le_rhoSL`).
Therefore

`‖A^{2m}‖_F² = ‖B²‖_F² ≤ 2 + (F−2)·4·rhoSL(tr A)^{2m} ≤ (2·rhoSL(tr A)^m·‖A^m‖_F)²`,

because `F ≥ 2` and `(2·rhoSL(tr A)^m)² ≥ 1`.  Both Frobenius norms are positive, so
taking square roots gives `‖A^{2m}‖_F ≤ 2·rhoSL(tr A)^m·‖A^m‖_F`, and taking logarithms
(`Real.log_le_log`, `Real.log_mul`, `Real.log_pow`) yields the claim.
-/

open Work.TMC7Core

namespace Work.TMComp.LocCantor

/-! ## Elementary bounds for unimodular real `2 × 2` matrices -/

/-- For a real `2 × 2` matrix of determinant `1` the sum of the squares of the entries
is at least `2`: `b₀₀² + b₁₁² ≥ 2 b₀₀ b₁₁` and `b₀₁² + b₁₀² ≥ -2 b₀₁ b₁₀`. -/
theorem two_le_sum_sq_of_det_one (B : Matrix (Fin 2) (Fin 2) ℝ) (hdet : B.det = 1) :
    2 ≤ B 0 0 ^ 2 + B 0 1 ^ 2 + B 1 0 ^ 2 + B 1 1 ^ 2 := by
  have h : B 0 0 * B 1 1 - B 0 1 * B 1 0 = 1 := by
    simpa [Matrix.det_fin_two] using hdet
  nlinarith [sq_nonneg (B 0 0 - B 1 1), sq_nonneg (B 0 1 + B 1 0)]

/-- The squared Frobenius norm of a real matrix viewed in `ℂ` is the sum of the squares
of its entries (`Complex.ofRealHom` version of `Scale.frob_map_ofReal_sq`). -/
theorem frob_sq_map_ofReal (B : Matrix (Fin 2) (Fin 2) ℝ) :
    frob (B.map Complex.ofRealHom) ^ 2
      = B 0 0 ^ 2 + B 0 1 ^ 2 + B 1 0 ^ 2 + B 1 1 ^ 2 := by
  have hfun : (fun x : ℝ => (x : ℂ)) = (⇑Complex.ofRealHom : ℝ → ℂ) := rfl
  rw [show B.map Complex.ofRealHom = B.map (fun x : ℝ => (x : ℂ)) from by rw [hfun]]
  exact Work.TMC7Core.Scale.frob_map_ofReal_sq B

/-- A real `SL₂` matrix has `‖B‖_F² ≥ 2`. -/
theorem two_le_frob_sq_ofReal (B : Matrix (Fin 2) (Fin 2) ℝ) (hdet : B.det = 1) :
    2 ≤ frob (B.map Complex.ofRealHom) ^ 2 := by
  rw [frob_sq_map_ofReal]
  exact two_le_sum_sq_of_det_one B hdet

/-- The Frobenius norm of a matrix with squared norm at least `2` is positive. -/
theorem frob_pos_of_sq_ge_two (X : Matrix (Fin 2) (Fin 2) ℂ) (h : 2 ≤ frob X ^ 2) :
    0 < frob X := by
  rcases eq_or_lt_of_le (frob_nonneg X) with h0 | h0
  · exfalso; rw [← h0] at h; linarith
  · exact h0

/-! ## The main theorem -/

theorem defect_upper (A : Matrix (Fin 2) (Fin 2) ℝ) (hdet : A.det = 1) (m : ℕ) (hm : 1 ≤ m) :
    Real.log (Work.TMC7Core.frob ((A.map Complex.ofRealHom) ^ (2 * m)))
      - Real.log (Work.TMC7Core.frob ((A.map Complex.ofRealHom) ^ m))
      - (m : ℝ) * Real.log (Work.TMC7Core.rhoSL A.trace) ≤ Real.log 2 := by
  set B : Matrix (Fin 2) (Fin 2) ℝ := A ^ m with hBdef
  have hBdet : B.det = 1 := by rw [hBdef, Matrix.det_pow, hdet, one_pow]
  have hmapB : B.map Complex.ofRealHom = (A.map Complex.ofRealHom) ^ m := by
    rw [hBdef]; exact Matrix.map_pow A Complex.ofRealHom m
  set ρ : ℝ := rhoSL A.trace with hρdef
  have hρ1 : 1 ≤ ρ := by rw [hρdef]; exact rhoSL_one_le A.trace
  have hρpos : 0 < ρ := lt_of_lt_of_le zero_lt_one hρ1
  have hρm_pos : 0 < ρ ^ m := pow_pos hρpos m
  have hρm1 : 1 ≤ ρ ^ m := le_trans hρ1 (le_self_pow₀ hρ1 (by omega))
  -- the trace of `B = A^m` is bounded by twice the `m`-th power of the spectral radius
  have htr : |B.trace| ≤ 2 * ρ ^ m := by
    rw [hBdef, hρdef]; exact trace_pow_abs_le_rhoSL A hdet m
  have htr2 : B.trace ^ 2 ≤ (2 * ρ ^ m) ^ 2 := by
    have h1 : 0 ≤ 2 * ρ ^ m - |B.trace| := by linarith [htr]
    have h2 : 0 ≤ 2 * ρ ^ m + |B.trace| := by linarith [abs_nonneg B.trace]
    have h3 := mul_nonneg h1 h2
    have h4 : (2 * ρ ^ m - |B.trace|) * (2 * ρ ^ m + |B.trace|)
        = (2 * ρ ^ m) ^ 2 - |B.trace| ^ 2 := by ring
    rw [h4, sq_abs] at h3
    linarith
  have hF : 2 ≤ frob (B.map Complex.ofRealHom) ^ 2 := two_le_frob_sq_ofReal B hBdet
  have hdouble := frob_sq_sq_of_det_one B hBdet
  have hy1 : 1 ≤ (2 * ρ ^ m) ^ 2 := by
    have h2 : (1 : ℝ) ≤ 2 * ρ ^ m := by nlinarith [hρm1]
    exact one_le_pow₀ h2
  -- the doubling inequality
  have hkey : frob ((B.map Complex.ofRealHom) ^ 2) ^ 2
      ≤ (2 * ρ ^ m) ^ 2 * frob (B.map Complex.ofRealHom) ^ 2 := by
    have hstep : (frob (B.map Complex.ofRealHom) ^ 2 - 2) * B.trace ^ 2
        ≤ (frob (B.map Complex.ofRealHom) ^ 2 - 2) * (2 * ρ ^ m) ^ 2 :=
      mul_le_mul_of_nonneg_left htr2 (by linarith)
    rw [hdouble]
    nlinarith [hstep, hF, hy1]
  have hpow : (A.map Complex.ofRealHom) ^ (2 * m) = (B.map Complex.ofRealHom) ^ 2 := by
    rw [hmapB, Nat.mul_comm 2 m, pow_mul]
  have hsq : frob ((A.map Complex.ofRealHom) ^ (2 * m)) ^ 2
      ≤ ((2 * ρ ^ m) * frob ((A.map Complex.ofRealHom) ^ m)) ^ 2 := by
    rw [hpow, ← hmapB]
    calc frob ((B.map Complex.ofRealHom) ^ 2) ^ 2
        ≤ (2 * ρ ^ m) ^ 2 * frob (B.map Complex.ofRealHom) ^ 2 := hkey
      _ = ((2 * ρ ^ m) * frob (B.map Complex.ofRealHom)) ^ 2 := by ring
  have hX0 : 0 ≤ frob ((A.map Complex.ofRealHom) ^ (2 * m)) := frob_nonneg _
  have hY0 : 0 ≤ (2 * ρ ^ m) * frob ((A.map Complex.ofRealHom) ^ m) :=
    mul_nonneg (by positivity) (frob_nonneg _)
  have hle : frob ((A.map Complex.ofRealHom) ^ (2 * m))
      ≤ (2 * ρ ^ m) * frob ((A.map Complex.ofRealHom) ^ m) := by
    calc frob ((A.map Complex.ofRealHom) ^ (2 * m))
        = Real.sqrt (frob ((A.map Complex.ofRealHom) ^ (2 * m)) ^ 2) := (Real.sqrt_sq hX0).symm
      _ ≤ Real.sqrt (((2 * ρ ^ m) * frob ((A.map Complex.ofRealHom) ^ m)) ^ 2) :=
          Real.sqrt_le_sqrt hsq
      _ = (2 * ρ ^ m) * frob ((A.map Complex.ofRealHom) ^ m) := Real.sqrt_sq hY0
  -- positivity of the two Frobenius norms
  have hYpos : 0 < frob ((A.map Complex.ofRealHom) ^ m) := by
    refine frob_pos_of_sq_ge_two _ ?_
    rwa [← hmapB]
  have hXpos : 0 < frob ((A.map Complex.ofRealHom) ^ (2 * m)) := by
    refine frob_pos_of_sq_ge_two _ ?_
    rw [hpow, hdouble]
    nlinarith [hF, sq_nonneg B.trace]
  -- take logarithms and rearrange
  have hlog := Real.log_le_log hXpos hle
  have hlog2 : Real.log ((2 * ρ ^ m) * frob ((A.map Complex.ofRealHom) ^ m))
      = Real.log 2 + (m : ℝ) * Real.log ρ
        + Real.log (frob ((A.map Complex.ofRealHom) ^ m)) := by
    rw [Real.log_mul (by positivity) (ne_of_gt hYpos),
      Real.log_mul (by norm_num) (ne_of_gt hρm_pos), Real.log_pow]
  rw [hlog2] at hlog
  linarith

end Work.TMComp.LocCantor
