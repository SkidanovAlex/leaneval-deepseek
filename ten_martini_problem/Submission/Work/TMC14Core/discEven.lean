import Mathlib
import Submission.Work.TMC14Core.Assembly

/-!
# TMC14Core: the discriminant of an even-denominator rational approximant is even

For `q = 2m+2` (even `q`) and `gcd(p,q) = 1`, the discriminant

  `disc p q lam = (blochMat p q lam (1/(4q)) 0).charpoly + 2`

is an even polynomial: `disc(-z) = disc(z)` for all `z : ℂ`.  Equivalently the union
spectrum of the rational approximant is symmetric about `0`.

The proof does not touch the `q × q` Bloch matrix.  It uses the `2 × 2` symmetries of the
transfer matrices:

* The involution `σ = diag(1,-1)` conjugates the transfer matrix at energy `z` into minus
  the transfer matrix at energy `-z` and phase shifted by `1/2`:
  `σ · S(z,x) · σ = -S(-z, x + 1/2)` (`sgMat_conj_tmC`), because
  `cos(2π(x+1/2)) = -cos(2πx)`.  Iterating (`sgMat_conj_iterC`), and using that conjugation
  by `σ` preserves the trace (`sgMat_conj_trace`),

  `tr A_q(z,θ) = (-1)^q tr A_q(-z, θ+1/2)`   (`trAq_neg_half`).

* Chambers' formula (`chambers`) evaluates `tr A_q` at the phase `1/(4q)`, where the
  oscillatory term `cos(2πqθ)` vanishes; the same is true at `1/(4q) + 1/2`, since
  `cos(π/2 + πq) = 0`.

For `q` even the factor `(-1)^q` is `1`, and `disc_eval` identifies
`disc(z)` with `tr A_q(z, 1/(4q))`, so
`disc(-z) = tr A_q(-z,1/(4q)) = tr A_q(-z,1/(4q)+1/2) = tr A_q(z,1/(4q)) = disc(z)`.
-/

namespace Work.TMC14Core

noncomputable section

/-- The involution `σ = diag(1,-1)`. -/
def sgMat : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]

theorem sgMat_sq : sgMat * sgMat = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [sgMat]

/-- Conjugation by `σ` is multiplicative (because `σ² = 1`). -/
theorem sgMat_conj_mul (A B : Matrix (Fin 2) (Fin 2) ℂ) :
    sgMat * (A * B) * sgMat = (sgMat * A * sgMat) * (sgMat * B * sgMat) := by
  have h : (sgMat * A * sgMat) * (sgMat * B * sgMat) = sgMat * A * (sgMat * sgMat) * B * sgMat := by
    simp only [Matrix.mul_assoc]
  rw [h, sgMat_sq, Matrix.mul_one]
  simp only [Matrix.mul_assoc]

/-- `σ · tm2 a · σ = -tm2(-a)`. -/
theorem sgMat_conj_tm2 (a : ℂ) : sgMat * tm2 a * sgMat = -tm2 (-a) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sgMat, tm2, Matrix.mul_apply, Fin.sum_univ_two]

/-- `σ · S(z,x) · σ = -S(-z, x + 1/2)`. -/
theorem sgMat_conj_tmC (lam : ℝ) (z : ℂ) (x : ℝ) :
    sgMat * tmC lam z x * sgMat = -tmC lam (-z) (x + 1/2) := by
  have hc : Real.cos (2 * Real.pi * (x + 1/2)) = -Real.cos (2*Real.pi*x) := by
    rw [show 2*Real.pi*(x+1/2) = 2*Real.pi*x + Real.pi from by ring, Real.cos_add_pi]
  have hkey : - (z - ((2*lam*Real.cos (2*Real.pi*x) : ℝ) : ℂ))
      = (-z) - ((2*lam*Real.cos (2*Real.pi*(x+1/2)) : ℝ) : ℂ) := by
    rw [hc]; push_cast; ring
  have h1 : tmC lam z x = tm2 (z - ((2*lam*Real.cos (2*Real.pi*x) : ℝ) : ℂ)) := rfl
  have h2 : tmC lam (-z) (x+1/2)
      = tm2 ((-z) - ((2*lam*Real.cos (2*Real.pi*(x+1/2)) : ℝ) : ℂ)) := rfl
  rw [h1, h2, sgMat_conj_tm2, hkey]

/-- `σ · A_n(z,x) · σ = (-1)^n A_n(-z, x + 1/2)`. -/
theorem sgMat_conj_iterC (α lam : ℝ) (z : ℂ) (n : ℕ) (x : ℝ) :
    sgMat * iterC α lam z n x * sgMat = (-1:ℂ)^n • iterC α lam (-z) n (x + 1/2) := by
  induction n generalizing x with
  | zero => simp [iterC, sgMat_sq]
  | succ n ih =>
    rw [iterC_succ, iterC_succ, sgMat_conj_mul, sgMat_conj_tmC, ih]
    rw [show x + (n:ℝ)*α + 1/2 = (x+1/2) + (n:ℝ)*α from by ring]
    rw [← neg_one_smul ℂ, Matrix.smul_mul, Matrix.mul_smul, smul_smul, pow_succ]
    congr 1
    ring

/-- Conjugation by `σ` preserves the trace. -/
theorem sgMat_conj_trace (M : Matrix (Fin 2) (Fin 2) ℂ) :
    (sgMat * M * sgMat).trace = M.trace := by
  rw [Matrix.trace_mul_comm (sgMat * M) sgMat]
  rw [← Matrix.mul_assoc, sgMat_sq, Matrix.one_mul]

/-- `tr A_q(z,θ) = (-1)^q tr A_q(-z, θ + 1/2)`. -/
theorem trAq_neg_half (p : ℤ) (q : ℕ) (lam : ℝ) (z : ℂ) (θ : ℝ) :
    trAq p q lam z θ = (-1:ℂ)^q * trAq p q lam (-z) (θ + 1/2) := by
  rw [trAq_eq_trace, trAq_eq_trace,
    ← sgMat_conj_trace (iterC ((p : ℝ) / (q : ℝ)) lam z q θ)]
  rw [sgMat_conj_iterC ((p:ℝ)/(q:ℝ)) lam z q θ, Matrix.trace_smul]
  simp [smul_eq_mul]

theorem discEven (p : ℤ) (q m : ℕ) (hm : q = 2*m+2) (hpq : Nat.Coprime p.natAbs q)
    (lam : ℝ) : ∀ z : ℂ, (disc p q lam).eval (-z) = (disc p q lam).eval z := by
  intro z
  have hq : 1 ≤ q := by omega
  have heven : Even q := ⟨m+1, by omega⟩
  -- `disc` is the trace of the `q`-step transfer matrix at phase `1/(4q)`.
  rw [disc_eval p q lam (-z) hq, disc_eval p q lam z hq]
  -- the energy symmetry of the `q`-step transfer matrix: `(-1)^q = 1` since `q` is even.
  have hconj := trAq_neg_half p q lam z (1/(4*(q:ℝ)))
  rw [Even.neg_one_pow heven, one_mul] at hconj
  rw [hconj]
  -- Chambers' formula at both phases; the oscillatory term vanishes at each.
  have h1 := chambers p q lam (-z) hpq hq (1 / (4*(q:ℝ)) + 1/2)
  have h2 := chambers p q lam (-z) hpq hq (1 / (4*(q:ℝ)))
  have hc2 : Real.cos (2 * Real.pi * (q:ℝ) * (1 / (4*(q:ℝ)))) = 0 := by
    rw [show 2 * Real.pi * (q:ℝ) * (1 / (4*(q:ℝ))) = Real.pi / 2 from by field_simp; ring]
    exact Real.cos_pi_div_two
  have hc1 : Real.cos (2 * Real.pi * (q:ℝ) * (1 / (4*(q:ℝ)) + 1/2)) = 0 := by
    rw [show 2 * Real.pi * (q:ℝ) * (1 / (4*(q:ℝ)) + 1/2)
        = Real.pi/2 + (q:ℝ)*Real.pi from by field_simp; ring]
    rw [Real.cos_eq_zero_iff]
    exact ⟨(q:ℤ), by push_cast; ring⟩
  rw [h1, h2, hc1, hc2]

end

end Work.TMC14Core
