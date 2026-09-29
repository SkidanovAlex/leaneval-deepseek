import Submission.Work.TMC14Core.Defs

/-!
# TMC14Core: the rational-frequency (`α = p/q`) algebra

Definitions and first lemmas for the rational approximants `p/q` of component C14.
The main object is the `q`-step transfer matrix `iterC (p/q) lam z q θ` and its trace
`trAq`, together with the Bloch matrix `blochMat` of the periodic problem.

Conventions (verified numerically in `scratch/`):
* `trAq p q lam z θ = Δ(z) + 2(-λ)^q(-1)^{p(q-1)} cos(2πqθ)`  (`chambers`)
  where `Δ` is a monic polynomial of degree `q` (the "discriminant").
  Equivalently `det(z - blochMat θ k) = Δ(z) + 2(-λ)^q(-1)^{p(q-1)}cos(2πqθ) - 2cos(2πk)`.
* the sign `(-1)^{p(q-1)}` is the one resolved in `ROUTE_LEAD.md` §4 C14 14a/14e
  (`2(-λ)^q(...)`, i.e. `-2λ^q cos 2πqθ` for `q` odd).
-/

open MeasureTheory Filter Topology Set
open LeanEval.Analysis.TenMartini

noncomputable section

namespace Work.TMC14Core

/-! ## 1. The oscillatory coefficient and the trace of the `q`-step transfer matrix -/

/-- `ω = e^{2πi p/q}`, the `q`-th root of unity attached to the frequency `p/q`. -/
def om (p : ℤ) (q : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * (p : ℂ) / (q : ℂ))

/-- `2(-λ)^q(-1)^{p(q-1)}`: twice the top Fourier coefficient of `θ ↦ tr A_q(θ,·)`. -/
def chamCoef (p : ℤ) (q : ℕ) (lam : ℝ) : ℂ :=
  2 * (-(lam : ℂ)) ^ q * (-1 : ℂ) ^ (p * ((q : ℤ) - 1))

/-- `tr A_q(θ,z)` for the frequency `p/q`. -/
def trAq (p : ℤ) (q : ℕ) (lam : ℝ) (z : ℂ) (θ : ℝ) : ℂ :=
  ((iterC ((p : ℝ) / (q : ℝ)) lam z q θ) 0 0) + ((iterC ((p : ℝ) / (q : ℝ)) lam z q θ) 1 1)

/-- The Bloch matrix of the periodic problem with frequency `p/q`, quasi-momentum `k`
and phase `θ`: diagonal `2λcos 2π(θ + i p/q)`, nearest-neighbour `1`'s and the two
corner entries `e^{±2πik}` of the Bloch boundary condition (added, so that the entries
coincide correctly when `q = 1` or `q = 2`). -/
def blochMat (p : ℤ) (q : ℕ) (lam : ℝ) (θ k : ℝ) : Matrix (Fin q) (Fin q) ℂ :=
  fun i j =>
    (if i = j then ((2 * lam * Real.cos (2 * Real.pi * (θ + (i : ℝ) * (p : ℝ) / (q : ℝ))) : ℝ) : ℂ)
      else 0)
    + (if (i : ℕ) + 1 = (j : ℕ) then (1 : ℂ) else 0)
    + (if (j : ℕ) + 1 = (i : ℕ) then (1 : ℂ) else 0)
    + (if (i : ℕ) = q - 1 ∧ (j : ℕ) = 0 then Complex.exp (2 * Real.pi * Complex.I * (k : ℂ))
        else 0)
    + (if (i : ℕ) = 0 ∧ (j : ℕ) = q - 1 then Complex.exp (-(2 * Real.pi * Complex.I * (k : ℂ)))
        else 0)

/-- The discriminant `Δ` of the rational approximant `p/q`, defined as the
characteristic polynomial of the Bloch matrix at `θ = 1/(4q)`, `k = 0`, plus `2`:
at that `θ` the oscillatory term `2(-λ)^q(-1)^{p(q-1)}cos(2πqθ)` vanishes. -/
def disc (p : ℤ) (q : ℕ) (lam : ℝ) : Polynomial ℂ :=
  (blochMat p q lam (1 / (4 * (q : ℝ))) 0).charpoly + Polynomial.C 2

/-! ## 2. Elementary transfer-matrix identities -/

@[simp] theorem tmC_det (lam : ℝ) (z : ℂ) (x : ℝ) : (tmC lam z x).det = 1 := by
  simp [tmC, Matrix.det_fin_two]

theorem iterC_succ (α lam : ℝ) (z : ℂ) (n : ℕ) (x : ℝ) :
    iterC α lam z (n + 1) x = tmC lam z (x + (n : ℝ) * α) * iterC α lam z n x := rfl

theorem iterC_zero (α lam : ℝ) (z : ℂ) (x : ℝ) : iterC α lam z 0 x = 1 := rfl

theorem iterC_det (α lam : ℝ) (z : ℂ) (n : ℕ) (x : ℝ) : (iterC α lam z n x).det = 1 := by
  induction n with
  | zero => simp [iterC]
  | succ n ih => rw [iterC_succ, Matrix.det_mul, tmC_det, ih, one_mul]

/-- `A_n(x+α) · S(x) = S(x+nα) · A_n(x)`.  Stated without inverses. -/
theorem iterC_add_alpha (α lam : ℝ) (z : ℂ) (n : ℕ) (x : ℝ) :
    iterC α lam z n (x + α) * tmC lam z x = tmC lam z (x + (n : ℝ) * α) * iterC α lam z n x := by
  induction n with
  | zero => simp [iterC]
  | succ n ih =>
    rw [iterC_succ, iterC_succ, mul_assoc, ih]
    congr 1
    push_cast
    ring

/-- Conjugation lemma: `A S = S B` with `det S = 1` forces `tr A = tr B`. -/
theorem trace_eq_of_mul_eq_of_det_eq_one {A B S : Matrix (Fin 2) (Fin 2) ℂ}
    (h : A * S = S * B) (hS : S.det = 1) : A.trace = B.trace := by
  have h2 : A = S * B * S.adjugate := by
    calc A = A * (S * S.adjugate) := by rw [Matrix.mul_adjugate, hS]; simp
         _ = (A * S) * S.adjugate := by rw [mul_assoc]
         _ = (S * B) * S.adjugate := by rw [h]
  rw [h2, Matrix.trace_mul_comm (S * B) S.adjugate, ← mul_assoc, Matrix.adjugate_mul, hS]
  simp

/-- `tr A_q(θ + p/q) = tr A_q(θ)`: the trace of the `q`-step transfer matrix is
`p/q`-periodic in the phase. -/
theorem trAq_period (p : ℤ) (q : ℕ) (lam : ℝ) (z : ℂ) (θ : ℝ) (hq : q ≠ 0) :
    trAq p q lam z (θ + (p : ℝ) / (q : ℝ)) = trAq p q lam z θ := by
  have hα : ((q : ℝ)) * ((p : ℝ) / (q : ℝ)) = (p : ℝ) := by
    field_simp
  have hmain := iterC_add_alpha ((p : ℝ) / (q : ℝ)) lam z q θ
  have hcos : Real.cos (2 * Real.pi * (θ + (p : ℝ))) = Real.cos (2 * Real.pi * θ) := by
    have : 2 * Real.pi * (θ + (p : ℝ)) = 2 * Real.pi * θ + (p : ℤ) * (2 * Real.pi) := by push_cast; ring
    rw [this, Real.cos_add_int_mul_two_pi]
  have hS : tmC lam z (θ + ((q : ℕ) : ℝ) * ((p : ℝ) / (q : ℝ))) = tmC lam z θ := by
    rw [hα]; simp [tmC, hcos]
  rw [hS] at hmain
  simp only [trAq]
  rw [← Matrix.trace_fin_two, ← Matrix.trace_fin_two]
  exact trace_eq_of_mul_eq_of_det_eq_one hmain (tmC_det lam z θ)

/-- `tr A_q` is `1`-periodic in the phase. -/
theorem tmC_add_one (lam : ℝ) (z : ℂ) (x : ℝ) : tmC lam z (x + 1) = tmC lam z x := by
  have h : Real.cos (2 * Real.pi * (x + 1)) = Real.cos (2 * Real.pi * x) := by
    have : 2 * Real.pi * (x + 1) = 2 * Real.pi * x + (1 : ℤ) * (2 * Real.pi) := by push_cast; ring
    rw [this, Real.cos_add_int_mul_two_pi]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [tmC, h]

theorem iterC_add_one (α lam : ℝ) (z : ℂ) (n : ℕ) (x : ℝ) :
    iterC α lam z n (x + 1) = iterC α lam z n x := by
  induction n with
  | zero => simp [iterC]
  | succ n ih =>
    rw [iterC_succ, iterC_succ, ih]
    congr 1
    rw [show x + 1 + (n : ℝ) * α = x + (n : ℝ) * α + 1 from by ring]
    exact tmC_add_one lam z (x + (n : ℝ) * α)

theorem trAq_add_one (p : ℤ) (q : ℕ) (lam : ℝ) (z : ℂ) (θ : ℝ) :
    trAq p q lam z (θ + 1) = trAq p q lam z θ := by
  simp only [trAq, iterC_add_one]

end Work.TMC14Core
