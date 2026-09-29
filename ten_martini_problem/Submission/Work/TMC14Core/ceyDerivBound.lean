import Mathlib
import Submission.Work.TMC14Core.ceyTraceOdd
import Submission.Work.TMC14Core.Chambers
import Submission.Work.TMC14Core.charpolyDerivAdj
import Submission.Work.TMC14Core.adjugateHermitianRankOne
import Submission.Work.TMC14Core.traceUnitaryLe

open Matrix
noncomputable section

namespace Work.TMC14Core

/-!
# `TMC14Core.ceyDerivBound`: CEY's lower bound for the derivative of the discriminant

For `q = 2m+1` odd and `gcd(p,q) = 1`, every real eigenvalue `a` of the Bloch matrix
`blochMat p q lam θ k` satisfies `q |λ|^m ≤ |Δ'(a)|`, where `Δ = disc p q lam` is the
discriminant (the characteristic polynomial of the Bloch matrix at `θ = 1/(4q)`, `k = 0`,
shifted by `2`).

The proof has three ingredients:

* `blochMat p q lam θ k` is Hermitian, so `N := a • 1 - blochMat p q lam θ k` is Hermitian
  and `N.mulVec v = 0` — the eigenvector equation;
* `charpolyDerivAdj` identifies `Δ'(a)` with `tr (adj N)` (the characteristic polynomial
  of the Bloch matrix differs from `Δ` by a constant, `disc_eq_charpoly_add`);
* `ceyTraceOdd` supplies a unitary `W` with `‖tr (adj N * W)‖ = q |λ|^m`, and
  `adjugateHermitianRankOne` writes `adj N = c • v v*`, so that `traceUnitaryLe` bounds
  `‖tr (adj N * W)‖` by `‖tr (adj N)‖`.
-/

/-- The Bloch matrix `blochMat p q lam θ k` is Hermitian (for real `lam, θ, k`). -/
theorem blochMat_isHermitian (p : ℤ) (q : ℕ) (lam θ k : ℝ) :
    (blochMat p q lam θ k).IsHermitian := by
  rw [BlochMatEq]
  have h1 : (wU q k + star (wU q k)).IsHermitian := by
    have h := isHermitian_add_transpose_self (α := ℂ) (wU q k)
    simpa [Matrix.star_eq_conjTranspose] using h
  have h2 : (wV p q θ + star (wV p q θ)).IsHermitian := by
    have h := isHermitian_add_transpose_self (α := ℂ) (wV p q θ)
    simpa [Matrix.star_eq_conjTranspose] using h
  have h3 : IsSelfAdjoint (lam : ℂ) := by
    rw [IsSelfAdjoint, Complex.star_def]
    exact Complex.conj_ofReal lam
  exact h1.add (h2.smul h3)

/-- The characteristic polynomial of the Bloch matrix differs from the discriminant `disc`
by the constant `2 cos 2πk - chamCoef cos 2πqθ`. -/
theorem disc_eq_charpoly_add (p : ℤ) (q m : ℕ) (hm : q = 2*m+1) (hpq : Nat.Coprime p.natAbs q)
    (lam θ k : ℝ) :
    disc p q lam = (blochMat p q lam θ k).charpoly
      + Polynomial.C (2 * ((Real.cos (2 * Real.pi * k) : ℝ) : ℂ)
          - chamCoef p q lam * ((Real.cos (2 * Real.pi * (q:ℝ) * θ) : ℝ) : ℂ)) := by
  have hq : 1 ≤ q := by omega
  apply Polynomial.funext
  intro z
  rw [Polynomial.eval_add, Polynomial.eval_C, Matrix.eval_charpoly]
  rw [show Matrix.scalar (Fin q) z = z • (1 : Matrix (Fin q) (Fin q) ℂ) from by
    ext i j
    rw [Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.smul_apply, smul_eq_mul,
      Matrix.one_apply]
    by_cases h : i = j <;> simp [h]]
  rw [blochMat_chambers p q lam θ k z hpq hq]
  ring_nf

/-- The derivative of the discriminant is the derivative of the characteristic polynomial of
the Bloch matrix (they differ by a constant). -/
theorem disc_derivative_eq (p : ℤ) (q m : ℕ) (hm : q = 2*m+1) (hpq : Nat.Coprime p.natAbs q)
    (lam θ k : ℝ) :
    (disc p q lam).derivative = (blochMat p q lam θ k).charpoly.derivative := by
  rw [disc_eq_charpoly_add p q m hm hpq lam θ k, Polynomial.derivative_add,
    Polynomial.derivative_C, add_zero]

/-- **CEY's lower bound.**  For `q = 2m+1` odd, `gcd(p,q) = 1`, and any real eigenvalue `a`
of the Bloch matrix of the rational approximant `p/q` (with non-zero eigenvector `v`),
`q |λ|^m ≤ |Δ'(a)|`. -/
theorem ceyDerivBound (p : ℤ) (q m : ℕ) (hm : q = 2*m+1) (hpq : Nat.Coprime p.natAbs q) (lam θ k : ℝ) (a : ℝ) (v : Fin q → ℂ) (hv : v ≠ 0) (hva : (blochMat p q lam θ k).mulVec v = (a : ℂ) • v) : (q : ℝ) * |lam| ^ m ≤ ‖(disc p q lam).derivative.eval (a : ℂ)‖ := by
  set N : Matrix (Fin q) (Fin q) ℂ := (a : ℂ) • 1 - blochMat p q lam θ k with hN
  obtain ⟨W, hW, hWval⟩ := ceyTraceOdd p q m hm hpq lam θ k (a : ℂ)
  rw [← hN] at hWval
  have hNherm : N.IsHermitian := by
    rw [hN]
    have ha : IsSelfAdjoint (a : ℂ) := by
      rw [IsSelfAdjoint, Complex.star_def]
      exact Complex.conj_ofReal a
    exact (Matrix.isHermitian_one.smul ha).sub (blochMat_isHermitian p q lam θ k)
  have hNv : N.mulVec v = 0 := by
    rw [hN, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, hva, sub_self]
  obtain ⟨c, hc⟩ := adjugateHermitianRankOne N hNherm v hv hNv
  have hkey : (disc p q lam).derivative.eval (a : ℂ) = N.adjugate.trace := by
    rw [disc_derivative_eq p q m hm hpq lam θ k, hN]
    exact charpolyDerivAdj (blochMat p q lam θ k) (blochMat_isHermitian p q lam θ k) (a : ℂ)
  calc (q : ℝ) * |lam| ^ m = ‖(N.adjugate * W).trace‖ := hWval.symm
    _ = ‖((c • Matrix.vecMulVec v (star v)) * W).trace‖ := by rw [hc]
    _ ≤ ‖(c • Matrix.vecMulVec v (star v)).trace‖ := traceUnitaryLe c v W hW
    _ = ‖N.adjugate.trace‖ := by rw [hc]
    _ = ‖(disc p q lam).derivative.eval (a : ℂ)‖ := by rw [hkey]

end Work.TMC14Core
