import Mathlib
import Submission.Work.TMContract.Components

/-!
# C6 (`P_IDSSpectrum`) — shared vocabulary

This file fixes the notation used by the proof of `Work.TMContract.P_IDSSpectrum`
(AJ (2.11): every spectral point is a point of increase of the integrated density of
states `N = ids`).

The proof goes through Sturm oscillation: the Prüfer angle of the AMO transfer matrices
counts the eigenvalues of the finite (Dirichlet) box matrices.

Objects:

* `pot α lam θ j = 2λ cos(2π(θ + jα))` — the potential at site `j` (agrees with
  `amoPot`).
* `jstate α lam θ E : ℕ → ℝ × ℝ` — the state vector `(u_n, u_{n-1})` of the solution of
  the Dirichlet eigenvalue equation, started at `(u_0, u_{-1}) = (1, 0)`; `uSeq` and
  `vSeq` are its two components.
* `jacPoly α lam θ n` — the characteristic polynomial of the `n`-site box matrix, defined
  by the three-term recursion `P_{n+1} = (X - v_n) P_n - P_{n-1}`, `P_0 = 1`,
  `P_{-1} = 0` (`jacPrev` is `P_{n-1}`).
* `Jbox α lam θ n` — the `n × n` complex Hermitian (real) symmetric tridiagonal box
  matrix with diagonal `v_j(θ)` and off-diagonal `1`.  `boxEig` is its eigenvalue list
  (`Fin n → ℝ`) and `boxCount` the number of eigenvalues `< E`.
* `shiftCount α θ δ n` — the number of `j < n` with `‖θ + jα‖_ℤ < δ`.

All definitions are `sorry`-free; the lemmas at the end are immediate.
-/

noncomputable section

open scoped BigOperators
open Polynomial

namespace Work.TMComp

open Work.TMContract

/-- The AMO potential at site `j`: `v_j(θ) = 2λ cos(2π(θ + jα))`. -/
def pot (α lam θ : ℝ) (j : ℕ) : ℝ := 2 * lam * Real.cos (2 * Real.pi * (θ + (j : ℝ) * α))

theorem pot_eq_amoPot (α lam θ : ℝ) (j : ℕ) :
    pot α lam θ j = amoPot α lam θ (j : ℤ) := by
  simp [pot, amoPot]

/-- The state vector `(u_n, u_{n-1})` of the solution of the eigenvalue equation
`u_{n+1} + u_{n-1} + v_n u_n = E u_n` with the (Dirichlet) initial data
`(u_0, u_{-1}) = (1, 0)`. -/
def jstate (α lam θ E : ℝ) : ℕ → ℝ × ℝ
  | 0 => (1, 0)
  | n + 1 =>
      ((E - pot α lam θ n) * (jstate α lam θ E n).1 - (jstate α lam θ E n).2,
        (jstate α lam θ E n).1)

/-- First component `u_n` of `jstate`. -/
def uSeq (α lam θ E : ℝ) (n : ℕ) : ℝ := (jstate α lam θ E n).1

/-- Second component `u_{n-1}` of `jstate`. -/
def vSeq (α lam θ E : ℝ) (n : ℕ) : ℝ := (jstate α lam θ E n).2

/-- Auxiliary pair recursion for the box characteristic polynomials:
`(P_n, P_{n-1})`. -/
def jacPair (α lam θ : ℝ) : ℕ → Polynomial ℝ × Polynomial ℝ
  | 0 => (1, 0)
  | n + 1 =>
      ((X - C (pot α lam θ n)) * (jacPair α lam θ n).1 - (jacPair α lam θ n).2,
        (jacPair α lam θ n).1)

/-- The characteristic polynomial of the `n`-site box matrix: `P_0 = 1` and
`P_{n+1} = (X - v_n) P_n - P_{n-1}`. -/
def jacPoly (α lam θ : ℝ) (n : ℕ) : Polynomial ℝ := (jacPair α lam θ n).1

/-- `P_{n-1}`, the second component of the auxiliary pair. -/
def jacPrev (α lam θ : ℝ) (n : ℕ) : Polynomial ℝ := (jacPair α lam θ n).2

/-- The `n × n` box matrix (Dirichlet truncation of the AMO at phase `θ`): diagonal
`v_j(θ)`, off-diagonal `1`. -/
def Jbox (α lam θ : ℝ) (n : ℕ) : Matrix (Fin n) (Fin n) ℂ :=
  fun i j =>
    if i = j then ((pot α lam θ (i : ℕ) : ℝ) : ℂ)
    else if (i : ℕ) + 1 = (j : ℕ) ∨ (j : ℕ) + 1 = (i : ℕ) then 1 else 0

theorem isHermitian_Jbox (α lam θ : ℝ) (n : ℕ) : (Jbox α lam θ n).IsHermitian := by
  ext i j
  simp only [Matrix.conjTranspose_apply, Jbox]
  by_cases hij : j = i
  · subst hij
    simp [Complex.conj_ofReal]
  · have hne : ¬ (i = j) := fun h => hij h.symm
    by_cases hc : (i : ℕ) + 1 = (j : ℕ) ∨ (j : ℕ) + 1 = (i : ℕ)
    · have hc' : (j : ℕ) + 1 = (i : ℕ) ∨ (i : ℕ) + 1 = (j : ℕ) := hc.symm
      simp [hij, hne, hc, hc']
    · have hc' : ¬ ((j : ℕ) + 1 = (i : ℕ) ∨ (i : ℕ) + 1 = (j : ℕ)) := by
        rwa [or_comm]
      simp [hij, hne, hc, hc']

/-- The eigenvalue list of the box matrix. -/
def boxEig (α lam θ : ℝ) (n : ℕ) : Fin n → ℝ :=
  (isHermitian_Jbox α lam θ n).eigenvalues

/-- Number of box eigenvalues `< E`. -/
def boxCount (α lam θ E : ℝ) (n : ℕ) : ℕ :=
  (Finset.univ.filter (fun k : Fin n => boxEig α lam θ n k < E)).card

/-- The `j`-th translate of a finitely supported sequence, as a vector of the `n`-site box. -/
def shiftVec (φ : ℤ → ℂ) (j : ℤ) (n : ℕ) : Fin n → ℂ := fun k => φ ((k : ℤ) - j)

/-- Number of `j < n` with `‖θ + jα‖_ℤ < δ` (`fracDist` is the distance to the nearest
integer). -/
def shiftCount (α θ δ : ℝ) (n : ℕ) : ℕ :=
  (Finset.univ.filter (fun j : Fin n => fracDist (θ + (j : ℝ) * α) < δ)).card

theorem jacPoly_succ (α lam θ : ℝ) (n : ℕ) :
    jacPoly α lam θ (n + 1) = (X - C (pot α lam θ n)) * jacPoly α lam θ n - jacPrev α lam θ n := by
  simp [jacPoly, jacPrev, jacPair]

theorem jacPrev_succ (α lam θ : ℝ) (n : ℕ) :
    jacPrev α lam θ (n + 1) = jacPoly α lam θ n := by
  simp [jacPoly, jacPrev, jacPair]

/-- The `n`-th box characteristic polynomial evaluated at `E` is the `n`-th component of
the Dirichlet state vector (same three-term recursion, same initial data). -/
theorem eval_jacPair (α lam θ E : ℝ) : ∀ n : ℕ,
    (((jacPair α lam θ n).1).eval E, ((jacPair α lam θ n).2).eval E) = jstate α lam θ E n
  | 0 => by simp [jacPair, jstate]
  | n + 1 => by
      have ih := eval_jacPair α lam θ E n
      have h1 : (jacPair α lam θ (n + 1)).1
          = (X - C (pot α lam θ n)) * (jacPair α lam θ n).1 - (jacPair α lam θ n).2 := by
        simp [jacPair]
      have h2 : (jacPair α lam θ (n + 1)).2 = (jacPair α lam θ n).1 := by simp [jacPair]
      have h3 : jstate α lam θ E (n + 1)
          = ((E - pot α lam θ n) * (jstate α lam θ E n).1 - (jstate α lam θ E n).2,
              (jstate α lam θ E n).1) := by simp [jstate]
      simp only [h1, h2, h3, Prod.mk.injEq, Polynomial.eval_sub, Polynomial.eval_mul,
        Polynomial.eval_X, Polynomial.eval_C]
      have ih1 : ((jacPair α lam θ n).1).eval E = (jstate α lam θ E n).1 := by
        simpa using congrArg Prod.fst ih
      have ih2 : ((jacPair α lam θ n).2).eval E = (jstate α lam θ E n).2 := by
        simpa using congrArg Prod.snd ih
      exact ⟨by rw [ih1, ih2], ih1⟩

theorem eval_jacPoly (α lam θ E : ℝ) (n : ℕ) :
    (jacPoly α lam θ n).eval E = uSeq α lam θ E n :=
  congrArg Prod.fst (eval_jacPair α lam θ E n)

end Work.TMComp
