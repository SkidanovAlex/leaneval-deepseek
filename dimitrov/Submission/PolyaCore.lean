import Mathlib
import Submission.Kronecker
import Submission.XTransfer

/-!
# E0: the moment/Hankel determinant identity (algebraic core of the Pólya shell)

Let `a : ℕ → ℤ` be an integer sequence (in the engine, the coefficients of the
formal square root `F(w) = Σ aₖ wᵏ` of `G := R₂R₄`, so `aₖ ∈ ℤ`), and let
`p₀, …, p_{k−1}` be monic polynomials with `deg pᵢ = i`.

Define the *moment pairing* restricted to degree `< k`:

    B_k(p, q) := ∑_{r,s < k} p.coeff r · q.coeff s · a (r + s)

(the residue at `∞` of `g(X) p(X) q(X) X⁻¹ dX` when `g(X) = Σ aₖ X⁻ᵏ` and the
series is integrated termwise on a large circle: `(1/2πi)∮ g X^{r+s−1} dX
= a_{r+s}`).  This module proves the purely algebraic identity

    det (B_k(pᵢ, pⱼ))_{i,j < k} = hankelDet a k

for any family of monic `pᵢ` with `deg pᵢ = i`.  (The change of basis from the
monomials `Xⁱ` to the `pᵢ` is unitriangular, so the determinant is unchanged.)

This is the bridge used by the Pólya/Hankel shell: the *integer* Hankel
determinant `hankelDet a k` (which vanishes eventually iff `a` is rational, by
`Submission.Kronecker.seriesRational_of_hankel_eventually_zero`) is expressed
as the determinant of the matrix of moment pairings with the near-extremal
monic polynomials `pᵢ` — the matrix whose entries are then bounded by the
contour/Cauchy estimates near the hedgehog (the analytic content E2, not in
this module).

Mathlib provides the key unitriangular fact ready-made
(`Matrix.det_matrixOfPolynomials`, LinearAlgebra/Matrix/Block.lean).
-/

noncomputable section

namespace Submission.PolyaCore

open Polynomial
open Submission.Kronecker

/-- The `k × k` matrix of moment pairings

    M_{ij} := ∑_{r < k} (∑_{s < k} (pᵢ).coeff s · a (s + r)) · (pⱼ).coeff r

i.e. `B_k(pᵢ,pⱼ) := ∑_{r,s < k} pᵢ.coeff s · pⱼ.coeff r · a (s + r)` (coincides
with `∑_{r,s} p_r q_s a_{r+s}` for degree-`< k` polynomials; `a (r+s) = a (s+r)`
so the summation order is immaterial).  Written in this contracted form it is
definitionally the entry of `Cᵀ H C` for the basis-change matrix `C`. -/
def momentMatrix (k : ℕ) (a : ℕ → ℤ) (p : Fin k → ℤ[X]) : Matrix (Fin k) (Fin k) ℤ :=
  fun i j =>
    ∑ r : Fin k, (∑ s : Fin k, (p i).coeff s.val * a (s.val + r.val)) * (p j).coeff r.val

/-- Change of basis: `C` has `(r, i)`-entry `(p i).coeff r` (column `i` is the
coefficient vector of `pᵢ` in the monomial basis). -/
def basisMatrix (k : ℕ) (p : Fin k → ℤ[X]) : Matrix (Fin k) (Fin k) ℤ :=
  fun r i => (p i).coeff r.val

/-- The moment matrix factorizes as `Cᵀ H C` with `H` the Hankel matrix and
`C` the (unitriangular) basis change.  (Definitional after unfolding.) -/
lemma momentMatrix_eq_basis_mul_hankel (k : ℕ) (a : ℕ → ℤ) (p : Fin k → ℤ[X]) :
    momentMatrix k a p = Matrix.transpose (basisMatrix k p) * hankelMat a k * basisMatrix k p := by
  classical
  ext i j
  simp [momentMatrix, basisMatrix, hankelMat, Matrix.mul_apply, Matrix.transpose_apply]

/-- **E0: the moment/Hankel identity.**  For monic `pᵢ` of degree `i`, the
determinant of the matrix of moment pairings equals the (unshifted) Hankel
determinant of `a`. -/
theorem hankelDet_eq_det_momentMatrix (k : ℕ) (a : ℕ → ℤ) (p : Fin k → ℤ[X])
    (hmonic : ∀ i : Fin k, (p i).Monic) (hdeg : ∀ i : Fin k, (p i).natDegree = i.val) :
    hankelDet a k = (momentMatrix k a p).det := by
  classical
  have hMom : momentMatrix k a p =
      Matrix.transpose (basisMatrix k p) * hankelMat a k * basisMatrix k p :=
    momentMatrix_eq_basis_mul_hankel k a p
  -- det(C) = 1: columns are monic polynomials of strictly increasing degree.
  -- `basisMatrix k p` is exactly Mathlib's polynomial matrix with (i,j)-entry
  -- `(p j).coeff i`, whose determinant `det_matrixOfPolynomials` computes as 1.
  have hdetC : (basisMatrix k p).det = 1 := by
    have hb : basisMatrix k p = Matrix.of (fun i j : Fin k => (p j).coeff i.val) := by
      ext i j
      rfl
    rw [hb]
    exact Matrix.det_matrixOfPolynomials (n := k) p (fun i => hdeg i) (fun i => hmonic i)
  rw [hMom]
  -- goal: hankelDet a k = (Cᵀ * H * C).det ; use det C = 1 to reduce to det H.
  have hdetprod : ((Matrix.transpose (basisMatrix k p)) * hankelMat a k * basisMatrix k p).det
      = (hankelMat a k).det := by
    calc
      ((Matrix.transpose (basisMatrix k p)) * hankelMat a k * basisMatrix k p).det
          = ((Matrix.transpose (basisMatrix k p)) * hankelMat a k).det * (basisMatrix k p).det :=
            Matrix.det_mul _ _
      _ = (Matrix.transpose (basisMatrix k p)).det * (hankelMat a k).det * (basisMatrix k p).det := by
            rw [Matrix.det_mul]
      _ = (hankelMat a k).det := by
            rw [Matrix.det_transpose, hdetC]
            norm_num
  rw [hdetprod]
  rfl


end Submission.PolyaCore

end

/-! ## The capacity hypothesis `HedgehogBound`

The Pólya shell (E2, `Submission.PolyaShell`) proves that the integer Hankel
determinants of the square-root sequence vanish, *assuming* that the hedgehog
`K := star S` of branch points is polynomially controllable: there is an
`ε > 0` such that on the `ε`-fattened hedgehog `FatStar S ε` there are monic
polynomials `pᵢ` of every degree `i` with sup-norm `≤ C·θⁱ` for a fixed
`θ < 1` (equivalently: the Chebyshev constant / logarithmic capacity of the
fattened hedgehog is `< 1`).

This is exactly what Dubinin's inequality supplies in the engine situation
(`Submission.AnalyticEngine`): for `S := conjugateValues α` with
`m := |argSet α|` phases, the hedgehog `star S` has at most `s ≤ 2m` distinct
spikes (Submission.Phases) all of length at most `house⁴`
(Submission.StarBounds), and under `house α < 2^(1/(4m))` Dubinin's bound
`cap ≤ 4^(-1/s)·house⁴ < 1` holds, which (capacity = Chebyshev deviation,
near-extremal polynomials) yields exactly `HedgehogBound (conjugateValues α)`.

Proving `HedgehogBound` from those facts is the deep analytic input (E1) —
symmetrization/conformal-map theory — and is NOT part of this module.  Here
we only *state* it as the hypothesis of the Pólya shell.
-/

namespace Submission.PolyaCore

open scoped Polynomial Topology

open Submission.XTransfer

/-- The `ε`-fattening of the hedgehog `star S` (all points within distance
`≤ ε` of the hedgehog). -/
def FatStar (S : Finset ℂ) (ε : ℝ) : Set ℂ :=
  {X : ℂ | ∃ Y ∈ star S, ‖X - Y‖ ≤ ε}

/-- **E1 (Dubinin content, stated).**  The hedgehog over `S` is
polynomially controllable: for some `ε > 0` and some `θ < 1`, for every
degree `j` there is a monic complex polynomial of degree `j` whose values on
the `ε`-fattened hedgehog are bounded by `C·θ^j`. -/
def HedgehogBound (S : Finset ℂ) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧ ∃ C : ℝ, 0 < C ∧ ∃ θ : ℝ, 0 ≤ θ ∧ θ < 1 ∧
    ∀ j : ℕ, ∃ p : ℂ[X], p.Monic ∧ p.natDegree = j ∧
      ∀ X : ℂ, X ∈ FatStar S ε → ‖p.eval X‖ ≤ C * θ ^ j

end Submission.PolyaCore

