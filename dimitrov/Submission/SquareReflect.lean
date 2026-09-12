import Mathlib
import Submission.Powers
import Submission.PowRev

/-!
# Reflection: a square of the reversed product gives a square of the product

Let `P : ℤ[X]` be monic with `d := P.natDegree`, `P₂ := pow2 P`, `P₄ := pow4 P`,
`R₂ := P₂.reflect d`, `R₄ := P₄.reflect d`, `G := R₂ * R₄`.

This module proves: if `G` is a perfect square in `ℤ[X]` then
`P₂ * P₄` is a perfect square in `ℤ[X]`.

This is the last purely algebraic step of the analytic engine: Pólya–Bertrandias
rationality makes the power series `f(1/X) = sqrt (R₂ R₄)` rational, hence a
polynomial; then `G = R₂ R₄` is a square, and by this lemma `P₂ P₄` is a
square; the dichotomy (`Submission.SquarePoly`, `Submission.RootOfUnity`) turns
that into a contradiction.

## Proof

The reflection map `Polynomial.reflect d` is involutive
(`Polynomial.reflect_reflect`) and multiplicative across degrees
(`Polynomial.reflect_mul`: if `natDegree A ≤ d₁`, `natDegree B ≤ d₂` then
`(A * B).reflect (d₁+d₂) = A.reflect d₁ * B.reflect d₂`).

Given `G = f²`: `P₂` and `P₄` are monic of degree `d`
(`Submission.RootCorr.pow2_natDegree`, `Submission.Powers.pow2_monic`), hence
`natDegree (reflect d P₂) ≤ d` (`Polynomial.natDegree_reflect_le`), so
`natDegree G ≤ 2d`.  Since `ℤ[X]` is a domain,
`natDegree (f²) = 2 · natDegree f` (`Polynomial.natDegree_pow`), giving
`natDegree f ≤ d`.  Then with `g := f.reflect d`:

* `g² = (f²).reflect (2d)`   (reflect_mul),
* `(f²).reflect (2d) = G.reflect (2d)` (congruence),
* `G.reflect (2d) = P₂.reflect d * P₄.reflect d .reflect (d+d) = P₂ * P₄`
  (reflect_mul then involutivity),
so `g² = P₂ * P₄`.
-/

noncomputable section

open Polynomial
open scoped Polynomial

namespace Submission.SquareReflect

open Submission.Powers
open Submission.RootCorr

/-- If the reversed power product
`(pow2 P).reflect d * (pow4 P).reflect d` (with `d := P.natDegree`) is a
perfect square in `ℤ[X]`, then so is `pow2 P * pow4 P`. -/
theorem pow_product_square_of_reflect_square (P : ℤ[X]) (hP : P.Monic) :
    (∃ f : ℤ[X],
      ((pow2 P).reflect P.natDegree * (pow4 P).reflect P.natDegree) = f ^ 2) →
    ∃ g : ℤ[X], pow2 P * pow4 P = g ^ 2 := by
  rintro ⟨f, hf⟩
  -- P₂ and P₄ are monic of degree d := P.natDegree
  have hdP2 : (pow2 P).natDegree = P.natDegree := pow2_natDegree P hP
  have hdP4 : (pow4 P).natDegree = P.natDegree := by
    change (pow2 (pow2 P)).natDegree = P.natDegree
    rw [pow2_natDegree (pow2 P) (pow2_monic P hP)]
    exact pow2_natDegree P hP
  -- the reflected polynomials have degree ≤ d
  have hdR2 : ((pow2 P).reflect P.natDegree).natDegree ≤ P.natDegree := by
    simpa [hdP2] using
      (natDegree_reflect_le (N := P.natDegree) (p := (pow2 P)))
  have hdR4 : ((pow4 P).reflect P.natDegree).natDegree ≤ P.natDegree := by
    simpa [hdP4] using
      (natDegree_reflect_le (N := P.natDegree) (p := (pow4 P)))
  -- hence the product G has natDegree ≤ 2d
  have hdegG : (((pow2 P).reflect P.natDegree) * ((pow4 P).reflect P.natDegree)).natDegree ≤
      2 * P.natDegree := by
    calc
      (((pow2 P).reflect P.natDegree) * ((pow4 P).reflect P.natDegree)).natDegree ≤
          ((pow2 P).reflect P.natDegree).natDegree
            + ((pow4 P).reflect P.natDegree).natDegree := natDegree_mul_le
      _ ≤ P.natDegree + P.natDegree := Nat.add_le_add hdR2 hdR4
      _ = 2 * P.natDegree := by omega
  -- from G = f² and natDegree (f²) = 2·natDegree f we get natDegree f ≤ d
  have hfd : natDegree f ≤ P.natDegree := by
    have hfnd : natDegree (f ^ 2) = 2 * natDegree f := by
      exact natDegree_pow (p := f) (n := 2)
    have hle : 2 * natDegree f ≤ 2 * P.natDegree := by
      rw [← hfnd]
      rw [← hf]
      exact hdegG
    omega
  -- g := reflect d f squares to P₂ * P₄
  refine ⟨f.reflect P.natDegree, ?_⟩
  apply Eq.symm
  calc
    (f.reflect P.natDegree) ^ 2
        = (f.reflect P.natDegree) * (f.reflect P.natDegree) := by rw [pow_two]
    _ = (f * f).reflect (2 * P.natDegree) := by
        rw [two_mul]
        rw [← reflect_mul f f (F := P.natDegree) (G := P.natDegree) hfd hfd]
    _ = (f ^ 2).reflect (2 * P.natDegree) := by rw [pow_two]
    _ = (((pow2 P).reflect P.natDegree) * ((pow4 P).reflect P.natDegree)).reflect
        (2 * P.natDegree) := by rw [hf]
    _ = pow2 P * pow4 P := by
        rw [two_mul]
        rw [reflect_mul ((pow2 P).reflect P.natDegree) ((pow4 P).reflect P.natDegree)
            (F := P.natDegree) (G := P.natDegree) hdR2 hdR4]
        simp

end Submission.SquareReflect

end
