import Mathlib
import Submission.Work.Diff.Alg.Pinch.Defs
import Submission.Work.Diff.Alg.Pinch.Strict
import Submission.Work.Diff.Alg.Pinch.Base
import Submission.Work.Diff.Alg.Pinch.inPIC2_metric_basic

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Component bounds for tensors with nonnegative complex sectional curvature

For an arbitrary `4`-index array `R : Submission.Diff.Alg.Curv4 n`, the condition
`InPIC2 R` says that the quartic form
`R4 R x z x z + R4 R x w x w + R4 R y z y z + R4 R y w y w - 2 * R4 R x y z w`
(read: the real form of `R(ζ,η,ζ̄,η̄) ≥ 0`) is nonnegative for all real vectors `x y z w`.

This file extracts two consequences that hold *without* any algebraic-curvature hypothesis:

* Every component is controlled by the scalar curvature: there is a universal constant `C`
  with `|R i j k l| ≤ C * scalAlg R` for all `i j k l`.
* If moreover `scalAlg R = 0` then `R = 0`.

The proof is elementary.  Evaluating the defining quartic form on the standard basis vectors
`eᵢ`, `eⱼ`, `eₖ`, `e_l` gives, for every `i j k l`,

`Rᵢₖᵢₖ + Rᵢₗᵢₗ + Rⱼₖⱼₖ + Rⱼₗⱼₗ ≥ 2 Rᵢⱼₖₗ`,

while evaluating on `eᵢ`, `-eⱼ`, `eₖ`, `e_l` gives the same with `+2 Rᵢⱼₖₗ`.  The four diagonal
terms `R_{abab} = secK e_a e_b` are individually nonnegative, their sum is `scalAlg R`, and the
two inequalities together bound `|Rᵢⱼₖₗ|` by half of that sum of four diagonal terms.  When
`scalAlg R = 0` each diagonal term vanishes and the two inequalities pin `Rᵢⱼₖₗ` to `0`.
-/

namespace Work.Diff.Alg.Pinch

open Finset Submission.Diff.Alg

variable {n : ℕ}

/-! ## Multilinearity of `R4` in a single vector slot (needed for the `-eⱼ` evaluation) -/

/-- `R4` is odd in its first argument. -/
private lemma R4_neg₁ (R : Curv4 n) (a b c d : Fin n → ℝ) :
    R4 R (-a) b c d = - R4 R a b c d := by
  simp only [R4, Pi.neg_apply]
  have h : ∀ i j k l, R i j k l * -(a i) * b j * c k * d l
      = - (R i j k l * a i * b j * c k * d l) := by intro i j k l; ring
  simp only [h, Finset.sum_neg_distrib]

/-- `R4` is odd in its second argument. -/
private lemma R4_neg₂ (R : Curv4 n) (a b c d : Fin n → ℝ) :
    R4 R a (-b) c d = - R4 R a b c d := by
  simp only [R4, Pi.neg_apply]
  have h : ∀ i j k l, R i j k l * a i * -(b j) * c k * d l
      = - (R i j k l * a i * b j * c k * d l) := by intro i j k l; ring
  simp only [h, Finset.sum_neg_distrib]

/-- `R4` is odd in its third argument. -/
private lemma R4_neg₃ (R : Curv4 n) (a b c d : Fin n → ℝ) :
    R4 R a b (-c) d = - R4 R a b c d := by
  simp only [R4, Pi.neg_apply]
  have h : ∀ i j k l, R i j k l * a i * b j * -(c k) * d l
      = - (R i j k l * a i * b j * c k * d l) := by intro i j k l; ring
  simp only [h, Finset.sum_neg_distrib]

/-! ## The defining quartic form on the standard basis

`EF_basis` and `EF_basis_neg` evaluate
`R4 x z x z + R4 x w x w + R4 y z y z + R4 y w y w - 2 * R4 x y z w`
on `(eᵢ, eⱼ, eₖ, e_l)` and on `(eᵢ, -eⱼ, eₖ, e_l)`. -/

/-- The defining form at `(eᵢ, eⱼ, eₖ, e_l)`. -/
private lemma EF_basis (R : Curv4 n) (i j k l : Fin n) :
    R4 R (Pi.single i 1) (Pi.single k 1) (Pi.single i 1) (Pi.single k 1)
      + R4 R (Pi.single i 1) (Pi.single l 1) (Pi.single i 1) (Pi.single l 1)
      + R4 R (Pi.single j 1) (Pi.single k 1) (Pi.single j 1) (Pi.single k 1)
      + R4 R (Pi.single j 1) (Pi.single l 1) (Pi.single j 1) (Pi.single l 1)
      - 2 * R4 R (Pi.single i 1) (Pi.single j 1) (Pi.single k 1) (Pi.single l 1)
    = R i k i k + R i l i l + R j k j k + R j l j l - 2 * R i j k l := by
  rw [R4_basis, R4_basis, R4_basis, R4_basis, R4_basis]

/-- The defining form at `(eᵢ, -eⱼ, eₖ, e_l)`. -/
private lemma EF_basis_neg (R : Curv4 n) (i j k l : Fin n) :
    R4 R (Pi.single i 1) (Pi.single k 1) (Pi.single i 1) (Pi.single k 1)
      + R4 R (Pi.single i 1) (Pi.single l 1) (Pi.single i 1) (Pi.single l 1)
      + R4 R (-(Pi.single j 1)) (Pi.single k 1) (-(Pi.single j 1)) (Pi.single k 1)
      + R4 R (-(Pi.single j 1)) (Pi.single l 1) (-(Pi.single j 1)) (Pi.single l 1)
      - 2 * R4 R (Pi.single i 1) (-(Pi.single j 1)) (Pi.single k 1) (Pi.single l 1)
    = R i k i k + R i l i l + R j k j k + R j l j l + 2 * R i j k l := by
  rw [R4_neg₁, R4_neg₃, R4_neg₁, R4_neg₃, R4_neg₂,
      R4_basis, R4_basis, R4_basis, R4_basis, R4_basis]
  ring

/-! ## The diagonal terms -/

/-- The diagonal components `R_{abab} = secK e_a e_b` are nonnegative. -/
private lemma diag_nonneg (R : Curv4 n) (hR : InPIC2 R) (a b : Fin n) : 0 ≤ R a b a b := by
  rw [← R4_basis R a b a b]
  exact inPIC2_R4_nonneg R hR _ _

/-- Each diagonal component is at most the scalar curvature. -/
private lemma diag_le_scal (R : Curv4 n) (hR : InPIC2 R) (a b : Fin n) :
    R a b a b ≤ scalAlg R := by
  rw [scalAlg]
  have h1 : R a b a b ≤ ∑ j, R a j a j :=
    Finset.single_le_sum (fun j _ => diag_nonneg R hR a j) (Finset.mem_univ b)
  have h2 : (∑ j, R a j a j) ≤ ∑ i, ∑ j, R i j i j :=
    Finset.single_le_sum (fun i _ => Finset.sum_nonneg (fun j _ => diag_nonneg R hR i j))
      (Finset.mem_univ a)
  linarith

/-! ## The lemma -/

theorem inPIC2_comp_bound (n : ℕ) :
    (∃ C : ℝ, ∀ R : Submission.Diff.Alg.Curv4 n, Submission.Diff.Alg.InPIC2 R →
      ∀ i j k l : Fin n, |R i j k l| ≤ C * Submission.Diff.Alg.scalAlg R) ∧
    (∀ R : Submission.Diff.Alg.Curv4 n, Submission.Diff.Alg.InPIC2 R →
      Submission.Diff.Alg.scalAlg R = 0 → R = 0) := by
  refine ⟨⟨(2:ℝ), ?_⟩, ?_⟩
  · intro R hR i j k l
    -- The two evaluations of the defining form bound `R i j k l` from both sides.
    have hb1 : R i j k l ≤ (1/2) * (R i k i k + R i l i l + R j k j k + R j l j l) := by
      have h := hR (Pi.single i 1) (Pi.single j 1) (Pi.single k 1) (Pi.single l 1)
      rw [EF_basis] at h
      linarith
    have hb2 : -(R i j k l) ≤ (1/2) * (R i k i k + R i l i l + R j k j k + R j l j l) := by
      have h := hR (Pi.single i 1) (-(Pi.single j 1)) (Pi.single k 1) (Pi.single l 1)
      rw [EF_basis_neg] at h
      linarith
    have habs : |R i j k l| ≤ (1/2) * (R i k i k + R i l i l + R j k j k + R j l j l) := by
      rw [abs_le]; exact ⟨by linarith, hb1⟩
    -- Each diagonal term is at most `scalAlg R`.
    have hterm : ∀ a b : Fin n, R a b a b ≤ scalAlg R := fun a b => diag_le_scal R hR a b
    have hS : R i k i k + R i l i l + R j k j k + R j l j l ≤ 4 * scalAlg R := by
      linarith [hterm i k, hterm i l, hterm j k, hterm j l]
    calc |R i j k l| ≤ (1/2) * (R i k i k + R i l i l + R j k j k + R j l j l) := habs
      _ ≤ (1/2) * (4 * scalAlg R) := by linarith
      _ = 2 * scalAlg R := by ring
  · intro R hR hscal
    -- `scalAlg R = 0` makes every diagonal component vanish.
    have hd : ∀ a b : Fin n, R a b a b = 0 := by
      intro a b
      have h0 := diag_nonneg R hR a b
      have h1 := diag_le_scal R hR a b
      rw [hscal] at h1
      linarith
    funext i j k l
    -- The two evaluations now squeeze `R i j k l` to `0`.
    have hb1 : R i j k l ≤ 0 := by
      have h := hR (Pi.single i 1) (Pi.single j 1) (Pi.single k 1) (Pi.single l 1)
      rw [EF_basis] at h
      rw [hd, hd, hd, hd] at h
      linarith
    have hb2 : 0 ≤ R i j k l := by
      have h := hR (Pi.single i 1) (-(Pi.single j 1)) (Pi.single k 1) (Pi.single l 1)
      rw [EF_basis_neg] at h
      rw [hd, hd, hd, hd] at h
      linarith
    simp only [Pi.zero_apply]
    linarith

end Work.Diff.Alg.Pinch
