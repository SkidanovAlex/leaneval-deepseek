import Mathlib
import Submission.Work.Diff.Alg.Pinch.Rot2Defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Invariance of the scalar contraction under an orthogonal change of frame

`Submission.Diff.Alg.scalAlg R = ∑ i j, R i j i j` is the full contraction of the curvature array
(the scalar curvature in an orthonormal frame). Changing the frame by `A ∈ O(n)`,
`rot A R i j k l = ∑ a b c d, A i a * A j b * A k c * A l d * R a b c d`, leaves it unchanged:

`scalAlg (rot A R) = scalAlg R`.

The proof is the elementary index computation: writing out the sixfold sum and using
`Aᵀ A = 1`, i.e. `∑ i, A i a * A i c = δ_{ac}`, the `i`- and `j`-contractions collapse to
`R a b a b`.

No algebraic-curvature hypothesis on `R` is needed -- only orthogonality of `A`.
-/

namespace Work.Diff.Alg.Pinch

open Finset
open scoped Matrix
open Submission.Diff.Alg

theorem scalAlg_rot (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) (hA : A ∈ Matrix.orthogonalGroup (Fin n) ℝ)
    (R : Submission.Diff.Alg.Curv4 n) :
    Submission.Diff.Alg.scalAlg (Submission.Diff.Alg.rot A R) = Submission.Diff.Alg.scalAlg R := by
  -- Orthogonality of `A`, column form.
  have horth : Aᵀ * A = 1 := (Matrix.mem_orthogonalGroup_iff' (Fin n) ℝ).mp hA
  have hcol : ∀ a c : Fin n, (∑ i, A i a * A i c) = (if a = c then (1 : ℝ) else 0) := by
    intro a c
    have h := congr_fun (congr_fun horth a) c
    rw [Matrix.mul_apply, Matrix.one_apply] at h
    simpa [Matrix.transpose_apply] using h
  -- Reorder a sixfold sum so that the two contracted indices come last.
  have hreorder_gen : ∀ (g : Fin n → Fin n → Fin n → Fin n → Fin n → Fin n → ℝ),
      (∑ i, ∑ j, ∑ a, ∑ b, ∑ c, ∑ d, g i j a b c d)
        = ∑ a, ∑ b, ∑ c, ∑ d, ∑ i, ∑ j, g i j a b c d := by
    intro g
    calc ∑ i, ∑ j, ∑ a, ∑ b, ∑ c, ∑ d, g i j a b c d
        = ∑ i, ∑ a, ∑ j, ∑ b, ∑ c, ∑ d, g i j a b c d := by
            apply Finset.sum_congr rfl; intro i _
            exact Finset.sum_comm
      _ = ∑ i, ∑ a, ∑ b, ∑ j, ∑ c, ∑ d, g i j a b c d := by
            apply Finset.sum_congr rfl; intro i _
            apply Finset.sum_congr rfl; intro a _
            exact Finset.sum_comm
      _ = ∑ i, ∑ a, ∑ b, ∑ c, ∑ j, ∑ d, g i j a b c d := by
            apply Finset.sum_congr rfl; intro i _
            apply Finset.sum_congr rfl; intro a _
            apply Finset.sum_congr rfl; intro b _
            exact Finset.sum_comm
      _ = ∑ i, ∑ a, ∑ b, ∑ c, ∑ d, ∑ j, g i j a b c d := by
            apply Finset.sum_congr rfl; intro i _
            apply Finset.sum_congr rfl; intro a _
            apply Finset.sum_congr rfl; intro b _
            apply Finset.sum_congr rfl; intro c _
            exact Finset.sum_comm
      _ = ∑ a, ∑ i, ∑ b, ∑ c, ∑ d, ∑ j, g i j a b c d := by
            exact Finset.sum_comm
      _ = ∑ a, ∑ b, ∑ i, ∑ c, ∑ d, ∑ j, g i j a b c d := by
            apply Finset.sum_congr rfl; intro a _
            exact Finset.sum_comm
      _ = ∑ a, ∑ b, ∑ c, ∑ i, ∑ d, ∑ j, g i j a b c d := by
            apply Finset.sum_congr rfl; intro a _
            apply Finset.sum_congr rfl; intro b _
            exact Finset.sum_comm
      _ = ∑ a, ∑ b, ∑ c, ∑ d, ∑ i, ∑ j, g i j a b c d := by
            apply Finset.sum_congr rfl; intro a _
            apply Finset.sum_congr rfl; intro b _
            apply Finset.sum_congr rfl; intro c _
            exact Finset.sum_comm
  -- A constant factors out of a twofold sum.
  have hfac : ∀ (K : ℝ) (u v : Fin n → ℝ),
      (∑ i, ∑ j, u i * v j * K) = (∑ i, u i) * (∑ j, v j) * K := by
    intro K u v
    rw [Finset.sum_comm]
    simp only [← Finset.sum_mul, ← Finset.mul_sum]
  -- The `(a,b,c,d)` block factors into the `a,c`- and `b,d`-contractions.
  have hterm : ∀ a b c d : Fin n,
      (∑ i, ∑ j, A i a * A j b * A i c * A j d * R a b c d)
        = (∑ i, A i a * A i c) * (∑ j, A j b * A j d) * R a b c d := by
    intro a b c d
    rw [show (∑ i, ∑ j, A i a * A j b * A i c * A j d * R a b c d)
          = ∑ i, ∑ j, (A i a * A i c) * (A j b * A j d) * R a b c d from by
        apply Finset.sum_congr rfl; intro i _
        apply Finset.sum_congr rfl; intro j _
        ring]
    exact hfac (R a b c d) (fun i => A i a * A i c) (fun j => A j b * A j d)
  -- With the columns orthonormal, only `c = a`, `d = b` survive.
  have hfinal : (∑ a, ∑ b, ∑ c, ∑ d,
        ((if a = c then (1 : ℝ) else 0) * (if b = d then (1 : ℝ) else 0)) * R a b c d)
      = ∑ a, ∑ b, R a b a b := by
    apply Finset.sum_congr rfl; intro a _
    apply Finset.sum_congr rfl; intro b _
    rw [Finset.sum_eq_single a]
    · rw [Finset.sum_eq_single b]
      · simp
      · intro d _ hd
        simp [show b ≠ d from fun h => hd h.symm]
      · intro h; exact absurd (Finset.mem_univ b) h
    · intro c _ hc
      simp [show a ≠ c from fun h => hc h.symm]
    · intro h; exact absurd (Finset.mem_univ a) h
  simp only [scalAlg, rot]
  rw [hreorder_gen (fun i j a b c d => A i a * A j b * A i c * A j d * R a b c d)]
  simp only [hterm, hcol]
  rw [hfinal]

end Work.Diff.Alg.Pinch
