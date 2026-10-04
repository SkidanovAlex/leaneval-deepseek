import Mathlib
import Submission.Work.Diff.Alg.q2p_defs
import Submission.Work.Diff.Alg.q2p_berger
import Submission.Work.Diff.Alg.Q2PF.norm_on4
import Submission.Work.Diff.Alg.Q2PZ.degenerate_bound

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Berger's inequality on a pairwise orthogonal four-tuple

`Work.Diff.Alg.q2p_berger` bounds the curvature component `R(x,y,z,w)` of an algebraic curvature
tensor whose sectional curvatures lie in `[a,b]` on an **orthonormal** four-frame by
`(2/3) (b - a)` (Berger's inequality, Brendle–Schoen Cor. 22).  This module removes the
normalisation hypothesis: for four merely **pairwise orthogonal** vectors `x, y, z, w`
(of arbitrary length, possibly zero) one has

`|R(x,y,z,w)| ≤ (2/3) (b - a) |x| |y| |z| |w|`,

where `|u| = √⟪u,u⟫` is the Euclidean length.

The reduction is the obvious one. `R4` is `4`-multilinear, so replacing each vector by its
normalisation `(√⟪x,x⟫)⁻¹ • x` rescales `R(x,y,z,w)` by the product of the four lengths
(`r4_normalize_orth`); pairwise orthogonality and nonvanishing are preserved, so the normalised
four-tuple is orthonormal (`Work.Diff.Alg.Q2PF.norm_on4`) and Berger's inequality applies.  If one
of the vectors is zero, both sides vanish (`Work.Diff.Alg.Q2PZ.degenerate_bound`), with no
hypothesis on the sign of `b - a`.
-/

namespace Work.Diff.Alg

open Submission.Diff.Alg

/-- `R4` is homogeneous of degree one in each slot, so normalising the four slots by the length
of the corresponding vector multiplies `R4` by the product of the four lengths.

This is the rescaled form of the four-fold multilinearity of `R4`
(`Work.Diff.Alg.Q2P.R4_smul₁` … `R4_smul₄`): writing `x = √⟪x,x⟫ • ((√⟪x,x⟫)⁻¹ • x)` (which holds
because the length of a nonzero vector is nonzero) and pulling the four scalars out. -/
theorem r4_normalize_orth {n : ℕ} (R : Curv4 n) {x y z w : Fin n → ℝ}
    (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0) (hw : w ≠ 0) :
    R4 R x y z w =
      (Real.sqrt (dot x x) * Real.sqrt (dot y y) * Real.sqrt (dot z z) * Real.sqrt (dot w w)) *
      R4 R ((Real.sqrt (dot x x))⁻¹ • x) ((Real.sqrt (dot y y))⁻¹ • y)
        ((Real.sqrt (dot z z))⁻¹ • z) ((Real.sqrt (dot w w))⁻¹ • w) := by
  have hxne : Real.sqrt (dot x x) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr (Q2PF.dot_self_pos' hx))
  have hyne : Real.sqrt (dot y y) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr (Q2PF.dot_self_pos' hy))
  have hzne : Real.sqrt (dot z z) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr (Q2PF.dot_self_pos' hz))
  have hwne : Real.sqrt (dot w w) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr (Q2PF.dot_self_pos' hw))
  have hx' : Real.sqrt (dot x x) • ((Real.sqrt (dot x x))⁻¹ • x) = x := by
    rw [smul_smul, mul_inv_cancel₀ hxne, one_smul]
  have hy' : Real.sqrt (dot y y) • ((Real.sqrt (dot y y))⁻¹ • y) = y := by
    rw [smul_smul, mul_inv_cancel₀ hyne, one_smul]
  have hz' : Real.sqrt (dot z z) • ((Real.sqrt (dot z z))⁻¹ • z) = z := by
    rw [smul_smul, mul_inv_cancel₀ hzne, one_smul]
  have hw' : Real.sqrt (dot w w) • ((Real.sqrt (dot w w))⁻¹ • w) = w := by
    rw [smul_smul, mul_inv_cancel₀ hwne, one_smul]
  conv_lhs => rw [← hx', ← hy', ← hz', ← hw']
  rw [Q2P.R4_smul₁, Q2P.R4_smul₂, Q2P.R4_smul₃, Q2P.R4_smul₄]
  ring

theorem q2p_berger_orth {n : ℕ} (R : Submission.Diff.Alg.Curv4 n)
    (hR : Submission.Diff.Alg.IsAlgCurv R) (a b : ℝ)
    (hsec : ∀ u v : Fin n → ℝ, Submission.Diff.Alg.IsONPair u v →
      a ≤ Submission.Diff.Alg.secK R u v ∧ Submission.Diff.Alg.secK R u v ≤ b)
    {x y z w : Fin n → ℝ} (h : Work.Diff.Alg.Q2P.PairwiseOrth x y z w) :
    |Submission.Diff.Alg.R4 R x y z w| ≤ (2 / 3) * (b - a) *
      (Real.sqrt (Submission.Diff.Alg.dot x x) * Real.sqrt (Submission.Diff.Alg.dot y y) *
       Real.sqrt (Submission.Diff.Alg.dot z z) * Real.sqrt (Submission.Diff.Alg.dot w w)) := by
  by_cases hdeg : x = 0 ∨ y = 0 ∨ z = 0 ∨ w = 0
  · exact Q2PZ.degenerate_bound R a b hdeg
  · push Not at hdeg
    obtain ⟨hx0, hy0, hz0, hw0⟩ := hdeg
    have hON4 : Q2P.IsON4 ((Real.sqrt (dot x x))⁻¹ • x) ((Real.sqrt (dot y y))⁻¹ • y)
        ((Real.sqrt (dot z z))⁻¹ • z) ((Real.sqrt (dot w w))⁻¹ • w) :=
      Q2PF.norm_on4 h hx0 hy0 hz0 hw0
    have hB := q2p_berger R hR a b hsec hON4
    have hsc := r4_normalize_orth R hx0 hy0 hz0 hw0
    have hprod : 0 ≤ Real.sqrt (dot x x) * Real.sqrt (dot y y) * Real.sqrt (dot z z) *
        Real.sqrt (dot w w) :=
      mul_nonneg (mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
        (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)
    have habs : |R4 R x y z w| = (Real.sqrt (dot x x) * Real.sqrt (dot y y) *
        Real.sqrt (dot z z) * Real.sqrt (dot w w)) *
        |R4 R ((Real.sqrt (dot x x))⁻¹ • x) ((Real.sqrt (dot y y))⁻¹ • y)
          ((Real.sqrt (dot z z))⁻¹ • z) ((Real.sqrt (dot w w))⁻¹ • w)| := by
      rw [hsc, abs_mul, abs_of_nonneg hprod]
    rw [habs]
    calc (Real.sqrt (dot x x) * Real.sqrt (dot y y) * Real.sqrt (dot z z) * Real.sqrt (dot w w)) *
          |R4 R ((Real.sqrt (dot x x))⁻¹ • x) ((Real.sqrt (dot y y))⁻¹ • y)
            ((Real.sqrt (dot z z))⁻¹ • z) ((Real.sqrt (dot w w))⁻¹ • w)|
        ≤ (Real.sqrt (dot x x) * Real.sqrt (dot y y) * Real.sqrt (dot z z) * Real.sqrt (dot w w)) *
          ((2 / 3) * (b - a)) := mul_le_mul_of_nonneg_left hB hprod
      _ = (2 / 3) * (b - a) *
          (Real.sqrt (dot x x) * Real.sqrt (dot y y) * Real.sqrt (dot z z) * Real.sqrt (dot w w)) := by
          ring

end Work.Diff.Alg
