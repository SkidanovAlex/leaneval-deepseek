import Mathlib
import Submission.Work.Diff.Alg.q2p_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `Work.Diff.Alg.q2p_estimate`

The algebraic core of Brendle–Schoen, *Manifolds with 1/4-pinched curvature are space forms*
(arXiv:0705.0766), Prop. 21 / Cor. 22: the sharp estimate turning a bound on sectional
curvatures (lower bound `a`) jointly with Berger's estimate on the "cross" component
(`|R(x,y,z,w)| ≤ (2/3)(b-a)∏‖·‖` for pairwise orthogonal vectors) into the `PIC2`-type
inequality with constant `(4a-b)/3`:

for pairwise orthogonal `x, y, z, w`
`((4a-b)/3) · (‖x‖² + ‖y‖²)(‖z‖² + ‖w‖²) ≤ R(x,z,x,z) + R(x,w,x,w) + R(y,z,y,z) + R(y,w,y,w) - 2 R(x,y,z,w)`.

## Proof

Write `dx = ⟪x,x⟫`, …, `Q = (dx+dy)(dz+dw)`. The diagonal hypothesis applied to the four
orthogonal pairs `(x,z)`, `(x,w)`, `(y,z)`, `(y,w)` gives

`a·Q ≤ S := R(x,z,x,z) + R(x,w,x,w) + R(y,z,y,z) + R(y,w,y,w)`,

while Berger's bound and the two-pair AM–GM inequality `4√(dx·dy·dz·dw) ≤ Q` give

`2 R(x,y,z,w) ≤ (b-a)/3 · Q`.

Combining, using `a = (4a-b)/3 + (b-a)/3`,

`EFun = S - 2R ≥ aQ - (b-a)Q/3 = ((4a-b)/3)·Q`.

No symmetry of `R` is used (only the two hypotheses); the inequality is an equality for the
round-sphere tensor `Iso n` with `a = b`, on an orthonormal four-frame.
-/

namespace Work.Diff.Alg

open Submission.Diff.Alg

variable {n : ℕ}

/-- `⟪u,u⟫ ≥ 0`: `dot u u` is a sum of squares. -/
theorem q2pe_dot_self_nonneg (u : Fin n → ℝ) : 0 ≤ Submission.Diff.Alg.dot u u := by
  simp only [Submission.Diff.Alg.dot]
  exact Finset.sum_nonneg fun i _ => mul_self_nonneg (u i)

/-- Two-pair AM–GM in the multiplicative form: for nonnegative `u v p q`,
`4 √u √v √p √q ≤ (u+v)(p+q)`. -/
theorem q2pe_amgm (u v p q : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) (hp : 0 ≤ p) (hq : 0 ≤ q) :
    4 * (Real.sqrt u * Real.sqrt v * Real.sqrt p * Real.sqrt q) ≤ (u + v) * (p + q) := by
  have h1 : 2 * (Real.sqrt u * Real.sqrt v) ≤ u + v := by
    have hsq : Real.sqrt u * Real.sqrt v = Real.sqrt (u * v) := (Real.sqrt_mul hu v).symm
    rw [hsq]
    have hle : Real.sqrt (u * v) ≤ (u + v) / 2 := by
      rw [Real.sqrt_le_left (by linarith)]
      nlinarith [sq_nonneg (u - v)]
    linarith
  have h2 : 2 * (Real.sqrt p * Real.sqrt q) ≤ p + q := by
    have hsq : Real.sqrt p * Real.sqrt q = Real.sqrt (p * q) := (Real.sqrt_mul hp q).symm
    rw [hsq]
    have hle : Real.sqrt (p * q) ≤ (p + q) / 2 := by
      rw [Real.sqrt_le_left (by linarith)]
      nlinarith [sq_nonneg (p - q)]
    linarith
  have hprod := mul_le_mul h1 h2 (by positivity) (by linarith)
  have : 2 * (Real.sqrt u * Real.sqrt v) * (2 * (Real.sqrt p * Real.sqrt q))
      = 4 * (Real.sqrt u * Real.sqrt v * Real.sqrt p * Real.sqrt q) := by ring
  linarith [hprod]

theorem q2p_estimate {n : ℕ} (R : Submission.Diff.Alg.Curv4 n) {a b : ℝ} (hab : a ≤ b)
    (hdiag : ∀ u v : Fin n → ℝ, Submission.Diff.Alg.dot u v = 0 →
      a * (Submission.Diff.Alg.dot u u * Submission.Diff.Alg.dot v v) ≤
        Submission.Diff.Alg.R4 R u v u v)
    (hcross : ∀ x y z w : Fin n → ℝ, Work.Diff.Alg.Q2P.PairwiseOrth x y z w →
      |Submission.Diff.Alg.R4 R x y z w| ≤ (2 / 3) * (b - a) *
        (Real.sqrt (Submission.Diff.Alg.dot x x) * Real.sqrt (Submission.Diff.Alg.dot y y) *
         Real.sqrt (Submission.Diff.Alg.dot z z) * Real.sqrt (Submission.Diff.Alg.dot w w)))
    {x y z w : Fin n → ℝ} (h : Work.Diff.Alg.Q2P.PairwiseOrth x y z w) :
    ((4 * a - b) / 3) * ((Submission.Diff.Alg.dot x x + Submission.Diff.Alg.dot y y) *
      (Submission.Diff.Alg.dot z z + Submission.Diff.Alg.dot w w)) ≤
      Work.Diff.Alg.Q2P.EFun R x y z w := by
  obtain ⟨hxy, hxz, hxw, hyz, hyw, hzw⟩ := h
  -- the four diagonal (sectional-curvature) bounds
  have hD : a * ((Submission.Diff.Alg.dot x x + Submission.Diff.Alg.dot y y) *
        (Submission.Diff.Alg.dot z z + Submission.Diff.Alg.dot w w)) ≤
      Submission.Diff.Alg.R4 R x z x z + Submission.Diff.Alg.R4 R x w x w +
        Submission.Diff.Alg.R4 R y z y z + Submission.Diff.Alg.R4 R y w y w := by
    nlinarith [hdiag x z hxz, hdiag x w hxw, hdiag y z hyz, hdiag y w hyw]
  -- Berger's bound on the cross term, plus AM–GM
  have hamgm := q2pe_amgm (Submission.Diff.Alg.dot x x) (Submission.Diff.Alg.dot y y)
    (Submission.Diff.Alg.dot z z) (Submission.Diff.Alg.dot w w)
    (q2pe_dot_self_nonneg x) (q2pe_dot_self_nonneg y) (q2pe_dot_self_nonneg z)
    (q2pe_dot_self_nonneg w)
  have hP : Submission.Diff.Alg.R4 R x y z w ≤ (2 / 3) * (b - a) *
      (Real.sqrt (Submission.Diff.Alg.dot x x) * Real.sqrt (Submission.Diff.Alg.dot y y) *
       Real.sqrt (Submission.Diff.Alg.dot z z) * Real.sqrt (Submission.Diff.Alg.dot w w)) :=
    le_trans (le_abs_self _) (hcross x y z w ⟨hxy, hxz, hxw, hyz, hyw, hzw⟩)
  have hQ : 2 * Submission.Diff.Alg.R4 R x y z w ≤ (b - a) / 3 *
      ((Submission.Diff.Alg.dot x x + Submission.Diff.Alg.dot y y) *
       (Submission.Diff.Alg.dot z z + Submission.Diff.Alg.dot w w)) := by
    have h3 : 0 ≤ (b - a) / 3 := by linarith
    have h4 := mul_le_mul_of_nonneg_left hamgm h3
    nlinarith [h4, hP]
  simp only [Work.Diff.Alg.Q2P.EFun]
  nlinarith [hD, hQ]

end Work.Diff.Alg
