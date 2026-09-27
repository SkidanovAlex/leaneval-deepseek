import Mathlib
import Submission.Work.Mostow.BaryBase
import Submission.Work.Mostow.BusemannQuad
import Submission.Work.Mostow.LogRatioArcosh

/-!
# The Busemann function is 1-Lipschitz

`busemann ξ u = log (tpart u - ⟪u,ξ⟫)`, and `hdist u v = arcosh (tpart u * tpart v - ⟪u,v⟫)`.
Put `A = tpart u - ⟪u,ξ⟫`, `B = tpart v - ⟪v,ξ⟫`, `C = tpart u * tpart v - ⟪u,v⟫ = cosh (hdist u v)`.
Both `A` and `B` are strictly positive, and the algebraic core of the statement is
`A^2 + B^2 - 2*C*A*B ≤ 0` (proved in `Work.Mostow.BusemannQuad`).  The final step
`A^2+B^2-2cAB ≤ 0 → |log A - log B| ≤ arcosh c` (for `A,B>0`, `c ≥ 1`) is the pure real
lemma `Work.Mostow.LogRatioArcosh`.
-/

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory

theorem BusemannLipschitz (n : ℕ) (ξ : Submission.Mostow.E n) (hξ : ξ ∈ Submission.Mostow.Sph n) (u v : Submission.Mostow.E n) :
    |Submission.Mostow.busemann ξ u - Submission.Mostow.busemann ξ v| ≤ Submission.Mostow.hdist u v := by
  have hA : 0 < tpart u - inner ℝ u ξ := busemann_arg_pos ξ hξ u
  have hB : 0 < tpart v - inner ℝ v ξ := busemann_arg_pos ξ hξ v
  have hc : 1 ≤ tpart u * tpart v - inner ℝ u v := one_le_cosh_hdist u v
  have h := LogRatioArcosh (tpart u - inner ℝ u ξ) (tpart v - inner ℝ v ξ)
      (tpart u * tpart v - inner ℝ u v) hA hB hc (BusemannQuad n ξ hξ u v)
  simpa only [Submission.Mostow.busemann, Submission.Mostow.hdist] using h

end Work.Mostow
