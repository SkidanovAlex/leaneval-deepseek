import Mathlib
import Submission.Work.MotC2.PoleSetup

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotC2

theorem w_sq_deg_constraints (L : Type*) [Field L] (E : WeierstrassCurve L) (p q : Polynomial L) :
    (p - q * Work.MotC2.linPoly E).degree ≤ 1 →
    (-(p * Work.MotC2.linPoly E) +
      q * (Work.MotC2.cubicPoly E + Work.MotC2.linPoly E ^ 2)).degree ≤ 2 →
    q = 0 ∧ p.degree ≤ 1 := by
  intro h1 h2
  -- `q * c` is a linear combination of the two bounded polynomials, so it is bounded too.
  have hid : q * Work.MotC2.cubicPoly E =
      (-(p * Work.MotC2.linPoly E) + q * (Work.MotC2.cubicPoly E + Work.MotC2.linPoly E ^ 2))
        + Work.MotC2.linPoly E * (p - q * Work.MotC2.linPoly E) := by ring
  suffices hq : q = 0 by
    refine ⟨hq, ?_⟩
    rw [hq] at h1
    simpa using h1
  by_contra hq
  have hc : (Work.MotC2.cubicPoly E).degree = 3 := Work.MotC2.cubicPoly_degree E
  have hcne : Work.MotC2.cubicPoly E ≠ 0 := fun h => by rw [h] at hc; norm_num at hc
  have hc' : (Work.MotC2.cubicPoly E).natDegree = 3 := Polynomial.natDegree_eq_of_degree_eq_some hc
  have h1' : (p - q * Work.MotC2.linPoly E).natDegree ≤ 1 := Polynomial.natDegree_le_iff_degree_le.mpr h1
  have h2' : (-(p * Work.MotC2.linPoly E) +
      q * (Work.MotC2.cubicPoly E + Work.MotC2.linPoly E ^ 2)).natDegree ≤ 2 :=
    Polynomial.natDegree_le_iff_degree_le.mpr h2
  -- the degree of `q * c` is at most `2`, by the two hypotheses
  have hdeg : (q * Work.MotC2.cubicPoly E).natDegree ≤ 2 := by
    rw [hid]
    refine le_trans (Polynomial.natDegree_add_le _ _) (max_le h2' ?_)
    refine le_trans (Polynomial.natDegree_mul_le) ?_
    have ht' : (Work.MotC2.linPoly E).natDegree ≤ 1 :=
      Polynomial.natDegree_le_iff_degree_le.mpr (Work.MotC2.linPoly_degree_le E)
    omega
  -- but `deg (q * c) = deg q + 3 ≥ 3`, contradiction
  rw [Polynomial.natDegree_mul hq hcne, hc'] at hdeg
  omega

end Work.MotC2
