import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Submission.Work.Spaces.MixedMulDefs
import Submission.Work.FTS.StrongPersist.L6Aux.PhiZopBound6
import Submission.Work.FTS.CoercivityFix.E2Bound.zop_phi_bound

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Aux

/-- **Boundedness of the `Zop`-iterates of `z ↦ z/(1+z)²` up to order six on `[0,∞)`.**

`Work.Spaces.Zop u = (z ↦ z·u'(z))` is the one-dimensional radial derivation.  The profile
`φ(z) = z/(1+z)²` is the Möbius-chart evaluation `gpoly Pphi` of `Pphi = ¼(1 - X²)`
(`Work.FTS.CoercivityFix.E2Bound.gpoly_Pphi`), and `Zop` intertwines the chart evaluation with
the polynomial map `P ↦ ½(1 - X²)·P'`; hence every iterate is a polynomial in the bounded
chart variable `(z-1)/(z+1) ∈ (-1,1)` for `z > 0`, and bounded there by the sum of the
absolute values of its coefficients.  This is exactly `zop_phi_bound`, stated on the closed
half-line: at the remaining point `z = 0` every iterate of order `≥ 1` vanishes because `Zop`
carries a factor `z`, and order `0` contributes `φ(0) = 0`. -/
theorem Zop_zdiv_bound : ∃ K : ℝ, 0 < K ∧ ∀ b ≤ 6, ∀ z : ℝ, 0 ≤ z →
    |Work.Spaces.Zop^[b] (fun z : ℝ => z / (1 + z) ^ 2) z| ≤ K := by
  obtain ⟨K, hK0, hKb⟩ := Work.FTS.CoercivityFix.E2Bound.zop_phi_bound 6
  refine ⟨K + 1, by linarith, ?_⟩
  intro b hb z hz
  rcases eq_or_lt_of_le hz with hz0 | hzpos
  · -- the endpoint `z = 0`: the linear factor `z` of `Zop` kills every iterate of order `≥ 1`
    rw [← hz0]
    rcases Nat.eq_zero_or_pos b with hb0 | hbpos
    · rw [hb0, Function.iterate_zero_apply]
      have h0 : (0 : ℝ) / (1 + 0) ^ 2 = 0 := by norm_num
      rw [h0, abs_zero]
      linarith
    · rw [Work.FTS.StrongPersist.L6Aux.Zop_iterate_zero_of_pos
            (fun z : ℝ => z / (1 + z) ^ 2) hbpos, abs_zero]
      linarith
  · -- `z > 0`: the Möbius-chart bound of `zop_phi_bound`
    exact le_trans (hKb b hb z hzpos) (by linarith)

end Work.FTS.StrongPersist.H6Aux
