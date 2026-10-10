import Mathlib
import Submission.Work.PointlessIndexFive.Defs
import Submission.Work.TorsorExistence.five_smul_cls
import Submission.Work.PointlessIndexFive.five_nsmul_mem_shift_range

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.PointlessIndexFive

/-- **`H¹(ℤ/5, E(L))` has exponent `5`.**  For every class `x` in `ker N/(σ-1)E(L)`, `5 • x = 0`.
This is the abstract form of the orbit-divisor argument (`five_smul_cls` is the special case of the
class of the cocycle `σ ↦ P`): for `y ∈ ker N`,
`5y - N(y) = Σ_{i<5} (y - σ^i y)` and each `y - σ^i y` is `-shift` of a partial sum. -/
theorem five_smul_eq_zero_H1 {𝕜 : Type} [Field 𝕜] [DecidableEq 𝕜] (D : QuinticTwist 𝕜)
    (x : D.H1) : (5 : ℕ) • x = 0 := by
  -- Every class is the class of a cocycle, so it suffices to treat `x = [y]` with `y ∈ ker N`.
  induction x using QuotientAddGroup.induction_on with
  | _ y =>
    -- `y` lies in `ker N = ker (1 + σ + σ² + σ³ + σ⁴)`, i.e. `y + σy + σ²y + σ³y + σ⁴y = 0`.
    have hy : D.norm y.1 = 0 := (AddMonoidHom.mem_ker).mp y.2
    rw [Work.TorsorExistence.QuinticTwist.norm_apply] at hy
    -- The orbit-divisor computation: `5y = (σ - 1)z` for an explicit `z`
    -- (each `y - σ^i y` is minus the shift of the partial sum `y + σy + … + σ^{i-1}y`).
    obtain ⟨z, hz⟩ := five_nsmul_mem_shift_range D.galMap y.1 hy
    -- `5 • [y] = [5 • y]` in the quotient `ker N / (σ - 1)E(L)`.
    have key : (5 : ℕ) • (QuotientAddGroup.mk' D.coboundaries y) =
        QuotientAddGroup.mk' D.coboundaries ((5 : ℕ) • y) := (map_nsmul _ 5 y).symm
    rw [show (↑y : D.H1) = QuotientAddGroup.mk' D.coboundaries y from rfl, key]
    -- It remains to see that `5 • y` is a coboundary; unfolding `coboundaries` this is exactly
    -- the statement that `5y` is the shift of `z`.
    refine (QuotientAddGroup.eq_zero_iff ((5 : ℕ) • y)).mpr ?_
    rw [show D.coboundaries = (AddSubgroup.map D.shift ⊤).comap (D.cocycles).subtype from rfl,
      AddSubgroup.mem_comap, AddSubgroup.mem_map]
    refine ⟨z, trivial, ?_⟩
    show D.galMap z - z = D.cocycles.subtype ((5 : ℕ) • y)
    rw [map_nsmul, show D.cocycles.subtype y = y.1 from rfl]
    exact hz

end Work.PointlessIndexFive
