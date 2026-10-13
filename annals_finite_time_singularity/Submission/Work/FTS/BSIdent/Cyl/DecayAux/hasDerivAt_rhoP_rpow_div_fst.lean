import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.Cyl.Coords
import Submission.Work.Cyl.Frame
import Submission.Work.Cyl.pdZ_comp_polar

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.BSIdent.Cyl.DecayAux

/-- `r ↦ ρ(r,z) = √(r²+z²)` has radial derivative `r/ρ`.  Radial counterpart of
`Work.Cyl.hasDerivAt_rhoP_polar`. -/
private lemma hasDerivAt_rhoP_fst_polar (r z : ℝ) (hr : 0 < r) :
    HasDerivAt (fun r' : ℝ => Work.Cyl.rhoP r' z) (r / Work.Cyl.rhoP r z) r := by
  have hsq : HasDerivAt (fun r' : ℝ => r' ^ 2 + z ^ 2) (2 * r) r := by
    have h : HasDerivAt (fun r' : ℝ => r' ^ 2) (2 * r) r := by
      simpa using (hasDerivAt_pow 2 r)
    simpa using h.add_const (z ^ 2)
  have hne : r ^ 2 + z ^ 2 ≠ 0 := by positivity
  have h := hsq.sqrt hne
  have hval : (2 * r) / (2 * Real.sqrt (r ^ 2 + z ^ 2)) = r / Work.Cyl.rhoP r z := by
    have hs : Real.sqrt (r ^ 2 + z ^ 2) ≠ 0 := by positivity
    rw [Work.Cyl.rhoP]; field_simp
  rw [hval] at h
  exact h

/-- `r ↦ ρ(r,z)^α` has radial derivative `α ρ^{α-1} · (r/ρ)`.  Radial counterpart of
`Work.Cyl.hasDerivAt_rhoP_rpow_polar`. -/
private lemma hasDerivAt_rhoP_fst_rpow (r α z : ℝ) (hr : 0 < r) :
    HasDerivAt (fun r' : ℝ => Work.Cyl.rhoP r' z ^ α)
      (α * Work.Cyl.rhoP r z ^ (α - 1) * (r / Work.Cyl.rhoP r z)) r := by
  have hbase := hasDerivAt_rhoP_fst_polar r z hr
  have h := hbase.rpow_const (p := α) (Or.inl (ne_of_gt (Work.Cyl.rhoP_pos hr z)))
  simpa only [mul_comm, mul_left_comm, mul_assoc] using h

/-- The radial derivative of `r' ↦ ρ(r',z)^p / b`, obtained from
`hasDerivAt_rhoP_fst_rpow` (which gives the derivative `p ρ^{p-1} · (r/ρ)` of
`r' ↦ ρ(r',z)^p`) after dividing by the constant `b` and rewriting
`ρ^{p-1} · (r/ρ) = ρ^p · (r/ρ^2)`. -/
theorem hasDerivAt_rhoP_rpow_div_fst (r p z b : ℝ) (hr : 0 < r) :
    HasDerivAt (fun r' : ℝ => Work.Cyl.rhoP r' z ^ p / b)
      (p * (Work.Cyl.rhoP r z ^ p / b) * (r / Work.Cyl.rhoP r z ^ 2)) r := by
  have h := (hasDerivAt_rhoP_fst_rpow r p z hr).div_const b
  have hne : Work.Cyl.rhoP r z ≠ 0 := Work.Cyl.rhoP_ne_zero hr z
  convert h using 1
  rw [Real.rpow_sub_one hne, div_eq_mul_inv, div_eq_mul_inv]
  field_simp

end Work.FTS.BSIdent.Cyl.DecayAux
