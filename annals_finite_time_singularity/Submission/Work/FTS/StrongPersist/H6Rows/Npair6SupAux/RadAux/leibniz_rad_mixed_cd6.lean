import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.StrongPersist.H6Rows.N0pair6bWork.Cd6.mixedMul_cd6
import Submission.Work.Elliptic.L12Aux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Rows.Npair6SupAux.RadAux

theorem leibniz_rad_mixed_cd6 {r : ℝ → ℝ} {g : ℝ → ℝ → ℝ}
    (hr : ContDiffOn ℝ 6 (Function.uncurry (fun z (_ : ℝ) => r z)) Work.FTS.EllipticEst.Q0)
    (hg : ContDiffOn ℝ 6 (Function.uncurry g) Work.FTS.EllipticEst.Q0)
    {j i : ℕ} (hi : 1 ≤ i) (hij : i + j ≤ 6) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Spaces.mixed j i (fun z θ => r z * g z θ) z θ
        = ∑ b ∈ Finset.range (j + 1), (j.choose b : ℝ)
            * (Work.Elliptic.DzdIter b r z * Work.Spaces.mixed (j - b) i g z θ) := by
  intro z θ hz hθ0 hθ1
  -- The general finite-order Leibniz rule for `D_z^j D_θ^i` applied to `(z,θ) ↦ r z · g z θ`.
  have h := Work.FTS.StrongPersist.H6Rows.N0pair6bWork.Cd6.mixedMul_cd6
    (f := fun z (_ : ℝ) => r z) (g := g) hr hg j i (by omega) z θ hz hθ0 hθ1
  rw [h]
  -- Every angular derivative of a function of `z` alone vanishes, so only the `b = 0` slot of
  -- the inner (angular) sum survives.
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_eq_single 0 ?_ ?_]
  · rw [Nat.choose_zero_right, Nat.sub_zero, Work.Spaces.mixed_zero_right,
      Work.Elliptic.DzIter_rad r a z θ]
    ring
  · intro b _ hb
    rw [show Work.Spaces.mixed a b (fun z _ => r z) z θ = 0 from
      congrFun (congrFun (Work.Elliptic.mixed_rad_eq_zero r (by omega)) z) θ]
    ring
  · intro h
    exact absurd (Finset.mem_range.mpr (by omega)) h

end Work.FTS.StrongPersist.H6Rows.Npair6SupAux.RadAux
