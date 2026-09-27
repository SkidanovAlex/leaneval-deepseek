import Mathlib
import Submission.Work.Geo.Radial.RadialDefs

namespace Work.Geo.Radial

/-- The sup-norm radius `radRho x = max_i |x i|` is continuous on `ℝⁿ`: it is the supremum
of the finitely many continuous coordinate functions `x ↦ |x i|`. -/
theorem radRho_continuous {n : ℕ} [NeZero n] :
    Continuous (radRho : PL.E n → ℝ) := by
  have hfun : (radRho : PL.E n → ℝ)
      = Finset.univ.sup' Finset.univ_nonempty (fun i : Fin n => fun x : PL.E n => |x i|) := by
    funext x
    simp [radRho]
  rw [hfun]
  exact Continuous.finset_sup' Finset.univ_nonempty
    (fun i _ => (PiLp.continuous_apply 2 (fun _ : Fin n => ℝ) i).abs)

end Work.Geo.Radial
