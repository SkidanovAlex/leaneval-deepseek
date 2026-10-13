/-
Copyright: work module for the Elgindi finite-time singularity project (area `FTS.EllSol`).

# The second angular derivative of the truncated data `uTr`

`uTr N b u = phiTr N · Gc N b u` is a product of the `θ`-independent cutoff `phiTr N` with the
backward particular solution `Gc N b u`.  Hence the angular derivatives of `uTr` are the angular
derivatives of `Gc N b u`, dressed with the constant factor `phiTr N t`:

`∂_θ (uTr N b u) = phiTr N t · ∂_θ (Gc N b u)`,
`∂_θ²(uTr N b u) = phiTr N t · ∂_θ²(Gc N b u)`.

The second angular derivative of `Gc` is `Gc_pth_pth`
(`Submission/Work/FTS/EllSol/ShiftFT/Gc_pth_pth.lean`), whose second summand is definitionally the
tail integral `tailE N b (∂_θ²u)`.  This file combines the two.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.EllSol.ShiftFT.uTrAthree.Defs
import Submission.Work.FTS.EllSol.ShiftFT.Gc_pth_pth

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.ShiftFT.uTrAthree

noncomputable section

set_option autoImplicit false

/-- **The first angular derivative of `uTr`.**  Since `uTr N b u = phiTr N · Gc N b u` and
`phiTr N t` does not depend on the angle, the constant factor comes out of the derivative. -/
theorem uTr_pth_eq (N b : ℝ) (u : ℝ → ℝ → ℝ) (t : ℝ) :
    Work.Spaces.pth (Work.FTS.EllSol.ShiftFT.uTr N b u) t
      = fun θ => Work.FTS.EllSol.ShiftFT.phiTr N t
          * Work.Spaces.pth (Work.FTS.EllSol.ShiftFT.Gc N b u) t θ := by
  funext θ
  simp only [Work.Spaces.pth, Work.FTS.EllSol.ShiftFT.uTr]
  exact deriv_const_mul_field _

/-- The tail integral `tailE` is, by definition, the second summand of `Gc N b u` with `u`
replaced by `f`. -/
theorem tailE_eq_tail (N b : ℝ) (f : ℝ → ℝ → ℝ) (t θ : ℝ) :
    tailE N b f t θ
      = Real.exp (b * t) * ∫ s in t..(2 * N),
          Real.exp (-(b * s)) * deriv (Work.FTS.EllSol.Trunc.chi N) s * f s θ := rfl

/-- **The second angular derivative of the truncated data.**  The double `θ`-derivative of
`uTr N b u` is `phiTr N t` times the double `θ`-derivative of `Gc N b u`, which by `Gc_pth_pth`
is `chi N t · ∂_θ²u + tailE N b (∂_θ²u)`. -/
theorem UTrPthPth (N b : ℝ) (u : ℝ → ℝ → ℝ)
    (hu : ContDiffOn ℝ 2 (Function.uncurry u) (Set.univ ×ˢ Set.Ioo 0 (Real.pi / 2))) :
    ∀ t : ℝ, ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      Work.Spaces.pth (Work.Spaces.pth (Work.FTS.EllSol.ShiftFT.uTr N b u)) t θ
        = Work.FTS.EllSol.ShiftFT.phiTr N t
          * (Work.FTS.EllSol.Trunc.chi N t
              * Work.Spaces.pth (Work.Spaces.pth u) t θ
              + Work.FTS.EllSol.ShiftFT.uTrAthree.tailE N b
                  (Work.Spaces.pth (Work.Spaces.pth u)) t θ) := by
  intro t θ hθ
  have hGc := Work.FTS.EllSol.ShiftFT.Gc_pth_pth N b u hu t θ hθ
  calc Work.Spaces.pth (Work.Spaces.pth (Work.FTS.EllSol.ShiftFT.uTr N b u)) t θ
      = deriv (fun θ' => Work.Spaces.pth (Work.FTS.EllSol.ShiftFT.uTr N b u) t θ') θ := rfl
    _ = deriv (fun θ' => Work.FTS.EllSol.ShiftFT.phiTr N t
            * Work.Spaces.pth (Work.FTS.EllSol.ShiftFT.Gc N b u) t θ') θ := by
          rw [uTr_pth_eq N b u t]
    _ = Work.FTS.EllSol.ShiftFT.phiTr N t
          * deriv (fun θ' => Work.Spaces.pth (Work.FTS.EllSol.ShiftFT.Gc N b u) t θ') θ :=
          deriv_const_mul_field _
    _ = Work.FTS.EllSol.ShiftFT.phiTr N t
          * Work.Spaces.pth (Work.Spaces.pth (Work.FTS.EllSol.ShiftFT.Gc N b u)) t θ := rfl
    _ = Work.FTS.EllSol.ShiftFT.phiTr N t
          * (Work.FTS.EllSol.Trunc.chi N t
              * Work.Spaces.pth (Work.Spaces.pth u) t θ
              + Work.FTS.EllSol.ShiftFT.uTrAthree.tailE N b
                  (Work.Spaces.pth (Work.Spaces.pth u)) t θ) := by
          rw [hGc, tailE_eq_tail]

end

end Work.FTS.EllSol.ShiftFT.uTrAthree
