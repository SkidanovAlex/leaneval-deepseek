import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Real.Sqrt
import Submission.Work.FTS.StrongEps.H5.Data
import Submission.Work.FTS.StrongEps.H5.LevelShift
import Submission.Work.FTS.StrongEps.H5.L5of
import Submission.Work.FTS.ClassC.Defs
import Submission.Work.FTS.GalFields.Norm.Basic
import Submission.Work.FTS.IPGen.OpenBasic
import Submission.Work.FTS.StrongLWP.Basic
import Submission.Work.FTS.StrongPersist.H6Aux.Facts

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.H5.Atoms

/-- **The `L5` data of the three `w`-atoms.**  `L5 α f a` (defined in
`Submission/Work/FTS/StrongEps/H5/Data.lean`) is the bundle `HQo α 4 f`, `HQo α 4 (Dz f)`,
`HQo α 4 (Dth f)` with the single bound `a` on the three level-four norms
`Xn α f, Xn α (Dz f), Xn α (Dth f)` (`Xn α = HkNorm α 4`).

For a `ClassC` datum `w` with `Xn α w ≤ C₀ α²` and `HkNorm α 6 w ≤ B` there is `a > 0`
(depending on `α, C₀, B` but not on `w`) with `L5 α w a`, `L5 α (Dz w) a`, `L5 α (Dth w) a`.

Route: `ClassC α w` gives `SmoothOpen w` and `HkMem α 7 w`.  Iterate
`Work.FTS.CoercivityFix.Transfer.HkMem_descent_Q0Sm` (level-general) with
`Work.FTS.StrongPersist.q0Sm_of_smoothOpen` to get `HkMem α 4` of `w`, `Dz w`, `Dth w`,
`Dz (Dz w)`, `Dz (Dth w)`, `Dth (Dz w)`, `Dth (Dth w)`; the norm bounds come from the sub-sum
comparisons `HkSq_Dz_le_Q0Sm` / `HkSq_Dth_le` iterated from level four to level six (e.g.
`HkSq α 4 (Dz (Dz w)) ≤ HkSq α 6 w`), hence every `Xn`-bound is `≤ HkNorm α 6 w ≤ B` (or
`≤ C₀ α²` for `w` itself).  A safe choice of the constant is
`a := max (max (C₀ * α ^ 2) B) 0 + 1` (the bound hypotheses are then vacuous for negative
`C₀`/`B`, which is harmless). -/
theorem L5AtomsW : ∀ {α : ℝ}, α ∈ Set.Ioc 0 1 → ∀ {C₀ B : ℝ},
    ∃ a : ℝ, 0 < a ∧ ∀ {w : Work.FTS.Galerkin.Fn},
      Work.FTS.ClassC.ClassC α w → Work.FTS.Nonlin.Xn α w ≤ C₀ * α ^ 2 →
      Work.Spaces.HkNorm α 6 w ≤ B →
      Work.FTS.StrongEps.H5.L5 α w a ∧
      Work.FTS.StrongEps.H5.L5 α (Work.Spaces.Dz w) a ∧
      Work.FTS.StrongEps.H5.L5 α (Work.Spaces.Dth w) a := by
  intro α hα C₀ B
  have hα0 : 0 < α := hα.1
  have hα10 : -(1 / 10 : ℝ) ≤ α := by linarith [hα.1]
  refine ⟨max (max (C₀ * α ^ 2) B) 0 + 1, ?_, ?_⟩
  · have h := le_max_right (max (C₀ * α ^ 2) B) (0 : ℝ)
    linarith
  · intro w hw _hXn hB
    have hreg : Work.FTS.EllipticEst.SmoothOpen w := hw.reg
    -- ### the level-five memberships of the atom and of its two first derivatives
    have h6 : Work.Spaces.HkMem α 6 w :=
      Work.FTS.OpenPkg.HkMem_mono_open hreg 6 (by norm_num) hw.mem
    have h5 : Work.Spaces.HkMem α 5 w :=
      Work.FTS.OpenPkg.HkMem_mono_open hreg 5 (by norm_num) hw.mem
    have h5Dz : Work.Spaces.HkMem α 5 (Work.Spaces.Dz w) :=
      Work.FTS.IPGen.HkMem_Dz_le hreg h6
    have h5Dth : Work.Spaces.HkMem α 5 (Work.Spaces.Dth w) :=
      Work.FTS.IPGen.HkMem_Dth_le hα10 hreg h6
    -- ### the level-five norm bounds, all dominated by `HkNorm α 6 w ≤ B`
    have haB : B ≤ max (max (C₀ * α ^ 2) B) 0 + 1 := by
      have h1 : B ≤ max (C₀ * α ^ 2) B := le_max_right _ _
      have h2 : max (C₀ * α ^ 2) B ≤ max (max (C₀ * α ^ 2) B) 0 := le_max_left _ _
      linarith
    have hb6 : Work.Spaces.HkNorm α 6 w ≤ max (max (C₀ * α ^ 2) B) 0 + 1 :=
      le_trans hB haB
    have hb5w : Work.Spaces.HkNorm α 5 w ≤ max (max (C₀ * α ^ 2) B) 0 + 1 :=
      le_trans (Work.FTS.StrongLWP.HkNorm_mono_of_mem (k := 6) (k' := 5) (by norm_num) h6) hb6
    have hb5Dz : Work.Spaces.HkNorm α 5 (Work.Spaces.Dz w)
        ≤ max (max (C₀ * α ^ 2) B) 0 + 1 :=
      calc Work.Spaces.HkNorm α 5 (Work.Spaces.Dz w)
          = Real.sqrt (Work.Spaces.HkSq α 5 (Work.Spaces.Dz w)) := rfl
        _ ≤ Real.sqrt (Work.Spaces.HkSq α 6 w) :=
            Real.sqrt_le_sqrt
              (Work.FTS.StrongPersist.H6Aux.HkSq_Dz_le_succ' α 5 hreg h6)
        _ = Work.Spaces.HkNorm α 6 w := rfl
        _ ≤ max (max (C₀ * α ^ 2) B) 0 + 1 := hb6
    have hb5Dth : Work.Spaces.HkNorm α 5 (Work.Spaces.Dth w)
        ≤ max (max (C₀ * α ^ 2) B) 0 + 1 :=
      calc Work.Spaces.HkNorm α 5 (Work.Spaces.Dth w)
          = Real.sqrt (Work.Spaces.HkSq α 5 (Work.Spaces.Dth w)) := rfl
        _ ≤ Real.sqrt (Work.Spaces.HkSq α 6 w) :=
            Real.sqrt_le_sqrt
              (Work.FTS.StrongPersist.H6Aux.HkSq_Dth_le_succ' α hα10 5 h6)
        _ = Work.Spaces.HkNorm α 6 w := rfl
        _ ≤ max (max (C₀ * α ^ 2) B) 0 + 1 := hb6
    exact ⟨Work.FTS.StrongEps.H5.L5_of_HQo5 hα0 ⟨hreg, h5⟩ hb5w,
      Work.FTS.StrongEps.H5.L5_of_HQo5 hα0 ⟨hreg.Dz, h5Dz⟩ hb5Dz,
      Work.FTS.StrongEps.H5.L5_of_HQo5 hα0 ⟨hreg.Dth, h5Dth⟩ hb5Dth⟩

end Work.FTS.StrongEps.H5.Atoms
