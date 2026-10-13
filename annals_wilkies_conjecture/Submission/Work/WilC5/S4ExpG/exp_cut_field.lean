import Mathlib
import Submission.Work.WilC5.expE_lt_iff_logFun_lt
import Submission.Work.WilC5.logFun_expE
import Submission.Work.WilC5.S4ExpF.Bridge

namespace Work.WilC5.S4ExpG

/-- **The cut of `exp x` computed by `log`**, in the field order of a model of `TE` with the
canonical `LEc`-data (to be proved in namespace `Work.WilC5.S4ExpG`).

For `w` with `0 < w` (the field order):

  `w < expE x ↔ logFun w < x`,   and   `expE x < w ↔ x < logFun w`.

The first is `Work.WilC5.expE_lt_iff_logFun_lt` (`w < exp x ↔ log w < x` for the definable order
`leE`) together with `Work.WilC5.S4ExpF.leE_zero_iff` (turning `0 < w` into
`leE zeroE w ∧ ¬ leE w zeroE`) and `hleneg` (turning `leE` into the field order `≤`); the second
follows from `Work.WilC5.expE_lt_expE_iff_of_model` (strict monotonicity of `exp`, transferred
from `ℝ`) applied at `x` and `logFun w`, using `Work.WilC5.expE_logFun_of_pos_of_model`
(`exp (logFun w) = w`), i.e. `expE x < w ↔ expE x < expE (logFun w) ↔ x < logFun w`. -/
theorem exp_cut_field {M : Type} [WilkiesDesign.CG.LEc.Structure M] [Field M] [LinearOrder M]
    [IsStrictOrderedRing M] [FirstOrder.Ring.CompatibleRing M]
    [WilkiesDesign.CG.rexpL.Structure M] [(FirstOrder.Language.constantsOn ℝ).Structure M]
    (hTE : FirstOrder.Language.Theory.Model M WilkiesDesign.CG.TE)
    (hadd : ∀ x y : M, Work.WilC5.addE x y = x + y)
    (hleneg : ∀ x y : M, Work.WilC5.leE x y ↔ x ≤ y)
    {w x : M} (hw : 0 < w) :
    ((w < Work.WilC5.expE x ↔ Work.WilC5.logFun w < x) ∧
      (Work.WilC5.expE x < w ↔ x < Work.WilC5.logFun w)) := by
  have hwE : Work.WilC5.leE Work.WilC5.zeroE w ∧ ¬ Work.WilC5.leE w Work.WilC5.zeroE :=
    (Work.WilC5.S4ExpF.leE_zero_iff hTE hadd hleneg w).mpr hw
  refine ⟨?_, ?_⟩
  · have h1 := Work.WilC5.expE_lt_iff_logFun_lt hTE (w := w) (x := x) hwE
    rw [hleneg w (Work.WilC5.expE x), hleneg (Work.WilC5.expE x) w,
      hleneg (Work.WilC5.logFun w) x, hleneg x (Work.WilC5.logFun w)] at h1
    simp only [lt_iff_le_not_ge]
    exact h1
  · have hexplog : Work.WilC5.expE (Work.WilC5.logFun w) = w :=
      Work.WilC5.expE_logFun_of_pos_of_model hTE hwE
    have h2 := Work.WilC5.expE_lt_expE_iff_of_model hTE x (Work.WilC5.logFun w)
    rw [hexplog] at h2
    rw [hleneg (Work.WilC5.expE x) w, hleneg w (Work.WilC5.expE x),
      hleneg x (Work.WilC5.logFun w), hleneg (Work.WilC5.logFun w) x] at h2
    simp only [lt_iff_le_not_ge]
    exact h2

end Work.WilC5.S4ExpG
