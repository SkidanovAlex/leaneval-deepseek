import Mathlib
import Submission.Work.ThomBordism.Grassmann.Model
import Submission.Work.ThomBordism.Grassmann.P2Base.Frame
import Submission.Work.ThomBordism.Grassmann.P2Base.Gauge

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

/-!
# Joint continuity of the coefficient functionals `aCoefL`, `bCoefL`

The coefficient functionals are continuous as functions of `(s, v)` on `{s ≠ 0} × ℂ⁶`; this is the
analytic input of the continuity of the gauge `V₄ ≅ Z₄` of the `p₂`-probe at `(4,8)`.
-/

namespace Work.ThomBordism.Grassmann.InclCrux

open Work.TangentClasses
open Work.ThomBordism.Grassmann.P2Base

noncomputable section

/-- The explicit value of `aCoefL s v` (`P2Base.aCoefL_apply` + `P2Base.bCoefL_apply`). -/
def aCoefFun (s : E5) (v : E6) : ℂ :=
  (((‖lamL s‖)⁻¹ : ℝ) : ℂ) * (inner ℂ (lamUnit s) v
    - (inner ℂ (lamUnit s) (lamR s)) * ((((‖wVec s‖ ^ 2)⁻¹ : ℝ) : ℂ) * inner ℂ (wVec s) v))

/-- The explicit value of `bCoefL s v`. -/
def bCoefFun (s : E5) (v : E6) : ℂ :=
  ((((‖wVec s‖ ^ 2)⁻¹ : ℝ) : ℂ) * inner ℂ (wVec s) v)

theorem aCoefL_eq (s : E5) (v : E6) : aCoefL s v = aCoefFun s v := by
  rw [aCoefL_apply, bCoefL_apply]
  rfl

theorem bCoefL_eq (s : E5) (v : E6) : bCoefL s v = bCoefFun s v := by
  rw [bCoefL_apply]
  rfl

theorem continuous_aCoefFun :
    Continuous fun q : ({s : E5 // s ≠ 0} × E6) => aCoefFun q.1.1 q.2 := by
  have hLL : Continuous fun q : ({s : E5 // s ≠ 0} × E6) => lamL q.1.1 :=
    lamL.continuous.comp (continuous_subtype_val.comp continuous_fst)
  have hLR : Continuous fun q : ({s : E5 // s ≠ 0} × E6) => lamR q.1.1 :=
    lamR.continuous.comp (continuous_subtype_val.comp continuous_fst)
  have hLU : Continuous fun q : ({s : E5 // s ≠ 0} × E6) => lamUnit q.1.1 :=
    continuous_lamUnit_subtype.comp continuous_fst
  have hw : Continuous fun q : ({s : E5 // s ≠ 0} × E6) => wVec q.1.1 :=
    continuous_wVec_subtype.comp continuous_fst
  have hv : Continuous fun q : ({s : E5 // s ≠ 0} × E6) => q.2 := continuous_snd
  have hLLn : Continuous fun q : ({s : E5 // s ≠ 0} × E6) =>
      (((‖lamL q.1.1‖ : ℝ) : ℂ))⁻¹ :=
    (Complex.continuous_ofReal.comp hLL.norm).inv₀ (fun q => by
      simp only [Function.comp_apply, ne_eq, Complex.ofReal_eq_zero]
      exact norm_ne_zero_iff.mpr (lamL_ne_zero q.1.2))
  have hwn : Continuous fun q : ({s : E5 // s ≠ 0} × E6) =>
      (((‖wVec q.1.1‖ ^ 2 : ℝ)) : ℂ)⁻¹ :=
    (Complex.continuous_ofReal.comp (hw.norm.pow 2)).inv₀ (fun q => by
      simp only [Function.comp_apply, ne_eq, Complex.ofReal_eq_zero]
      exact pow_ne_zero 2 (norm_ne_zero_iff.mpr (wVec_ne_zero q.1.1 q.1.2)))
  have hin1 : Continuous fun q : ({s : E5 // s ≠ 0} × E6) => inner ℂ (lamUnit q.1.1) q.2 :=
    continuous_inner.comp (hLU.prodMk hv)
  have hin2 : Continuous fun q : ({s : E5 // s ≠ 0} × E6) =>
      inner ℂ (lamUnit q.1.1) (lamR q.1.1) :=
    continuous_inner.comp (hLU.prodMk hLR)
  have hin3 : Continuous fun q : ({s : E5 // s ≠ 0} × E6) => inner ℂ (wVec q.1.1) q.2 :=
    continuous_inner.comp (hw.prodMk hv)
  have hmain := hLLn.mul (hin1.sub (hin2.mul (hwn.mul hin3)))
  refine hmain.congr (fun q => ?_)
  simp only [Pi.mul_apply, Pi.sub_apply, aCoefFun, Complex.ofReal_inv]

theorem continuous_bCoefFun :
    Continuous fun q : ({s : E5 // s ≠ 0} × E6) => bCoefFun q.1.1 q.2 := by
  have hw : Continuous fun q : ({s : E5 // s ≠ 0} × E6) => wVec q.1.1 :=
    continuous_wVec_subtype.comp continuous_fst
  have hv : Continuous fun q : ({s : E5 // s ≠ 0} × E6) => q.2 := continuous_snd
  have hwn : Continuous fun q : ({s : E5 // s ≠ 0} × E6) =>
      (((‖wVec q.1.1‖ ^ 2 : ℝ)) : ℂ)⁻¹ :=
    (Complex.continuous_ofReal.comp (hw.norm.pow 2)).inv₀ (fun q => by
      simp only [Function.comp_apply, ne_eq, Complex.ofReal_eq_zero]
      exact pow_ne_zero 2 (norm_ne_zero_iff.mpr (wVec_ne_zero q.1.1 q.1.2)))
  have hin3 : Continuous fun q : ({s : E5 // s ≠ 0} × E6) => inner ℂ (wVec q.1.1) q.2 :=
    continuous_inner.comp (hw.prodMk hv)
  have hmain := hwn.mul hin3
  refine hmain.congr (fun q => ?_)
  simp only [Pi.mul_apply, bCoefFun, Complex.ofReal_inv]

end

end Work.ThomBordism.Grassmann.InclCrux
