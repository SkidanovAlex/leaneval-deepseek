import Mathlib
import Submission.Work.BG.S02
import Submission.Work.BG.s02_bsValueT
import Submission.Work.BG.H0Conj

namespace Work.BG

open OddOrder.RepresentationTheory

/-- **I-3 of design10: `BSValueProp`, the value of `(μ - ν)* = ind C (μ - ν)` at `t`.**

This is the specialisation `g = t` of the `T`-version `BSValueTProp` (`s02_bsValueT`).
Indeed `t` is central in `H` (`C.t_comm_H`), and `s ∈ H`, so `s t s⁻¹ = t`; evaluating
`BSValueTProp` at `g = t` gives

`ind C (μ - ν) (t) = (μ - ν)(t) + (μ - ν)(t) = 2 * (μ C.t - ν C.t)`.

(Note `(t : G) ∉ C.P.U` by `C.t_not_mem_U`, so the hypothesis of `BSValueTProp` is met.) -/
theorem s02_bsValueAtT {G : Type} [Group G] [Finite G] [Fintype G] [Invertible (Nat.card G : ℂ)]
    (C : Work.BG.Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)] :
    Work.BG.BSValueProp C := by
  intro μ ν hμ hν hLam
  -- `t` is fixed by conjugation by `s`, since `t` is central in `H ∋ s`.
  have hfix : conjMulEquiv C.P C.s C.t = C.t := by
    apply Subtype.ext
    rw [conjMulEquiv_apply, C.t_comm_H (C.s : G) C.s.2, mul_assoc, mul_inv_cancel, mul_one]
  -- The `T`-version at `g = t`.
  have h := s02_bsValueT C μ ν hμ hν hLam C.t C.t_not_mem_U
  rw [hfix] at h
  rw [h, ClassFunction.sub_apply]
  ring

end Work.BG
