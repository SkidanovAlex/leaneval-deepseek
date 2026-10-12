import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring.RingNF
import Submission.Work.BoseFixB1.PerBoxNames
import Submission.Work.BoseFixB1.RegimeAux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1S.sbCut_cube_eq` — the exact cube of FS's spectral cut-off

At FS's parameters `d = X⁶`, `s = X`, `ℓ = A·X^{-163}` (`X = (μA³)^{1/323}`) the
small-box spectral cut-off of `eq:appTB` is

    sbCut μ A = (d s ℓ)⁻¹ = A⁻¹ · X^{156} = A⁻¹ · (μA³)^{156/323},

see `sbCut_eq_inv_mul` below (equivalently `sbCut μ A · A = (μA³)^{156/323}`,
`Work.BoseFixB1S.sbCut_mul_eq`).  Cubing and using `X³·156 = X^{468}` together
with `(A³)⁻¹ = (A⁻¹)³` gives the requested identity

    (sbCut μ A)³ = (A³)⁻¹ · X^{468},

which is the pure-arithmetic normal form the sector bookkeeping needs.
-/

namespace Work.BoseFixB1S

open Work.BoseBox

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **The closed form of FS's spectral cut-off.**  At FS's parameters
`sbCut μ A = (d s ℓ)⁻¹ = A⁻¹·(μA³)^{156/323}`.

Indeed `d s ℓ = A·(μA³)^{-156/323}`: with `d = X⁶`, `s = X = X^1` and
`ℓ = A·X^{-163}` (`Work.BoseFixB1.sideAt_eq_fsXp`), the product is
`A·X^{6+1-163} = A·X^{-156}`. -/
lemma sbCut_eq_inv_mul {μ A : ℝ} (hA : 0 < A) (hμ : 0 < μ) :
    Work.BoseFixB1.sbCut μ A = A⁻¹ * fsXp (μ * A ^ 3) 156 := by
  have ht : (0 : ℝ) < μ * A ^ 3 := by positivity
  have hden : (paramsAt μ A).d * (paramsAt μ A).s * sideAt μ A
      = A * fsXp (μ * A ^ 3) (-156) := by
    have hds := Work.BoseFixB1.d_mul_sideAt_eq (A := A) (μ := μ) hA hμ
    have hs : (paramsAt μ A).s = fsXp (μ * A ^ 3) 1 := rfl
    calc (paramsAt μ A).d * (paramsAt μ A).s * sideAt μ A
        = ((paramsAt μ A).d * sideAt μ A) * (paramsAt μ A).s := by ring
      _ = (A * fsXp (μ * A ^ 3) (-157)) * fsXp (μ * A ^ 3) 1 := by rw [hds, hs]
      _ = A * fsXp (μ * A ^ 3) (-156) := by
            rw [mul_assoc, fsXp_mul ht]
            norm_num
  rw [Work.BoseFixB1.sbCut, hden, mul_inv, fsXp_inv ht]
  norm_num

/-- The requested identity: `(sbCut μ A)³ = (A³)⁻¹·X^{468}` with
`X = (μA³)^{1/323} = (paramsAt μ A).X`. -/
theorem sbCut_cube_eq {μ α : ℝ} (hα : 0 < α) (hμ : 0 < μ) :
    (Work.BoseFixB1.sbCut μ α) ^ 3
      = (α ^ 3)⁻¹ * ((Work.BoseBox.paramsAt μ α).X) ^ 468 := by
  have ht : (0 : ℝ) < μ * α ^ 3 := by positivity
  have hX : (paramsAt μ α).X = fsXp (μ * α ^ 3) 1 := rfl
  rw [hX, sbCut_eq_inv_mul hα hμ, mul_pow, inv_pow,
    fsXp_pow ht.le 156 3, fsXp_pow ht.le 1 468]
  norm_num

end Work.BoseFixB1S
