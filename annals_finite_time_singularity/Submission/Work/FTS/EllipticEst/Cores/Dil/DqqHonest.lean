/-
Copyright: work module for the Elgindi finite-time singularity project.

# The second radial difference quotient of a datum of class `ℋ⁰` after two radial derivatives

`DqqHonest` is the honest (`HkMem`) form of the twice-iterated radial difference-quotient
estimate: for `g` of class `C^∞` on the open quadrant whose *second* radial derivative
`D_z (D_z g)` is honestly in `ℋ⁰`, and `c > 1`, the second difference quotient

  `dq c (dq c g) = (g (c²·) - 2 g (c·) + g)/(c-1)²`

is again in `ℋ⁰`, with squared `ℋ⁰`-norm bounded by `c⁶` times that of `D_z (D_z g)`.
The exponent `6 = 3 + 3` is the square of the one-step constant: the difference quotient
`dq c h` is an average of `D_z h` along the `log`-path `s ↦ z e^s` over `[0, log c]`, so
`HkSq α 0 (dq c h) ≤ c³ HkSq α 0 (D_z h)` (Cauchy–Schwarz in `s` together with
`log c ≤ c - 1` and the weight comparison `w (z e^{-s})² ≤ e^{4s} w z²`), and the two
applications are glued by the commutation `D_z (dq c h) = dq c (D_z h)` on the open quadrant.

The one-step engine and its iterated consequences are proved in
`Submission/Work/FTS/EllipticEst/Cores/pPureShiftAux/Basic.lean`:
`HkMem_dq_and_HkSq_dq_le_self` (the engine), `Dz_dq_eqOn` (the commutation),
`HkMem_dqq` and `HkSq_dqq_le` (the two conjuncts of the present statement).  This module
only records the statement under its requested name, assembled from those.
-/
import Mathlib.Basic.Real.Basic
import Submission.Work.FTS.EllipticEst.Cores.Dil.DilBasic
import Submission.Work.FTS.EllipticEst.Cores.pPureShiftAux.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Cores.Dil

theorem DqqHonest {α c : ℝ} {g : ℝ → ℝ → ℝ}
    (hg : Work.FTS.EllipticEst.SmoothOpen g)
    (hgmem : Work.Spaces.HkMem α 0 (Work.Spaces.Dz (Work.Spaces.Dz g)))
    (hc : 1 < c) :
    Work.Spaces.HkMem α 0 (Work.FTS.EllipticEst.Cores.Dil.dq c (Work.FTS.EllipticEst.Cores.Dil.dq c g)) ∧
      Work.Spaces.HkSq α 0 (Work.FTS.EllipticEst.Cores.Dil.dq c (Work.FTS.EllipticEst.Cores.Dil.dq c g))
        ≤ c ^ 6 * Work.Spaces.HkSq α 0 (Work.Spaces.Dz (Work.Spaces.Dz g)) :=
  ⟨Work.FTS.EllipticEst.Cores.pPureShiftAux.HkMem_dqq hg hg.Dz hgmem hc,
    Work.FTS.EllipticEst.Cores.pPureShiftAux.HkSq_dqq_le hg hg.Dz hgmem hc⟩

end Work.FTS.EllipticEst.Cores.Dil
