import Mathlib
import Submission.Work.KT.Fund.kappa_hopf_defs

/-!
# `Work.KT.Fund.kappa_hopf_pullup`

The Hopf idempotent `hopfMat` over `S² = ℂP¹` is the rank-one projection
`(1 + x₀σ₁ + x₁σ₂ + x₂σ₃)/2` written out in terms of the coordinate functions
`coordC 3 i` on `S²`.  Restricting it to the closed upper hemisphere
`up : D → S²` (a disc parametrised by the unit ball of `ℂ`) and pulling the
result back along the projection `X × S² → S²` gives, on `X × D`, the matrix

`!![(1 + s)/2, c̄/2; c/2, (1 - s)/2]`

where `c = cCoord X` is the disc coordinate and `s = cHeight X = √(1-‖c‖²)`
is the height function.  This is the "clutching data" form of the Hopf class
used in the proof of `kappa_hopf`.
-/

namespace Work.KT.Fund

open _root_.Matrix

noncomputable section

/-- **Restriction of the Hopf idempotent to the upper hemisphere.**
Writing `c : C(X × D, ℂ)` for the disc coordinate and `s = √(1-‖c‖²)` for the
height, the matrix `hopfMat` pulled back along `X × D → X × S² → S²` is
`!![(1+s)/2, c̄/2; c/2, (1-s)/2]`. -/
theorem kappa_hopf_pullup (X : Type) [TopologicalSpace X] :
    (hopfMat.map (pullAlg (ContinuousMap.snd : C(X × S2, S2))).toRingHom).map (pullUp X)
      = !![(1 + cHeight X) * halfC X, star (cCoord X) * halfC X;
           cCoord X * halfC X, (1 - cHeight X) * halfC X] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.map, Matrix.of_apply, hopfMat, Matrix.smul_apply, Matrix.cons_val',
      Matrix.empty_val', Matrix.cons_val_fin_one]
  all_goals
    apply Complex.ext <;>
      simp [cHeight, cCoord, halfC, coordC, up, upPt, mk3] <;> ring

end

end Work.KT.Fund
