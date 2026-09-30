import Mathlib
import Submission.Work.Pi6.EFACTS.Basic
import Submission.Work.Pi6.EFACTS.LowDefs
import Submission.Work.Pi6.EFACTS.FibreRing
import Submission.Work.Pi6.EFACTS.Z.WangThetaCupLow
import Submission.Work.Pi6.EFACTS.Z.WangThetaCupThree

/-!
# The transgression coefficients of the cover

For the cover `E = Ecov g3` (so `b = 3`, `p = proj g3`, `F = fib g3`) and a class
`x ∈ H²(F)`:

* `θ_{-1}(x) = c₁ • 1` (a multiple of the unit),
* `θ₁(x²) = 2 • (x ⌣ θ_{-1} x)`,
* `θ₃(x³) = 3 • (x² ⌣ θ_{-1} x)`.

The integer coefficients `c_k = k c₁` (with `c₁ = ±1`) follow from these and the ring structure of
`H^*(F)` (`FibreRing.fibreRing`).
-/

open CategoryTheory CategoryTheory.Limits
open scoped Topology

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

namespace Work.Pi6.EFACTS

noncomputable section

/-- The outer trivialisation data of `proj g3`. -/
abbrev hTO {P3 : Type} [TopologicalSpace P3] (g3 : C(S3, P3)) :
    Work.StemsB.FibrewiseTrivial (proj g3) (Work.StemsB.sphLoopOuter 3)
      (Work.StemsB.dOuter 3) :=
  fibrewiseTrivial_proj_outer g3

/-- The inner trivialisation data of `proj g3`. -/
abbrev hTG {P3 : Type} [TopologicalSpace P3] (g3 : C(S3, P3)) :
    Work.StemsB.FibrewiseTrivial (proj g3) (Work.StemsB.sphLoopBig 3) shellPt :=
  fibrewiseTrivial_proj_big g3

/-- The inner degree transport of the low-degree Wang statement, for `b = 3`, is the identity. -/
theorem transT_inner {Y : Type} [TopologicalSpace Y] (v : Coh ℤ Y (2 + 2)) :
    Work.StemsB.transT Y (show (3 - 1) + (3 - 1) = (3 - 2) + 3 from by omega) v = v :=
  (Work.StemsB.transT_congr (show (3 - 1) + (3 - 1) = (3 - 2) + 3 from by omega)
      (show (3 - 1) + (3 - 1) = (3 - 2) + 3 from rfl) v).trans
    (Work.StemsB.transT_self (k := 4) rfl v)

/-- `cpow x 2 = x ⌣ x` (in the `cupT` spelling). -/
theorem cpow_two_eq_cupT {P3 : Type} [TopologicalSpace P3] (g3 : C(S3, P3))
    (x : Coh ℤ (fib g3) 2) :
    cpow x 2 = Work.StemsB.cupT ↥((proj g3) ⁻¹' {OnePoint.infty}) 2 2 x x := by
  show Work.Cohomology.cupH' ℤ (TopCat.toSSet.obj (TopCat.of (fib g3))) (2 * 1) 2 (cpow x 1) x
    = Work.StemsB.cupT ↥((proj g3) ⁻¹' {OnePoint.infty}) 2 2 x x
  rw [cpow_one_eq x]
  rfl

/-- **`θ₁(x²) = 2 · x ⌣ θ_{-1}(x)`** (the `k = 2` transgression coefficient). -/
theorem c2_eq {P3 : Type} [TopologicalSpace P3] (g3 : C(S3, P3)) (x : Coh ℤ (fib g3) 2) :
    Work.StemsB.wangTheta 3 (by norm_num) (proj g3) shellPt (hTG g3) (hTO g3) 1 (cpow x 2)
      = (2 : ℤ) • cup ℤ (fib g3) 2 0 x
          (wangThetaLow 3 (by norm_num) (Ecov g3) (proj g3) (isHurewiczFibration_proj g3)
            (hTO g3) shellPt (hTG g3) x) := by
  have h := Work.StemsB.wangTheta_cup_low 3 (by norm_num) (Ecov g3) (proj g3) shellPt
    (hTG g3) (hTO g3) x
  rw [Work.StemsB.coeff_odd 3 (by decide : Odd 3)] at h
  simp only [Work.StemsB.transT_self] at h
  rw [transT_inner (Y := ↥((proj g3) ⁻¹' {OnePoint.infty}))
    (Work.StemsB.cupT ↥((proj g3) ⁻¹' {OnePoint.infty}) 2 2 x x)] at h
  rw [cpow_two_eq_cupT g3 x]
  exact h

/-- Concrete transport-stripping helpers for the `b = 3` instances of the ported statements. -/
theorem transT_h1 {Y : Type} [TopologicalSpace Y] (v : Coh ℤ Y (2 * 3 - 3 + 1)) :
    Work.StemsB.transT Y (show 2 * 3 - 3 + 1 = (3 - 1) + (3 - 1) from by omega) v = v :=
  (Work.StemsB.transT_congr (show 2 * 3 - 3 + 1 = (3 - 1) + (3 - 1) from by omega)
      (show 2 * 3 - 3 + 1 = (3 - 1) + (3 - 1) from rfl) v).trans
    (Work.StemsB.transT_self (k := 2 * 3 - 3 + 1) rfl v)

theorem transT_h2 {Y : Type} [TopologicalSpace Y]
    (v : Coh ℤ Y ((3 - 1) + ((3 - 2) + 3))) :
    Work.StemsB.transT Y (show (3 - 1) + ((3 - 2) + 3) = (2 * 3 - 3) + 3 from by omega) v = v :=
  (Work.StemsB.transT_congr (show (3 - 1) + ((3 - 2) + 3) = (2 * 3 - 3) + 3 from by omega)
      (show (3 - 1) + ((3 - 2) + 3) = (2 * 3 - 3) + 3 from rfl) v).trans
    (Work.StemsB.transT_self (k := (3 - 1) + ((3 - 2) + 3)) rfl v)

theorem transT_h3 {Y : Type} [TopologicalSpace Y] (v : Coh ℤ Y (((3 - 2) + 3) + 0)) :
    Work.StemsB.transT Y (show ((3 - 2) + 3) + 0 = (3 - 1) + (3 - 1) from by omega) v = v :=
  (Work.StemsB.transT_congr (show ((3 - 2) + 3) + 0 = (3 - 1) + (3 - 1) from by omega)
      (show ((3 - 2) + 3) + 0 = (3 - 1) + (3 - 1) from rfl) v).trans
    (Work.StemsB.transT_self (k := ((3 - 2) + 3) + 0) rfl v)

/-- Concrete transport-stripping helpers for the high Leibniz rule at `x² ⌣ x²`. -/
theorem transT_c4a {Y : Type} [TopologicalSpace Y] (v : Coh ℤ Y ((1 + 3) + (1 + 3))) :
    Work.StemsB.transT Y (show (1 + 3) + (1 + 3) = (1 + 1 + 3) + 3 from by omega) v = v :=
  (Work.StemsB.transT_congr (show (1 + 3) + (1 + 3) = (1 + 1 + 3) + 3 from by omega)
      (show (1 + 3) + (1 + 3) = (1 + 1 + 3) + 3 from rfl) v).trans
    (Work.StemsB.transT_self (k := (1 + 3) + (1 + 3)) rfl v)

theorem transT_c4b {Y : Type} [TopologicalSpace Y] (v : Coh ℤ Y ((1 + 3) + (1 + 1))) :
    Work.StemsB.transT Y (show (1 + 3) + (1 + 1) = (1 + 1 + 3) + 1 from by omega) v = v :=
  (Work.StemsB.transT_congr (show (1 + 3) + (1 + 1) = (1 + 1 + 3) + 1 from by omega)
      (show (1 + 3) + (1 + 1) = (1 + 1 + 3) + 1 from rfl) v).trans
    (Work.StemsB.transT_self (k := (1 + 3) + (1 + 1)) rfl v)

theorem transT_c4c {Y : Type} [TopologicalSpace Y] (v : Coh ℤ Y ((1 + 1) + (1 + 3))) :
    Work.StemsB.transT Y (show (1 + 1) + (1 + 3) = (1 + 1 + 3) + 1 from by omega) v = v :=
  (Work.StemsB.transT_congr (show (1 + 1) + (1 + 3) = (1 + 1 + 3) + 1 from by omega)
      (show (1 + 1) + (1 + 3) = (1 + 1 + 3) + 1 from rfl) v).trans
    (Work.StemsB.transT_self (k := (1 + 1) + (1 + 3)) rfl v)

/-- **The high Leibniz rule at `x² ⌣ x²`**: `θ₅(x² ⌣ x²) = x² ⌣ θ₁(x²) + θ₁(x²) ⌣ x²`. -/
theorem c4_high {P3 : Type} [TopologicalSpace P3] (g3 : C(S3, P3)) (x : Coh ℤ (fib g3) 2) :
    Work.StemsB.wangTheta 3 (by norm_num) (proj g3) shellPt (hTG g3) (hTO g3) 5
        (Work.StemsB.cupT ↥((proj g3) ⁻¹' {OnePoint.infty}) 4 4
          (Work.StemsB.cupT ↥((proj g3) ⁻¹' {OnePoint.infty}) 2 2 x x)
          (Work.StemsB.cupT ↥((proj g3) ⁻¹' {OnePoint.infty}) 2 2 x x))
      = Work.StemsB.cupT ↥((proj g3) ⁻¹' {OnePoint.infty}) 4 2
            (Work.StemsB.cupT ↥((proj g3) ⁻¹' {OnePoint.infty}) 2 2 x x)
            (Work.StemsB.wangTheta 3 (by norm_num) (proj g3) shellPt (hTG g3) (hTO g3) 1
              (Work.StemsB.cupT ↥((proj g3) ⁻¹' {OnePoint.infty}) 2 2 x x))
        + Work.StemsB.cupT ↥((proj g3) ⁻¹' {OnePoint.infty}) 2 4
            (Work.StemsB.wangTheta 3 (by norm_num) (proj g3) shellPt (hTG g3) (hTO g3) 1
              (Work.StemsB.cupT ↥((proj g3) ⁻¹' {OnePoint.infty}) 2 2 x x))
            (Work.StemsB.cupT ↥((proj g3) ⁻¹' {OnePoint.infty}) 2 2 x x) := by
  have h := Work.StemsB.wangTheta_cup 3 (by norm_num) (Ecov g3) (proj g3) shellPt (hTG g3) (hTO g3)
    1 1 (Work.StemsB.cupT ↥((proj g3) ⁻¹' {OnePoint.infty}) 2 2 x x)
    (Work.StemsB.cupT ↥((proj g3) ⁻¹' {OnePoint.infty}) 2 2 x x)
  norm_num at h
  simp only [one_smul, Work.StemsB.transT_self, transT_c4a, transT_c4b, transT_c4c] at h
  exact h

end

end Work.Pi6.EFACTS
