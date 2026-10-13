/-
# `bridge_Iz_interval` — the support bridge for the cut-off integral

`Work.Spaces.Iz = Set.Ici 0 = [0,∞)`.  If `F` vanishes on `(0,∞)` outside the support window
`[cA k, cB k]` of the logarithmic cut-off `χ k` (`0 < cA k`, `cA k ≤ cB k`), then the integral of
`F` over `Iz` is the *interval* integral of `F` over `cA k .. cB k` — no integrability hypothesis
is needed, only the a.e. vanishing, and the possible junk values of `F` at `z = 0` and on `z < 0`
are killed because `{0}` is a null set.

The reduction is exactly the one proved in
`Work.FTS.EllipticEst.Aux.setIntegral_Ioi_eq_intervalIntegral_of_support`, preceded by
`MeasureTheory.integral_Ici_eq_integral_Ioi` to convert the half-open `[0,∞)` into `(0,∞)`.
-/
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.EllSol.PkgK5.InterpTraceCore

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.PkgK5.InterpTrace

set_option autoImplicit false
-- `hχ` is part of the (fixed) statement but is not needed: the bridge only uses the support
-- window `cA k ≤ cB k` of the cut-off, together with `0 < cA k`.
set_option linter.unusedVariables false

open MeasureTheory Set

theorem bridge_Iz_interval {χ : ℕ → ℝ → ℝ} {K : ℝ}
    (hχ : Work.FTS.EllSol.PkgK5.CutFam χ K) (k : ℕ) (F : ℝ → ℝ)
    (hzero : ∀ z : ℝ, 0 < z → (z < Work.FTS.EllSol.PkgK5.cA k ∨ Work.FTS.EllSol.PkgK5.cB k < z) → F z = 0) :
    (∫ z in Work.Spaces.Iz, F z) = ∫ z in (Work.FTS.EllSol.PkgK5.cA k)..(Work.FTS.EllSol.PkgK5.cB k), F z := by
  have ha : 0 < Work.FTS.EllSol.PkgK5.cA k := Work.FTS.EllSol.PkgK5.cA_pos k
  have hab : Work.FTS.EllSol.PkgK5.cA k ≤ Work.FTS.EllSol.PkgK5.cB k :=
    Work.FTS.EllSol.PkgK5.cA_le_cB k
  -- `[0,∞)` and `(0,∞)` differ by the null set `{0}`
  have h1 : (∫ z in Work.Spaces.Iz, F z) = ∫ z in Set.Ioi 0, F z := by
    rw [Work.Spaces.Iz]
    exact integral_Ici_eq_integral_Ioi
  -- `F` vanishes a.e. on `(0,∞) \ [cA k, cB k]`
  have h2 : (∫ z in Set.Ioi 0, F z) = ∫ z in Set.Icc (Work.FTS.EllSol.PkgK5.cA k)
      (Work.FTS.EllSol.PkgK5.cB k), F z :=
    MeasureTheory.setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
      (fun x hx => by simp only [Set.mem_Ioi]; linarith [hx.1, ha])
      (fun x hx => by
        have hx2 : x < Work.FTS.EllSol.PkgK5.cA k ∨ Work.FTS.EllSol.PkgK5.cB k < x := by
          simpa only [Set.mem_Icc, not_and_or, not_le] using hx.2
        exact hzero x hx.1 hx2)
  rw [h1, h2, MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab]

end Work.FTS.EllSol.PkgK5.InterpTrace
