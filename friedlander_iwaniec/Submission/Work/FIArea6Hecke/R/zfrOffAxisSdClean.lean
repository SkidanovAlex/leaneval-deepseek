import Mathlib
import Submission.Work.FIArea6Hecke.R.zfrOffAxisSdSelfDual
import Submission.Work.FIArea6Hecke.R.zfrOffAxisSdNonSelfDualV2

/-!
# `Submission.Work.FIArea6Hecke.R.zfrOffAxisSdClean`

**The de la Vallée Poussin zero-free region (16.20) for the corrected exceptional set**, i.e. the
statement `Work.FIArea6Hecke.R.ZFRoffAxisSd`, assembled from its two cases:

* `Work.FIArea6Hecke.R.zfrOffAxisSdSelfDual` — the self-dual case (`psi^2 = 1` on the primary
  units), where the only exception admitted by the statement is `im s = 0`, obtained from the
  proved complex zero-free region for real characters
  (`Work.FIArea6Hecke.R.realPsiComplexZeroFree`) by the transfer
  `Work.FIArea6Hecke.R.lval_eq_of_same_series`;
* `Work.FIArea6Hecke.R.zfrOffAxisSdNonSelfDual` — the complement, where the classical `(3,4,1)`
  argument carries no exceptional zero.

The two constants are combined by taking their minimum; the region of the statement is then
contained in both regions, since `log(4d + |m| + |im s|) > 0`.
-/
set_option autoImplicit false

namespace Work.FIArea6Hecke.R

open Complex Metric
open scoped Topology BigOperators

noncomputable section

/-- **`ZFRoffAxisSd` from its two cases.** -/
theorem zfrOffAxisSdClean : Work.FIArea6Hecke.R.ZFRoffAxisSd := by
  obtain ⟨c1, hc1, h1⟩ := zfrOffAxisSdSelfDual
  obtain ⟨c2, hc2, h2⟩ := zfrOffAxisSdNonSelfDualV2
  refine ⟨min c1 c2, lt_min hc1 hc2, ?_⟩
  intro d chi m Lam hd hchi hAn hagr s hreg hsle2 hexc
  have hlogpos : 0 < Real.log (4 * (d : ℝ) + |(m : ℝ)| + |s.im|) := by
    apply Real.log_pos
    have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    have hm0 : (0 : ℝ) ≤ |(m : ℝ)| := abs_nonneg _
    have hi0 : (0 : ℝ) ≤ |s.im| := abs_nonneg _
    nlinarith
  have hreg1 : 1 - c1 / Real.log (4 * (d : ℝ) + |(m : ℝ)| + |s.im|) < s.re := by
    have h3 : min c1 c2 / Real.log (4 * (d : ℝ) + |(m : ℝ)| + |s.im|)
        ≤ c1 / Real.log (4 * (d : ℝ) + |(m : ℝ)| + |s.im|) :=
      div_le_div_of_nonneg_right (min_le_left _ _) hlogpos.le
    linarith
  have hreg2 : 1 - c2 / Real.log (4 * (d : ℝ) + |(m : ℝ)| + |s.im|) < s.re := by
    have h3 : min c1 c2 / Real.log (4 * (d : ℝ) + |(m : ℝ)| + |s.im|)
        ≤ c2 / Real.log (4 * (d : ℝ) + |(m : ℝ)| + |s.im|) :=
      div_le_div_of_nonneg_right (min_le_right _ _) hlogpos.le
    linarith
  by_cases hsd : Work.FIArea6Hecke.R.SelfDual d chi m
  · refine h1 d chi m Lam hd hchi hAn hagr hsd s hreg1 hsle2 (fun h => hexc ⟨h, hsd⟩)
  · exact h2 d chi m Lam hd hchi hAn hagr hsd s hreg2 hsle2

end

end Work.FIArea6Hecke.R
