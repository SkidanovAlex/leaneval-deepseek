/-
# `Submission.Work.FIPiChain.Defs` --- the vocabulary of the `PiBig` endgame chapter

This chapter reruns the FIChain endgame (`Submission/Work/FIChain/`) on the **integrated** windows
that the seven round-6 areas actually produce, so that the only remaining input of the challenge is
the area-4 hole and the (unprovable, and unnecessary) `PiRemoval` is deleted from the chain.  See
`Submission/Work/FIFinal/PIREMOVAL_LEAD.md` for the lead design.

The chapter uses FIChain's vocabulary verbatim (`Yc`, `zc`, `sc`, `Jc`, `Deltac`, `Pzc`, `etac`,
`AcountAtilC`, `atilc`, `wc`, `S3minusC`, `S3avgFix`, `BprimeWindowInt`, `RhoWindowInt2`,
`SieveInput`), and adds exactly one definition of its own:

* `Grho N C t` --- the inner `s`-integral of the `rho`-window weight at position `t`,

      `Grho N C t = ∫_{1}^{C} (Σ_{m ≤ N} wc m · |XrhoC atilc N m s t (2t)|) / s  ds`.

  With this notation `RhoWindowInt2 atilc N wc E C lo hi` is *by definition* the statement
  `∫_{lo}^{hi} Grho N C t / t ≤ E` (`RhoWindowInt2_atilc_iff`, `rfl`).

The whole chapter lives in the namespace `Work.FIPiChain`; FIChain's names are opened so that the
copied chain modules read exactly like the originals.
-/
import Mathlib
import Submission.Work.FIChain.Defs
import Submission.Work.FIChain.BprimeWindowIntegrated
import Submission.Work.FIChain.RhoWindowIntegrated2
import Submission.Work.FIChain.Aw_le_of_PiBig
import Submission.Work.FIChain.abs_S3minusC_le
import Submission.Work.FIChain.measurable_s3halves
import Submission.Work.FIChain.exists_z1_le_of_measurable_zavg

set_option autoImplicit false

namespace Work.FIPiChain

open Finset MeasureTheory
open scoped BigOperators Interval

attribute [local instance] Classical.propDecidable

noncomputable section

/-- The `rho`-window weight at position `t`, integrated over the truncation level `s ∈ (1, C]`:

`Grho N C t = ∫_{1}^{C} (Σ_{m ≤ N} wc m · |XrhoC atilc N m s t (2t)|) / s  ds`.

By definition the FIChain `rho`-window hypothesis is `∫_{lo}^{hi} Grho N C t / t ≤ E`
(`RhoWindowInt2_atilc_iff`). -/
def Grho (N : ℕ) (C t : ℝ) : ℝ :=
  ∫ s in (1 : ℝ)..C,
    (∑ m ∈ Finset.Icc 1 N, Work.FIChain.wc m
      * |Work.FITop.XrhoC Work.FIChain.atilc N m s t (2 * t)|) / s

/-- The `rho`-window hypothesis of the chapter, in the `Grho` notation. -/
theorem RhoWindowInt2_atilc_iff (N : ℕ) (E C lo hi : ℝ) :
    Work.FIChain.RhoWindowInt2 Work.FIChain.atilc N Work.FIChain.wc E C lo hi ↔
      (∫ t in lo..hi, Grho N C t / t) ≤ E :=
  Iff.rfl

/-- The `B'`-window hypothesis of the chapter, unfolded. -/
theorem BprimeWindowInt_atilc_iff (N : ℕ) (E lo hi : ℝ) :
    Work.FIChain.BprimeWindowInt Work.FIChain.atilc N Work.FIChain.wc E lo hi ↔
      (∫ t in lo..hi,
        (∑ m ∈ Finset.Icc 1 N, Work.FIChain.wc m
          * |Submission.ASP.Xsum Work.FIChain.atilc N m t (2 * t)|) / t) ≤ E :=
  Iff.rfl

/-- `Grho` is nonnegative (the integrand is an absolute value). -/
theorem Grho_nonneg (N : ℕ) {C : ℝ} (hC : 1 ≤ C) (t : ℝ) : 0 ≤ Grho N C t := by
  rw [Grho]
  refine intervalIntegral.integral_nonneg hC (fun s hs => div_nonneg ?_ (le_trans zero_le_one hs.1))
  exact Finset.sum_nonneg (fun m _ =>
    mul_nonneg (by rw [Work.FIChain.wc, Work.FITop.w0]; positivity) (abs_nonneg _))

end

end Work.FIPiChain
