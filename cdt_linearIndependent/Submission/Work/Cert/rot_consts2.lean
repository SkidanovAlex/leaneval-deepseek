import Mathlib
import Submission.Work.Cert.Spec
import Submission.Work.Cert.rot_aux

/-! Guidance from the project lead (the requester):

Lead — certificate v4 (2026-09-29): the conjunct-2 certificate now lives on the 1024-grid (`NARC2 : Nat := 1024` in
Defs.lean; `WR2`, `WI2` = round(S·cos/sin(2π/1024)); `gridStep2`, `arcOK2`, `arcsOK2`), with Spec Props `RotConsts2`,
`ArcCover2`, `DENS2 = 7168000`, `Conj2Cert2` — literal copies of `RotConsts`' W-part, `ArcCover`, `DENS`, `Conj2Cert`
with 4096 → NARC2, gridStep → gridStep2, DENS → DENS2 (read the end of Submission/Work/Cert/Spec.lean and Defs.lean).
Your target is a COPY-EDIT of an already PROVED 4096-grid lemma (named below): copy its file(s) into new files
(new names, e.g. suffix 2 / directory v4 — do not edit or import-break the old ones), replace 4096 by NARC2
(or by 1024 where a numeral is needed: `NARC2 = 1024` is `rfl`; give a literal-level helper
`(NARC2 : ℝ) = 1024 := by norm_num [NARC2]`), WR/WI/gridStep/arcsOK/DENS by WR2/WI2/gridStep2/arcsOK2/DENS2, and
re-check the numeric side conditions (they only get easier: 1024 steps instead of 4096, same 65536/S drift budget,
same ETOL). Chunk data: Chunks/C000..C096 (≤ 60 leaves, `okC### : arcsOK2 endC###.1 endC###.2 arcsC### = true`),
Final.lean (`link_ok`, `first_ok`, `total_ok`, `vals_length : vals.length = 3 * 1024`, `arcs_kj` over range 1024,
`DEN = 7168000`). Oleans are being rebuilt by the lead (unit cdt-cert-v4, ~1 h); you will be told when they land.
NEVER `decide`/`rfl` over arcsAll or chunk data outside the chunk theorems.

Starting point: Submission/Work/Cert/rot_consts.lean and its helpers (rotW_bound.lean, rot_aux.lean) — the W-part `‖cx WR WI − rot (1/4096)‖ ≤ 2/S` is proved there; redo it for WR2/WI2 and rot(1/1024) (|2π/1024| ≈ 0.0061, even fewer Taylor terms needed).
-/

/-!
# `RotConsts2`: the grid step of the conjunct-2 certificate

`RotConsts2` (`Submission/Work/Cert/Spec.lean`) asserts that the integer pair
`(WR2, WI2) = (109949092978033035917, 674647651843760786)` of `Defs.lean`, divided by the scale
`S = 2^40·10^8`, is within `2/S` of `rot (1/1024) = e^{2πi/1024}`.

The constants are the correctly rounded values of `S·cos(2π/1024)` and `S·sin(2π/1024)`; here is
the exact statement of that computation.  With `θ_lo = 2·3.14159265358979323846/1024` and
`θ_hi = 2·3.14159265358979323847/1024` (so `θ_lo ≤ 2π/1024 ≤ θ_hi`, `Real.pi_gt_d20`/`pi_lt_d20`),
the twenty-six-term Taylor enclosure of `e^{iθ}` gives

  `109949092978033035917 ≤ S·cos(2π/1024) ≤ 109949092978033035918`
  `674647651843760786     ≤ S·sin(2π/1024) ≤ 674647651843760787`

so each coordinate of `(WR2, WI2)` is within `1` of the exact scaled value, which is far inside
the `2/S` budget.  The proof below is the same six lines as `rotW_bound`
(`Submission/Work/Cert/rotW_bound.lean`): the glue lemma `rot_bound_aux` of
`Submission/Work/Cert/rot_aux.lean` reduces everything to four exact rational comparisons
discharged by `norm_num` — no numerics are evaluated by reflection in the kernel.
-/

namespace Work.Cert

open Complex Submission.CDTPlan Work.CNum

/-- `1/(NARC2 : ℝ) = 1/1024`, the grid angle of the `NARC2`-grid certificate. -/
lemma rc2_NARC2_cast : ((NARC2 : ℝ)) = 1024 := by norm_num [NARC2]

/-- `e^{2πi/1024}` correctly rounded at scale `S` (the grid step of the conjunct-2 certificate). -/
theorem rotW2_bound : ‖cx WR2 WI2 - rot (1 / 1024)‖ ≤ 2 / (S : ℝ) := by
  open Work.CNum in
  have h4 : 2 * (3.14159265358979323847 : ℝ) * (1 / 1024) ≤ Real.pi / 4 := by
    have h1 : 2 * (3.14159265358979323847 : ℝ) * (1 / 1024)
        ≤ (3.14159265358979323846 : ℝ) / 4 := by norm_num
    have h2 : (3.14159265358979323846 : ℝ) / 4 ≤ Real.pi / 4 := by
      linarith [Real.pi_gt_d20]
    linarith
  refine rot_bound_aux (1 / 1024) WR2 WI2 (by norm_num) h4 ?_ ?_ ?_ ?_
  · rw [Work.CNum.cosP]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    norm_num [S, WR2]
  · rw [Work.CNum.cosP]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    norm_num [S, WR2]
  · rw [Work.CNum.sinP]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    norm_num [S, WI2]
  · rw [Work.CNum.sinP]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    norm_num [S, WI2]

theorem rot_consts2 : RotConsts2 := by
  unfold RotConsts2
  rw [rc2_NARC2_cast]
  exact rotW2_bound

end Work.Cert
