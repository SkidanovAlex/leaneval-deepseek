import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseFixB1.RegimeAux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseFixB1S.noDLBoxDataAtWholeBox` — **no `DLBoxData` lives at the whole box**

`Submission/Work/BoseFixB1B/wholeBoxSmallbox.lean` reduces the low-state count window to a single
*seed* `Work.BoseFixB1B.DLSeedAt v R`: for every admissible `μ` and every count `n` there should be
a `DLBoxData` at the **whole-box** side `D.s = sideAt μ (a v)`.  That file records that "no
`DLBoxData` has ever been *constructed* in this tree" — the theorem below shows the reason is not
scarcity of effort: **no such bundle can exist at all.**

Every `DLBoxData` carries the regime datum

    hblkMax : Work.DLRepoint.D4Regime D.s D.μ D.R0 D.K_B D.Ct D.c₀ D.cgap D.v (⌊9·D.μ·D.s³⌋−1),

and `Work.DLRepoint.D4Regime.hchi` reads

    (D.μ · a D.v · D.s ^ 2) · (1600 + 1850 · chiSup ^ 2) ≤ 1 .

At the whole box, however, `one_le_mu_a_sideAt_sq` gives `1 ≤ μ · a v · (sideAt μ (a v))²` as soon
as `μ (a v)³ ≤ 1` (the bundle itself forces this, through
`hKB1 : 1 ≤ K_B` and `hKBcap : K_B³ (μ(av)³)^{1/2} ≤ 1`), while `1600 + 1850·chiSup² ≥ 1600`.
Hence `1600 ≤ 1` — a contradiction.

**Consequence.**  `Work.BoseFixB1B.DLSeedAt v R` is *unprovable* (for every `v` with `0 < a v` and
every `ε₀ > 0` that admits a chemical potential), so the whole-box route to the count window
(`Work.BoseFixB1B.wholeBoxSmallboxBound_of_seed`, `Work.BoseFixB1B.lowCountBound_of_seed`) is
**dead**: its hypothesis is unsatisfiable, not merely unproved.  This confirms, from the bundle
side, the obstruction diagnosed in
`Submission/Work/BoseFixB1S/FINDING_wholeBoxSmallboxBound_blocked.md` (the corpus's DL regimes are
designed for `s ≲ (μa)^{-1/2}/120`, not for `s = sideAt μ (a v) = (μa)^{-1/2}K_ℓ`).
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Real Topology BigOperators

namespace Work.BoseFixB1S

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

/-- A negative exponent of a number in `(0,1]` gives a value `≥ 1`. -/
private theorem one_le_rpow_of_le_one {t y : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) (hy : y ≤ 0) :
    1 ≤ t ^ y := by
  have h1 : t ^ (-y) ≤ 1 := Real.rpow_le_one ht0.le ht1 (by linarith)
  have h2 : (0 : ℝ) < t ^ (-y) := Real.rpow_pos_of_pos ht0 _
  have h3 : (1 : ℝ) ≤ (t ^ (-y))⁻¹ := by
    rw [one_le_inv₀ h2]; exact h1
  rw [← Real.rpow_neg ht0.le] at h3
  simpa using h3

/-- **The whole-box arithmetic**: `1 ≤ μ · A · (sideAt μ A)²` whenever `0 < A`, `0 < μ`,
`μA³ ≤ 1`.  With `t = μA³`, `sideAt μ A = A·t^{−163/323}` (`Work.BoseFixB1.sideAt_eq_fsXp`), so
`μA·(sideAt μ A)² = t·t^{−326/323} = t^{−3/323} ≥ 1`. -/
theorem one_le_mu_a_sideAt_sq {A μ : ℝ} (hA : 0 < A) (hμ : 0 < μ) (ht : μ * A ^ 3 ≤ 1) :
    1 ≤ μ * A * (Work.BoseBox.sideAt μ A) ^ 2 := by
  have ht0 : 0 < μ * A ^ 3 := mul_pos hμ (pow_pos hA 3)
  set t : ℝ := μ * A ^ 3 with htd
  have ht1 : t ≤ 1 := by rw [htd]; exact ht
  rw [Work.BoseFixB1.sideAt_eq_fsXp hA hμ]
  -- `(fsXp t (−163))² = t^{−326/323}`
  have hsq : (Work.BoseBox.fsXp t (-163)) ^ 2 = t ^ (-(326 / 323) : ℝ) := by
    rw [Work.BoseBox.fsXp, ← Real.rpow_natCast (t ^ ((-163 : ℝ) / 323)) 2,
      ← Real.rpow_mul ht0.le]
    norm_num
  rw [mul_pow, hsq]
  -- `μ · A · A² = t`
  rw [show μ * A * (A ^ 2 * t ^ (-(326 / 323) : ℝ)) = (μ * A ^ 3) * t ^ (-(326 / 323) : ℝ)
    by ring]
  rw [← htd]
  have hcollapse : t * t ^ (-(326 / 323) : ℝ) = t ^ (-(3 / 323) : ℝ) := by
    calc t * t ^ (-(326 / 323) : ℝ) = t ^ (1 : ℝ) * t ^ (-(326 / 323) : ℝ) := by
          rw [Real.rpow_one]
      _ = t ^ ((1 : ℝ) + -(326 / 323)) := (Real.rpow_add ht0 1 (-(326 / 323))).symm
      _ = t ^ (-(3 / 323) : ℝ) := by norm_num
  rw [hcollapse]
  exact one_le_rpow_of_le_one ht0 ht1 (by norm_num)

/-- **There is no `DLBoxData` at the whole-box side.**  Given `0 < a v` and a chemical potential
with `μ (a v)³ ≤ 1` (which any `DLBoxData` forces on its own data), no `DLBoxData` whose box side is
`sideAt μ (a v)` and whose chemical potential is `μ` can exist. -/
theorem noDLBoxDataAtWholeBox {v : E3 → ℝ} {μ : ℝ} (hav : 0 < _root_.BoseGases.a v)
    (hμ : 0 < μ) (ht : μ * (_root_.BoseGases.a v) ^ 3 ≤ 1) :
    ¬ ∃ D : Submission.BoseGases.DLBoxData, D.v = v ∧ D.μ = μ ∧
        D.s = Work.BoseBox.sideAt μ (_root_.BoseGases.a v) := by
  rintro ⟨D, hvD, hμD, hsD⟩
  -- the bundle forces `D.μ (a D.v)³ ≤ 1` through `hKB1` and `hKBcap`
  have hKB3 : (1 : ℝ) ≤ D.K_B ^ 3 := by
    have h0 : 0 < D.K_B := lt_of_lt_of_le one_pos D.hKB1
    nlinarith [D.hKB1, sq_nonneg D.K_B, sq_nonneg (D.K_B - 1)]
  have hsq1 : (D.μ * (_root_.BoseGases.a D.v) ^ 3) ≤ 1 := by
    have hle : (D.μ * (_root_.BoseGases.a D.v) ^ 3) ^ (1 / 2 : ℝ)
        ≤ D.K_B ^ 3 * (D.μ * (_root_.BoseGases.a D.v) ^ 3) ^ (1 / 2 : ℝ) := by
      calc (D.μ * (_root_.BoseGases.a D.v) ^ 3) ^ (1 / 2 : ℝ)
          = 1 * (D.μ * (_root_.BoseGases.a D.v) ^ 3) ^ (1 / 2 : ℝ) := (one_mul _).symm
        _ ≤ D.K_B ^ 3 * (D.μ * (_root_.BoseGases.a D.v) ^ 3) ^ (1 / 2 : ℝ) :=
            mul_le_mul_of_nonneg_right hKB3
              (Real.rpow_nonneg (mul_nonneg D.hμ.le (pow_nonneg (le_of_lt D.hav) 3)) _)
    have h2 : (D.μ * (_root_.BoseGases.a D.v) ^ 3) ^ (1 / 2 : ℝ) ≤ 1 :=
      le_trans hle D.hKBcap
    have ht0 : 0 < D.μ * (_root_.BoseGases.a D.v) ^ 3 :=
      mul_pos D.hμ (pow_pos D.hav 3)
    have hsq : ((D.μ * (_root_.BoseGases.a D.v) ^ 3) ^ (1 / 2 : ℝ)) ^ 2
        = D.μ * (_root_.BoseGases.a D.v) ^ 3 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul ht0.le]
      norm_num
    calc D.μ * (_root_.BoseGases.a D.v) ^ 3
        = ((D.μ * (_root_.BoseGases.a D.v) ^ 3) ^ (1 / 2 : ℝ)) ^ 2 := hsq.symm
      _ ≤ 1 ^ 2 := by nlinarith [h2, Real.rpow_nonneg ht0.le (1 / 2 : ℝ)]
      _ = 1 := by norm_num
  -- the bundle's `hchi` in the bundle's own data, against the whole-box arithmetic
  have hsD' : D.s = Work.BoseBox.sideAt D.μ (_root_.BoseGases.a D.v) := by
    rw [hsD, hμD, hvD]
  have hgeo : 1 ≤ D.μ * (_root_.BoseGases.a D.v)
      * (Work.BoseBox.sideAt D.μ (_root_.BoseGases.a D.v)) ^ 2 :=
    one_le_mu_a_sideAt_sq D.hav D.hμ hsq1
  have hgeos : 1 ≤ D.μ * (_root_.BoseGases.a D.v) * D.s ^ 2 := by
    rw [hsD']; exact hgeo
  have hcs : (0 : ℝ) ≤ Submission.BoseGases.chiSup ^ 2 := sq_nonneg _
  have hY : (1600 : ℝ) ≤ 1600 + 1850 * Submission.BoseGases.chiSup ^ 2 := by linarith
  have hchi : (1600 : ℝ) ≤ (D.μ * (_root_.BoseGases.a D.v) * D.s ^ 2)
      * (1600 + 1850 * Submission.BoseGases.chiSup ^ 2) := by
    calc (1600 : ℝ) ≤ 1600 + 1850 * Submission.BoseGases.chiSup ^ 2 := hY
      _ = 1 * (1600 + 1850 * Submission.BoseGases.chiSup ^ 2) := (one_mul _).symm
      _ ≤ (D.μ * (_root_.BoseGases.a D.v) * D.s ^ 2)
            * (1600 + 1850 * Submission.BoseGases.chiSup ^ 2) :=
          mul_le_mul_of_nonneg_right hgeos (by linarith)
  linarith [hchi, D.hblkMax.hchi]

end Work.BoseFixB1S
