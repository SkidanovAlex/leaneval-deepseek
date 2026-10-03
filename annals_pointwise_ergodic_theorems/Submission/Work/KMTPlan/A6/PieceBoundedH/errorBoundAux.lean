/-
# Auxiliary bookkeeping for the §6 model-approximation error at bounded heights

This module collects the elementary facts shared by the two halves of

  `Work.KMTPlan.A6.PieceBoundedH.errorBound`

(the `ℓ¹(ℤ;V^r)` bound for `mainPartTuple − modelTupleRep` at bounded heights `lcL ≤ B`,
`1 ≤ l₁`, `1 ≤ l₂`, arbitrary `ρ ∈ (0,1]`):

* `lmaxR_eq_lcL'`, `lmaxR_le_of_lcL_le` — the height `lmaxR` of the §6 weights is the real cast
  of `lcL`, hence bounded by the height bound `B` of the statement;
* `uRep_le_uRep_B` — the band parameter `uRep ρ l₁ l₂ k₁ k₂` is monotone in the quadruple, so
  bounded by `uRep ρ B B B B` on the range `lcL ≤ B`; this is what turns "off the band" into a
  bound on the physical scale `N` (hence, by lacunarity, into *finitely many* contributing
  scales).

Nothing here is used at a single place: the off-band half needs the boundedness of `uRep`, and
the on-band half needs the boundedness of `repWeight` (through `lmaxR`).

## How the two halves of `Work.KMTPlan.A6.PieceBoundedH.errorBound` are meant to be proved

**`errorBoundOnBand`** (`Submission/Work/KMTPlan/A6/PieceBoundedH/errorBoundOnBand.lean`):
`Work.KMTAreas.A7.VarNormTsumLp` bounds `‖V^r uOn‖₁ ≤ ∑' n, 4 * ‖uOn n‖₁`; on the scales satisfying
`hiCore ∧ bandCond`, `Work.KMTAreas.A7.repSingleScale` (mass hypothesis from
`Work.KMTAreas.A7.RepMassBound`, which is stated for `0 < ρ ≤ 1` and — unlike `repMain` — needs
neither `AreaA1` nor `ρ ≤ 1/(4C₀)`) gives
`‖uOn n‖₁ ≤ ofReal D * ofReal (repWeight A ρ l₁ l₂ k₁ k₂) * ofReal (⌊a n⌋⁻¹) * (‖f‖₂ * ‖g‖₂)`
(the exponent `(2⁻¹ + 2⁻¹)⁻¹` is `1`, `inv_two_add_inv_two_inv`); `lcL ≤ B` bounds both
`repWeight` and `uRep` (`lmaxR_le_of_lcL_le`, `uRep_le_uRep_B`).  Finally
`Work.KMTAreas.A7.invFloor_tsum_le` bounds `∑' n, ((⌊a n⌋ : ℕ) : ℝ)⁻¹` by a constant of `Λ` alone
(choose it with `Classical.choose` exactly as `Work.KMTAreas.A7.repMain` does), and
`ENNReal.ofReal_tsum_of_nonneg` moves the `ofReal` through the `tsum`.

**`errorBoundOffBand`** (`Submission/Work/KMTPlan/A6/PieceBoundedH/errorBoundOffBand.lean`): off the
band `modelTupleRep = 0` and `mainPartTuple = varpPiece (kmtPj ρ) P P.natDegree (⌊a n⌋) …`, so the
summand is the concrete column `Work.Analysis.EndVar.varpPiece`; `offBand_lt_nBound` puts the
support in `Finset.range (nBound Λ (offBandLog ρ B) + 1)`,
`Submission.SingleScale.eLpNorm_variationalNorm_le_sum` (finite support) together with the crude
single-scale bound `Work.KMTAreas.A7.RepOffBandCrude` (at `Boff := max B (offBandLog ρ B)`) and
`Work.KMTAreas.A7.term_sum_le` finish.

Both halves are *unconditional* in `f`, `g` (no `MemLp` hypothesis): the degenerate cases
`eLpNorm f 2 = 0` / `g = 0` (whence the family vanishes, `Work.KMTAreas.A7.repMainPartTuple_zero_*`,
`repModelTupleRep_zero_*`, `rep_eq_zero_of_eLpNorm_count_eq_zero`) and `eLpNorm f 2 = ⊤` (whence the
right-hand side is `⊤`, `ENNReal.mul_top`/`ENNReal.top_mul`) are handled as in
`Work.KMTAreas.A7.repMain`.
-/
import Mathlib
import Submission.Work.KMTAreas.A7.ExceptionalSupport
import Submission.Work.KMTAreas.A7.RepAux
import Submission.Work.KMTAreas.A7.RepMassBound
import Submission.Work.KMTAreas.A7.RepOffBandCrude

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.KMTPlan.A6.PieceBoundedH

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open PointwiseErgodicTheorems Submission.PointwiseErgodicTheorems

/-- The height `lmaxR` of the §6 weights is the real cast of `lcL`. -/
theorem lmaxR_eq_lcL' (l₁ l₂ k₁ k₂ : ℕ) :
    Work.KMTAreas.A7.lmaxR l₁ l₂ k₁ k₂ = (lcL l₁ l₂ k₁ k₂ : ℝ) := by
  rw [Work.KMTAreas.A7.lmaxR, ← lcL_eq]
  push_cast
  ring

/-- The height bound `lcL ≤ B` of the statement bounds `lmaxR`. -/
theorem lmaxR_le_of_lcL_le {l₁ l₂ k₁ k₂ B : ℕ} (h : lcL l₁ l₂ k₁ k₂ ≤ B) :
    Work.KMTAreas.A7.lmaxR l₁ l₂ k₁ k₂ ≤ (B : ℝ) := by
  rw [lmaxR_eq_lcL']
  exact_mod_cast h

/-- `lcL ≤ B` bounds each of the four height parameters. -/
theorem le_of_lcL_le {l₁ l₂ k₁ k₂ B : ℕ} (h : lcL l₁ l₂ k₁ k₂ ≤ B) :
    l₁ ≤ B ∧ l₂ ≤ B ∧ k₁ ≤ B ∧ k₂ ≤ B := by
  have h' : max (max l₁ l₂) (max k₁ k₂) ≤ B := by simpa only [lcL] using h
  refine ⟨?_, ?_, ?_, ?_⟩ <;> omega

/-- The window scale `uScale ρ` is monotone in the height (for `ρ ≥ 0`). -/
theorem uScale_mono (ρ : ℝ) (hρ : 0 ≤ ρ) : Monotone (Work.KMTAreas.A7.uScale ρ) :=
  Work.KMTAreas.A7.ExcSupport.scaleCount_mono 1 hρ

/-- **The band parameter is bounded on the height-bounded range.**  If `lcL l₁ l₂ k₁ k₂ ≤ B` then
`uRep ρ l₁ l₂ k₁ k₂ ≤ uRep ρ B B B B` (for `ρ ≥ 0`); indeed both the window scale
`uScale ρ (lcL …)` and the `max l₁ l₂ + 3` term are monotone in the quadruple. -/
theorem uRep_le_uRep_B (ρ : ℝ) (hρ : 0 ≤ ρ) {l₁ l₂ k₁ k₂ B : ℕ}
    (h : lcL l₁ l₂ k₁ k₂ ≤ B) :
    Work.KMTAreas.A7.uRep ρ l₁ l₂ k₁ k₂ ≤ Work.KMTAreas.A7.uRep ρ B B B B := by
  have hL : max (max l₁ l₂) (max k₁ k₂) ≤ B := by simpa only [lcL] using h
  have hmax : max (max l₁ l₂) (max k₁ k₂) ≤ max (max B B) (max B B) := by omega
  have hsc : Work.KMTAreas.A7.uScale ρ (max (max l₁ l₂) (max k₁ k₂))
      ≤ Work.KMTAreas.A7.uScale ρ (max (max B B) (max B B)) := uScale_mono ρ hρ hmax
  have hM : max l₁ l₂ + 3 ≤ max B B + 3 := by omega
  rw [Work.KMTAreas.A7.uRep]
  exact max_le_max hsc hM

/-- `(2 : ℝ≥0∞)⁻¹ + (2 : ℝ≥0∞)⁻¹ = 1`, and hence its inverse is `1`. -/
theorem inv_two_add_inv_two_inv :
    ((2 : ENNReal)⁻¹ + (2 : ENNReal)⁻¹)⁻¹ = 1 := by
  rw [ENNReal.inv_two_add_inv_two, inv_one]

/-! ## Off the band: the physical scale is bounded

The band condition of the §6 model is `k + 1 + 2 u ≤ Log N` for the two continuous scales; its
failure, together with the height bound `lcL ≤ B`, bounds the *logarithmic* scale `Log N` by the
`(ρ,B)`-constant `B + 1 + 2 uRep ρ B B B B`.  By lacunarity this bounds the *number* of admissible
scales at which the model can differ from the concrete column. -/

/-- The argument of `2 ^ ·` in the off-band scale bound. -/
noncomputable def offBandLog (ρ : ℝ) (B : ℕ) : ℕ :=
  B + 1 + 2 * Work.KMTAreas.A7.uRep ρ B B B B

/-- Failure of the band condition bounds the logarithmic scale. -/
theorem logN_toNat_lt_of_not_bandCond (ρ : ℝ) (hρ : 0 ≤ ρ) {l₁ l₂ k₁ k₂ N B : ℕ}
    (hLB : lcL l₁ l₂ k₁ k₂ ≤ B)
    (hbc : ¬ Work.KMTAreas.A7.bandCond ρ l₁ l₂ k₁ k₂ N) :
    (Work.Analysis.EndVar.logN N).toNat < offBandLog ρ B := by
  obtain ⟨h1, h2, h3, h4⟩ := le_of_lcL_le hLB
  have hu : Work.KMTAreas.A7.uRep ρ l₁ l₂ k₁ k₂ ≤ Work.KMTAreas.A7.uRep ρ B B B B :=
    uRep_le_uRep_B ρ hρ hLB
  rw [Work.KMTAreas.A7.bandCond, not_and_or] at hbc
  have h2mul := Nat.mul_le_mul_left 2 hu
  rcases hbc with hlt | hlt
  · refine lt_of_lt_of_le (not_le.mp hlt) ?_
    unfold offBandLog
    omega
  · refine lt_of_lt_of_le (not_le.mp hlt) ?_
    unfold offBandLog
    omega

/-- An upper bound on the logarithmic scale bounds the scale itself. -/
theorem le_two_pow_of_logN_toNat_lt {N C : ℕ}
    (h : (Work.Analysis.EndVar.logN N).toNat < C) : N ≤ 2 ^ C := by
  have h1 : Nat.log 2 (max N 2) < C := by
    have h2 := h
    rw [Work.Analysis.EndVar.logN, Int.toNat_natCast] at h2
    exact h2
  have h2 : max N 2 < 2 ^ C := by
    have h3 : max N 2 < 2 ^ (Nat.log 2 (max N 2) + 1) :=
      Nat.lt_pow_succ_log_self (by norm_num) (max N 2)
    have h4 : 2 ^ (Nat.log 2 (max N 2) + 1) ≤ 2 ^ C :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  omega

/-- **The off-band scales are among the first `nBound` scales.**  If the height is bounded by `B`
and the band condition fails at the admissible scale `⌊a n⌋`, then `n < nBound Λ (offBandLog ρ B)`;
hence the off-band family is supported in `Finset.range (nBound Λ (offBandLog ρ B) + 1)`. -/
theorem offBand_lt_nBound {Λ : NNReal} (hΛ : 1 < Λ) {a : ℕ → NNReal}
    (ha : PointwiseErgodicTheorems.Lacunary Λ a) (ha1 : ∀ n, 1 ≤ a n)
    (ρ : ℝ) (hρ : 0 ≤ ρ) (P : Polynomial ℤ) (C₀ : ℕ) {l₁ l₂ k₁ k₂ B n : ℕ}
    (hLB : lcL l₁ l₂ k₁ k₂ ≤ B)
    (_hc : Work.KMTAreas.A7.hiCore ρ P C₀ a l₁ l₂ k₁ k₂ n)
    (hbc : ¬ Work.KMTAreas.A7.bandCond ρ l₁ l₂ k₁ k₂ (Nat.floor (a n))) :
    n < Work.KMTAreas.A7.nBound Λ (offBandLog ρ B) := by
  have hlog := logN_toNat_lt_of_not_bandCond ρ hρ hLB hbc
  have hN : Nat.floor (a n) ≤ 2 ^ offBandLog ρ B := le_two_pow_of_logN_toNat_lt hlog
  by_contra hcon
  have hgt := Work.KMTAreas.A7.floor_a_gt hΛ ha ha1 (offBandLog ρ B) (not_lt.mp hcon)
  omega

end

end Work.KMTPlan.A6.PieceBoundedH
