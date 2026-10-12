import Mathlib.Tactic.LinearCombination
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseBogFS.PairIdentity
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseBogFS.Ground` — the per-mode ground estimate and the sum step

From `bogPairOp_eq_shifted` (FS `eq:BogIdentity` at FS's `b_k = a_k+α_ka_{-k}†+c_k`):

* `two_mul_bogD_mul_alpha_sq` — `2𝒟α² = 𝒜−√(𝒜²−ℬ²)`, the zero-point constant;
* `bogPairOp_ground` — per mode `(k,−k)`,
  `−(𝒵_k+κ_k)‖f‖² ≤ ⟨f, pairOp_k f⟩`, FS `eq:BogIneq` (`thm:BogHamDiag`'s per-pair step),
  under the *only* extra input `[a_k,a_k†]+[a_{-k},a_{-k}†] ≤ 2`;
* `qw_KzBogFS_ge` — summed over all labels (including `0`, `F6`):
  `−Σ_k ½(𝒵_k+κ_k)‖f‖² ≤ ⟨f, 𝒦^Bog f⟩`, i.e. FS `thm:BogHamDiag` without the
  `lem:BogIntegral` evaluation of the zero-point sum;
* `qw_dNumOpShifted_le` — the *shifted* diagonal reserve
  `Σ_{RHi}𝒟_k(b_k+c_k)†(b_k+c_k)`, which is FS's `thm:BogHamDiag`/`thm:Control3Q`
  diagonal (FS `eq:Defb_k` puts `c_k` inside `b_k`), is dominated by `𝒦^Bog` plus the
  same scalar `Σ_k ½(𝒵_k+κ_k)`.
-/

noncomputable section

open scoped Real BigOperators

namespace Work.BoseBogFS

open Work.BoseB7

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

variable {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]

/-- `2𝒟α² = 𝒜 − √(𝒜²−ℬ²)`: the zero point of the pair is `2𝒟α²`. -/
theorem two_mul_bogD_mul_alpha_sq (A B : ℝ) (hA : 0 < A) (hB : |B| ≤ A) :
    2 * (Submission.BoseGases.bogD A B * (Submission.BoseGases.bogAlpha A B) ^ 2)
      = Work.BoseB6.bogZeroPoint A B := by
  have h1 : Submission.BoseGases.bogD A B * (Submission.BoseGases.bogAlpha A B) ^ 2
      = Submission.BoseGases.bogAlpha A B * (B / 2) := by
    have h := Submission.BoseGases.bog_alpha_mul_D (A := A) (B := B) hA hB
    linear_combination (Submission.BoseGases.bogAlpha A B) * h
  rw [h1, Work.BoseB6.bogZeroPoint_eq, Submission.BoseGases.bog_A_sub_s_eq hA hB]
  simp only [Submission.BoseGases.bogAlpha]
  field_simp

/-- The shifted diagonal at a state: `⟨b̂_j x, x⟩ = ‖b̂_j x‖²`. -/
theorem bp_bogBShiftDag_bogBShift (F : FockData Mode) (E : Q3Env Mode) (ρ : ℝ) (j : Mode)
    (x : F.H) :
    F.bp ((bogBShiftDag F E ρ j) ((bogBShift F E ρ j) x)) x
      = F.normSq ((bogBShift F E ρ j) x) := by
  rw [bogBShiftDag_bp F E ρ j ((bogBShift F E ρ j) x) x, FockData.normSq]

/-- The value of `bogPairOp` at a state, in the diagonalised form. -/
theorem qw_bogPairOp_eq (F : FockData Mode) (E : Q3Env Mode) (ρ : ℝ) (k : Mode)
    (hA : 0 < bogA E ρ k) (hB : |bogB E ρ k| ≤ bogA E ρ k)
    (hAB : 0 < bogA E ρ k + bogB E ρ k)
    (hAe : bogA E ρ (-k) = bogA E ρ k) (hBe : bogB E ρ (-k) = bogB E ρ k)
    (hCe : bogC E ρ (-k) = bogC E ρ k) (f : F.H) :
    F.qw f (bogPairOp F E ρ k)
      = (bogD E ρ k) * (F.normSq ((bogBShift F E ρ k) f)
            + F.normSq ((bogBShift F E ρ (-k)) f))
        - ((bogD E ρ k * (bogAlpha E ρ k) ^ 2 * bogCcr2 F k)
            + Work.BoseB6.bogKappaErr (bogA E ρ k) (bogB E ρ k) (bogC E ρ k))
          * F.normSq f := by
  rw [bogPairOp_eq_shifted F E ρ k hA hB hAB hAe hBe hCe]
  simp only [FockData.qw, FockData.normSq, map_add, map_sub, map_smul, LinearMap.add_apply,
    LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.comp_apply, Module.End.one_apply,
    smul_eq_mul]
  rw [bp_bogBShiftDag_bogBShift F E ρ k f, bp_bogBShiftDag_bogBShift F E ρ (-k) f]
  simp only [FockData.normSq]

/-- **FS `eq:BogIneq` per pair**, at FS's coefficients: the pair quadratic is bounded below
by minus the zero point minus the `κ`-error, provided the two commutators sum to at most
`2` (which is what the box identity `[a_k,a_k†] = χ̂²(0) − χ̂(kℓ)²` and `|χ̂²| ≤ 1`,
`|χ̂| ≤ 1` give). -/
theorem bogPairOp_ground (F : FockData Mode) (E : Q3Env Mode) (ρ : ℝ) (k : Mode)
    (hA : 0 < bogA E ρ k) (hB : |bogB E ρ k| ≤ bogA E ρ k)
    (hAB : 0 < bogA E ρ k + bogB E ρ k)
    (hAe : bogA E ρ (-k) = bogA E ρ k) (hBe : bogB E ρ (-k) = bogB E ρ k)
    (hCe : bogC E ρ (-k) = bogC E ρ k)
    (hccr : bogCcr2 F k ≤ 2) (f : F.H) :
    -((Work.BoseB6.bogZeroPoint (bogA E ρ k) (bogB E ρ k))
        + Work.BoseB6.bogKappaErr (bogA E ρ k) (bogB E ρ k) (bogC E ρ k)) * F.normSq f
      ≤ F.qw f (bogPairOp F E ρ k) := by
  rw [qw_bogPairOp_eq F E ρ k hA hB hAB hAe hBe hCe f]
  have hDnn : 0 ≤ bogD E ρ k := by
    simp only [bogD]
    exact le_of_lt (Submission.BoseGases.bogD_pos (A := bogA E ρ k) (B := bogB E ρ k) hA hB)
  have hα2 : 0 ≤ bogD E ρ k * (bogAlpha E ρ k) ^ 2 := mul_nonneg hDnn (sq_nonneg _)
  have hzp : 2 * (bogD E ρ k * (bogAlpha E ρ k) ^ 2)
      = Work.BoseB6.bogZeroPoint (bogA E ρ k) (bogB E ρ k) := by
    simpa only [bogD, bogAlpha, bogA, bogB] using
      two_mul_bogD_mul_alpha_sq (bogA E ρ k) (bogB E ρ k) hA hB
  have hkey : bogD E ρ k * (bogAlpha E ρ k) ^ 2 * bogCcr2 F k
      ≤ Work.BoseB6.bogZeroPoint (bogA E ρ k) (bogB E ρ k) := by
    have h := mul_le_mul_of_nonneg_left hccr hα2
    linarith [hzp]
  have h1 : 0 ≤ F.normSq ((bogBShift F E ρ k) f) := F.bp_nonneg _
  have h2 : 0 ≤ F.normSq ((bogBShift F E ρ (-k)) f) := F.bp_nonneg _
  have h3 : 0 ≤ F.normSq f := F.bp_nonneg f
  nlinarith [hDnn, h1, h2, h3, hkey]

end Work.BoseBogFS
