import Mathlib
import Submission.Work.Extraction.Accumulate
import Submission.Work.Lattice.UniformBddBelow
import Submission.Work.Lattice.Prop42Upper
import Submission.Work.Lattice.SlopeLambda
import Submission.Work.Lattice.MaxFlagMinima

/-!
# The explicit constants of the §3 production

These are the constants of the §3 extraction (de Saxcé, Prop. 5), all depending only on `d`, `ℓ`
and `k` (and the slack `A`):

* `Aconst d = d log 2` — a valid choice of the slack of the φ-polygon;
* `deltaK d ℓ k` — the relative annulus error, chosen so that `(1+δ)^k - 1 < floorSeq d ℓ d`;
* `cK d ℓ k` — the resulting `π₊`-dominance constant;
* `blkFactorK d A` — a uniform bound on the "covering factor" `blockConstMax/λ` over all flag
  members (only the rank enters, and the rank is `≤ d`);
* `DK d ℓ k A` — the scale constant `M j = DK · λ_{j_s}`;
* `lamConst d A` — the `λ`-interface constant `Kconst d + 2 A d² + 2 dataCeil d`;
* `C0K d ℓ k A` — the bound on the flowed wedge norm.

Module `Submission.Work.Extraction.Constants`, namespace `Submission.Production`.
-/

noncomputable section
open Module exteriorPower InnerProductGeometry Real
open scoped BigOperators
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 800000

namespace Submission.Production

open Submission.Accumulate
open Submission.Prop42Upper
open Submission.SlopeLambda
open Submission.UniformBddBelow

variable {d : ℕ}

/-- The slack of the φ-polygon used by the §3 flag. -/
noncomputable def Aconst (d : ℕ) : ℝ := (d : ℝ) * Real.log 2

lemma Aconst_pos {d : ℕ} (hd : 0 < d) : 0 < Aconst d := by
  unfold Aconst
  exact mul_pos (by exact_mod_cast hd) (Real.log_pos (by norm_num))

/-- The relative annulus error. -/
noncomputable def deltaK (d ℓ k : ℕ) : ℝ :=
  min (1 / 2) (floorSeq d ℓ d / ((2 : ℝ) ^ k * 2))

lemma deltaK_pos (d ℓ k : ℕ) : 0 < deltaK d ℓ k := by
  refine lt_min (by norm_num) (div_pos (floorSeq_pos d ℓ d) (by positivity))

lemma deltaK_le_half (d ℓ k : ℕ) : deltaK d ℓ k ≤ 1 / 2 := min_le_left _ _

lemma deltaK_le_one (d ℓ k : ℕ) : deltaK d ℓ k ≤ 1 := by
  linarith [deltaK_le_half d ℓ k]

lemma deltaK_le (d ℓ k : ℕ) : deltaK d ℓ k * ((2 : ℝ) ^ k * 2) ≤ floorSeq d ℓ d := by
  have h := min_le_right (1 / 2 : ℝ) (floorSeq d ℓ d / ((2 : ℝ) ^ k * 2))
  have hpos : (0 : ℝ) < (2 : ℝ) ^ k * 2 := by positivity
  calc deltaK d ℓ k * ((2 : ℝ) ^ k * 2) ≤
        (floorSeq d ℓ d / ((2 : ℝ) ^ k * 2)) * ((2 : ℝ) ^ k * 2) :=
        mul_le_mul_of_nonneg_right h (le_of_lt hpos)
    _ = floorSeq d ℓ d := div_mul_cancel₀ _ (ne_of_gt hpos)

/-- The `π₊`-dominance constant. -/
noncomputable def cK (d ℓ k : ℕ) : ℝ :=
  (floorSeq d ℓ d - ((1 + deltaK d ℓ k) ^ k - 1)) / (1 + deltaK d ℓ k) ^ k

lemma one_add_deltaK_pow_sub_one_lt (d ℓ k : ℕ) (hk1 : 1 ≤ k) :
    (1 + deltaK d ℓ k) ^ k - 1 < floorSeq d ℓ d := by
  have hδ1 : deltaK d ℓ k ≤ 1 := deltaK_le_one d ℓ k
  have hδ0 : 0 ≤ deltaK d ℓ k := le_of_lt (deltaK_pos d ℓ k)
  -- Bernoulli-type bound: `(1+δ)^m ≤ 1 + (2^m - 1)δ`
  have hbernoulli : ∀ m : ℕ, (1 + deltaK d ℓ k) ^ m ≤ 1 + ((2 : ℝ) ^ m - 1) * deltaK d ℓ k := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
        have h2k : (1 : ℝ) ≤ (2 : ℝ) ^ m := one_le_pow₀ (by norm_num)
        have hstep : (1 + deltaK d ℓ k) ^ (m + 1) =
            (1 + deltaK d ℓ k) ^ m * (1 + deltaK d ℓ k) := by rw [pow_succ]
        have h1 : ((2 : ℝ) ^ m - 1) * deltaK d ℓ k * deltaK d ℓ k ≤
            ((2 : ℝ) ^ m - 1) * deltaK d ℓ k := by
          have hA : 0 ≤ ((2 : ℝ) ^ m - 1) * deltaK d ℓ k := by
            exact mul_nonneg (by linarith) hδ0
          nlinarith [hA, hδ0, hδ1]
        rw [hstep]
        calc (1 + deltaK d ℓ k) ^ m * (1 + deltaK d ℓ k)
            ≤ (1 + ((2 : ℝ) ^ m - 1) * deltaK d ℓ k) * (1 + deltaK d ℓ k) :=
              mul_le_mul_of_nonneg_right ih (by linarith)
          _ = 1 + ((2 : ℝ) ^ (m + 1) - 1) * deltaK d ℓ k -
                (((2 : ℝ) ^ m - 1) * deltaK d ℓ k -
                  ((2 : ℝ) ^ m - 1) * deltaK d ℓ k * deltaK d ℓ k) := by
              push_cast [pow_succ]
              ring
          _ ≤ 1 + ((2 : ℝ) ^ (m + 1) - 1) * deltaK d ℓ k := by linarith [h1]
  have hk : 1 ≤ k := hk1
  have h2k : (1 : ℝ) ≤ (2 : ℝ) ^ k := one_le_pow₀ (by norm_num)
  have hfin : ((2 : ℝ) ^ k - 1) * deltaK d ℓ k ≤ (2 : ℝ) ^ k * deltaK d ℓ k := by
    nlinarith [hδ0, h2k]
  have hd : deltaK d ℓ k * ((2 : ℝ) ^ k * 2) ≤ floorSeq d ℓ d := deltaK_le d ℓ k
  have h3 : (2 : ℝ) ^ k * deltaK d ℓ k ≤ floorSeq d ℓ d / 2 := by
    have h2pos : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
    nlinarith [hd, h2pos, hδ0]
  have h4 : (0 : ℝ) < floorSeq d ℓ d := floorSeq_pos d ℓ d
  have := hbernoulli k
  linarith

lemma cK_pos (d ℓ k : ℕ) (hk1 : 1 ≤ k) : 0 < cK d ℓ k := by
  have h1 := one_add_deltaK_pow_sub_one_lt d ℓ k hk1
  have h2 : 0 < (1 + deltaK d ℓ k) ^ k :=
    pow_pos (by linarith [deltaK_pos d ℓ k]) k
  exact div_pos (by linarith) h2

/-- A uniform bound on the "covering factor" `blockConstMax/λ` over flag members (only the rank,
which is `≤ d`, enters). -/
noncomputable def blkFactorK (d : ℕ) (A : ℝ) : ℝ :=
  max 1 ((Finset.range (d + 1)).sup' ⟨0, Finset.mem_range.mpr (Nat.succ_pos d)⟩
    (fun j => (2 : ℝ) ^ (2 * d) / unitBallVol j *
      Real.exp ((d : ℝ) * (Kconst d + 2 * A * (d : ℝ) ^ 2) +
        (1 / 2) * Real.log (Nat.choose d j))))

lemma blkFactorK_pos (d : ℕ) (A : ℝ) : 0 < blkFactorK d A := lt_of_lt_of_le one_pos (le_max_left _ _)

/-- The factor bound: for `1 ≤ j ≤ d`, the covering factor of a rank-`j` member is at most
`blkFactorK d A`. -/
lemma blockFactor_le_blkFactorK {d j : ℕ} {A : ℝ} (hj : j ≤ d) :
    (2 : ℝ) ^ (2 * d) / unitBallVol j *
      Real.exp ((d : ℝ) * (Kconst d + 2 * A * (d : ℝ) ^ 2) +
        (1 / 2) * Real.log (Nat.choose d j)) ≤ blkFactorK d A := by
  have hmem : j ∈ Finset.range (d + 1) := Finset.mem_range.mpr (by omega)
  refine le_trans (Finset.le_sup' (f := fun j => (2 : ℝ) ^ (2 * d) / unitBallVol j *
    Real.exp ((d : ℝ) * (Kconst d + 2 * A * (d : ℝ) ^ 2) +
      (1 / 2) * Real.log (Nat.choose d j))) hmem) (le_max_right _ _)

/-- The scale constant. -/
noncomputable def DK (d ℓ k : ℕ) (A : ℝ) : ℝ :=
  ((d : ℝ) + 1) * (blkFactorK d A + 1) / deltaK d ℓ k

lemma DK_pos (d ℓ k : ℕ) (A : ℝ) : 0 < DK d ℓ k A := by
  unfold DK
  have h1 : (0 : ℝ) < (d : ℝ) + 1 := by positivity
  have h2 : (0 : ℝ) < blkFactorK d A + 1 := by linarith [blkFactorK_pos d A]
  exact div_pos (mul_pos h1 h2) (deltaK_pos d ℓ k)

/-- The `λ`-interface constant. -/
noncomputable def lamConst (d : ℕ) (A : ℝ) : ℝ :=
  Kconst d + 2 * A * (d : ℝ) ^ 2 + 2 * dataCeil d

/-- The bound on the flowed wedge norm. -/
noncomputable def C0K (d ℓ k : ℕ) (A : ℝ) : ℝ :=
  (1 + deltaK d ℓ k) ^ k *
    Real.exp ((k : ℝ) * (Real.log (DK d ℓ k A) + (ℓ : ℝ) * ((d : ℝ) - (ℓ : ℝ)) / (d : ℝ) +
      lamConst d A))

lemma C0K_pos (d ℓ k : ℕ) (A : ℝ) : 0 < C0K d ℓ k A := by
  unfold C0K
  exact mul_pos (pow_pos (by linarith [deltaK_pos d ℓ k]) k) (Real.exp_pos _)

end Submission.Production

end
