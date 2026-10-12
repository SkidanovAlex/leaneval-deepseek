import ChallengeDeps
import Submission.Work.BlockBound4.Repoint
import Submission.Work.UBBInputs.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.UBBInputs.Comparison` — the faithful-word ↔ corpus-word comparison

The lead's brief for item (1) asks for the *comparison lemma* between the
corpus's word-based energy (`kinWord + qLHSword` at the chosen kernels) and FS's
own word (the faithful per-box transcription of `eq:HBU`/`eq:appTB`,
`Work.BlockBound4.diagWWord = cgap·cnPlus + pDiagForm s (fsKinCoeff c₀)`).
The *per-state* comparison is delivered by
`Work.BlockBound4.diagWWord_le_kinWord_gap`
(`pDiagForm_eq_T0Form` + `T0Form_le_kinWord` + `winErrorQ_le_cnPlus`, assembled);
this module puts it in the two forms the chains actually consume:

* **`diagWEnergy_le_sboxE_add`** — the *energy* comparison: the faithful
  per-box energy is below the corpus `sboxE` plus the explicit window error;
* **`diagWordDens_le_wordDens_add`** — the *density* comparison (quotient form).

## Direction, and what this comparison does and does not supply

Since `diagWWord ≤ 2chiSup²·kinWord + 2cgap·cnPlus`, the faithful word is
**below** the corpus word up to the window error.  Hence this comparison
supplies

* the **localisation hypothesis** `hslide` of the sliding chapter
  (`∫_u eBf u ≤ kinWord + qLHSword`) whenever `eBf` is built from the faithful
  word — this is the role assigned to it in `Work.BlockBound4/README.md` §2.4
  ("DIRECTION (important): this is an UPPER bound on the faithful word … its
  role is to supply the SLIDING layer's localisation hypothesis");

and it does **not** supply the per-box *lower* bound field `SlidingSumData.hbox`
(`eBf u ≤ 𝒯_B(u) + qLHSwordB u`), because that needs the *opposite* comparison:
the delivered `smallbox_dl_energy_bound_at_count` bounds the *infimum*
`Work.BlockBound4.diagWeBAt` from below, while `hbox` needs a bound of that
number *above* the localised word of the big-box state at `u`.  The missing
ingredient there is the per-box *operator-level* form of FS `thm:smallbox`
(`H_B(μ) ≥ …·1`, which is what FS state) together with the identification of the
χ-weighted localised word with a small-box state's quotient — the mismatch
recorded in `Work.SmallBoxSliding/NOTES.md` §7 and in `Defs.lean`'s doc for
`BoxSumBound`.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.UBBInputs

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

open _root_.BoseGases
open Submission.BoseGases
open Work.UBB

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-- **The energy-level comparison** between FS's faithful per-box energy and the
corpus word: `diagWEnergy ≤ sboxE + (2chiSup² − 1)·kinWord + 2cgap·cnPlus`. -/
theorem diagWEnergy_le_sboxE_add {n : ℕ} {s μ c₀ cgap K : ℝ} (hs : 0 < s)
    (hc₀ : 0 ≤ c₀) (hK : 0 ≤ K)
    (hgrad : ∀ x : ℝ³,
      (∑ k : Fin 3, (fderiv ℝ (chiScale s) x (kcStdBasis k)) ^ 2) ≤ K / s ^ 2)
    (hpay : 2 * (K / s ^ 2) ≤ cgap)
    {v : ℝ³ → ℝ} {h : ScatSol v} {Φ : X (n + 1) → ℝ}
    (hΦ : ContDiff ℝ ∞ Φ) (hsupp : tsupport Φ ⊆ abox (n + 1) s) :
    Work.BlockBound4.diagWEnergy n s μ (wPairC s v) (wPairC s (g0 v h)) c₀ cgap Φ
      ≤ sboxE (n + 1) s μ (wPairC s v) (wPairC s (g0 v h)) Φ
        + (2 * chiSup ^ 2 - 1) * kinWord (n + 1) s Φ + 2 * cgap * cnPlus s Φ := by
  have h1 := Work.BlockBound4.diagWWord_le_kinWord_gap (n := n) (s := s) (c := c₀)
    (cgap := cgap) (K := K) hs hc₀ hK hgrad hpay hΦ hsupp
  rw [Work.BlockBound4.diagWEnergy_eq, sboxE]
  linarith [h1]

/-- The faithful per-box energy of `Work.BlockBound4` and the `N`-indexed
`Work.DLRepoint.diagEnergy` at count `N` are the same object (both are
`diagSlotWord + qLHSword`). -/
lemma diagWEnergy_eq_diagEnergy {n : ℕ} {s μ : ℝ} {v : ℝ³ → ℝ} {h : ScatSol v}
    {c₀ cgap : ℝ} (Φ : X (n + 1) → ℝ) :
    Work.BlockBound4.diagWEnergy n s μ (wPairC s v) (wPairC s (g0 v h)) c₀ cgap Φ
      = Work.DLRepoint.diagEnergy (n + 1) s μ v h c₀ cgap Φ := by
  rw [Work.BlockBound4.diagWEnergy_eq, Work.DLRepoint.diagEnergy_eq]
  simp only [Work.BlockBound4.diagWWord, Work.KinPSuperadd.diagSlotWord]

/-- **The density-level comparison**: the faithful density quotient is at most
the corpus density quotient plus the same window error divided by the volume. -/
theorem diagWordDens_le_wordDens_add {n : ℕ} {s μ c₀ cgap K : ℝ} (hs : 0 < s)
    (hc₀ : 0 ≤ c₀) (hK : 0 ≤ K)
    (hgrad : ∀ x : ℝ³,
      (∑ k : Fin 3, (fderiv ℝ (chiScale s) x (kcStdBasis k)) ^ 2) ≤ K / s ^ 2)
    (hpay : 2 * (K / s ^ 2) ≤ cgap)
    {v : ℝ³ → ℝ} {h : ScatSol v} {Φ : X (n + 1) → ℝ}
    (hΦ : ContDiff ℝ ∞ Φ) (hpos : 0 < ∫ x in abox (n + 1) s, (Φ x) ^ 2)
    (hsupp : tsupport Φ ⊆ abox (n + 1) s) :
    Work.DLRepoint.diagWordDens (n + 1) s μ v h c₀ cgap Φ
      ≤ WordDens (n + 1) s μ v h Φ
        + ((2 * chiSup ^ 2 - 1) * kinWord (n + 1) s Φ + 2 * cgap * cnPlus s Φ)
            / (s ^ 3 * ∫ x in abox (n + 1) s, (Φ x) ^ 2) := by
  have hE := diagWEnergy_le_sboxE_add (n := n) (s := s) (μ := μ) (c₀ := c₀)
    (cgap := cgap) (K := K) hs hc₀ hK hgrad hpay (v := v) (h := h) hΦ hsupp
  have hden : 0 < s ^ 3 * ∫ x in abox (n + 1) s, (Φ x) ^ 2 :=
    mul_pos (by positivity) hpos
  have hE' : Work.BlockBound4.diagWEnergy n s μ (wPairC s v) (wPairC s (g0 v h)) c₀ cgap Φ
      ≤ sboxE (n + 1) s μ (wPairC s v) (wPairC s (g0 v h)) Φ
        + ((2 * chiSup ^ 2 - 1) * kinWord (n + 1) s Φ + 2 * cgap * cnPlus s Φ) := by
    linarith [hE]
  rw [Work.DLRepoint.diagWordDens, WordDens, ← diagWEnergy_eq_diagEnergy (n := n) (s := s)
    (μ := μ) (v := v) (h := h) (c₀ := c₀) (cgap := cgap) Φ, ← add_div]
  exact (div_le_div_iff_of_pos_right hden).mpr hE'

end Work.UBBInputs
