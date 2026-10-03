/-
# The clamped variational norm increases to the challenge's variational norm (area A8)

`Work.KMTAreas.vNormK r K a = supK K a + varK r K a` is the challenge's variational norm
`PointwiseErgodicTheorems.variationalNorm r a` computed from the coordinates `a 0, …, a K` only:
`supK` is the maximum of `‖a n‖` over `n ≤ K`, `varK` the maximum of the `ℓ^r` norms of the
increments along a monotone chain of indices in `{0, …, K}`.

This module proves `vNormK_basic`: for `1 ≤ r` and every `a : ℕ → ℂ`,
1. `ENNReal.ofReal (vNormK r K a) ≤ variationalNorm r a` for every `K`;
2. `K ↦ vNormK r K a` is monotone;
3. `⨆ K, ENNReal.ofReal (vNormK r K a) = variationalNorm r a`.

The proof splits the variational norm into its two summands
(`Work.KMTAreas.A8.variationalNorm_eq_add`: `(⨆ n, ‖a n‖ₑ) + varPart r a`, definitional), and
identifies each with the corresponding clamped quantity:
* `Work.KMTAreas.A8.supK_basic`: `ENNReal.ofReal (supK K a) = ⨆ k : Fin (K+1), ‖a k‖ₑ`,
  together with nonnegativity, monotonicity in `K`, and `⨆ K, ofReal (supK K a) = ⨆ n, ‖a n‖ₑ`;
* `Work.KMTAreas.A8.varK_basic`: nonnegativity and monotonicity of `varK` in `K`;
* `Work.KMTAreas.A8.varK_le_varPart` and `Work.KMTAreas.A8.varPart_le_iSup_varK`: the two
  inequalities that identify `⨆ K, ENNReal.ofReal (varK r K a)` with `varPart r a`.

The two `iSup`s are then combined with the monotonicity of the two summands
(`iSup_add_monotone`, in this file).

The variation part `Work.KMTAreas.A8.varPart` used above is, verbatim, the second summand of
`PointwiseErgodicTheorems.variationalNorm`; it is definitionally equal to the pre-existing
`Submission.PointwiseErgodicTheorems.varPart` of `Submission/VarNorm.lean` and is recorded
locally (`Submission/Work/KMTAreas/A8/vNormK_defs.lean`) so that the clamping lemmas form a
self-contained module.
-/
import Mathlib
import Submission.Work.KMTAreas.A8.supK_basic
import Submission.Work.KMTAreas.A8.varK_basic
import Submission.Work.KMTAreas.A8.varK_le_varPart
import Submission.Work.KMTAreas.A8.varPart_le_iSup_varK

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.KMTAreas.A8

open scoped BigOperators ENNReal NNReal

/-- For monotone sequences in `ℝ≥0∞`, the supremum of the sums is the sum of the suprema. -/
private theorem iSup_add_monotone {a b : ℕ → ℝ≥0∞} (ha : Monotone a) (hb : Monotone b) :
    (⨆ n, a n + b n) = (⨆ n, a n) + (⨆ n, b n) := by
  have h2 : (⨆ n, a n) + (⨆ m, b m) = ⨆ n, ⨆ m, (a n + b m) := by
    rw [ENNReal.iSup_add]
    refine iSup_congr fun n => ?_
    rw [ENNReal.add_iSup]
  refine le_antisymm (iSup_le fun n => add_le_add (le_iSup a n) (le_iSup b n)) ?_
  calc (⨆ n, a n) + (⨆ m, b m) = ⨆ n, ⨆ m, (a n + b m) := h2
    _ ≤ ⨆ n, (a n + b n) := iSup_le fun n => iSup_le fun m => by
        rcases le_total n m with h | h
        · exact le_trans (add_le_add_left (ha h) _) (le_iSup (fun k => a k + b k) m)
        · exact le_trans (add_le_add_right (hb h) _) (le_iSup (fun k => a k + b k) n)

theorem vNormK_basic (r : NNReal) (hr : 1 ≤ r) (a : ℕ → ℂ) :
    (∀ K, ENNReal.ofReal (Work.KMTAreas.vNormK r K a) ≤ PointwiseErgodicTheorems.variationalNorm r a) ∧
    (∀ K K', K ≤ K' → Work.KMTAreas.vNormK r K a ≤ Work.KMTAreas.vNormK r K' a) ∧
    ((iSup fun K => ENNReal.ofReal (Work.KMTAreas.vNormK r K a)) = PointwiseErgodicTheorems.variationalNorm r a) := by
  have hsup_nonneg : ∀ K, (0 : ℝ) ≤ Work.KMTAreas.supK K a := fun K => (supK_basic K a).1
  have hvar_nonneg : ∀ K, (0 : ℝ) ≤ Work.KMTAreas.varK r K a := fun K => (varK_basic r a).1 K
  have hdecomp : ∀ K, ENNReal.ofReal (Work.KMTAreas.vNormK r K a)
      = ENNReal.ofReal (Work.KMTAreas.supK K a) + ENNReal.ofReal (Work.KMTAreas.varK r K a) := by
    intro K
    rw [Work.KMTAreas.vNormK, ENNReal.ofReal_add (hsup_nonneg K) (hvar_nonneg K)]
  have hsup_le : ∀ K, ENNReal.ofReal (Work.KMTAreas.supK K a) ≤ ⨆ n, ‖a n‖ₑ := by
    intro K
    rw [(supK_basic K a).2.1]
    exact iSup_le fun k => le_iSup (fun n => ‖a n‖ₑ) (k : ℕ)
  have hsup_mono : Monotone fun K => ENNReal.ofReal (Work.KMTAreas.supK K a) :=
    fun K K' h => ENNReal.ofReal_le_ofReal ((supK_basic K a).2.2.1 K' h)
  have hvar_mono : Monotone fun K => ENNReal.ofReal (Work.KMTAreas.varK r K a) :=
    fun K K' h => ENNReal.ofReal_le_ofReal ((varK_basic r a).2 K K' h)
  have hvar_iSup : (⨆ K, ENNReal.ofReal (Work.KMTAreas.varK r K a)) = varPart r a :=
    le_antisymm (iSup_le fun K => varK_le_varPart r hr a K) (varPart_le_iSup_varK r hr a)
  refine ⟨fun K => ?_, fun K K' h => ?_, ?_⟩
  · calc ENNReal.ofReal (Work.KMTAreas.vNormK r K a)
        = ENNReal.ofReal (Work.KMTAreas.supK K a) + ENNReal.ofReal (Work.KMTAreas.varK r K a) :=
          hdecomp K
      _ ≤ (⨆ n, ‖a n‖ₑ) + varPart r a := add_le_add (hsup_le K) (varK_le_varPart r hr a K)
      _ = PointwiseErgodicTheorems.variationalNorm r a := (variationalNorm_eq_add r a).symm
  · rw [Work.KMTAreas.vNormK, Work.KMTAreas.vNormK]
    exact add_le_add ((supK_basic K a).2.2.1 K' h) ((varK_basic r a).2 K K' h)
  · calc (⨆ K, ENNReal.ofReal (Work.KMTAreas.vNormK r K a))
        = ⨆ K, (ENNReal.ofReal (Work.KMTAreas.supK K a) + ENNReal.ofReal (Work.KMTAreas.varK r K a)) :=
          iSup_congr hdecomp
      _ = (⨆ K, ENNReal.ofReal (Work.KMTAreas.supK K a)) + (⨆ K, ENNReal.ofReal (Work.KMTAreas.varK r K a)) :=
          iSup_add_monotone hsup_mono hvar_mono
      _ = (⨆ n, ‖a n‖ₑ) + varPart r a := by rw [(supK_basic 0 a).2.2.2, hvar_iSup]
      _ = PointwiseErgodicTheorems.variationalNorm r a := (variationalNorm_eq_add r a).symm

end Work.KMTAreas.A8
