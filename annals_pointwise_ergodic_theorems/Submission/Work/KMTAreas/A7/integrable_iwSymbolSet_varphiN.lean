import Mathlib
import Submission.Work.KMTAreas.A7.ModelOps
import Submission.Work.KMTAreas.A7.varphiNt_bounds

namespace Work.KMTAreas.A7

open MeasureTheory

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-- The unmodulated KMT bump `φ_N` is bounded by `2`: it is either a single cutoff `η` (at the
bottom scale `k = 0`) or the difference of two cutoffs, each bounded by `1`. -/
lemma norm_varphiN_le_two (N k : ℕ) (ξ : ℝ) : ‖varphiN N k ξ‖ ≤ 2 := by
  by_cases hk : k = 0
  · simp only [varphiN, if_pos hk]
    exact le_trans (Work.KMTContract.norm_kmtEta_le _) (by norm_num)
  · simp only [varphiN, if_neg hk]
    calc ‖Work.KMTContract.kmtEta (((2 : ℝ) ^ ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ))) * ξ)
            - Work.KMTContract.kmtEta
              (((2 : ℝ) ^ ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ) + 1)) * ξ)‖
        ≤ ‖Work.KMTContract.kmtEta
              (((2 : ℝ) ^ ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ))) * ξ)‖
          + ‖Work.KMTContract.kmtEta
              (((2 : ℝ) ^ ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ) + 1)) * ξ)‖ :=
          norm_sub_le _ _
      _ ≤ 1 + 1 := add_le_add (Work.KMTContract.norm_kmtEta_le _)
          (Work.KMTContract.norm_kmtEta_le _)
      _ = 2 := by norm_num

/-- The periodisation of the KMT bump `φ_N` is in `L^∞(ℝ/ℤ)`: `φ_N` is measurable, bounded by
`2` and supported in `[-2^{k - Log N}, 2^{k - Log N}]`, so the periodisation is a finite sum of
translates. -/
theorem memLp_periodize_varphiN (N k : ℕ) :
    MeasureTheory.MemLp
      (Work.Analysis.IonescuWainger.periodize (varphiN N k)) ⊤
      Work.Analysis.IonescuWainger.circleMeasure := by
  have hR : 0 ≤ (2 : ℝ) ^ ((k : ℝ) - (Work.Analysis.EndVar.logN N : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hφ0 : ∀ x : ℝ, (2 : ℝ) ^ ((k : ℝ) - (Work.Analysis.EndVar.logN N : ℝ)) < |x| →
      varphiN N k x = 0 := by
    intro x hx
    by_contra hne
    exact absurd (varphiN_support N k x hne) (not_le.mpr hx)
  exact Work.Analysis.IonescuWainger.memLp_periodize
    (contDiff_varphiN N k).continuous.measurable hR hφ0 (fun x => norm_varphiN_le_two N k x)

theorem integrable_iwSymbolSet_varphiN (ρ : ℝ) (l N k : ℕ) :
    MeasureTheory.Integrable
      (Work.Analysis.IonescuWainger.iwSymbolSet (Work.KMTAreas.A7.diffFreqs ρ l)
        (Work.Analysis.IonescuWainger.periodize (Work.KMTAreas.A7.varphiN N k)))
      Work.Analysis.IonescuWainger.circleMeasure :=
  (Work.Analysis.IWMultiplier.memLp_iwSymbolSet (diffFreqs ρ l)
    (memLp_periodize_varphiN N k)).integrable le_top

end Work.KMTAreas.A7
