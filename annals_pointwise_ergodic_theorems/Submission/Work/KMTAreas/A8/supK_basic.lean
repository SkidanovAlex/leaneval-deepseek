import Mathlib
import Submission.Work.KMTAreas.A8Defs

namespace Work.KMTAreas.A8

open scoped ENNReal NNReal BigOperators

/-! ## Basic properties of the clamped sup norm `supK`

`Work.KMTAreas.supK K a = max {‖a n‖ : n ≤ K}` is the supremum part of the clamped
variational norm `vNormK`.  Here we record the four elementary facts the rest of area A8
needs: it is nonnegative, its `ENNReal.ofReal` is the `iSup` of the `enorm`s of the first
`K+1` coordinates, it is monotone in `K`, and its `ofReal` values increase to the `iSup` of
all the `enorm`s of `a`. -/

/-- `ENNReal.ofReal (supK K a)` is the sup of the `enorm`s of the coordinates `a 0, …, a K`. -/
private lemma ofReal_supK_eq_iSup_enorm (K : ℕ) (a : ℕ → ℂ) :
    ENNReal.ofReal (Work.KMTAreas.supK K a) = ⨆ k : Fin (K + 1), ‖a k‖ₑ := by
  apply le_antisymm
  · -- the sup is attained, at some index `n₀ ≤ K`
    obtain ⟨n₀, hn₀, hsup⟩ :=
      Finset.exists_mem_eq_sup' ⟨0, Finset.mem_range.mpr (Nat.succ_pos K)⟩ (fun n => ‖a n‖)
    have : Work.KMTAreas.supK K a = ‖a n₀‖ := by rw [Work.KMTAreas.supK]; exact hsup
    rw [this]
    simpa [enorm_eq_nnnorm] using
      le_iSup (fun k : Fin (K + 1) => ‖a k‖ₑ) ⟨n₀, Finset.mem_range.mp hn₀⟩
  · -- conversely every coordinate with index `≤ K` is bounded by the sup
    apply iSup_le
    intro k
    have h1 : ‖a k‖ ≤ Work.KMTAreas.supK K a := by
      rw [Work.KMTAreas.supK]
      exact Finset.le_sup' (fun n => ‖a n‖) (Finset.mem_range.mpr k.isLt)
    calc ‖a k‖ₑ = ENNReal.ofReal ‖a k‖ := by simp [enorm_eq_nnnorm]
      _ ≤ ENNReal.ofReal (Work.KMTAreas.supK K a) := ENNReal.ofReal_le_ofReal h1

/-- `supK K a` is monotone in `K`. -/
private lemma supK_mono (a : ℕ → ℂ) {K K' : ℕ} (h : K ≤ K') :
    Work.KMTAreas.supK K a ≤ Work.KMTAreas.supK K' a := by
  rw [Work.KMTAreas.supK, Work.KMTAreas.supK]
  apply Finset.sup'_le
  intro b hb
  refine Finset.le_sup' (fun n => ‖a n‖) (Finset.mem_range.mpr ?_)
  rw [Finset.mem_range] at hb
  omega

theorem supK_basic (K : ℕ) (a : ℕ → ℂ) :
    (0 ≤ Work.KMTAreas.supK K a) ∧
    (ENNReal.ofReal (Work.KMTAreas.supK K a) = ⨆ k : Fin (K + 1), ‖a k‖ₑ) ∧
    (∀ K', K ≤ K' → Work.KMTAreas.supK K a ≤ Work.KMTAreas.supK K' a) ∧
    ((⨆ K, ENNReal.ofReal (Work.KMTAreas.supK K a)) = ⨆ n, ‖a n‖ₑ) := by
  refine ⟨?_, ofReal_supK_eq_iSup_enorm K a, ?_, ?_⟩
  · -- nonnegativity: `supK` is attained, hence is the norm of a vector
    rw [Work.KMTAreas.supK]
    exact le_trans (norm_nonneg (a 0))
      (Finset.le_sup' (fun n => ‖a n‖) (Finset.mem_range.mpr (Nat.succ_pos K)))
  · exact fun K' h => supK_mono a h
  · -- the increasing `ofReal (supK K a)` have the same sup as all the `enorm`s
    apply le_antisymm
    · refine iSup_le fun K => ?_
      rw [ofReal_supK_eq_iSup_enorm K a]
      exact iSup_le fun k : Fin (K + 1) => le_iSup (fun n : ℕ => ‖a n‖ₑ) (k : ℕ)
    · refine iSup_le fun n => ?_
      have h1 : ‖a n‖ ≤ Work.KMTAreas.supK n a := by
        rw [Work.KMTAreas.supK]
        exact Finset.le_sup' (fun m => ‖a m‖) (Finset.mem_range.mpr (Nat.lt_succ_self n))
      calc ‖a n‖ₑ = ENNReal.ofReal ‖a n‖ := by simp [enorm_eq_nnnorm]
        _ ≤ ENNReal.ofReal (Work.KMTAreas.supK n a) := ENNReal.ofReal_le_ofReal h1
        _ ≤ ⨆ K, ENNReal.ofReal (Work.KMTAreas.supK K a) :=
            le_iSup (fun K => ENNReal.ofReal (Work.KMTAreas.supK K a)) n

end Work.KMTAreas.A8
