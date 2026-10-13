import Mathlib
import Submission.Work.Wilkies.E.Spec
import Submission.Work.WilE7.ProdDefs

namespace Work.WilE7

open WilkiesDesign WilkiesDesign.E

/-- If `X.basics` has no trivial branch then every branch has degree `≥ 1`, so the length is
bounded by the degree.  If it does have a trivial branch, `redBasics X` collapses to a single
branch of degree `0`.  Either way the number of branches of `redBasics X` is at most `X.deg + 1`. -/
theorem redBasics_length_le_deg_add_one {k : ℕ} (X : WilkiesDesign.E.SemiPf k) :
    (redBasics X).length ≤ ((redBasics X).map WilkiesDesign.E.Basic.deg).sum + 1 := by
  by_cases h : hasTrivial X
  · rw [show redBasics X = [trivialB k X.r] from ite_eq_left h]
    simp [trivialB, WilkiesDesign.E.Basic.deg]
  · rw [show redBasics X = X.basics from ite_eq_right h]
    have hle : X.basics.length ≤ (X.basics.map WilkiesDesign.E.Basic.deg).sum := by
      apply length_le_sum_map
      intro B hB
      apply one_le_basic_deg
      intro hnil
      rw [List.append_eq_nil_iff] at hnil
      exact h ⟨B, hB, hnil.1, hnil.2⟩
    omega

theorem semiPf_normalize_exists {k : ℕ} (X : WilkiesDesign.E.SemiPf k) :
    ∃ Y : WilkiesDesign.E.SemiPf k, Y.set = X.set ∧ Y.fmt = X.fmt ∧ Y.deg ≤ X.deg ∧
      Y.basics.length ≤ Y.deg + 1 := by
  refine ⟨⟨X.r, X.c, redBasics X⟩, ?_, ?_, ?_, ?_⟩
  · ext x
    simp only [WilkiesDesign.E.SemiPf.set, Set.mem_ofPred_eq]
    exact and_congr_right (fun _ => exists_holds_redBasics X x)
  · rfl
  · exact redBasics_deg_le X
  · exact redBasics_length_le_deg_add_one X

end Work.WilE7
