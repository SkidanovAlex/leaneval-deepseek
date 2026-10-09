import Mathlib
import Submission.Work.SSGRoute.prop5.pCentralSeries_inter_lowerCentralSeries_le
import Submission.Work.SSGRoute.prop5.lemma4ii_filtration
import Submission.Work.SSGRoute.prop5.lowerCentralSeriesCore
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute

/-- Lemma 4(ii) of Schmidt–Wingberg specialised to the adjacent indices `(i, j) = (j+1, j)`:
the `j`-th term of the descending central series of a free group meets the `p`-central series
`P_j` (with `p = 2`) exactly in `γ_j² · γ_{j+1}`.

The inclusion `⊆` is the `j + 1`-st step of `pCentralSeries_inter_lowerCentralSeries_le`
(whose right hand side is the finite supremum `⨆ k ∈ Icc j (j+1), γ_k^{2^{j+1-k}}`, which for
this index range collapses to `γ_j² ⊔ γ_{j+1}`), and the reverse inclusion is immediate because
both `γ_j²` and `γ_{j+1}` lie in `γ_j` and in `P_j`. -/
theorem lcs_inter_pCentralSeries_eq {X : Type} [Fintype X] (j : ℕ) (hj : 1 ≤ j) :
    (⊤ : Subgroup (FreeGroup X)).lowerCentralSeries (j - 1) ⊓
      Work.Shrinking.pCentralSeries 2 (FreeGroup X) j
    = Work.Shrinking.powSubgroup 2 ((⊤ : Subgroup (FreeGroup X)).lowerCentralSeries (j - 1)) ⊔
      (⊤ : Subgroup (FreeGroup X)).lowerCentralSeries j := by
  -- The supremum appearing in Lemma 4(ii) collapses, for `i = j + 1`, to `γ_j² ⊔ γ_{j+1}`.
  have hsup : (⨆ k ∈ Finset.Icc j (j + 1), Work.Shrinking.powSubgroup (2 ^ (j + 1 - k))
        ((⊤ : Subgroup (FreeGroup X)).lowerCentralSeries (k - 1))) =
      Work.Shrinking.powSubgroup 2 ((⊤ : Subgroup (FreeGroup X)).lowerCentralSeries (j - 1)) ⊔
        (⊤ : Subgroup (FreeGroup X)).lowerCentralSeries j := by
    have hpf : (⨆ k ∈ Finset.Icc j (j + 1), Work.Shrinking.powSubgroup (2 ^ (j + 1 - k))
          ((⊤ : Subgroup (FreeGroup X)).lowerCentralSeries (k - 1)))
        = Work.SSGRoute.prop5.pFilt 2 (j + 1) j := rfl
    rw [hpf, Work.SSGRoute.prop5.pFilt_succ (p := 2) (i := j + 1) (j := j) le_rfl,
      Work.SSGRoute.prop5.pFilt_self (p := 2) (i := j + 1),
      show j + 1 - j = 1 from by omega, pow_one]
    rfl
  apply le_antisymm
  · -- `⊆`: Lemma 4(ii) at `(i, j) = (j+1, j)`.
    rw [inf_comm]
    exact le_trans
      (Work.SSGRoute.prop5.pCentralSeries_inter_lowerCentralSeries_le 2 X (j + 1) j hj (by omega))
      (le_of_eq hsup)
  · -- `⊇`: both `γ_j²` and `γ_{j+1}` lie in `γ_j` and in `P_j`.
    refine sup_le ?_ ?_
    · refine le_inf ?_ ?_
      · exact Work.Shrinking.powSubgroup_le 2 _
      · have h := Work.SSGRoute.prop5.powSubgroup_G_le_pSeries (X := X) 2 j 1 hj
        rw [show (2:ℕ)^1 = 2 from by norm_num, show j + 1 - 1 = j from by omega] at h
        exact h
    · refine le_inf ?_ ?_
      · exact Subgroup.lowerCentralSeries_antitone _ (by omega : j - 1 ≤ j)
      · exact Work.ProP.lowerCentralSeries_le_pCentralSeries 2 (FreeGroup X) j

end Work.SSGRoute
