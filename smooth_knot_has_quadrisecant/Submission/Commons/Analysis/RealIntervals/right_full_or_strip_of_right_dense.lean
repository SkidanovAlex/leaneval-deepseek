import Mathlib
import Submission.Commons.Analysis.RealIntervals.exists_interior_interval_of_dense_no_full_right

set_option linter.unusedVariables false

open Set
open scoped Topology

namespace Commons.Analysis.RealIntervals

/-- **Structural dichotomy for an open `S` with points right-dense at `c`**:
if `c ∉ S` (`0 < c < 1`) and every right-neighbourhood of `c` meets `S`,
then either `S` contains the whole interval `(c,1)`, or a strip `(a,b)`
(`c ≤ a < b < 1`) lies inside `S` with both endpoints outside `S`.

Proof structure: if `(c,1) ⊆ S` we are done.  Otherwise, when a full
prefix `(c,b) ⊆ S` (`b ≤ 1`) exists, the maximal prefix end
`p = sSup {b | c < b ∧ (c,b) ⊆ S}` is `< 1` (else `(c,1) ⊆ S`); the
interval `(c,p)` lies in `S` (every point below the supremum is covered by
some prefix), and `p ∉ S` because otherwise openness of `S` would extend
the prefix beyond the supremum; hence `(c,p)` is the required strip (its
left endpoint `c` is outside `S` by hypothesis).  When no such prefix
exists, the interior-strip lemma
`exists_interior_interval_of_dense_no_full_right` (the right-handed version
of the left-dense result, obtained by reflection) applies directly. -/
theorem right_full_or_strip_of_right_dense {S : Set ℝ} (hSopen : IsOpen S) {c : ℝ}
    (hc0 : 0 < c) (hc1 : c < 1) (hcNot : c ∉ S)
    (hdense : ∀ ε : ℝ, 0 < ε → ∃ x : ℝ, x ∈ S ∧ c < x ∧ x < c + ε) :
    Set.Ioo c 1 ⊆ S ∨
    ∃ a b : ℝ, c ≤ a ∧ a < b ∧ b < 1 ∧ Set.Ioo a b ⊆ S ∧ a ∉ S ∧ b ∉ S := by
  by_cases hleft : Set.Ioo c 1 ⊆ S
  · exact Or.inl hleft
  · right
    by_cases hfull : ∃ b : ℝ, c < b ∧ b ≤ 1 ∧ Set.Ioo c b ⊆ S
    · -- A full prefix strip `(c, b)` from `c` exists.  Take the maximal such
      -- right end `p = sSup {b | c < b ∧ (c,b) ⊆ S}`; then `(c,p)` is a
      -- strip with both endpoints outside `S` and `p < 1`.
      let B : Set ℝ := {b : ℝ | c < b ∧ Set.Ioo c b ⊆ S}
      have hBne : B.Nonempty := by
        rcases hfull with ⟨b0, hb0c, _hb01, hb0sub⟩
        exact ⟨b0, hb0c, hb0sub⟩
      have hBle1 : ∀ b : ℝ, b ∈ B → b ≤ 1 := by
        intro b hb
        rcases hb with ⟨_hcb, hbsub⟩
        by_contra hbnot
        have h1b : 1 < b := lt_of_not_ge hbnot
        have hsub1 : Set.Ioo c 1 ⊆ Set.Ioo c b := by
          intro x hx
          exact ⟨hx.1, lt_trans hx.2 h1b⟩
        exact hleft (subset_trans hsub1 hbsub)
      have hBbd : BddAbove B := ⟨1, hBle1⟩
      let p : ℝ := sSup B
      have hcp : c < p := by
        rcases hfull with ⟨b0, hb0c, _hb01, hb0sub⟩
        have hb0B : b0 ∈ B := ⟨hb0c, hb0sub⟩
        exact lt_of_lt_of_le hb0c (le_csSup hBbd hb0B)
      have hp1 : p < 1 := by
        by_contra hnot
        have h1le : 1 ≤ p := le_of_not_gt hnot
        apply hleft
        intro x hx
        rcases hx with ⟨hcx, hx1⟩
        have hxp : x < p := by linarith
        rcases exists_lt_of_lt_csSup hBne hxp with ⟨b, hbB, hxb⟩
        rcases hbB with ⟨_hcb, hbsub⟩
        exact hbsub ⟨hcx, hxb⟩
      have hsub_cp : Set.Ioo c p ⊆ S := by
        intro x hx
        rcases hx with ⟨hcx, hxp⟩
        rcases exists_lt_of_lt_csSup hBne hxp with ⟨b, hbB, hxb⟩
        rcases hbB with ⟨_hcb, hbsub⟩
        exact hbsub ⟨hcx, hxb⟩
      have hp_notS : p ∉ S := by
        intro hpS
        rcases Metric.isOpen_iff.mp hSopen p hpS with ⟨δ, hδ0, hball⟩
        let δ' : ℝ := min δ (1 - p)
        have hδ'0 : 0 < δ' := lt_min hδ0 (by linarith)
        let q : ℝ := p + δ' / 2
        have hq_gt_p : p < q := by dsimp [q]; linarith
        have hq_lt_1 : q < 1 := by
          dsimp [q]
          have hhalf : δ' / 2 < δ' := half_lt_self hδ'0
          have h1p : 0 < 1 - p := by linarith
          have hd' : δ' ≤ 1 - p := min_le_right δ (1 - p)
          have hpq : p + δ' / 2 < p + δ' := by linarith
          have hq1 : p + δ' ≤ 1 := by linarith
          exact lt_of_lt_of_le hpq hq1
        have hqB : q ∈ B := by
          refine ⟨lt_trans hcp hq_gt_p, ?_⟩
          intro x hx
          rcases hx with ⟨hcx, hxq⟩
          by_cases hxle : x ≤ p
          · rcases lt_or_eq_of_le hxle with hxl | hxeq
            · exact hsub_cp ⟨hcx, hxl⟩
            · exact hxeq ▸ hpS
          · have hp_lt_x : p < x := lt_of_not_ge hxle
            have hxsub : x - p < δ := by
              have hxq' : x < p + δ' / 2 := by simpa [q] using hxq
              have hxδ'2 : x - p < δ' / 2 := by linarith
              have hδ'2_lt_δ : δ' / 2 < δ := by
                have hlt1 : δ' / 2 < δ' := half_lt_self hδ'0
                have hle2 : δ' ≤ δ := min_le_left δ (1 - p)
                exact lt_of_lt_of_le hlt1 hle2
              exact lt_trans hxδ'2 hδ'2_lt_δ
            have hxball : x ∈ Metric.ball p δ := by
              rw [Metric.mem_ball, Real.dist_eq]
              rw [abs_of_pos (sub_pos.mpr hp_lt_x)]
              exact hxsub
            exact hball hxball
        have hq_le_p : q ≤ p := le_csSup hBbd hqB
        linarith
      exact ⟨c, p, le_rfl, hcp, hp1, hsub_cp, hcNot, hp_notS⟩
    · -- No full prefix strip `(c,b) ⊆ S` with `b ≤ 1`: the interior-strip
      -- lemma applies directly.
      rcases exists_interior_interval_of_dense_no_full_right (S := S) hSopen hc1 hdense hfull with
        ⟨a, b, hac, hab, hb1, hsub, haS, hbS⟩
      exact ⟨a, b, le_of_lt hac, hab, hb1, hsub, haS, hbS⟩

end Commons.Analysis.RealIntervals
