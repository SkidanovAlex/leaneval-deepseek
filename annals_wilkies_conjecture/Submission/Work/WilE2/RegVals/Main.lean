/-
  `Work.WilE2.RegVals.Main` — assembly of the codimension-one Sard theorem.
-/
import Mathlib
import Submission.Work.WilE2.RegVals.Basic
import Submission.Work.WilE2.RegVals.volume_image_eq_zero_of_uniform_flat
import Submission.Work.WilE2.RegVals.flat_sigma0
import Submission.Work.WilE2.RegVals.isClosed_setOf_not_surjective
import Submission.Work.WilE2.RegVals.reduction_step

open MeasureTheory

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

namespace Work.WilE2

/-- The critical set is closed for a `C¹` map. -/
theorem isClosed_critSet {n m : ℕ} (f : (Fin n → ℝ) → (Fin m → ℝ)) (hf : ContDiff ℝ 1 f) :
    IsClosed (critSet f) := by
  have hcont : Continuous (fderiv ℝ f) := hf.continuous_fderiv (by simp)
  exact RegVals.isClosed_setOf_not_surjective.preimage hcont

/-- **Codimension-one Sard theorem.**  The set of critical values of a `C²` map
`g : ℝⁿ → ℝⁿ⁻¹` is Lebesgue-null. -/
theorem sard_codim_one : ∀ n : ℕ, ∀ (g : (Fin n → ℝ) → (Fin (n-1) → ℝ)), ContDiff ℝ 2 g →
    volume (g '' critSet g) = 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro g hg
    by_cases hn : n < 2
    · -- the target `Fin (n-1)` is trivial
      have hempty : critSet g = ∅ := by
        ext z
        simp only [mem_critSet, Set.mem_empty_iff_false, iff_false, not_not]
        refine fun _ => ⟨0, ?_⟩
        funext i
        exact absurd i.isLt (by omega)
      rw [hempty, Set.image_empty]
      simp
    · push Not at hn
      have hcr : IsClosed (critSet g) := isClosed_critSet g (hg.of_le (by norm_num))
      have hcont : Continuous (fderiv ℝ g) := hg.continuous_fderiv (by norm_num)
      have hdec : ∀ R : ℕ,
          volume (g '' (critSet g ∩ Metric.closedBall 0 (R : ℝ))) = 0 := by
        intro R
        have hpiece : ∀ z, z ∈ critSet g ∩ Metric.closedBall 0 (R : ℝ) →
            z ∈ (critSet g ∩ {z | fderiv ℝ g z = 0} ∩ Metric.closedBall 0 (R : ℝ))
              ∪ (⋃ j : ℕ, critSet g ∩ {z | ((j : ℝ) + 1)⁻¹ ≤ ‖fderiv ℝ g z‖}
                  ∩ Metric.closedBall 0 (R : ℝ)) := by
          intro z hz
          rcases hz with ⟨hzc, hzb⟩
          by_cases hz0 : fderiv ℝ g z = 0
          · exact Or.inl ⟨⟨hzc, hz0⟩, hzb⟩
          · have hpos : 0 < ‖fderiv ℝ g z‖ := norm_pos_iff.mpr hz0
            obtain ⟨j, hj⟩ := exists_nat_gt (‖fderiv ℝ g z‖)⁻¹
            have hjpos : 0 < j := by
              rcases Nat.eq_zero_or_pos j with h | h
              · subst h
                simp only [Nat.cast_zero] at hj
                have h1 : (0 : ℝ) < (‖fderiv ℝ g z‖)⁻¹ := by positivity
                exact absurd hj (not_lt.mpr h1.le)
              · exact h
            have h1 : ((j : ℝ))⁻¹ < ‖fderiv ℝ g z‖ :=
              (inv_lt_comm₀ hpos (by positivity)).mp hj
            have h2 : ((j : ℝ) + 1)⁻¹ ≤ ((j : ℝ))⁻¹ := by
              rw [inv_le_inv₀ (by positivity) (by positivity)]
              linarith
            exact Or.inr (Set.mem_iUnion.mpr ⟨j, ⟨⟨hzc, le_trans h2 h1.le⟩, hzb⟩⟩)
        have hflat : volume (g '' (critSet g ∩ {z | fderiv ℝ g z = 0}
            ∩ Metric.closedBall 0 (R : ℝ))) = 0 := by
          have hsub : critSet g ∩ {z | fderiv ℝ g z = 0} ∩ Metric.closedBall 0 (R : ℝ)
              ⊆ {z | fderiv ℝ g z = 0} ∩ Metric.closedBall 0 (R : ℝ) := by
            intro z hz; exact ⟨hz.1.2, hz.2⟩
          refine measure_mono_null (Set.image_mono hsub) ?_
          refine RegVals.volume_image_eq_zero_of_uniform_flat (n := n) (m := n - 1) (q := 2)
            (hm := by omega) (hq := by omega) g _
            (Metric.isBounded_closedBall.subset Set.inter_subset_right) ?_
          intro ε hε
          obtain ⟨δ, hδ, hδprop⟩ := RegVals.flat_sigma0 g hg (R : ℝ) ε hε
          refine ⟨δ, hδ, fun x hx y hy hxy => ?_⟩
          have hxR : ‖x‖ ≤ (R : ℝ) := by
            simpa [Metric.mem_closedBall, dist_eq_norm] using hx.2
          have hyR : ‖y‖ ≤ (R : ℝ) := by
            simpa [Metric.mem_closedBall, dist_eq_norm] using hy.2
          exact hδprop x y hxR hyR hx.1 hy.1 hxy
        have hred : volume (g '' (⋃ j : ℕ, critSet g ∩ {z | ((j : ℝ) + 1)⁻¹ ≤ ‖fderiv ℝ g z‖}
            ∩ Metric.closedBall 0 (R : ℝ))) = 0 := by
          have hterm : ∀ j : ℕ, volume (g '' (critSet g ∩ {z | ((j : ℝ) + 1)⁻¹
              ≤ ‖fderiv ℝ g z‖} ∩ Metric.closedBall 0 (R : ℝ))) = 0 := by
            intro j
            set Kset : Set (Fin n → ℝ) := critSet g ∩ {z | ((j : ℝ) + 1)⁻¹ ≤ ‖fderiv ℝ g z‖}
              ∩ Metric.closedBall 0 (R : ℝ) with hKset
            have hKc : IsCompact Kset := Metric.isCompact_iff_isClosed_bounded.mpr
              ⟨(hcr.inter (isClosed_le continuous_const hcont.norm)).inter Metric.isClosed_closedBall,
                Metric.isBounded_closedBall.subset Set.inter_subset_right⟩
            have hloc : ∀ w ∈ Kset, ∃ δ : ℝ,
                0 < δ ∧ volume (g '' (Metric.ball w δ ∩ critSet g)) = 0 := by
              intro w hw
              have hwm : w ∈ critSet g ∧ ((j : ℝ) + 1)⁻¹ ≤ ‖fderiv ℝ g w‖
                  ∧ w ∈ Metric.closedBall 0 (R : ℝ) := by
                have hh := hw; rw [hKset] at hh
                exact ⟨hh.1.1, hh.1.2, hh.2⟩
              have hzn : fderiv ℝ g w ≠ 0 := by
                intro h0
                have h1 : ((j : ℝ) + 1)⁻¹ ≤ (0 : ℝ) := by
                  simpa [h0] using hwm.2.1
                have h2 : (0 : ℝ) < ((j : ℝ) + 1)⁻¹ := by positivity
                linarith
              exact RegVals.reduction_step hn g hg w hwm.1 hzn (fun k hk h hh => ih k hk h hh)
            choose δ hδ using fun (z : ↥Kset) => hloc (Subtype.val z) (Subtype.property z)
            obtain ⟨t, ht⟩ := hKc.elim_finite_subcover
              (fun z : ↥Kset => Metric.ball (Subtype.val z) (δ z))
              (fun z => Metric.isOpen_ball)
              (fun w hw => Set.mem_iUnion.mpr ⟨⟨w, hw⟩, Metric.mem_ball_self (hδ ⟨w, hw⟩).1⟩)
            have hsub : Kset ⊆ ⋃ z ∈ t, Metric.ball (Subtype.val z) (δ z) ∩ critSet g := by
              intro w hw
              obtain ⟨z, hzt, hzw⟩ := Set.mem_iUnion₂.mp (ht hw)
              exact Set.mem_iUnion₂.mpr ⟨z, hzt, hzw, hw.1.1⟩
            have hfin : (∑ z ∈ t, volume (g '' (Metric.ball (Subtype.val z) (δ z) ∩ critSet g))) = 0 :=
              Finset.sum_eq_zero (fun z _ => (hδ z).2)
            refine le_antisymm ?_ bot_le
            calc volume (g '' Kset)
                ≤ volume (g '' (⋃ z ∈ t, Metric.ball (Subtype.val z) (δ z) ∩ critSet g)) :=
                  measure_mono (Set.image_mono hsub)
              _ = volume (⋃ z ∈ t, g '' (Metric.ball (Subtype.val z) (δ z) ∩ critSet g)) := by
                  rw [Set.image_iUnion₂]
              _ ≤ ∑ z ∈ t, volume (g '' (Metric.ball (Subtype.val z) (δ z) ∩ critSet g)) :=
                  measure_biUnion_finset_le t _
              _ = 0 := hfin
          have hsum : (∑' j : ℕ, volume (g '' (critSet g ∩ {z | ((j : ℝ) + 1)⁻¹
              ≤ ‖fderiv ℝ g z‖} ∩ Metric.closedBall 0 (R : ℝ)))) = 0 := by
            simp only [hterm]
            exact tsum_zero
          refine le_antisymm ?_ bot_le
          calc volume (g '' (⋃ j : ℕ, critSet g ∩ {z | ((j : ℝ) + 1)⁻¹ ≤ ‖fderiv ℝ g z‖}
                ∩ Metric.closedBall 0 (R : ℝ)))
              = volume (⋃ j : ℕ, g '' (critSet g ∩ {z | ((j : ℝ) + 1)⁻¹
                  ≤ ‖fderiv ℝ g z‖} ∩ Metric.closedBall 0 (R : ℝ))) := by rw [Set.image_iUnion]
            _ ≤ ∑' j : ℕ, volume (g '' (critSet g ∩ {z | ((j : ℝ) + 1)⁻¹
                  ≤ ‖fderiv ℝ g z‖} ∩ Metric.closedBall 0 (R : ℝ))) := measure_iUnion_le _
            _ = 0 := hsum
        refine le_antisymm ?_ bot_le
        calc volume (g '' (critSet g ∩ Metric.closedBall 0 (R : ℝ)))
            ≤ volume (g '' ((critSet g ∩ {z | fderiv ℝ g z = 0} ∩ Metric.closedBall 0 (R : ℝ))
                ∪ (⋃ j : ℕ, critSet g ∩ {z | ((j : ℝ) + 1)⁻¹ ≤ ‖fderiv ℝ g z‖}
                    ∩ Metric.closedBall 0 (R : ℝ)))) := by
              refine measure_mono (Set.image_mono ?_)
              intro z hz; exact hpiece z hz
          _ ≤ volume (g '' (critSet g ∩ {z | fderiv ℝ g z = 0} ∩ Metric.closedBall 0 (R : ℝ)))
              + volume (g '' (⋃ j : ℕ, critSet g ∩ {z | ((j : ℝ) + 1)⁻¹ ≤ ‖fderiv ℝ g z‖}
                    ∩ Metric.closedBall 0 (R : ℝ))) := by
              rw [Set.image_union]
              exact measure_union_le _ _
          _ = 0 := by rw [hflat, hred, add_zero]
      have hcover : critSet g ⊆ ⋃ R : ℕ, (critSet g ∩ Metric.closedBall 0 (R : ℝ)) := by
        intro z hz
        obtain ⟨R, hR⟩ := exists_nat_ge ‖z‖
        exact Set.mem_iUnion.mpr ⟨R, hz, by simpa [Metric.mem_closedBall, dist_eq_norm] using hR⟩
      have hsum : (∑' R : ℕ, volume (g '' (critSet g ∩ Metric.closedBall 0 (R : ℝ)))) = 0 := by
        simp only [hdec]
        exact tsum_zero
      refine le_antisymm ?_ bot_le
      calc volume (g '' critSet g)
          ≤ volume (g '' (⋃ R : ℕ, (critSet g ∩ Metric.closedBall 0 (R : ℝ)))) :=
            measure_mono (Set.image_mono hcover)
        _ = volume (⋃ R : ℕ, g '' (critSet g ∩ Metric.closedBall 0 (R : ℝ))) := by
            rw [Set.image_iUnion]
        _ ≤ ∑' R : ℕ, volume (g '' (critSet g ∩ Metric.closedBall 0 (R : ℝ))) :=
            measure_iUnion_le _
        _ = 0 := hsum

end Work.WilE2
