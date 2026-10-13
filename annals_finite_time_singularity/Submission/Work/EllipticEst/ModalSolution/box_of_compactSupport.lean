import Mathlib.Analysis.Real.Pi.Bounds
import Submission.Work.FTS.EllipticEst.OpenQDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real

namespace Work.EllipticEst.ModalSolution

/-- A compact subset of the open quadrant `(0,∞) × (0,π/2)` is contained in a box
`(a,b) × (c,d)` with `0 < a < b` and `0 < c < d < π/2`.

(The box is obtained from the extreme value theorem applied to the two coordinates on the
compact set; note that no condition links the box to the support -- it only has to *contain*
it, and to be contained in the closed strip `[0,∞) × [0,π/2)`.) -/
private theorem exists_box_of_isCompact_subset_Q0 {K : Set (ℝ × ℝ)} (hK : IsCompact K)
    (hsub : K ⊆ Work.FTS.EllipticEst.Q0) :
    ∃ a b c d : ℝ, 0 < a ∧ a < b ∧ 0 < c ∧ c < d ∧ d < π / 2 ∧
      K ⊆ Set.Ioo a b ×ˢ Set.Ioo c d := by
  obtain rfl | hne := K.eq_empty_or_nonempty
  · exact ⟨1, 2, 1 / 4, 1 / 2, by norm_num, by norm_num, by norm_num, by norm_num,
      by linarith [Real.pi_gt_three], Set.empty_subset _⟩
  · -- the extreme value theorem for the two coordinates on the compact set `K`
    obtain ⟨p₁, hp₁K, hmin₁⟩ := hK.exists_isMinOn hne continuous_fst.continuousOn
    obtain ⟨p₂, hp₂K, hmax₁⟩ := hK.exists_isMaxOn hne continuous_fst.continuousOn
    obtain ⟨q₁, hq₁K, hmin₂⟩ := hK.exists_isMinOn hne continuous_snd.continuousOn
    obtain ⟨q₂, hq₂K, hmax₂⟩ := hK.exists_isMaxOn hne continuous_snd.continuousOn
    have hpp : p₁.1 ≤ p₂.1 := (isMinOn_iff.mp hmin₁) p₂ hp₂K
    have hqq : q₁.2 ≤ q₂.2 := (isMinOn_iff.mp hmin₂) q₂ hq₂K
    have hp₁ : 0 < p₁.1 := (hsub hp₁K).1
    have hq₁ : 0 < q₁.2 := (hsub hq₁K).2.1
    have hq₂ : q₂.2 < π / 2 := (hsub hq₂K).2.2
    refine ⟨p₁.1 / 2, p₂.1 + 1, q₁.2 / 2, (q₂.2 + π / 2) / 2, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · linarith
    · linarith
    · linarith
    · linarith [Real.pi_pos]
    · linarith
    · intro p hpK
      have h1 : p₁.1 / 2 < p.1 := by
        have h := (isMinOn_iff.mp hmin₁) p hpK
        linarith
      have h2 : p.1 < p₂.1 + 1 := by
        have h := (isMaxOn_iff.mp hmax₁) p hpK
        linarith
      have h3 : q₁.2 / 2 < p.2 := by
        have h := (isMinOn_iff.mp hmin₂) p hpK
        linarith
      have h4 : p.2 < (q₂.2 + π / 2) / 2 := by
        have h := (isMaxOn_iff.mp hmax₂) p hpK
        linarith
      exact ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩

theorem box_of_compactSupport {ψ : ℝ → ℝ → ℝ}
    (hc : HasCompactSupport (Function.uncurry ψ))
    (hs : tsupport (Function.uncurry ψ) ⊆ Work.FTS.EllipticEst.Q0) :
    ∃ a b c d : ℝ, 0 < a ∧ a < b ∧ 0 < c ∧ c < d ∧ d < π / 2 ∧
      ∀ p : ℝ × ℝ, p ∉ Set.Ioo a b ×ˢ Set.Ioo c d → ψ p.1 p.2 = 0 := by
  obtain ⟨a, b, c, d, ha, hab, hcc, hcd, hd, hbox⟩ :=
    exists_box_of_isCompact_subset_Q0 hc.isCompact hs
  refine ⟨a, b, c, d, ha, hab, hcc, hcd, hd, fun p hp => ?_⟩
  -- the box contains the support of `ψ`, hence `ψ` vanishes outside it
  change Function.uncurry ψ p = 0
  exact image_eq_zero_of_notMem_tsupport fun h => hp (hbox h)

end Work.EllipticEst.ModalSolution
