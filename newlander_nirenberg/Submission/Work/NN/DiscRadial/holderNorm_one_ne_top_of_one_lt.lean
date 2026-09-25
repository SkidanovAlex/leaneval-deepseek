import Mathlib
import Submission.Work.CR.Flat.Holder

namespace Work.NN.DiscRadial

open scoped NNReal ENNReal
open Set

/-- If `1 ≤ α` then the `C^{i,1}`-Hölder seminorm is controlled by the
`C^{i,α}`-Hölder seminorm together with the `i`-th derivative sup norm.

Indeed, for a pair `x ≠ y` with `d = ‖x - y‖`:
* if `d ≤ 1` then `d ^ α ≤ d`, so `‖·‖ / d ≤ ‖·‖ / d ^ α`;
* if `d ≥ 1` then `‖·‖ / d ≤ ‖·‖ ≤ ‖D^i f x‖ + ‖D^i f y‖`. -/
private lemma holderSeminorm_one_le {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {α : ℝ} (hα : 1 ≤ α) (i : ℕ) (g : X → ℂ) (Ω : Set X) :
    Work.CR.Flat.holderSeminorm i 1 g Ω
      ≤ Work.CR.Flat.holderSeminorm i α g Ω
        + Work.CR.Flat.iterDerivNorm i g Ω + Work.CR.Flat.iterDerivNorm i g Ω :=
  iSup₂_le fun x hx => iSup₂_le fun y hy => iSup_le fun hxy => by
    have hdpos : 0 < ‖x - y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
    have hS : ENNReal.ofReal
        (‖iteratedFDerivWithin ℝ i g Ω x - iteratedFDerivWithin ℝ i g Ω y‖ / ‖x - y‖ ^ α)
        ≤ Work.CR.Flat.holderSeminorm i α g Ω :=
      Work.CR.Flat.le_holderSeminorm i α g Ω hx hy hxy
    have hMx : ENNReal.ofReal ‖iteratedFDerivWithin ℝ i g Ω x‖
        ≤ Work.CR.Flat.iterDerivNorm i g Ω :=
      Work.CR.Flat.le_iterDerivNorm i g Ω hx
    have hMy : ENNReal.ofReal ‖iteratedFDerivWithin ℝ i g Ω y‖
        ≤ Work.CR.Flat.iterDerivNorm i g Ω :=
      Work.CR.Flat.le_iterDerivNorm i g Ω hy
    rw [Real.rpow_one]
    by_cases hd : ‖x - y‖ ≤ 1
    · have hdα : ‖x - y‖ ^ α ≤ ‖x - y‖ :=
        Real.rpow_le_self_of_le_one (norm_nonneg _) hd hα
      have hle : ‖iteratedFDerivWithin ℝ i g Ω x - iteratedFDerivWithin ℝ i g Ω y‖ / ‖x - y‖
          ≤ ‖iteratedFDerivWithin ℝ i g Ω x - iteratedFDerivWithin ℝ i g Ω y‖
              / ‖x - y‖ ^ α :=
        div_le_div_of_nonneg_left (norm_nonneg _) (Real.rpow_pos_of_pos hdpos α) hdα
      calc ENNReal.ofReal
            (‖iteratedFDerivWithin ℝ i g Ω x - iteratedFDerivWithin ℝ i g Ω y‖ / ‖x - y‖)
          ≤ ENNReal.ofReal
              (‖iteratedFDerivWithin ℝ i g Ω x - iteratedFDerivWithin ℝ i g Ω y‖
                / ‖x - y‖ ^ α) :=
            ENNReal.ofReal_le_ofReal hle
        _ ≤ Work.CR.Flat.holderSeminorm i α g Ω := hS
        _ ≤ Work.CR.Flat.holderSeminorm i α g Ω + Work.CR.Flat.iterDerivNorm i g Ω
              + Work.CR.Flat.iterDerivNorm i g Ω :=
            le_add_right (le_add_right le_rfl)
    · have hd1 : 1 ≤ ‖x - y‖ := le_of_lt (not_le.mp hd)
      have hle : ‖iteratedFDerivWithin ℝ i g Ω x - iteratedFDerivWithin ℝ i g Ω y‖ / ‖x - y‖
          ≤ ‖iteratedFDerivWithin ℝ i g Ω x - iteratedFDerivWithin ℝ i g Ω y‖ :=
        div_le_self (norm_nonneg _) hd1
      calc ENNReal.ofReal
            (‖iteratedFDerivWithin ℝ i g Ω x - iteratedFDerivWithin ℝ i g Ω y‖ / ‖x - y‖)
          ≤ ENNReal.ofReal
              ‖iteratedFDerivWithin ℝ i g Ω x - iteratedFDerivWithin ℝ i g Ω y‖ :=
            ENNReal.ofReal_le_ofReal hle
        _ ≤ ENNReal.ofReal
              (‖iteratedFDerivWithin ℝ i g Ω x‖ + ‖iteratedFDerivWithin ℝ i g Ω y‖) :=
            ENNReal.ofReal_le_ofReal (norm_sub_le _ _)
        _ = ENNReal.ofReal ‖iteratedFDerivWithin ℝ i g Ω x‖
              + ENNReal.ofReal ‖iteratedFDerivWithin ℝ i g Ω y‖ :=
            ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _)
        _ ≤ Work.CR.Flat.iterDerivNorm i g Ω + Work.CR.Flat.iterDerivNorm i g Ω :=
            add_le_add hMx hMy
        _ ≤ Work.CR.Flat.holderSeminorm i α g Ω + Work.CR.Flat.iterDerivNorm i g Ω
              + Work.CR.Flat.iterDerivNorm i g Ω :=
            add_le_add (le_add_left le_rfl) le_rfl

theorem holderNorm_one_ne_top_of_one_lt {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {k : ℕ} {α : ℝ} (hα : 1 < α) {g : X → ℂ} {Ω : Set X}
    (h : Work.CR.Flat.holderNorm k α g Ω ≠ ⊤) :
    Work.CR.Flat.holderNorm k 1 g Ω ≠ ⊤ := by
  have hα1 : (1 : ℝ) ≤ α := le_of_lt hα
  rw [Work.CR.Flat.holderNorm] at h ⊢
  rw [ENNReal.sum_ne_top] at h ⊢
  intro i hi
  have hh := h i hi
  rw [ENNReal.add_ne_top] at hh
  obtain ⟨hM, hS⟩ := hh
  rw [ENNReal.add_ne_top]
  exact ⟨hM, ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr ⟨hS, hM⟩, hM⟩)
    (holderSeminorm_one_le hα1 i g Ω)⟩

end Work.NN.DiscRadial
