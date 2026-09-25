import Mathlib
import Submission.Work.CR.Flat.Holder

namespace Work.CR.Flat.Holder

open scoped NNReal ENNReal
open Set

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- The supremum of the operator norms of the `i`-th iterated derivatives of a
sum is bounded by the sum of the corresponding suprema. -/
private lemma iterDerivNorm_add_le (i : ℕ) {f g : X → ℂ} {Ω : Set X}
    (hf : ContDiffOn ℝ (i : ℕ∞) f Ω) (hg : ContDiffOn ℝ (i : ℕ∞) g Ω)
    (hΩ : UniqueDiffOn ℝ Ω) :
    iterDerivNorm i (f + g) Ω ≤ iterDerivNorm i f Ω + iterDerivNorm i g Ω := by
  refine iSup₂_le fun x hx => ?_
  rw [iteratedFDerivWithin_add_apply (hf.contDiffWithinAt hx) (hg.contDiffWithinAt hx) hΩ hx]
  calc ENNReal.ofReal ‖iteratedFDerivWithin ℝ i f Ω x + iteratedFDerivWithin ℝ i g Ω x‖
      ≤ ENNReal.ofReal (‖iteratedFDerivWithin ℝ i f Ω x‖ + ‖iteratedFDerivWithin ℝ i g Ω x‖) :=
        ENNReal.ofReal_le_ofReal (norm_add_le _ _)
    _ = ENNReal.ofReal ‖iteratedFDerivWithin ℝ i f Ω x‖
          + ENNReal.ofReal ‖iteratedFDerivWithin ℝ i g Ω x‖ :=
        ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _)
    _ ≤ iterDerivNorm i f Ω + iterDerivNorm i g Ω :=
        add_le_add (le_iterDerivNorm i f Ω hx) (le_iterDerivNorm i g Ω hx)

/-- The Hölder seminorms of the `i`-th iterated derivatives of a sum are
subadditive. -/
private lemma holderSeminorm_add_le (i : ℕ) (α : ℝ) {f g : X → ℂ} {Ω : Set X}
    (hf : ContDiffOn ℝ (i : ℕ∞) f Ω) (hg : ContDiffOn ℝ (i : ℕ∞) g Ω)
    (hΩ : UniqueDiffOn ℝ Ω) :
    holderSeminorm i α (f + g) Ω ≤ holderSeminorm i α f Ω + holderSeminorm i α g Ω := by
  refine iSup₂_le fun x hx => iSup₂_le fun y hy => iSup_le fun hxy => ?_
  rw [iteratedFDerivWithin_add_apply (hf.contDiffWithinAt hx) (hg.contDiffWithinAt hx) hΩ hx,
    iteratedFDerivWithin_add_apply (hf.contDiffWithinAt hy) (hg.contDiffWithinAt hy) hΩ hy]
  have hd : 0 ≤ ‖x - y‖ ^ α := Real.rpow_nonneg (norm_nonneg _) _
  have hsub : (iteratedFDerivWithin ℝ i f Ω x + iteratedFDerivWithin ℝ i g Ω x)
      - (iteratedFDerivWithin ℝ i f Ω y + iteratedFDerivWithin ℝ i g Ω y)
      = (iteratedFDerivWithin ℝ i f Ω x - iteratedFDerivWithin ℝ i f Ω y)
        + (iteratedFDerivWithin ℝ i g Ω x - iteratedFDerivWithin ℝ i g Ω y) := by
    abel
  rw [hsub]
  calc ENNReal.ofReal
        (‖(iteratedFDerivWithin ℝ i f Ω x - iteratedFDerivWithin ℝ i f Ω y)
          + (iteratedFDerivWithin ℝ i g Ω x - iteratedFDerivWithin ℝ i g Ω y)‖ / ‖x - y‖ ^ α)
      ≤ ENNReal.ofReal
          ((‖iteratedFDerivWithin ℝ i f Ω x - iteratedFDerivWithin ℝ i f Ω y‖
            + ‖iteratedFDerivWithin ℝ i g Ω x - iteratedFDerivWithin ℝ i g Ω y‖) / ‖x - y‖ ^ α) :=
        ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right (norm_add_le _ _) hd)
    _ = ENNReal.ofReal
          (‖iteratedFDerivWithin ℝ i f Ω x - iteratedFDerivWithin ℝ i f Ω y‖ / ‖x - y‖ ^ α
            + ‖iteratedFDerivWithin ℝ i g Ω x - iteratedFDerivWithin ℝ i g Ω y‖ / ‖x - y‖ ^ α) := by
        rw [add_div]
    _ = ENNReal.ofReal
          (‖iteratedFDerivWithin ℝ i f Ω x - iteratedFDerivWithin ℝ i f Ω y‖ / ‖x - y‖ ^ α)
        + ENNReal.ofReal
          (‖iteratedFDerivWithin ℝ i g Ω x - iteratedFDerivWithin ℝ i g Ω y‖ / ‖x - y‖ ^ α) :=
        ENNReal.ofReal_add (div_nonneg (norm_nonneg _) hd) (div_nonneg (norm_nonneg _) hd)
    _ ≤ holderSeminorm i α f Ω + holderSeminorm i α g Ω :=
        add_le_add (le_holderSeminorm i α f Ω hx hy hxy) (le_holderSeminorm i α g Ω hx hy hxy)

/-- The `C^{k,α}` norm defined in `Submission/Work/CR/Flat/Holder.lean` is
subadditive on functions that are `C^k` on `Ω`.

`holderNorm k α f Ω` is the `ℝ≥0∞`-valued sum over `i ≤ k` of the quantities
`⨆ x ∈ Ω, ENNReal.ofReal ‖D^i f x‖` and
`⨆ x ≠ y ∈ Ω, ENNReal.ofReal (‖D^i f x - D^i f y‖ / ‖x - y‖ ^ α)`,
where `D^i` is `iteratedFDerivWithin ℝ i · Ω`. -/
theorem holderNorm_add_le {k : ℕ} {α : ℝ} {f g : X → ℂ} {Ω : Set X}
    (hf : ContDiffOn ℝ (k : ℕ∞) f Ω) (hg : ContDiffOn ℝ (k : ℕ∞) g Ω)
    (hΩ : UniqueDiffOn ℝ Ω) :
    holderNorm k α (f + g) Ω ≤ holderNorm k α f Ω + holderNorm k α g Ω := by
  unfold holderNorm
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i hi => ?_
  have hik : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  have hfi : ContDiffOn ℝ (i : ℕ∞) f Ω := hf.of_le (by exact_mod_cast hik)
  have hgi : ContDiffOn ℝ (i : ℕ∞) g Ω := hg.of_le (by exact_mod_cast hik)
  calc iterDerivNorm i (f + g) Ω + holderSeminorm i α (f + g) Ω
      ≤ (iterDerivNorm i f Ω + iterDerivNorm i g Ω)
        + (holderSeminorm i α f Ω + holderSeminorm i α g Ω) :=
        add_le_add (iterDerivNorm_add_le i hfi hgi hΩ) (holderSeminorm_add_le i α hfi hgi hΩ)
    _ = (iterDerivNorm i f Ω + holderSeminorm i α f Ω)
        + (iterDerivNorm i g Ω + holderSeminorm i α g Ω) := by
        rw [add_add_add_comm]

end Work.CR.Flat.Holder
