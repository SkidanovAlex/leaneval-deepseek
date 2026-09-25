import Mathlib
import Submission.Work.CR.Flat.Holder

namespace Work.CR.Flat.Holder

open scoped NNReal ENNReal
open Set

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

omit [NormedAddCommGroup X] [NormedSpace ℝ X] in
/-- Pulling a constant `a : ℝ≥0∞` out of a supremum indexed by `x ∈ s`. -/
private lemma mul_iSup_mem (a : ℝ≥0∞) (s : Set X) (g : X → ℝ≥0∞) :
    a * (⨆ x ∈ s, g x) = ⨆ x ∈ s, a * g x := by
  simp_rw [ENNReal.mul_iSup]

/-- The iterated within-derivative of `c • f` is `c` times that of `f`, at points of `Ω`. -/
private lemma iteratedFDerivWithin_const_smul_eq {k : ℕ} (c : ℂ) {f : X → ℂ} {Ω : Set X}
    (hf : ContDiffOn ℝ (k : ℕ∞) f Ω) (hΩ : UniqueDiffOn ℝ Ω) {i : ℕ} (hi : i ≤ k) {x : X}
    (hx : x ∈ Ω) :
    iteratedFDerivWithin ℝ i (c • f) Ω x = c • iteratedFDerivWithin ℝ i f Ω x :=
  iteratedFDerivWithin_const_smul_apply ((hf x hx).of_le (by exact_mod_cast hi)) hΩ hx

/-- The pointwise norm identity underlying the homogeneity of `iterDerivNorm`. -/
private lemma ofReal_norm_iteratedFDerivWithin_const_smul {k : ℕ} (c : ℂ) {f : X → ℂ}
    {Ω : Set X} (hf : ContDiffOn ℝ (k : ℕ∞) f Ω) (hΩ : UniqueDiffOn ℝ Ω) {i : ℕ} (hi : i ≤ k)
    {x : X} (hx : x ∈ Ω) :
    ENNReal.ofReal ‖iteratedFDerivWithin ℝ i (c • f) Ω x‖
      = ENNReal.ofReal ‖c‖ * ENNReal.ofReal ‖iteratedFDerivWithin ℝ i f Ω x‖ := by
  rw [iteratedFDerivWithin_const_smul_eq c hf hΩ hi hx, norm_smul,
    ENNReal.ofReal_mul (norm_nonneg c)]

/-- `iterDerivNorm` is positively homogeneous under multiplication by a constant. -/
private lemma iterDerivNorm_const_smul {k : ℕ} (c : ℂ) {f : X → ℂ} {Ω : Set X}
    (hf : ContDiffOn ℝ (k : ℕ∞) f Ω) (hΩ : UniqueDiffOn ℝ Ω) {i : ℕ} (hi : i ≤ k) :
    iterDerivNorm i (c • f) Ω = ENNReal.ofReal ‖c‖ * iterDerivNorm i f Ω := by
  unfold iterDerivNorm
  rw [mul_iSup_mem]
  refine iSup_congr fun x => iSup_congr fun hx => ?_
  exact ofReal_norm_iteratedFDerivWithin_const_smul c hf hΩ hi hx

/-- The pointwise identity for one summand of `holderSeminorm`. -/
private lemma holderSeminorm_body {k : ℕ} {α : ℝ} (c : ℂ) {f : X → ℂ} {Ω : Set X}
    (hf : ContDiffOn ℝ (k : ℕ∞) f Ω) (hΩ : UniqueDiffOn ℝ Ω) {i : ℕ} (hi : i ≤ k) {x y : X}
    (hx : x ∈ Ω) (hy : y ∈ Ω) :
    ENNReal.ofReal
        (‖iteratedFDerivWithin ℝ i (c • f) Ω x - iteratedFDerivWithin ℝ i (c • f) Ω y‖
          / ‖x - y‖ ^ α)
      = ENNReal.ofReal ‖c‖ *
        ENNReal.ofReal
          (‖iteratedFDerivWithin ℝ i f Ω x - iteratedFDerivWithin ℝ i f Ω y‖
            / ‖x - y‖ ^ α) := by
  rw [iteratedFDerivWithin_const_smul_eq c hf hΩ hi hx,
    iteratedFDerivWithin_const_smul_eq c hf hΩ hi hy, ← smul_sub, norm_smul, mul_div_assoc,
    ENNReal.ofReal_mul (norm_nonneg c)]

/-- `holderSeminorm` is positively homogeneous under multiplication by a constant. -/
private lemma holderSeminorm_const_smul {k : ℕ} {α : ℝ} (c : ℂ) {f : X → ℂ} {Ω : Set X}
    (hf : ContDiffOn ℝ (k : ℕ∞) f Ω) (hΩ : UniqueDiffOn ℝ Ω) {i : ℕ} (hi : i ≤ k) :
    holderSeminorm i α (c • f) Ω = ENNReal.ofReal ‖c‖ * holderSeminorm i α f Ω := by
  refine le_antisymm ?_ ?_
  · unfold holderSeminorm
    refine iSup₂_le fun x hx => iSup₂_le fun y hy => iSup_le fun hxy => ?_
    rw [holderSeminorm_body c hf hΩ hi hx hy]
    exact mul_le_mul_right (le_holderSeminorm i α f Ω hx hy hxy) _
  · unfold holderSeminorm
    simp_rw [ENNReal.mul_iSup]
    refine iSup₂_le fun x hx => iSup₂_le fun y hy => iSup_le fun hxy => ?_
    exact le_iSup₂_of_le x hx (le_iSup₂_of_le y hy
      (le_iSup_of_le hxy (holderSeminorm_body c hf hΩ hi hx hy).symm.le))

/-- The `C^{k,α}` norm of `Submission/Work/CR/Flat/Holder.lean` is positively
homogeneous under multiplication by a constant `c : ℂ` (with respect to the
natural `ℂ`-module structure on `ℂ`-valued functions). -/
theorem holderNorm_smul {k : ℕ} {α : ℝ} (c : ℂ) {f : X → ℂ} {Ω : Set X}
    (hf : ContDiffOn ℝ (k : ℕ∞) f Ω) (hΩ : UniqueDiffOn ℝ Ω) :
    holderNorm k α (c • f) Ω = ENNReal.ofReal ‖c‖ * holderNorm k α f Ω := by
  unfold holderNorm
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hik : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  rw [iterDerivNorm_const_smul c hf hΩ hik, holderSeminorm_const_smul c hf hΩ hik, mul_add]

end Work.CR.Flat.Holder
