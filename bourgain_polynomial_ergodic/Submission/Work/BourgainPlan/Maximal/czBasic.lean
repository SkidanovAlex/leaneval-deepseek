import Mathlib
import Submission.Work.BourgainPlan.Maximal.annulusCZDefs
import Submission.Work.BourgainPlan.Maximal.dyCZ

/-!
# Elementary structure of the Calderón--Zygmund pieces

`czBasic` collects the *pointwise* facts about the objects of `annulusCZDefs.lean` that the
assembly needs, all of which are immediate from the disjointness of the maximal dyadic cells
(`czMax_disjoint`, `czMax_eq_of_mem`):

* on a maximal cell, `czGood` is the complex cell average and `czBad` is `f - (cell average)`;
* off the CZ set `lwtOm σ c`, `czBad` vanishes and `czGood` is `f`;
* each bad piece has mean zero (this is the only place where integrability of `f` is used, since
  Lean's Bochner integral is `0` for non-integrable functions);
* the complement of the enlargement `czStar σ c` lies in the region `{|x - c_p| > 2^{n_p+1}}` of
  `AnnulusBadPartBound b`, for every maximal cell `p` at once;
* the norm of the complex cell average is the `σ`-average of the cell, in the exact shape used by
  `czMax_avg_le`.
-/

open MeasureTheory Set Measure
open scoped ENNReal BigOperators Classical

namespace Work.BourgainPlan.Maximal

/-- Off its own cell, a bad piece vanishes. -/
lemma czBadPiece_of_notMem (f : ℝ → ℂ) (p : ℤ × ℤ) {x : ℝ} (hx : x ∉ dyCell p.1 p.2) :
    czBadPiece f p x = 0 := by
  simp only [czBadPiece, hx, if_false]

/-- On its own cell, a bad piece is `f` minus the cell average. -/
lemma czBadPiece_of_mem (f : ℝ → ℂ) (p : ℤ × ℤ) {x : ℝ} (hx : x ∈ dyCell p.1 p.2) :
    czBadPiece f p x = f x - czCellAvgC f p := by
  simp only [czBadPiece, hx, if_true]

/-- The bad part vanishes off the CZ set. -/
lemma czBad_of_notMem {f : ℝ → ℂ} {σ : ℝ → ℝ≥0∞} {c : ℝ≥0∞} {x : ℝ}
    (hx : x ∉ lwtOm σ c) : czBad f σ c x = 0 := by
  have hzero : ∀ p : ℤ × ℤ, (if p ∈ czMax σ c then czBadPiece f p x else 0) = 0 := by
    intro p
    by_cases hp : p ∈ czMax σ c
    · have hxd : x ∉ dyCell p.1 p.2 := by
        intro hmem
        exact hx (mem_iUnion₂.mpr ⟨p, hp, hmem⟩)
      rw [if_pos hp, czBadPiece_of_notMem f p hxd]
    · rw [if_neg hp]
  rw [czBad, show (fun p : ℤ × ℤ => if p ∈ czMax σ c then czBadPiece f p x else 0)
      = fun _ => (0 : ℂ) from funext hzero]
  simp

/-- The good part is `f` off the CZ set. -/
lemma czGood_of_notMem {f : ℝ → ℂ} {σ : ℝ → ℝ≥0∞} {c : ℝ≥0∞} {x : ℝ}
    (hx : x ∉ lwtOm σ c) : czGood f σ c x = f x := by
  rw [czGood, czBad_of_notMem hx, sub_zero]

/-- On the maximal cell `p`, the bad part is `f` minus the cell average: only the term `p` of the
sum survives, by disjointness of the maximal cells. -/
lemma czBad_of_mem_cell {f : ℝ → ℂ} {σ : ℝ → ℝ≥0∞} {c : ℝ≥0∞} {p : ℤ × ℤ}
    (hp : p ∈ czMax σ c) {x : ℝ} (hx : x ∈ dyCell p.1 p.2) :
    czBad f σ c x = f x - czCellAvgC f p := by
  have h : ∀ q : ℤ × ℤ, q ≠ p →
      (if q ∈ czMax σ c then czBadPiece f q x else 0) = 0 := by
    intro q hqp
    by_cases hqcm : q ∈ czMax σ c
    · have hxq : x ∉ dyCell q.1 q.2 := by
        intro hmem
        exact hqp (czMax_eq_of_mem (p := p) (q := q) hp hqcm hx hmem).symm
      rw [if_pos hqcm, czBadPiece_of_notMem f q hxq]
    · rw [if_neg hqcm]
  rw [czBad, tsum_eq_single p (fun q hqp => h q hqp), if_pos hp, czBadPiece_of_mem f p hx]

/-- On the maximal cell `p`, the good part is the complex cell average of `f`. -/
lemma czGood_of_mem_cell {f : ℝ → ℂ} {σ : ℝ → ℝ≥0∞} {c : ℝ≥0∞} {p : ℤ × ℤ}
    (hp : p ∈ czMax σ c) {x : ℝ} (hx : x ∈ dyCell p.1 p.2) :
    czGood f σ c x = czCellAvgC f p := by
  rw [czGood, czBad_of_mem_cell hp hx]
  ring

/-- The norm of the complex cell average is at most the `σ`-average of the cell, in the exact shape
in which `czMax_avg_le` bounds the latter. -/
lemma czCellAvgC_enorm_le (f : ℝ → ℂ) (p : ℤ × ℤ) :
    ‖czCellAvgC f p‖ₑ
      ≤ ENNReal.ofReal (((2 : ℝ) ^ p.1)⁻¹) * ∫⁻ y in dyCell p.1 p.2, ‖f y‖ₑ := by
  have hpos : (0 : ℝ) < (2 : ℝ) ^ p.1 := zpow_two_pos p.1
  calc ‖czCellAvgC f p‖ₑ
      = ‖((2 : ℝ) ^ p.1)⁻¹‖ₑ * ‖∫ y in dyCell p.1 p.2, f y‖ₑ := by
        rw [czCellAvgC, enorm_smul]
    _ = ENNReal.ofReal (((2 : ℝ) ^ p.1)⁻¹) * ‖∫ y in dyCell p.1 p.2, f y‖ₑ := by
        rw [Real.enorm_eq_ofReal (inv_nonneg.mpr hpos.le)]
    _ ≤ ENNReal.ofReal (((2 : ℝ) ^ p.1)⁻¹) * ∫⁻ y in dyCell p.1 p.2, ‖f y‖ₑ :=
        mul_le_mul' le_rfl
          (enorm_integral_le_lintegral_enorm (μ := volume.restrict (dyCell p.1 p.2)) f)

/-- **Mean zero of the bad pieces.**  For an integrable `f`, every bad piece has vanishing
integral. -/
lemma czBadPiece_integral_eq_zero {f : ℝ → ℂ} (hf : Integrable f volume) (p : ℤ × ℤ) :
    ∫ x, czBadPiece f p x = 0 := by
  have hpos : (0 : ℝ) < (2 : ℝ) ^ p.1 := zpow_two_pos p.1
  have hvol : volume (dyCell p.1 p.2) ≠ ⊤ := by
    rw [dyCell_volume_eq]; exact ENNReal.ofReal_ne_top
  have hIntC : IntegrableOn (fun _ : ℝ => czCellAvgC f p) (dyCell p.1 p.2) volume := by
    haveI : IsFiniteMeasure (volume.restrict (dyCell p.1 p.2)) :=
      ⟨lt_top_iff_ne_top.mpr (by rwa [Measure.restrict_apply_univ])⟩
    exact integrable_const (czCellAvgC f p)
  have h1 : czBadPiece f p
      = (dyCell p.1 p.2).indicator (fun y => f y - czCellAvgC f p) := by
    funext x
    rw [Set.indicator_apply]
    by_cases hx : x ∈ dyCell p.1 p.2
    · rw [czBadPiece_of_mem f p hx, if_pos hx]
    · rw [czBadPiece_of_notMem f p hx, if_neg hx]
  have hsub : ∫ x in dyCell p.1 p.2, (f x - czCellAvgC f p)
      = (∫ x in dyCell p.1 p.2, f x) - ∫ x in dyCell p.1 p.2, czCellAvgC f p := by
    simpa using integral_sub hf.integrableOn hIntC
  have hconst : ∫ x in dyCell p.1 p.2, czCellAvgC f p
      = Measure.real volume (dyCell p.1 p.2) • czCellAvgC f p := setIntegral_const _
  have h3 : Measure.real volume (dyCell p.1 p.2) • czCellAvgC f p
      = ∫ x in dyCell p.1 p.2, f x := by
    have hreal : Measure.real volume (dyCell p.1 p.2) = ((2 : ℝ) ^ p.1) := by
      rw [Measure.real_def, dyCell_volume_eq, ENNReal.toReal_ofReal hpos.le]
    rw [hreal, czCellAvgC, smul_smul, mul_inv_cancel₀ (ne_of_gt hpos), one_smul]
  rw [h1, integral_indicator (dyCell_measurable p.1 p.2), hsub, hconst, h3, sub_self]

/-- **The complement of `czStar`.**  Outside the enlargement of the CZ set, every maximal cell `p`
lies at distance more than `2^{n_p+1}` from its pivot `k_p·2^{n_p}`, which is exactly the region of
`AnnulusBadPartBound b`. -/
lemma czStar_compl {σ : ℝ → ℝ≥0∞} {c : ℝ≥0∞} {x : ℝ} (hx : x ∉ czStar σ c)
    {p : ℤ × ℤ} (hp : p ∈ czMax σ c) :
    2 * (2 : ℝ) ^ p.1 < |x - (p.2 : ℝ) * (2 : ℝ) ^ p.1| := by
  have hp1 : (0 : ℝ) < (2 : ℝ) ^ p.1 := zpow_two_pos p.1
  have h2 : (2 : ℝ) ^ (p.1 + 1) = 2 * (2 : ℝ) ^ p.1 := by
    rw [zpow_add_one₀ (by norm_num : (2 : ℝ) ≠ 0), mul_comm]
  have hnot : ¬ ((p.2 : ℝ) * (2 : ℝ) ^ p.1 - 2 * (2 : ℝ) ^ p.1 ≤ x
      ∧ x ≤ (p.2 : ℝ) * (2 : ℝ) ^ p.1 + 2 * (2 : ℝ) ^ p.1) := by
    intro hcon
    have hI : x ∈ Set.Icc (((p.2 : ℝ) * (2 : ℝ) ^ p.1) - (2 : ℝ) ^ (p.1 + 1))
        (((p.2 : ℝ) * (2 : ℝ) ^ p.1) + (2 : ℝ) ^ (p.1 + 1)) := by
      rw [Set.mem_Icc, h2]
      exact hcon
    exact hx (mem_iUnion₂.mpr ⟨p, hp, hI⟩)
  rw [not_and_or] at hnot
  rcases hnot with h | h
  · rw [not_le] at h
    rw [show x - (p.2 : ℝ) * (2 : ℝ) ^ p.1
        = -((p.2 : ℝ) * (2 : ℝ) ^ p.1 - x) by ring, abs_neg,
      abs_of_pos (by linarith)]
    linarith
  · rw [not_le] at h
    rw [abs_of_pos (by linarith)]
    linarith

end Work.BourgainPlan.Maximal
