import Mathlib
import Submission.Work.CR.Flat.Holder
import Submission.Work.CR.Flat.Polydisc
import Submission.Work.NN.Final.iterDerivNorm_comp_smul

namespace Work.NN.Newton.ThinLocal

open scoped NNReal ENNReal
open Set

/-- A dilation `z ↦ s • z` with `s > 0` maps the polydisc of multi-radius `r` at the
origin onto the polydisc of multi-radius `r * s`; equivalently the preimage of
`polydisc 0 (r * s)` is `polydisc 0 r`. -/
private lemma smul_mem_polydisc_zero {n : ℕ} {s r : ℝ} (hs0 : 0 < s) :
    {z : Fin n → ℂ | s • z ∈ Work.CR.Flat.polydisc 0 (fun _ => r * s)}
      = Work.CR.Flat.polydisc 0 (fun _ => r) := by
  ext z
  simp only [Set.mem_ofPred_eq, Work.CR.Flat.mem_polydisc, Pi.zero_apply, sub_zero]
  constructor
  · intro h j
    have hj : ‖(s • z) j‖ < r * s := h j
    rw [Pi.smul_apply, norm_smul, Real.norm_of_nonneg hs0.le, mul_comm r s] at hj
    exact lt_of_mul_lt_mul_left hj hs0.le
  · intro h j
    have hj : ‖z j‖ < r := h j
    rw [Pi.smul_apply, norm_smul, Real.norm_of_nonneg hs0.le, mul_comm r s]
    exact mul_lt_mul_of_pos_left hj hs0

/-- Multiplication by a number `≤ 1` in `ℝ≥0∞` is a contraction. -/
private lemma enNReal_mul_le_self {a b : ℝ≥0∞} (ha : a ≤ 1) : a * b ≤ b := by
  calc a * b ≤ 1 * b := by gcongr
    _ = b := one_mul b

/-- `ofReal (|s| ^ i) ≤ 1` for `0 < s ≤ 1`. -/
private lemma ofReal_pow_le_one {s : ℝ} (hs0 : 0 < s) (hs1 : s ≤ 1) (i : ℕ) :
    ENNReal.ofReal (|s| ^ i) ≤ 1 := by
  rw [ENNReal.ofReal_le_one, abs_of_pos hs0]
  exact pow_le_one₀ hs0.le hs1

/-- `ofReal (|s| ^ r) ≤ 1` for `0 < s ≤ 1` and `r ≥ 0`. -/
private lemma ofReal_rpow_le_one {s : ℝ} (hs0 : 0 < s) (hs1 : s ≤ 1) {r : ℝ} (hr : 0 ≤ r) :
    ENNReal.ofReal (|s| ^ r) ≤ 1 := by
  rw [ENNReal.ofReal_le_one, abs_of_pos hs0]
  calc s ^ r ≤ 1 ^ r := Real.rpow_le_rpow hs0.le hs1 hr
    _ = 1 := Real.one_rpow r

/-- **Scaling of the `C^{1,α}` norm under a dilation with `0 < s ≤ 1`.**
Precomposing with `ζ ↦ s • ζ` and shrinking the polydisc from radius `4` to radius
`4 * s` does not increase the `C^{1,α}` norm: the loss from the dilation on the
derivatives is exactly compensated (indeed over-compensated) by the
`|s| ^ (i + α)` scaling factor, which is `≤ 1` on the whole range `i = 0, 1`. -/
theorem scalingF {n : ℕ} {α : ℝ} (hα0 : 0 < α) {s : ℝ} (hs0 : 0 < s) (hs1 : s ≤ 1)
    (h : (Fin n → ℂ) → ℂ) :
    Work.CR.Flat.holderNorm 1 α (fun ζ => h (s • ζ))
        (Work.CR.Flat.polydisc 0 (fun _ => 4)) ≤
      Work.CR.Flat.holderNorm 1 α h (Work.CR.Flat.polydisc 0 (fun _ => 4 * s)) := by
  have hsne : s ≠ 0 := ne_of_gt hs0
  have hset : {z : Fin n → ℂ | s • z ∈ Work.CR.Flat.polydisc 0 (fun _ => 4 * s)}
      = Work.CR.Flat.polydisc 0 (fun _ => 4) := smul_mem_polydisc_zero hs0
  have hΩ : IsOpen (Work.CR.Flat.polydisc 0 (fun _ : Fin n => 4 * s)) :=
    Work.CR.Flat.isOpen_polydisc _ _
  rw [Work.CR.Flat.holderNorm, Work.CR.Flat.holderNorm]
  apply Finset.sum_le_sum
  intro i hi
  have hkey := Work.NN.Final.iterDerivNorm_comp_smul s hsne i α h hΩ
  obtain ⟨hA, hB⟩ := hkey
  rw [hset] at hA hB
  rw [hA, hB]
  apply add_le_add
  · exact enNReal_mul_le_self (ofReal_pow_le_one hs0 hs1 i)
  · exact enNReal_mul_le_self (ofReal_rpow_le_one hs0 hs1 (by positivity))

end Work.NN.Newton.ThinLocal
