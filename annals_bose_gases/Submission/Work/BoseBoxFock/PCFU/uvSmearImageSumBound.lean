import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.PCFU.lowKer_imageSum_bound
import Submission.Work.BoseBoxFock.uvSmear_continuous_decay
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.PCFU.uvSmearImageSumBound`

**The lattice image sum of the UV-smoothed weight is uniformly bounded on a bounded window.**

`uvSmear fu Λ f = uvKernel fu Λ ⋆ f` is the convolution of the smoothing kernel (the inverse
Fourier transform of the compactly supported symbol `uvSymbol fu Λ = fu.f(2π‖·‖/Λ)`, hence a
Schwartz function) with the `L¹`-function `f`.  If moreover `f` has compact support, then
`uvSmear fu Λ f` decays faster than any polynomial (`Work.BoseBoxFock.uvSmear_rapidDecay`), and
consequently its periodisation along the lattice `ℓℤ³` is bounded, *uniformly* over the
displacement `w ∈ closedBall 0 (ℓ/2)`:

    `Σ_{d ∈ ℤ³} ‖uvSmear fu Λ f (q - w + ℓ • latVec d)‖ ≤ C`,

with `C` depending only on `fu`, `Λ`, `f`, `ℓ` and `q` (not on `w`).

## Route

* `uvSmear_rapidDecay fu hΛ hf hfs 4` gives `Cdec ≥ 0` with
  `‖uvSmear fu Λ f z‖ ≤ Cdec (1 + ‖z‖)^{-4}`, i.e. `(1 + ‖z‖)^4 ‖uvSmear fu Λ f z‖ ≤ Cdec`
  (`hdec` below).
* The elementary far/near comparison of the lattice weights (`inv_one_add_norm_le`, the uniform
  version — over `‖z‖ ≤ B` — of the computation inside
  `Work.BoseBoxFock.summable_shift_latVec`) gives, with
  `m = min 1 (ℓ/2) > 0` and `R = 2B/ℓ`,

      `(1 + ‖z + ℓ • latVec d‖)^{-4} ≤ (((m^4)⁻¹) + (1 + R)^4) (1 + ‖latVec d‖)^{-4}`;

  the comparison constant is written as a *sum* of the two case constants
  (`imageSumConst`), so that each branch needs only `le_add_of_nonneg_left/right`.
* `summable_one_add_norm_latVec_pow_inv (N := 4) le_rfl` is the unshifted p-series, so
  `Summable.of_nonneg_of_le` gives summability of the image sum and `Summable.tsum_le_tsum`
  the bound, with `tsum_mul_left` factoring out the constant.
* In the target one takes `B = ‖q‖ + ℓ/2`: for `w ∈ closedBall 0 (ℓ/2)` one has
  `‖q - w‖ ≤ ‖q‖ + ‖w‖ ≤ ‖q‖ + ℓ/2`.
-/

namespace Work.BoseBoxFock.PCFU

open scoped BigOperators

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ## 1. The uniform lattice comparison -/

/-- The comparison constant for the lattice image sum at lattice spacing `ℓ` and displacement
bound `B`: the sum of the "far" constant `((min 1 (ℓ/2))^4)⁻¹` and the "near" constant
`(1 + 2B/ℓ)^4`. -/
private noncomputable def imageSumConst (ℓ B : ℝ) : ℝ :=
  ((min 1 (ℓ / 2)) ^ 4)⁻¹ + (1 + 2 * B / ℓ) ^ 4

/-- `imageSumConst ℓ B` is non-negative for `0 < ℓ` and `0 ≤ B`. -/
private theorem imageSumConst_nonneg {ℓ B : ℝ} (hℓ : 0 < ℓ) (hB : 0 ≤ B) :
    0 ≤ imageSumConst ℓ B := by
  rw [imageSumConst]
  have hmpos : 0 < min 1 (ℓ / 2) := lt_min one_pos (by linarith)
  refine add_nonneg (inv_nonneg.mpr (pow_nonneg hmpos.le 4)) (pow_nonneg ?_ 4)
  have h2B : 0 ≤ 2 * B / ℓ := div_nonneg (by linarith) hℓ.le
  linarith

/-- **The uniform far/near comparison of the lattice weights.**  For `‖z‖ ≤ B` and every lattice
vector `d`,

`(1 + ‖z + ℓ • latVec d‖)^{-4} ≤ imageSumConst ℓ B · (1 + ‖latVec d‖)^{-4}`.

Far away (`‖latVec d‖ ≥ 2B/ℓ`) the reverse triangle inequality gives
`‖z + ℓ • latVec d‖ ≥ (ℓ/2)‖latVec d‖ ≥ ‖z‖`, so `1 + ‖z + ℓ • latVec d‖ ≥ m (1 + ‖latVec d‖)`
with `m = min 1 (ℓ/2)`, and the ratio is `≤ m^{-4}`.  Near the origin the left weight is `≤ 1`
while the right one is `≥ (1 + 2B/ℓ)^{-4}`, and the ratio is `≤ (1 + 2B/ℓ)^4`. -/
private theorem inv_one_add_norm_le {ℓ B : ℝ} (hℓ : 0 < ℓ) (hB : 0 ≤ B) :
    ∀ (z : E3), ‖z‖ ≤ B → ∀ d : Fin 3 → ℤ,
      ((1 + ‖z + ℓ • Work.BoseBoxFock.latVec d‖) ^ 4)⁻¹
        ≤ imageSumConst ℓ B * ((1 + ‖Work.BoseBoxFock.latVec d‖) ^ 4)⁻¹ := by
  rw [imageSumConst]
  set m : ℝ := min 1 (ℓ / 2) with hmdef
  set R : ℝ := 2 * B / ℓ with hRdef
  have hmpos : 0 < m := by rw [hmdef]; exact lt_min one_pos (by linarith)
  have hmle1 : m ≤ 1 := by rw [hmdef]; exact min_le_left _ _
  have hmlea : m ≤ ℓ / 2 := by rw [hmdef]; exact min_le_right _ _
  have hRnn : 0 ≤ R := by rw [hRdef]; positivity
  intro z hz d
  have hu4pos : (0 : ℝ) < (1 + ‖Work.BoseBoxFock.latVec d‖) ^ 4 := by positivity
  have hv1 : (1 : ℝ) ≤ 1 + ‖z + ℓ • Work.BoseBoxFock.latVec d‖ := by
    have := norm_nonneg (z + ℓ • Work.BoseBoxFock.latVec d); linarith
  have hvpos : (0 : ℝ) < 1 + ‖z + ℓ • Work.BoseBoxFock.latVec d‖ := lt_of_lt_of_le one_pos hv1
  rcases le_or_gt R ‖Work.BoseBoxFock.latVec d‖ with hcase | hcase
  · -- far region: `‖z + ℓ • latVec d‖ ≥ (ℓ/2)‖latVec d‖ ≥ ‖z‖`
    have hz2 : ‖z‖ ≤ ℓ * ‖Work.BoseBoxFock.latVec d‖ / 2 := by
      have h' : 2 * B ≤ ℓ * ‖Work.BoseBoxFock.latVec d‖ := by
        rw [hRdef, div_le_iff₀ hℓ] at hcase
        linarith
      linarith
    have htri : ℓ * ‖Work.BoseBoxFock.latVec d‖ - ‖z‖
        ≤ ‖z + ℓ • Work.BoseBoxFock.latVec d‖ := by
      have h := norm_sub_norm_le (ℓ • Work.BoseBoxFock.latVec d) (-z)
      rw [norm_neg] at h
      have heq : ℓ • Work.BoseBoxFock.latVec d - (-z) = z + ℓ • Work.BoseBoxFock.latVec d := by
        rw [sub_neg_eq_add, add_comm]
      rwa [heq, norm_smul, Real.norm_of_nonneg hℓ.le] at h
    have hvge : (ℓ / 2) * ‖Work.BoseBoxFock.latVec d‖ ≤ ‖z + ℓ • Work.BoseBoxFock.latVec d‖ := by
      linarith
    have hmu : m * (1 + ‖Work.BoseBoxFock.latVec d‖)
        ≤ 1 + ‖z + ℓ • Work.BoseBoxFock.latVec d‖ := by
      have h1 : m * (1 + ‖Work.BoseBoxFock.latVec d‖)
          ≤ 1 + (ℓ / 2) * ‖Work.BoseBoxFock.latVec d‖ := by
        nlinarith [hmle1, hmlea, norm_nonneg (Work.BoseBoxFock.latVec d)]
      linarith
    have hmupos : 0 < m * (1 + ‖Work.BoseBoxFock.latVec d‖) := by positivity
    have h1 : ((1 + ‖z + ℓ • Work.BoseBoxFock.latVec d‖) ^ 4)⁻¹
        ≤ ((m * (1 + ‖Work.BoseBoxFock.latVec d‖)) ^ 4)⁻¹ :=
      (inv_le_inv₀ (pow_pos hvpos 4) (pow_pos hmupos 4)).mpr (pow_le_pow_left₀ hmupos.le hmu 4)
    have hmain : ((1 + ‖z + ℓ • Work.BoseBoxFock.latVec d‖) ^ 4)⁻¹
        ≤ (m ^ 4)⁻¹ * ((1 + ‖Work.BoseBoxFock.latVec d‖) ^ 4)⁻¹ :=
      calc ((1 + ‖z + ℓ • Work.BoseBoxFock.latVec d‖) ^ 4)⁻¹
          ≤ ((m * (1 + ‖Work.BoseBoxFock.latVec d‖)) ^ 4)⁻¹ := h1
        _ = (m ^ 4)⁻¹ * ((1 + ‖Work.BoseBoxFock.latVec d‖) ^ 4)⁻¹ := by rw [mul_pow, mul_inv]
    exact le_trans hmain
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (by positivity))
        (inv_nonneg.mpr hu4pos.le))
  · -- near region: the left weight is `≤ 1`, the right one `≥ (1+R)^{-4}`
    have hR1 : (0 : ℝ) < 1 + R := by linarith
    have huR : 1 + ‖Work.BoseBoxFock.latVec d‖ ≤ 1 + R := by linarith
    have hvle1 : ((1 + ‖z + ℓ • Work.BoseBoxFock.latVec d‖) ^ 4)⁻¹ ≤ 1 :=
      inv_le_one_of_one_le₀ (one_le_pow₀ hv1)
    have h2 : (1 : ℝ) ≤ (1 + R) ^ 4 * ((1 + ‖Work.BoseBoxFock.latVec d‖) ^ 4)⁻¹ := by
      have hpow : (1 + ‖Work.BoseBoxFock.latVec d‖) ^ 4 ≤ (1 + R) ^ 4 :=
        pow_le_pow_left₀ (by positivity) huR 4
      have hle := (inv_le_inv₀ (pow_pos hR1 4) hu4pos).mpr hpow
      have hmul := mul_le_mul_of_nonneg_left hle (pow_nonneg hR1.le 4)
      rwa [mul_inv_cancel₀ (pow_ne_zero 4 (by linarith : (1 : ℝ) + R ≠ 0))] at hmul
    have hmain : ((1 + ‖z + ℓ • Work.BoseBoxFock.latVec d‖) ^ 4)⁻¹
        ≤ (1 + R) ^ 4 * ((1 + ‖Work.BoseBoxFock.latVec d‖) ^ 4)⁻¹ := le_trans hvle1 h2
    exact le_trans hmain
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (by positivity))
        (inv_nonneg.mpr hu4pos.le))

/-! ## 2. The uniform image-sum bound for a rapidly decaying function -/

/-- **The image sum of a `(1+‖·‖)^{-4}`-decaying function, bound uniform in the displacement.**
If `(1 + ‖z‖)^4 ‖Φ z‖ ≤ Cdec` for all `z` and `‖z‖ ≤ B`, then the lattice sum of `‖Φ‖` along the
shifted lattice `z + ℓℤ³` is bounded by `Cdec · imageSumConst ℓ B · Σ_d (1 + ‖latVec d‖)^{-4}`. -/
private theorem imageSum_le_of_decay {Φ : E3 → ℝ} {Cdec : ℝ} (hCdec0 : 0 ≤ Cdec)
    (hdec : ∀ z : E3, (1 + ‖z‖) ^ 4 * |Φ z| ≤ Cdec)
    {ℓ B : ℝ} (hℓ : 0 < ℓ) (hB : 0 ≤ B) {z : E3} (hz : ‖z‖ ≤ B) :
    (∑' d : Fin 3 → ℤ, ‖Φ (z + ℓ • Work.BoseBoxFock.latVec d)‖)
      ≤ Cdec * imageSumConst ℓ B
          * (∑' d : Fin 3 → ℤ, ((1 + ‖Work.BoseBoxFock.latVec d‖) ^ 4)⁻¹) := by
  classical
  -- the unshifted lattice weight is summable
  have hWsumm : Summable (fun d : Fin 3 → ℤ => ((1 + ‖Work.BoseBoxFock.latVec d‖) ^ 4)⁻¹) :=
    Work.BoseBoxFock.summable_one_add_norm_latVec_pow_inv (N := 4) le_rfl
  -- the pointwise comparison with the unshifted lattice weight
  have hpt : ∀ d : Fin 3 → ℤ, ‖Φ (z + ℓ • Work.BoseBoxFock.latVec d)‖
      ≤ Cdec * imageSumConst ℓ B * ((1 + ‖Work.BoseBoxFock.latVec d‖) ^ 4)⁻¹ := by
    intro d
    have hdec' : ‖Φ (z + ℓ • Work.BoseBoxFock.latVec d)‖
        ≤ Cdec * ((1 + ‖z + ℓ • Work.BoseBoxFock.latVec d‖) ^ 4)⁻¹ := by
      rw [Real.norm_eq_abs]
      rw [le_mul_inv_iff₀ (by positivity :
        (0 : ℝ) < (1 + ‖z + ℓ • Work.BoseBoxFock.latVec d‖) ^ 4)]
      rw [mul_comm]
      exact hdec _
    have hw := inv_one_add_norm_le hℓ hB z hz d
    calc ‖Φ (z + ℓ • Work.BoseBoxFock.latVec d)‖
        ≤ Cdec * ((1 + ‖z + ℓ • Work.BoseBoxFock.latVec d‖) ^ 4)⁻¹ := hdec'
      _ ≤ Cdec * (imageSumConst ℓ B * ((1 + ‖Work.BoseBoxFock.latVec d‖) ^ 4)⁻¹) :=
          mul_le_mul_of_nonneg_left hw hCdec0
      _ = Cdec * imageSumConst ℓ B * ((1 + ‖Work.BoseBoxFock.latVec d‖) ^ 4)⁻¹ := by ring
  have hsumm : Summable (fun d : Fin 3 → ℤ => ‖Φ (z + ℓ • Work.BoseBoxFock.latVec d)‖) :=
    Summable.of_nonneg_of_le (fun d => norm_nonneg _) hpt
      (hWsumm.mul_left (Cdec * imageSumConst ℓ B))
  calc ∑' d : Fin 3 → ℤ, ‖Φ (z + ℓ • Work.BoseBoxFock.latVec d)‖
      ≤ ∑' d : Fin 3 → ℤ, Cdec * imageSumConst ℓ B
          * ((1 + ‖Work.BoseBoxFock.latVec d‖) ^ 4)⁻¹ :=
        Summable.tsum_le_tsum hpt hsumm (hWsumm.mul_left (Cdec * imageSumConst ℓ B))
    _ = Cdec * imageSumConst ℓ B
          * ∑' d : Fin 3 → ℤ, ((1 + ‖Work.BoseBoxFock.latVec d‖) ^ 4)⁻¹ := tsum_mul_left

/-! ## 3. The target -/

theorem uvSmearImageSumBound {fu : Work.BoseBoxFix.LowCut} {Λ : ℝ} (hΛ : 0 < Λ)
    {f : EuclideanSpace ℝ (Fin 3) → ℝ} (hf : MeasureTheory.Integrable f)
    (hfs : HasCompactSupport f) {ℓ : ℝ} (hℓ : 0 < ℓ)
    (q : EuclideanSpace ℝ (Fin 3)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) (ℓ / 2),
      (∑' d : Fin 3 → ℤ, ‖Work.BoseBoxFock.uvSmear fu Λ f
        (q - w + ℓ • Work.BoseBoxFock.latVec d)‖) ≤ C := by
  classical
  -- the rapid decay of the smoothed weight, in the `(1+‖z‖)^4 ‖·‖ ≤ C` form
  obtain ⟨Cdec, hCdec0, hCdec⟩ := uvSmear_rapidDecay fu hΛ hf hfs 4
  have hdec : ∀ z : E3, (1 + ‖z‖) ^ 4 * |Work.BoseBoxFock.uvSmear fu Λ f z| ≤ Cdec := by
    intro z
    have h := hCdec z
    rw [zpow_neg, zpow_natCast] at h
    have hpos : (0 : ℝ) < (1 + ‖z‖) ^ 4 := by positivity
    calc (1 + ‖z‖) ^ 4 * |Work.BoseBoxFock.uvSmear fu Λ f z|
        ≤ (1 + ‖z‖) ^ 4 * (Cdec * ((1 + ‖z‖) ^ 4)⁻¹) :=
          mul_le_mul_of_nonneg_left h hpos.le
      _ = Cdec := by
          rw [show (1 + ‖z‖) ^ 4 * (Cdec * ((1 + ‖z‖) ^ 4)⁻¹)
                = Cdec * ((1 + ‖z‖) ^ 4 * ((1 + ‖z‖) ^ 4)⁻¹) by ring]
          rw [mul_inv_cancel₀ (ne_of_gt hpos), mul_one]
  refine ⟨Cdec * imageSumConst ℓ (‖q‖ + ℓ / 2)
      * (∑' d : Fin 3 → ℤ, ((1 + ‖Work.BoseBoxFock.latVec d‖) ^ 4)⁻¹), ?_, ?_⟩
  · refine mul_nonneg (mul_nonneg hCdec0 ?_) ?_
    · exact imageSumConst_nonneg hℓ (by positivity)
    · exact tsum_nonneg (fun d => inv_nonneg.mpr (pow_nonneg (by positivity) 4))
  · intro w hw
    have hw' : ‖w‖ ≤ ℓ / 2 := by
      rw [Metric.mem_closedBall, dist_zero_right] at hw
      exact hw
    have hzB : ‖q - w‖ ≤ ‖q‖ + ℓ / 2 := by
      have h1 : ‖q - w‖ ≤ ‖q‖ + ‖w‖ := norm_sub_le _ _
      linarith
    exact imageSum_le_of_decay (ℓ := ℓ) (B := ‖q‖ + ℓ / 2) (z := q - w)
      hCdec0 hdec hℓ (by positivity) hzB

end Work.BoseBoxFock.PCFU
