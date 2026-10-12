import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseBoxFock.PCFU.lowKer_decay
import Submission.Work.BoseBoxFock.summable_shift_latVec
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock.PCFU

/-! **The lattice image sum of the low-momentum kernel is uniformly bounded on the box.**

`lowKer fc κ z = (2π)^{-3}∫_p f(‖p‖/κ)cos⟪p,z⟫` is the position-space kernel of FS's
low-momentum multiplier: it is continuous (`lowKer_regular`) and decays faster than any polynomial
(`lowKer_decay`).  Hence its periodisation along the lattice `ℓℤ³` is a *bounded* function on every
bounded set; here on the box `acube ℓ` carrying the `j`-th coordinate `x j` of the configuration
`x` (the bound is allowed to depend on `x j`, since `C` is quantified after `x`).

Route (every ingredient is on disk):
* `lowKer_decay fc hκ 2` gives `Cdec` with `0 ≤ Cdec` and
  `∀ z, (1 + ‖z‖)^4 * ‖lowKer fc κ z‖ ≤ Cdec`, i.e. `‖lowKer fc κ z‖ ≤ Cdec (1+‖z‖)^{-4}`;
* for `u ∈ acube ℓ` (`Submission.BoseGases.mem_acube_iff`) one has `‖u - x j‖ ≤ B := ‖x j‖ + ℓ`;
* the elementary far/near comparison (the computation inside
  `Work.BoseBoxFock.summable_shift_latVec`, made *uniform* over `‖z‖ ≤ B`, with
  `m := min 1 (ℓ/2) > 0` and `K := max ((m^4)⁻¹) ((1 + 2B/ℓ)^4)`) gives
  `(1 + ‖u - x j + ℓ • latVec d‖)^{-4} ≤ K (1 + ‖latVec d‖)^{-4}` for every `d`;
* `Work.BoseBoxFock.summable_one_add_norm_latVec_pow_inv (N := 4) le_rfl` gives summability of
  `d ↦ (1 + ‖latVec d‖)^{-4}`, so `Summable` of the comparison majorant and of the image sum of
  `‖lowKer‖` follow from `Summable.of_nonneg_of_le`, and `Summable.tsum_le_tsum` gives the bound
  `Cdec · K · ∑' d, (1 + ‖latVec d‖)^{-4}`.

Suggested discharge: return `C := Cdec * K * ∑' d, (1 + ‖latVec d‖)^{-4}` (nonnegativity from
`mul_nonneg` and `tsum_nonneg`).

**Implementation note.**  The comparison constant is realised as the *sum*
`kerImageConst ℓ B = ((min 1 (ℓ/2))^4)⁻¹ + (1 + 2B/ℓ)^4` of the two case constants (rather than
their maximum), because each case constant is then a summand of the stored constant and the two
branches need no comparison between them. -/

open scoped BigOperators

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ## Auxiliary geometric and arithmetic facts -/

/-- The elementary cube bound: `‖z‖ ≤ ℓ` for `z ∈ acube ℓ` (the centred cube of side `ℓ` has
circumradius `√3 ℓ/2 ≤ ℓ`). -/
private lemma norm_le_of_mem_acube {ℓ : ℝ} (hℓ : 0 ≤ ℓ) {z : E3}
    (hz : z ∈ Submission.BoseGases.acube ℓ) : ‖z‖ ≤ ℓ := by
  have hcoord : ∀ m : Fin 3, z m ∈ Set.Icc (-ℓ / 2) (ℓ / 2) :=
    (Submission.BoseGases.mem_acube_iff ℓ z).mp hz
  have h1 : ∀ m : Fin 3, (z m) ^ 2 ≤ (ℓ / 2) ^ 2 := by
    intro m
    have hm : |z m| ≤ ℓ / 2 := by
      rw [abs_le]
      exact ⟨by linarith [(hcoord m).1], (hcoord m).2⟩
    nlinarith [abs_nonneg (z m), sq_abs (z m)]
  have hsq : ∑ m : Fin 3, (z m) ^ 2 ≤ ℓ ^ 2 := by
    calc ∑ m : Fin 3, (z m) ^ 2 ≤ ∑ _m : Fin 3, (ℓ / 2) ^ 2 :=
          Finset.sum_le_sum (fun m _ => h1 m)
      _ = 3 * (ℓ / 2) ^ 2 := by simp
      _ ≤ ℓ ^ 2 := by nlinarith
  have hnormsq : ‖z‖ ^ 2 = ∑ m : Fin 3, (z m) ^ 2 := by
    rw [EuclideanSpace.norm_eq]
    simp [Real.sq_sqrt (Finset.sum_nonneg (fun m _ => sq_nonneg (z m))), Real.norm_eq_abs]
  nlinarith [norm_nonneg z, hℓ]

/-- The comparison constant for the lattice image sum at box size `ℓ` and displacement bound `B`:
the sum of the "far" constant `((min 1 (ℓ/2))^4)⁻¹` and the "near" constant `(1 + 2B/ℓ)^4`. -/
private noncomputable def kerImageConst (ℓ B : ℝ) : ℝ :=
  ((min 1 (ℓ / 2)) ^ 4)⁻¹ + (1 + 2 * B / ℓ) ^ 4

/-- **The uniform far/near comparison of the lattice weights.**  For `‖z‖ ≤ B` and every lattice
vector `d`,

`(1 + ‖z + ℓ • latVec d‖)^{-4} ≤ kerImageConst ℓ B · (1 + ‖latVec d‖)^{-4}`.

Far away (`‖latVec d‖ ≥ 2B/ℓ`) the reverse triangle inequality gives
`‖z + ℓ • latVec d‖ ≥ (ℓ/2)‖latVec d‖`, so `1 + ‖z + ℓ • latVec d‖ ≥ m (1 + ‖latVec d‖)` with
`m = min 1 (ℓ/2)`: ratio `≤ m^{-4}`.  Near the origin the left weight is `≤ 1` while the right one
is `≥ (1 + 2B/ℓ)^{-4}`: ratio `≤ (1 + 2B/ℓ)^4`. -/
private theorem inv_one_add_norm_le {ℓ B : ℝ} (hℓ : 0 < ℓ) (hB : 0 ≤ B) :
    ∀ (z : E3), ‖z‖ ≤ B → ∀ d : Fin 3 → ℤ,
      ((1 + ‖z + ℓ • Work.BoseBoxFock.latVec d‖) ^ 4)⁻¹
        ≤ kerImageConst ℓ B * ((1 + ‖Work.BoseBoxFock.latVec d‖) ^ 4)⁻¹ := by
  rw [kerImageConst]
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
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (by positivity)) (inv_nonneg.mpr hu4pos.le))
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
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (by positivity)) (inv_nonneg.mpr hu4pos.le))

/-! ## The main bound -/

theorem lowKer_imageSum_bound (fc : Work.BoseBoxFix.LowCut) {κ ℓ : ℝ} (hκ : 0 < κ) (hℓ : 0 < ℓ)
    {n : ℕ} (j : Fin n) (x : Submission.BoseGases.X n) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u ∈ Submission.BoseGases.acube ℓ,
      ∑' d : Fin 3 → ℤ, ‖Work.BoseBoxFock.PCFU.lowKer fc κ
        (u - x j + ℓ • Work.BoseBoxFock.latVec d)‖ ≤ C := by
  classical
  obtain ⟨Cdec, hCdec0, hCdec⟩ := lowKer_decay fc hκ 2
  have hCdec4 : ∀ z : E3, (1 + ‖z‖) ^ 4 * ‖lowKer fc κ z‖ ≤ Cdec := by
    intro z
    have h := hCdec z
    norm_num at h
    exact h
  -- the unshifted lattice weight is summable
  have hWsumm : Summable (fun d : Fin 3 → ℤ => ((1 + ‖Work.BoseBoxFock.latVec d‖) ^ 4)⁻¹) :=
    Work.BoseBoxFock.summable_one_add_norm_latVec_pow_inv (N := 4) le_rfl
  refine ⟨Cdec * kerImageConst ℓ (‖x j‖ + ℓ)
      * ∑' d : Fin 3 → ℤ, ((1 + ‖Work.BoseBoxFock.latVec d‖) ^ 4)⁻¹, ?_, ?_⟩
  · refine mul_nonneg (mul_nonneg hCdec0 ?_) ?_
    · rw [kerImageConst]; positivity
    · exact tsum_nonneg (fun d => inv_nonneg.mpr (pow_nonneg (by positivity) 4))
  · intro u hu
    -- the displacement from the box is bounded by `B = ‖x j‖ + ℓ`
    have hzB : ‖u - x j‖ ≤ ‖x j‖ + ℓ := by
      have h1 : ‖u - x j‖ ≤ ‖u‖ + ‖x j‖ := norm_sub_le _ _
      have h2 : ‖u‖ ≤ ℓ := norm_le_of_mem_acube hℓ.le hu
      linarith
    -- the pointwise comparison with the unshifted lattice weight
    have hpt : ∀ d : Fin 3 → ℤ, ‖lowKer fc κ (u - x j + ℓ • Work.BoseBoxFock.latVec d)‖
        ≤ Cdec * kerImageConst ℓ (‖x j‖ + ℓ)
            * ((1 + ‖Work.BoseBoxFock.latVec d‖) ^ 4)⁻¹ := by
      intro d
      have hdec : ‖lowKer fc κ (u - x j + ℓ • Work.BoseBoxFock.latVec d)‖
          ≤ Cdec * ((1 + ‖u - x j + ℓ • Work.BoseBoxFock.latVec d‖) ^ 4)⁻¹ := by
        rw [le_mul_inv_iff₀ (by positivity :
          (0 : ℝ) < (1 + ‖u - x j + ℓ • Work.BoseBoxFock.latVec d‖) ^ 4)]
        rw [mul_comm]
        exact hCdec4 _
      have hw := inv_one_add_norm_le hℓ (by positivity : (0 : ℝ) ≤ ‖x j‖ + ℓ) (u - x j) hzB d
      calc ‖lowKer fc κ (u - x j + ℓ • Work.BoseBoxFock.latVec d)‖
          ≤ Cdec * ((1 + ‖u - x j + ℓ • Work.BoseBoxFock.latVec d‖) ^ 4)⁻¹ := hdec
        _ ≤ Cdec * (kerImageConst ℓ (‖x j‖ + ℓ)
              * ((1 + ‖Work.BoseBoxFock.latVec d‖) ^ 4)⁻¹) :=
              mul_le_mul_of_nonneg_left hw hCdec0
        _ = Cdec * kerImageConst ℓ (‖x j‖ + ℓ)
              * ((1 + ‖Work.BoseBoxFock.latVec d‖) ^ 4)⁻¹ := by ring
    have hsumm : Summable
        (fun d : Fin 3 → ℤ => ‖lowKer fc κ (u - x j + ℓ • Work.BoseBoxFock.latVec d)‖) :=
      Summable.of_nonneg_of_le (fun d => norm_nonneg _) hpt
        (hWsumm.mul_left (Cdec * kerImageConst ℓ (‖x j‖ + ℓ)))
    calc ∑' d : Fin 3 → ℤ, ‖lowKer fc κ (u - x j + ℓ • Work.BoseBoxFock.latVec d)‖
        ≤ ∑' d : Fin 3 → ℤ, Cdec * kerImageConst ℓ (‖x j‖ + ℓ)
            * ((1 + ‖Work.BoseBoxFock.latVec d‖) ^ 4)⁻¹ :=
          Summable.tsum_le_tsum hpt hsumm
            (hWsumm.mul_left (Cdec * kerImageConst ℓ (‖x j‖ + ℓ)))
      _ = Cdec * kerImageConst ℓ (‖x j‖ + ℓ)
            * ∑' d : Fin 3 → ℤ, ((1 + ‖Work.BoseBoxFock.latVec d‖) ^ 4)⁻¹ := tsum_mul_left

end Work.BoseBoxFock.PCFU
