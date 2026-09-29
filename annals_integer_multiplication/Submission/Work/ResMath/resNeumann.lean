import Mathlib
import Submission.Work.ResMath.defs

/-! ### Neumann series for `N = 1 + E` (`Work.ResMath.resNeumann`)

`Nmat = 1 + Emat`, so if `Emat` has operator norm `< 1` then `Nmat` is invertible with
`Nmat⁻¹ = ∑ₘ (-Emat)ᵐ`, and the Neumann series converges to it.  Consequently
`Jmat = Nmat⁻¹` has norm `≤ 50/29` and `(1/2) • Jmat` has norm `≤ 7/8`.

The matrix norm used here is the `L^∞` operator norm
`‖A‖ = sup_i ∑_j ‖A_{ij}‖ = sup_{‖v‖ ≤ 1} ‖A.mulVec v‖`, which is a genuine normed ring
structure on square matrices (Mathlib's `Matrix.Norms.Operator`). -/
open scoped Matrix.Norms.Operator

namespace Work.ResMath

theorem resNeumann (s t α : ℕ) (hs : 2 ≤ s)
    (hE : ∀ u : Fin s → ℂ, ‖(HvdH.Emat s t α).mulVec u‖ ≤ 21 / 50 * ‖u‖) :
    (HvdH.Nmat s t α * HvdH.Jmat s t α = 1 ∧ HvdH.Jmat s t α * HvdH.Nmat s t α = 1) ∧
    (∀ u : Fin s → ℂ, HasSum (fun m : ℕ => ((-HvdH.Emat s t α) ^ m).mulVec u) ((HvdH.Jmat s t α).mulVec u)) ∧
    (∀ u : Fin s → ℂ, ‖((1 / 2 : ℂ) • HvdH.Jmat s t α).mulVec u‖ ≤ 7 / 8 * ‖u‖) := by
  have hne : Nonempty (Fin s) := ⟨⟨0, by omega⟩⟩
  -- `Nmat = 1 + Emat` has operator norm at most `21/50`
  have hEnorm : ‖HvdH.Emat s t α‖ ≤ 21 / 50 := by
    rw [Matrix.linfty_opNorm_eq_opNorm (HvdH.Emat s t α)]
    apply ContinuousLinearMap.opNorm_le_bound
    · norm_num
    · intro u
      simpa [Matrix.mulVecLin_apply] using hE u
  have hM : ‖(-(HvdH.Emat s t α))‖ < 1 := by
    rw [norm_neg]
    linarith
  have hsub : (1 : Matrix (Fin s) (Fin s) ℂ) - (-(HvdH.Emat s t α)) = HvdH.Nmat s t α := by
    rw [sub_neg_eq_add]
    simp only [HvdH.Emat]
    abel
  -- `Nmat` is a unit, hence its determinant is a unit
  have hAunit : IsUnit (HvdH.Nmat s t α) := by
    rw [← hsub]
    exact IsUnit.one_sub_of_norm_lt_one hM
  have hAdet : IsUnit (HvdH.Nmat s t α).det :=
    (Matrix.isUnit_iff_isUnit_det (HvdH.Nmat s t α)).mp hAunit
  have h1 : HvdH.Nmat s t α * (HvdH.Nmat s t α)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hAdet
  have h2 : (HvdH.Nmat s t α)⁻¹ * HvdH.Nmat s t α = 1 := Matrix.nonsing_inv_mul _ hAdet
  -- the Neumann series is summable, and is the inverse of `Nmat`
  have hsum : Summable (fun n : ℕ => (-(HvdH.Emat s t α)) ^ n) :=
    summable_geometric_of_norm_lt_one hM
  have hPmul : HvdH.Nmat s t α * (∑' n : ℕ, (-(HvdH.Emat s t α)) ^ n) = 1 := by
    have h := mul_neg_geom_series (-(HvdH.Emat s t α)) hM
    rwa [hsub] at h
  have hPmul' : (∑' n : ℕ, (-(HvdH.Emat s t α)) ^ n) * HvdH.Nmat s t α = 1 := by
    have h := geom_series_mul_neg (-(HvdH.Emat s t α)) hM
    rwa [hsub] at h
  have hPi : HvdH.Jmat s t α = ∑' n : ℕ, (-(HvdH.Emat s t α)) ^ n := by
    change (HvdH.Nmat s t α)⁻¹ = _
    calc (HvdH.Nmat s t α)⁻¹
        = 1 * (HvdH.Nmat s t α)⁻¹ := (one_mul _).symm
      _ = ((∑' n : ℕ, (-(HvdH.Emat s t α)) ^ n) * HvdH.Nmat s t α)
            * (HvdH.Nmat s t α)⁻¹ := by rw [hPmul']
      _ = (∑' n : ℕ, (-(HvdH.Emat s t α)) ^ n)
            * (HvdH.Nmat s t α * (HvdH.Nmat s t α)⁻¹) := by rw [Matrix.mul_assoc]
      _ = (∑' n : ℕ, (-(HvdH.Emat s t α)) ^ n) * 1 := by rw [h1]
      _ = (∑' n : ℕ, (-(HvdH.Emat s t α)) ^ n) := mul_one _
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · show HvdH.Nmat s t α * (HvdH.Nmat s t α)⁻¹ = 1
    exact h1
  · show (HvdH.Nmat s t α)⁻¹ * HvdH.Nmat s t α = 1
    exact h2
  · -- the Neumann series applied to `u` converges to `Jmat.mulVec u`
    intro u
    have hPsum : HasSum (fun m : ℕ => (-(HvdH.Emat s t α)) ^ m) (HvdH.Jmat s t α) := by
      rw [hPi]
      exact hsum.hasSum
    -- `M ↦ M.mulVec u` is a continuous linear map
    let Φlin : Matrix (Fin s) (Fin s) ℂ →ₗ[ℂ] (Fin s → ℂ) :=
      { toFun := fun M => M.mulVec u
        map_add' := fun M N => by simp [Matrix.add_mulVec]
        map_smul' := fun c M => by simp [Matrix.smul_mulVec] }
    let Φ : Matrix (Fin s) (Fin s) ℂ →L[ℂ] (Fin s → ℂ) :=
      { toLinearMap := Φlin
        cont := LinearMap.continuous_of_finiteDimensional Φlin }
    exact ContinuousLinearMap.hasSum Φ hPsum
  · -- norm estimate for `(1/2) • Jmat`
    intro u
    have hnorm1 : ‖(1 : Matrix (Fin s) (Fin s) ℂ)‖ = 1 := by simp
    have hPn : ‖HvdH.Jmat s t α‖ ≤ 50 / 29 := by
      rw [hPi]
      refine (tsum_geometric_le_of_norm_lt_one (-(HvdH.Emat s t α)) hM).trans ?_
      have hle : (29 : ℝ) / 50 ≤ 1 - ‖HvdH.Emat s t α‖ := by linarith
      have hinv : (1 - ‖HvdH.Emat s t α‖)⁻¹ ≤ (29 / 50 : ℝ)⁻¹ :=
        (inv_le_inv₀ (by linarith) (by norm_num)).mpr hle
      calc ‖(1 : Matrix (Fin s) (Fin s) ℂ)‖ - 1 + (1 - ‖(-(HvdH.Emat s t α))‖)⁻¹
          = (1 - ‖HvdH.Emat s t α‖)⁻¹ := by rw [hnorm1, norm_neg]; ring
        _ ≤ (29 / 50 : ℝ)⁻¹ := hinv
        _ = 50 / 29 := by norm_num
    calc ‖((1 / 2 : ℂ) • HvdH.Jmat s t α).mulVec u‖
        = ‖(1 / 2 : ℂ)‖ * ‖(HvdH.Jmat s t α).mulVec u‖ := by
          rw [Matrix.smul_mulVec, norm_smul]
      _ ≤ (1 / 2) * (‖HvdH.Jmat s t α‖ * ‖u‖) := by
          rw [show ‖(1 / 2 : ℂ)‖ = (1 / 2 : ℝ) by norm_num]
          gcongr
          exact Matrix.linfty_opNorm_mulVec _ u
      _ ≤ 7 / 8 * ‖u‖ := by nlinarith [hPn, norm_nonneg u]

end Work.ResMath
