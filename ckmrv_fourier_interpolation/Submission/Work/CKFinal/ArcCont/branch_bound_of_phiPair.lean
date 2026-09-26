import Mathlib
import Submission.Work.Asymptotics.arcT_graze_vanish
import Submission.Work.Asymptotics.arcT_branch_bound

/-!
# Boundedness of the interpolation kernel near a `phi`-annihilated branch point

Let `δ ∈ SL(2,ℤ)` satisfy the CKMRV pair condition (3.12)
`φ₊(δ) + φ₋(δ) = 0`, let `t₀ > 0`, `t₀ ≠ 1`, and put `z₀ = i t₀`. Then the interpolation
kernel `K^{(d)}` is bounded on a Euclidean neighbourhood of the branch point
`(δ • z₀, z₀)`: the pole divisor `j τ = j z` of `K^{(d)}` passes through this point along the
branch `z = δ⁻¹ • τ`, and that pole is removable because the cleared kernel vanishes on it
(`Work.Asymptotics.KfunClear_vanish_uncond`, which is precisely the pair condition (3.12)).

The proof is the same one-zero maximum-modulus argument as
`Work.Asymptotics.graze_branch_bound` (itself the grazing-branch analogue of
`Work.Asymptotics.Graze.key_bound_arc'`): the one-zero bound
`Work.Asymptotics.KaxisMid.KbcAux2.one_zero_apply` together with the lower bound for
`j τ - j z` at the non-elliptic contour point `z₀`
(`Work.Asymptotics.MiddleRange.exists_diffQuotient_lower_general`).  The only input that
depended on `δ` being a grazing element was the vanishing of the cleared kernel along the
branch, which for us is supplied directly by the pair condition.
-/

set_option maxHeartbeats 1600000
set_option linter.unusedSimpArgs false

noncomputable section

open UpperHalfPlane ModularForm ModularGroup Matrix
open scoped MatrixGroups Topology
open Work.Kernels
open Work.Asymptotics.KaxisMid

namespace Work.Asymptotics

/-- **Boundedness of the kernel near a removable-pole branch point.**

If the cleared kernel vanishes along the whole branch `z = δ⁻¹ • τ` (equivalently
`KfunClear ℓ d (δ • z) z = 0` for every `z`), then `K^{(d)}` is bounded on a Euclidean
neighbourhood of `(δ • z₀, z₀)`, `z₀ = i t₀`, for `t₀ > 0`, `t₀ ≠ 1`. -/
theorem branch_bound_of_vanish (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (δ : SL(2, ℤ))
    (hv : ∀ z : ℍ, Work.Kernels.KfunClear ℓ d (δ • z) z = 0)
    {t₀ : ℝ} (ht₀ : 0 < t₀) (hne : t₀ ≠ 1) :
    ∃ ρ C : ℝ, 0 < ρ ∧ 0 ≤ C ∧ ∀ (τ z : ℍ),
      ‖(τ:ℂ) - ((δ • Work.Kernels.imagAxis t₀ ht₀ : ℍ) : ℂ)‖ < ρ →
      ‖(z:ℂ) - ((Work.Kernels.imagAxis t₀ ht₀ : ℍ) : ℂ)‖ < ρ →
      ‖Work.Kernels.Kfun ℓ d τ z‖ ≤ C := by
  set z₀ : ℍ := Work.Kernels.imagAxis t₀ ht₀ with hz₀
  set τ₀ : ℍ := δ • z₀ with hτ₀
  have hZτ₀ : (δ⁻¹) • τ₀ = z₀ := by
    rw [hτ₀, ← mul_smul, inv_mul_cancel, one_smul]
  have hZzero : ∀ τ : ℍ, Work.Kernels.KfunClear ℓ d τ ((δ⁻¹) • τ) = 0 := by
    intro τ
    have h := hv ((δ⁻¹) • τ)
    rw [← mul_smul, mul_inv_cancel, one_smul] at h
    exact h
  have hZj : ∀ τ : ℍ, Work.Kernels.jInvariantFun ((δ⁻¹) • τ) = Work.Kernels.jInvariantFun τ :=
    fun τ => Work.Asymptotics.jInvariantFun_smul_of_slash δ⁻¹ τ
  obtain ⟨M, hMpos, hMbd⟩ := KaxisMid.KbcAux2.exists_bound_KfunClear_of_balls ℓ d hd τ₀ z₀
    (R₁ := τ₀.im / 2) (R₂ := z₀.im / 2) (by linarith [τ₀.im_pos]) (by linarith [z₀.im_pos])
  obtain ⟨ρ₀, hρ₀, c₀, hc₀, hlow⟩ :=
    Work.Asymptotics.MiddleRange.exists_diffQuotient_lower_general (t₀ := t₀) ht₀ hne
  obtain ⟨ρdτ, δ₁, hρdτ, hδ₁, hbδ₁⟩ := KaxisMid.AtIAux.exists_DeltaFun_lower τ₀
  obtain ⟨ρdz, δ₂, hρdz, hδ₂, hbδ₂⟩ := KaxisMid.AtIAux.exists_DeltaFun_lower z₀
  obtain ⟨C₀, hC₀pos, hC₀b⟩ := KaxisMid.exists_bound_Kfun_of_coincidence ℓ d hd
    (isCompact_closedBall τ₀ 1) (isCompact_closedBall z₀ 1)
  obtain ⟨δZ, cZ, hδZ, hcZ, hZlip⟩ := exists_lipschitz_smul' δ⁻¹ τ₀
  set ρ₁ : ℝ := min δZ (min (ρ₀ / 2) (z₀.im / 8)) with hρ₁
  set ρ₂ : ℝ := min (ρ₀ / (2 * cZ)) (z₀.im / (8 * cZ)) with hρ₂
  set ρ₃ : ℝ := min (min (τ₀.im / 2) ρdτ) (min ρdz (min ρ₀ (z₀.im / 4))) with hρ₃
  set ρ : ℝ := min ρ₁ (min ρ₂ ρ₃) with hρ
  have hρ₁pos : 0 < ρ₁ := lt_min hδZ (lt_min (by positivity) (by positivity))
  have hρ₂pos : 0 < ρ₂ := lt_min (by positivity) (by positivity)
  have hρ₃pos : 0 < ρ₃ :=
    lt_min (lt_min (by linarith [τ₀.im_pos]) hρdτ) (lt_min hρdz (lt_min hρ₀ (by positivity)))
  have hρpos : 0 < ρ := lt_min hρ₁pos (lt_min hρ₂pos hρ₃pos)
  have hρδZ : ρ ≤ δZ := le_trans (min_le_left _ _) (min_le_left _ _)
  have hρρ2 : ρ ≤ ρ₀ / 2 := le_trans (min_le_left _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  have hρz8 : ρ ≤ z₀.im / 8 := le_trans (min_le_left _ _) (le_trans (min_le_right _ _) (min_le_right _ _))
  have hρcρ : ρ ≤ ρ₀ / (2 * cZ) := le_trans (min_le_right _ _) (le_trans (min_le_left _ _) (min_le_left _ _))
  have hρc8 : ρ ≤ z₀.im / (8 * cZ) := le_trans (min_le_right _ _) (le_trans (min_le_left _ _) (min_le_right _ _))
  have hρτ2 : ρ ≤ τ₀.im / 2 := le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (le_trans (min_le_left _ _) (min_le_left _ _)))
  have hρdτ' : ρ ≤ ρdτ := le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (le_trans (min_le_left _ _) (min_le_right _ _)))
  have hρdz' : ρ ≤ ρdz := le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _)))
  have hρρ0' : ρ ≤ ρ₀ := le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))))
  have hρz4' : ρ ≤ z₀.im / 4 := le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _))))
  refine ⟨ρ, max C₀ ((4 * M / z₀.im) / c₀ / (δ₁ * δ₂ ^ (if d = 8 then 1 else 2))),
    hρpos, le_trans hC₀pos.le (le_max_left _ _), ?_⟩
  intro τ z hτ hz
  have hτδZ : ‖(τ:ℂ) - (τ₀:ℂ)‖ < δZ := lt_of_lt_of_le hτ hρδZ
  have hτρ2 : ‖(τ:ℂ) - (τ₀:ℂ)‖ < ρ₀ / 2 := lt_of_lt_of_le hτ hρρ2
  have hτρcρ : ‖(τ:ℂ) - (τ₀:ℂ)‖ < ρ₀ / (2 * cZ) := lt_of_lt_of_le hτ hρcρ
  have hτρc8 : ‖(τ:ℂ) - (τ₀:ℂ)‖ < z₀.im / (8 * cZ) := lt_of_lt_of_le hτ hρc8
  have hττ2 : ‖(τ:ℂ) - (τ₀:ℂ)‖ < τ₀.im / 2 := lt_of_lt_of_le hτ hρτ2
  have hτdτ : ‖(τ:ℂ) - (τ₀:ℂ)‖ < ρdτ := lt_of_lt_of_le hτ hρdτ'
  have hzρ2 : ‖(z:ℂ) - (z₀:ℂ)‖ < ρ₀ / 2 := lt_of_lt_of_le hz hρρ2
  have hzz8 : ‖(z:ℂ) - (z₀:ℂ)‖ < z₀.im / 8 := lt_of_lt_of_le hz hρz8
  have hzz4 : ‖(z:ℂ) - (z₀:ℂ)‖ < z₀.im / 4 := lt_of_lt_of_le hz hρz4'
  have hzdz : ‖(z:ℂ) - (z₀:ℂ)‖ < ρdz := lt_of_lt_of_le hz hρdz'
  have hzρ : ‖(z:ℂ) - (z₀:ℂ)‖ < ρ₀ := lt_of_lt_of_le hz hρρ0'
  -- the branch point is close to `z₀`
  have hZclose : ‖(((δ⁻¹) • τ : ℍ) : ℂ) - (z₀ : ℂ)‖ ≤ cZ * ‖(τ:ℂ) - (τ₀ : ℂ)‖ := by
    have h := hZlip τ hτδZ
    rwa [hZτ₀] at h
  have hZρ : ‖(((δ⁻¹) • τ : ℍ) : ℂ) - (z₀ : ℂ)‖ < ρ₀ := by
    have h2 : cZ * ‖(τ:ℂ) - (τ₀ : ℂ)‖ < ρ₀ / 2 := by
      calc cZ * ‖(τ:ℂ) - (τ₀ : ℂ)‖ < cZ * (ρ₀ / (2 * cZ)) :=
            mul_lt_mul_of_pos_left hτρcρ hcZ
        _ = ρ₀ / 2 := by field_simp
    have h3 := lt_of_le_of_lt hZclose h2
    linarith [hρ₀]
  have hZ4 : ‖(((δ⁻¹) • τ : ℍ) : ℂ) - (z₀ : ℂ)‖ < z₀.im / 2 / 2 := by
    have h2 : cZ * ‖(τ:ℂ) - (τ₀ : ℂ)‖ < z₀.im / 8 := by
      calc cZ * ‖(τ:ℂ) - (τ₀ : ℂ)‖ < cZ * (z₀.im / (8 * cZ)) :=
            mul_lt_mul_of_pos_left hτρc8 hcZ
        _ = z₀.im / 8 := by field_simp
    have h3 := lt_of_le_of_lt hZclose h2
    linarith [z₀.im_pos]
  have hz4 : ‖(z:ℂ) - (z₀ : ℂ)‖ < z₀.im / 2 / 2 := by linarith [z₀.im_pos, hzz4]
  -- the one-zero bound
  have hbd : ∀ w : ℍ, ‖(w : ℂ) - (z₀ : ℂ)‖ ≤ z₀.im / 2 → ‖KfunClear ℓ d τ w‖ ≤ M :=
    fun w hw => hMbd τ w (le_of_lt hττ2) hw
  have hone := KaxisMid.KbcAux2.one_zero_apply (f := fun w : ℍ => KfunClear ℓ d τ w)
    (KaxisMid.KbcAux2.mdifferentiable_KfunClear_snd ℓ d hd τ) (c := z₀) (r := z₀.im / 2) (M := M)
    (by linarith [z₀.im_pos]) (by linarith [z₀.im_pos]) hbd
    (w₀ := (δ⁻¹) • τ) hZ4 (hZzero τ)
  have hnum : ‖KfunClear ℓ d τ z‖ ≤ (4 * M / z₀.im) * ‖(z:ℂ) - (((δ⁻¹) • τ : ℍ) : ℂ)‖ := by
    have h := hone z hz4
    have h2 : 2 * M / (z₀.im / 2) = 4 * M / z₀.im := by
      rw [div_div_eq_mul_div]; ring
    rwa [h2] at h
  -- the lower bound for the `j`-difference
  have hjlow : c₀ * ‖(z:ℂ) - (((δ⁻¹) • τ : ℍ) : ℂ)‖
      ≤ ‖Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z‖ := by
    have h := hlow ((δ⁻¹) • τ) z hZρ hzρ
    rw [norm_sub_rev] at h
    rwa [hZj τ] at h
  by_cases hJ : Work.Kernels.jInvariantFun τ = Work.Kernels.jInvariantFun z
  · refine le_trans (hC₀b τ z ?_ ?_ hJ) (le_max_left _ _)
    · exact KaxisMid.AtIAux.dist_le_one_of_norm_lt (c := τ₀) (ρ := τ₀.im / 2) (le_refl _) hττ2
    · exact KaxisMid.AtIAux.dist_le_one_of_norm_lt (c := z₀) (ρ := z₀.im / 2) (le_refl _)
        (by linarith [z₀.im_pos, hzz8])
  · have hznorm : (0 : ℝ) < ‖(z:ℂ) - (((δ⁻¹) • τ : ℍ) : ℂ)‖ := by
      rw [norm_pos_iff]
      intro hh
      refine hJ ?_
      have h2 : z = (δ⁻¹) • τ := UpperHalfPlane.ext (sub_eq_zero.mp hh)
      rw [h2, hZj τ]
    have hΔτ : δ₁ ≤ ‖DeltaFun τ‖ := hbδ₁ τ hτdτ
    have hΔz : δ₂ ≤ ‖DeltaFun z‖ := hbδ₂ z hzdz
    have hden : δ₁ * δ₂ ^ (if d = 8 then 1 else 2) * c₀ * ‖(z:ℂ) - (((δ⁻¹) • τ : ℍ) : ℂ)‖
        ≤ ‖growthPrefactor d τ z‖ := by
      rw [KaxisMid.norm_growthPrefactor]
      have hBe : δ₂ ^ (if d = 8 then 1 else 2) ≤ ‖DeltaFun z‖ ^ (if d = 8 then 1 else 2) :=
        pow_le_pow_left₀ hδ₂.le hΔz _
      have h3 : δ₁ * δ₂ ^ (if d = 8 then 1 else 2)
          ≤ ‖DeltaFun τ‖ * ‖DeltaFun z‖ ^ (if d = 8 then 1 else 2) :=
        mul_le_mul hΔτ hBe (pow_nonneg hδ₂.le _) (norm_nonneg _)
      calc δ₁ * δ₂ ^ (if d = 8 then 1 else 2) * c₀ * ‖(z:ℂ) - (((δ⁻¹) • τ : ℍ) : ℂ)‖
          = (δ₁ * δ₂ ^ (if d = 8 then 1 else 2))
              * (c₀ * ‖(z:ℂ) - (((δ⁻¹) • τ : ℍ) : ℂ)‖) := by ring
        _ ≤ (‖DeltaFun τ‖ * ‖DeltaFun z‖ ^ (if d = 8 then 1 else 2))
              * ‖jInvariantFun τ - jInvariantFun z‖ :=
            mul_le_mul h3 hjlow (by positivity)
              (mul_nonneg (norm_nonneg _) (pow_nonneg (norm_nonneg _) _))
        _ = ‖DeltaFun τ‖ * ‖DeltaFun z‖ ^ (if d = 8 then 1 else 2)
              * ‖jInvariantFun τ - jInvariantFun z‖ := by ring
    have hgp_pos : 0 < ‖growthPrefactor d τ z‖ :=
      lt_of_lt_of_le (by positivity) hden
    have hKfun_eq : ‖Kfun ℓ d τ z‖ = ‖KfunClear ℓ d τ z‖ / ‖growthPrefactor d τ z‖ := by
      rw [Kfun_eq_KfunClear_div' ℓ d hd τ z hJ, norm_div]
    have hratio : ‖(z:ℂ) - (((δ⁻¹) • τ : ℍ) : ℂ)‖ / ‖growthPrefactor d τ z‖
        ≤ 1 / (δ₁ * δ₂ ^ (if d = 8 then 1 else 2) * c₀) := by
      rw [div_le_iff₀ hgp_pos]
      rw [show 1 / (δ₁ * δ₂ ^ (if d = 8 then 1 else 2) * c₀) * ‖growthPrefactor d τ z‖
          = ‖growthPrefactor d τ z‖ / (δ₁ * δ₂ ^ (if d = 8 then 1 else 2) * c₀) by ring]
      rw [le_div_iff₀ (by positivity : (0:ℝ) < δ₁ * δ₂ ^ (if d = 8 then 1 else 2) * c₀)]
      calc ‖(z:ℂ) - (((δ⁻¹) • τ : ℍ) : ℂ)‖ * (δ₁ * δ₂ ^ (if d = 8 then 1 else 2) * c₀)
          = δ₁ * δ₂ ^ (if d = 8 then 1 else 2) * c₀ * ‖(z:ℂ) - (((δ⁻¹) • τ : ℍ) : ℂ)‖ := by ring
        _ ≤ ‖growthPrefactor d τ z‖ := hden
    calc ‖Kfun ℓ d τ z‖ = ‖KfunClear ℓ d τ z‖ / ‖growthPrefactor d τ z‖ := hKfun_eq
      _ ≤ ((4 * M / z₀.im) * ‖(z:ℂ) - (((δ⁻¹) • τ : ℍ) : ℂ)‖) / ‖growthPrefactor d τ z‖ :=
          div_le_div_of_nonneg_right hnum hgp_pos.le
      _ = (4 * M / z₀.im)
            * (‖(z:ℂ) - (((δ⁻¹) • τ : ℍ) : ℂ)‖ / ‖growthPrefactor d τ z‖) := by ring
      _ ≤ (4 * M / z₀.im) * (1 / (δ₁ * δ₂ ^ (if d = 8 then 1 else 2) * c₀)) :=
          mul_le_mul_of_nonneg_left hratio (by positivity)
      _ = (4 * M / z₀.im) / c₀ / (δ₁ * δ₂ ^ (if d = 8 then 1 else 2)) := by
          ring_nf
      _ ≤ max C₀ ((4 * M / z₀.im) / c₀ / (δ₁ * δ₂ ^ (if d = 8 then 1 else 2))) :=
          le_max_right _ _
end Work.Asymptotics

namespace Work.CKFinal.ArcCont

theorem branch_bound_of_phiPair (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (δ : Matrix.SpecialLinearGroup (Fin 2) ℤ)
    (hδ : Work.Residues.phiPlus (MonoidAlgebra.single δ (1 : ℂ))
        + Work.Residues.phiMinus (MonoidAlgebra.single δ (1 : ℂ)) = 0)
    {t₀ : ℝ} (ht₀ : 0 < t₀) (hne : t₀ ≠ 1) :
    ∃ ρ C : ℝ, 0 < ρ ∧ 0 ≤ C ∧ ∀ (τ z : UpperHalfPlane),
      ‖(τ : ℂ) - ((δ • Work.Kernels.imagAxis t₀ ht₀ : UpperHalfPlane) : ℂ)‖ < ρ →
      ‖(z : ℂ) - ((Work.Kernels.imagAxis t₀ ht₀ : UpperHalfPlane) : ℂ)‖ < ρ →
      ‖Work.Kernels.Kfun ℓ d τ z‖ ≤ C := by
  exact Work.Asymptotics.branch_bound_of_vanish ℓ d hd δ
    (fun z => Work.Asymptotics.KfunClear_vanish_uncond ℓ d hd δ hδ z) ht₀ hne

end Work.CKFinal.ArcCont
