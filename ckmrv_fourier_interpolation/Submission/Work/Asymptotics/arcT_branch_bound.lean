/-
# Local boundedness of the kernel along a grazing branch

Let `eta ∈ GrazeElem`, `t₀ > 0`, `t₀ ≠ 1`, `z₀ = i t₀` and `τ₀ = eta • z₀`.  The pole divisor
`j τ = j z` of the kernel passes through `(τ₀, z₀)` along the branch `z = eta⁻¹ • τ`, and that
pole is *removable*: the cleared kernel vanishes on the branch
(`Work.Asymptotics.KfunClear_vanish_graze_uncond`).  Consequently `K^{(d)}` is bounded on a
Euclidean neighbourhood of `(τ₀, z₀)`.  The proof is the one-zero maximum-modulus bound
(`Work.Asymptotics.KaxisMid.KbcAux2.one_zero_apply`) combined with the lower bound for
`j τ - j z` at the non-elliptic contour point `z₀`
(`Work.Asymptotics.MiddleRange.exists_diffQuotient_lower_general`).

This is the grazing-branch analogue of `Work.Asymptotics.Graze.key_bound_arc'` (which treats
the tangency points, where `t₀ = 1` and two branches merge).
-/
import Mathlib
import Submission.Work.Asymptotics.Graze.Points
import Submission.Work.Asymptotics.arcT_graze_vanish
import Submission.Work.Asymptotics.KaxisMid.exists_local_bound_coincidence
import Submission.Work.Asymptotics.KaxisMid.Main
import Submission.Work.Asymptotics.KaxisMid.exists_bound_Kfun_of_coincidence
import Submission.Work.Asymptotics.MiddleRange.exists_diffQuotient_lower_general
import Submission.Work.Asymptotics.differentiableAt_Kfun_tau

set_option maxHeartbeats 1600000
set_option linter.unusedSimpArgs false

noncomputable section

open UpperHalfPlane ModularForm ModularGroup Matrix
open scoped MatrixGroups Topology
open Work.Kernels
open Work.Asymptotics.KaxisMid

namespace Work.Asymptotics

/-- The Möbius action of a fixed element is locally Lipschitz. -/
lemma exists_lipschitz_smul' (γ : SL(2, ℤ)) (z₀ : ℍ) :
    ∃ δZ cZ : ℝ, 0 < δZ ∧ 0 < cZ ∧ ∀ z : ℍ,
      ‖(z:ℂ) - (z₀:ℂ)‖ < δZ →
      ‖((γ • z : ℍ) : ℂ) - ((γ • z₀ : ℍ) : ℂ)‖ ≤ cZ * ‖(z:ℂ) - (z₀:ℂ)‖ := by
  set c : ℂ := (((γ 1 0 : ℤ) : ℝ) : ℂ) with hc
  set d : ℂ := (((γ 1 1 : ℤ) : ℝ) : ℂ) with hd
  have hden0 : c * (z₀:ℂ) + d ≠ 0 := by
    intro h
    have him := congrArg Complex.im h
    have hre := congrArg Complex.re h
    rw [hc, hd] at him hre
    simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.zero_im, Complex.add_re, Complex.mul_re, Complex.zero_re, UpperHalfPlane.coe_im,
      UpperHalfPlane.coe_re, mul_zero, zero_mul, add_zero] at him hre
    have hc0 : γ 1 0 = 0 := by
      have : ((γ 1 0 : ℤ) : ℝ) = 0 := by
        rcases mul_eq_zero.mp him with h1 | h1
        · exact h1
        · exact absurd h1 (ne_of_gt z₀.im_pos)
      exact_mod_cast this
    have hd0 : γ 1 1 = 0 := by
      have : ((γ 1 1 : ℤ) : ℝ) = 0 := by
        rw [hc0] at hre; simpa using hre
      exact_mod_cast this
    have hdet := γ.2
    rw [Matrix.det_fin_two, hc0, hd0] at hdet
    norm_num at hdet
  have hcont : Continuous (fun z : ℂ => c * z + d) :=
    (continuous_const.mul continuous_id).add continuous_const
  obtain ⟨δZ, hδZ, hδZb⟩ := Metric.continuousAt_iff.mp hcont.continuousAt (‖c * (z₀:ℂ) + d‖/2)
    (by positivity)
  refine ⟨δZ, 2 / ‖c * (z₀:ℂ) + d‖^2, hδZ, by positivity, fun z hz => ?_⟩
  have hw : (0:ℝ) < ‖c * (z₀:ℂ) + d‖ := by positivity
  have hsub : ‖c * ((z:ℂ) - (z₀:ℂ))‖ < ‖c * (z₀:ℂ) + d‖ / 2 := by
    have hb := hδZb (by rw [dist_eq_norm]; exact hz)
    rw [dist_eq_norm, show c * (z:ℂ) + d - (c * (z₀:ℂ) + d) = c * ((z:ℂ) - (z₀:ℂ)) by ring] at hb
    exact hb
  have hdenz : c * (z:ℂ) + d ≠ 0 := by
    intro h0
    have h1 : c * ((z:ℂ) - (z₀:ℂ)) = -(c * (z₀:ℂ) + d) := by
      linear_combination h0
    have h2 := hsub
    rw [h1, norm_neg] at h2
    linarith [hw]
  have hden : ‖c * (z₀:ℂ) + d‖/2 ≤ ‖c * (z:ℂ) + d‖ := by
    have htri : ‖c * (z₀:ℂ) + d‖ ≤ ‖c * (z:ℂ) + d‖ + ‖c * ((z:ℂ) - (z₀:ℂ))‖ := by
      have := norm_sub_le (c * (z:ℂ) + d) (c * ((z:ℂ) - (z₀:ℂ)))
      rw [show c * (z:ℂ) + d - c * ((z:ℂ) - (z₀:ℂ)) = c * (z₀:ℂ) + d by ring] at this
      exact this
    linarith [htri, hsub]
  have hdiff : ((γ • z : ℍ) : ℂ) - ((γ • z₀ : ℍ) : ℂ)
      = ((z:ℂ) - (z₀:ℂ)) / ((c * (z:ℂ) + d) * (c * (z₀:ℂ) + d)) := by
    have hcz : ((algebraMap ℤ ℝ (γ 1 0) : ℝ) : ℂ) * (z:ℂ) + ((algebraMap ℤ ℝ (γ 1 1) : ℝ) : ℂ)
        = c * (z:ℂ) + d := by rw [hc, hd]; simp
    have hcz0 : ((algebraMap ℤ ℝ (γ 1 0) : ℝ) : ℂ) * (z₀:ℂ) + ((algebraMap ℤ ℝ (γ 1 1) : ℝ) : ℂ)
        = c * (z₀:ℂ) + d := by rw [hc, hd]; simp
    rw [UpperHalfPlane.coe_specialLinearGroup_apply, UpperHalfPlane.coe_specialLinearGroup_apply,
      hcz, hcz0, div_sub_div _ _ hdenz hden0]
    rw [div_eq_div_iff (mul_ne_zero hdenz hden0) (mul_ne_zero hdenz hden0)]
    have hdetC : ((algebraMap ℤ ℝ (γ 0 0) : ℝ) : ℂ) * ((algebraMap ℤ ℝ (γ 1 1) : ℝ) : ℂ)
        - ((algebraMap ℤ ℝ (γ 0 1) : ℝ) : ℂ) * ((algebraMap ℤ ℝ (γ 1 0) : ℝ) : ℂ) = 1 := by
      have h := γ.2
      rw [Matrix.det_fin_two] at h
      have h2 := congrArg (fun n : ℤ => (((n : ℝ) : ℂ))) h
      push_cast at h2
      simpa using h2
    linear_combination hdetC * ((z:ℂ) - (z₀:ℂ)) * ((c * (z:ℂ) + d) * (c * (z₀:ℂ) + d))
  rw [hdiff, norm_div, norm_mul]
  calc ‖(z:ℂ) - (z₀:ℂ)‖ / (‖c * (z:ℂ) + d‖ * ‖c * (z₀:ℂ) + d‖)
      ≤ ‖(z:ℂ) - (z₀:ℂ)‖ / ((‖c * (z₀:ℂ) + d‖/2) * ‖c * (z₀:ℂ) + d‖) :=
        div_le_div_of_nonneg_left (norm_nonneg _) (by positivity) (by nlinarith [hden, hw])
    _ = 2 / ‖c * (z₀:ℂ) + d‖^2 * ‖(z:ℂ) - (z₀:ℂ)‖ := by
        field_simp

/-- Off the pole divisor, the kernel is the cleared kernel divided by the growth prefactor. -/
lemma Kfun_eq_KfunClear_div' (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (τ z : ℍ) (h : Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun z) :
    Work.Kernels.Kfun ℓ d τ z = Work.Kernels.KfunClear ℓ d τ z / Work.Kernels.growthPrefactor d τ z := by
  rw [eq_div_iff (growthPrefactor_ne_zero d h), mul_comm]
  exact (KfunClear_eq_growthPrefactor_mul ℓ d hd h).symm

/-- **Boundedness of the kernel near a point of a grazing branch.** -/
theorem graze_branch_bound (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (eta : SL(2, ℤ)) (hη : Graze.GrazeElem eta) {t₀ : ℝ} (ht₀ : 0 < t₀) (hne : t₀ ≠ 1) :
    ∃ ρ C : ℝ, 0 < ρ ∧ 0 ≤ C ∧ ∀ (τ z : ℍ),
      ‖(τ:ℂ) - ((eta • Work.Kernels.imagAxis t₀ ht₀ : ℍ) : ℂ)‖ < ρ →
      ‖(z:ℂ) - ((Work.Kernels.imagAxis t₀ ht₀ : ℍ) : ℂ)‖ < ρ →
      ‖Work.Kernels.Kfun ℓ d τ z‖ ≤ C := by
  set z₀ : ℍ := Work.Kernels.imagAxis t₀ ht₀ with hz₀
  set τ₀ : ℍ := eta • z₀ with hτ₀
  have hZτ₀ : (eta⁻¹) • τ₀ = z₀ := by
    rw [hτ₀, ← mul_smul, inv_mul_cancel, one_smul]
  have hZzero : ∀ τ : ℍ, Work.Kernels.KfunClear ℓ d τ ((eta⁻¹) • τ) = 0 := by
    intro τ
    have h := Work.Asymptotics.KfunClear_vanish_graze_uncond ℓ d hd eta hη ((eta⁻¹) • τ)
    rw [← mul_smul, mul_inv_cancel, one_smul] at h
    exact h
  have hZj : ∀ τ : ℍ, Work.Kernels.jInvariantFun ((eta⁻¹) • τ) = Work.Kernels.jInvariantFun τ :=
    fun τ => Work.Asymptotics.jInvariantFun_smul_of_slash eta⁻¹ τ
  obtain ⟨M, hMpos, hMbd⟩ := KaxisMid.KbcAux2.exists_bound_KfunClear_of_balls ℓ d hd τ₀ z₀
    (R₁ := τ₀.im / 2) (R₂ := z₀.im / 2) (by linarith [τ₀.im_pos]) (by linarith [z₀.im_pos])
  obtain ⟨ρ₀, hρ₀, c₀, hc₀, hlow⟩ :=
    Work.Asymptotics.MiddleRange.exists_diffQuotient_lower_general (t₀ := t₀) ht₀ hne
  obtain ⟨ρdτ, δ₁, hρdτ, hδ₁, hbδ₁⟩ := KaxisMid.AtIAux.exists_DeltaFun_lower τ₀
  obtain ⟨ρdz, δ₂, hρdz, hδ₂, hbδ₂⟩ := KaxisMid.AtIAux.exists_DeltaFun_lower z₀
  obtain ⟨C₀, hC₀pos, hC₀b⟩ := KaxisMid.exists_bound_Kfun_of_coincidence ℓ d hd
    (isCompact_closedBall τ₀ 1) (isCompact_closedBall z₀ 1)
  obtain ⟨δZ, cZ, hδZ, hcZ, hZlip⟩ := exists_lipschitz_smul' eta⁻¹ τ₀
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
  have hZclose : ‖(((eta⁻¹) • τ : ℍ) : ℂ) - (z₀ : ℂ)‖ ≤ cZ * ‖(τ:ℂ) - (τ₀ : ℂ)‖ := by
    have h := hZlip τ hτδZ
    rwa [hZτ₀] at h
  have hZρ : ‖(((eta⁻¹) • τ : ℍ) : ℂ) - (z₀ : ℂ)‖ < ρ₀ := by
    have h2 : cZ * ‖(τ:ℂ) - (τ₀ : ℂ)‖ < ρ₀ / 2 := by
      calc cZ * ‖(τ:ℂ) - (τ₀ : ℂ)‖ < cZ * (ρ₀ / (2 * cZ)) :=
            mul_lt_mul_of_pos_left hτρcρ hcZ
        _ = ρ₀ / 2 := by field_simp
    have h3 := lt_of_le_of_lt hZclose h2
    linarith [hρ₀]
  have hZ4 : ‖(((eta⁻¹) • τ : ℍ) : ℂ) - (z₀ : ℂ)‖ < z₀.im / 2 / 2 := by
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
    (w₀ := (eta⁻¹) • τ) hZ4 (hZzero τ)
  have hnum : ‖KfunClear ℓ d τ z‖ ≤ (4 * M / z₀.im) * ‖(z:ℂ) - (((eta⁻¹) • τ : ℍ) : ℂ)‖ := by
    have h := hone z hz4
    have h2 : 2 * M / (z₀.im / 2) = 4 * M / z₀.im := by
      rw [div_div_eq_mul_div]; ring
    rwa [h2] at h
  -- the lower bound for the `j`-difference
  have hjlow : c₀ * ‖(z:ℂ) - (((eta⁻¹) • τ : ℍ) : ℂ)‖
      ≤ ‖Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z‖ := by
    have h := hlow ((eta⁻¹) • τ) z hZρ hzρ
    rw [norm_sub_rev] at h
    rwa [hZj τ] at h
  by_cases hJ : Work.Kernels.jInvariantFun τ = Work.Kernels.jInvariantFun z
  · refine le_trans (hC₀b τ z ?_ ?_ hJ) (le_max_left _ _)
    · exact KaxisMid.AtIAux.dist_le_one_of_norm_lt (c := τ₀) (ρ := τ₀.im / 2) (le_refl _) hττ2
    · exact KaxisMid.AtIAux.dist_le_one_of_norm_lt (c := z₀) (ρ := z₀.im / 2) (le_refl _)
        (by linarith [z₀.im_pos, hzz8])
  · have hznorm : (0 : ℝ) < ‖(z:ℂ) - (((eta⁻¹) • τ : ℍ) : ℂ)‖ := by
      rw [norm_pos_iff]
      intro hh
      refine hJ ?_
      have h2 : z = (eta⁻¹) • τ := UpperHalfPlane.ext (sub_eq_zero.mp hh)
      rw [h2, hZj τ]
    have hΔτ : δ₁ ≤ ‖DeltaFun τ‖ := hbδ₁ τ hτdτ
    have hΔz : δ₂ ≤ ‖DeltaFun z‖ := hbδ₂ z hzdz
    have hden : δ₁ * δ₂ ^ (if d = 8 then 1 else 2) * c₀ * ‖(z:ℂ) - (((eta⁻¹) • τ : ℍ) : ℂ)‖
        ≤ ‖growthPrefactor d τ z‖ := by
      rw [KaxisMid.norm_growthPrefactor]
      have hBe : δ₂ ^ (if d = 8 then 1 else 2) ≤ ‖DeltaFun z‖ ^ (if d = 8 then 1 else 2) :=
        pow_le_pow_left₀ hδ₂.le hΔz _
      have h3 : δ₁ * δ₂ ^ (if d = 8 then 1 else 2)
          ≤ ‖DeltaFun τ‖ * ‖DeltaFun z‖ ^ (if d = 8 then 1 else 2) :=
        mul_le_mul hΔτ hBe (pow_nonneg hδ₂.le _) (norm_nonneg _)
      calc δ₁ * δ₂ ^ (if d = 8 then 1 else 2) * c₀ * ‖(z:ℂ) - (((eta⁻¹) • τ : ℍ) : ℂ)‖
          = (δ₁ * δ₂ ^ (if d = 8 then 1 else 2))
              * (c₀ * ‖(z:ℂ) - (((eta⁻¹) • τ : ℍ) : ℂ)‖) := by ring
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
    have hratio : ‖(z:ℂ) - (((eta⁻¹) • τ : ℍ) : ℂ)‖ / ‖growthPrefactor d τ z‖
        ≤ 1 / (δ₁ * δ₂ ^ (if d = 8 then 1 else 2) * c₀) := by
      rw [div_le_iff₀ hgp_pos]
      rw [show 1 / (δ₁ * δ₂ ^ (if d = 8 then 1 else 2) * c₀) * ‖growthPrefactor d τ z‖
          = ‖growthPrefactor d τ z‖ / (δ₁ * δ₂ ^ (if d = 8 then 1 else 2) * c₀) by ring]
      rw [le_div_iff₀ (by positivity : (0:ℝ) < δ₁ * δ₂ ^ (if d = 8 then 1 else 2) * c₀)]
      calc ‖(z:ℂ) - (((eta⁻¹) • τ : ℍ) : ℂ)‖ * (δ₁ * δ₂ ^ (if d = 8 then 1 else 2) * c₀)
          = δ₁ * δ₂ ^ (if d = 8 then 1 else 2) * c₀ * ‖(z:ℂ) - (((eta⁻¹) • τ : ℍ) : ℂ)‖ := by ring
        _ ≤ ‖growthPrefactor d τ z‖ := hden
    calc ‖Kfun ℓ d τ z‖ = ‖KfunClear ℓ d τ z‖ / ‖growthPrefactor d τ z‖ := hKfun_eq
      _ ≤ ((4 * M / z₀.im) * ‖(z:ℂ) - (((eta⁻¹) • τ : ℍ) : ℂ)‖) / ‖growthPrefactor d τ z‖ :=
          div_le_div_of_nonneg_right hnum hgp_pos.le
      _ = (4 * M / z₀.im)
            * (‖(z:ℂ) - (((eta⁻¹) • τ : ℍ) : ℂ)‖ / ‖growthPrefactor d τ z‖) := by ring
      _ ≤ (4 * M / z₀.im) * (1 / (δ₁ * δ₂ ^ (if d = 8 then 1 else 2) * c₀)) :=
          mul_le_mul_of_nonneg_left hratio (by positivity)
      _ = (4 * M / z₀.im) / c₀ / (δ₁ * δ₂ ^ (if d = 8 then 1 else 2)) := by
          ring_nf
      _ ≤ max C₀ ((4 * M / z₀.im) / c₀ / (δ₁ * δ₂ ^ (if d = 8 then 1 else 2))) :=
          le_max_right _ _

end Work.Asymptotics
