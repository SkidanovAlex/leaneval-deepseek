import Mathlib
import Submission.Work.KMTAreas.A4.tsum_finset_jbDecay_shift
import Submission.Work.KMTAreas.A4.eps_tsum_jbDecay_twelve_int_le

set_option autoImplicit false
set_option maxHeartbeats 1000000

open scoped BigOperators
open MeasureTheory

namespace Work.KMTAreas.A4

open Work.Analysis.InverseTheory

/-!
# The `ℓ¹` mass of the smoothing weight `lipWeight`

`lipWeight ψ ε N' m = ε (N')⁻¹ ∑_{m' ∈ [1,N']} ψ(ε(m - m'))` is the coefficient of the smoothing
operator of Proposition `lip` of Krause--Mirek--Tao (§5, "the alternate inverse theorem for `f`").
This module proves the *uniform* (in `0 < ε ≤ 1` and `1 ≤ N'`) bound on its `ℓ¹` mass which is
needed to control the smoothing of a bounded test function: the total mass of the weight is a
constant depending only on `ψ`.

The two analytic inputs are the `ℤ`-lattice sum bound `ε ∑_{m ∈ ℤ} ⟨εm⟩^{-12} ≤ 2^61` (a uniform
version of the Riemann-sum comparison `riemann_shift`) and the reindexing of a finite sum of
translates of that decay factor.
-/

/-- The decay constant `C = 2^12 (S + 1)` of `schwartz_decay`. -/
noncomputable def lipC (ψ : SchwartzR) : ℝ := (2 : ℝ) ^ 12 * (schwartzSeminormSum ψ + 1)

lemma lipC_pos (ψ : SchwartzR) : 0 < lipC ψ := by
  rw [lipC]
  have h := schwartzSeminormSum_nonneg ψ
  positivity

lemma one_le_lipC (ψ : SchwartzR) : 1 ≤ lipC ψ := by
  rw [lipC]
  have h := schwartzSeminormSum_nonneg ψ
  nlinarith [show (1 : ℝ) ≤ (2 : ℝ) ^ 12 by norm_num]

/-! ## The main lemma -/

theorem lipWeightTsumLe (ψ : Work.Analysis.InverseTheory.SchwartzR) :
    ∃ K : ℝ, 0 < K ∧ ∀ {ε : ℝ}, 0 < ε → ε ≤ 1 → ∀ {N' : ℕ}, 1 ≤ N' →
      ∑' m : ℤ, ‖Work.KMTAreas.A4.lipWeight ψ ε N' m‖ ≤ K := by
  refine ⟨lipC ψ * (2 : ℝ) ^ 61, ?_, ?_⟩
  · exact mul_pos (lipC_pos ψ) (by norm_num)
  · intro ε hε0 hε1 N' hN'
    set C : ℝ := lipC ψ with hC
    have hCpos : 0 < C := by rw [hC]; exact lipC_pos ψ
    have hC0 : 0 ≤ C := hCpos.le
    have hN'0 : (0 : ℝ) < (N' : ℝ) := by
      have h1 : (1 : ℝ) ≤ (N' : ℝ) := by exact_mod_cast hN'
      linarith
    have hN'ne : (N' : ℝ) ≠ 0 := ne_of_gt hN'0
    have hdecay : ∀ t : ℝ, ‖(ψ : ℝ → ℂ) t‖ ≤ C * jbDecay 12 t := fun t => by
      rw [hC, lipC]
      exact schwartz_decay ψ t
    set J : Finset ℕ := Finset.Icc 1 N' with hJ
    set D : ℝ := ∑' u : ℤ, jbDecay 12 (ε * (u : ℝ)) with hD
    set A : ℤ → ℝ := fun m => ∑ y ∈ J, ε * jbDecay 12 (ε * ((m : ℝ) - (y : ℝ))) with hA
    have hA_sum : Summable A := by
      rw [hA]
      exact summable_finset_sum J
        (fun y _ => (summable_jbDecay_twelve_shift hε0 (y : ℤ)).mul_left ε)
    -- pointwise bound
    have hbound : ∀ m : ℤ, ‖lipWeight ψ ε N' m‖ ≤ C * (N' : ℝ)⁻¹ * A m := by
      intro m
      have hnorm_eps : ‖(ε : ℂ)‖ = ε := by
        rw [Complex.norm_real, Real.norm_of_nonneg hε0.le]
      have hnorm_inv : ‖(((N' : ℝ)⁻¹ : ℝ) : ℂ)‖ = (N' : ℝ)⁻¹ := by
        rw [Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.mpr hN'0.le)]
      rw [lipWeight]
      calc ‖(ε : ℂ) * (((N' : ℝ)⁻¹ : ℝ) * ∑ m' ∈ Finset.Icc 1 N',
              (ψ (ε * ((m : ℝ) - (m' : ℝ))) : ℂ))‖
          = ε * ((N' : ℝ)⁻¹ * ‖∑ m' ∈ Finset.Icc 1 N',
              (ψ (ε * ((m : ℝ) - (m' : ℝ))) : ℂ)‖) := by
            rw [norm_mul, norm_mul, hnorm_eps, hnorm_inv]
        _ ≤ ε * ((N' : ℝ)⁻¹ * ∑ m' ∈ Finset.Icc 1 N',
              ‖(ψ (ε * ((m : ℝ) - (m' : ℝ))) : ℂ)‖) := by
            refine mul_le_mul_of_nonneg_left ?_ hε0.le
            exact mul_le_mul_of_nonneg_left (norm_sum_le _ _) (inv_nonneg.mpr hN'0.le)
        _ ≤ ε * ((N' : ℝ)⁻¹ * ∑ m' ∈ Finset.Icc 1 N',
              C * jbDecay 12 (ε * ((m : ℝ) - (m' : ℝ)))) := by
            refine mul_le_mul_of_nonneg_left ?_ hε0.le
            refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun m' _ => ?_))
              (inv_nonneg.mpr hN'0.le)
            exact hdecay _
        _ = C * (N' : ℝ)⁻¹ * A m := by
            have h1 : (∑ m' ∈ Finset.Icc 1 N', C * jbDecay 12 (ε * ((m : ℝ) - (m' : ℝ))))
                = C * ∑ m' ∈ Finset.Icc 1 N',
                    jbDecay 12 (ε * ((m : ℝ) - (m' : ℝ))) :=
              (Finset.mul_sum _ _ C).symm
            have h2 : A m = ε * ∑ m' ∈ Finset.Icc 1 N',
                    jbDecay 12 (ε * ((m : ℝ) - (m' : ℝ))) := by
              rw [hA, hJ]
              exact (Finset.mul_sum _ _ ε).symm
            rw [h1, h2]
            ring
    have hnorm_summable : Summable (fun m : ℤ => ‖lipWeight ψ ε N' m‖) :=
      Summable.of_nonneg_of_le (fun m => norm_nonneg _) hbound
        (hA_sum.mul_left (C * (N' : ℝ)⁻¹))
    have hmaj_summable : Summable (fun m : ℤ => C * (N' : ℝ)⁻¹ * A m) :=
      hA_sum.mul_left (C * (N' : ℝ)⁻¹)
    have hle := Summable.tsum_le_tsum hbound hnorm_summable hmaj_summable
    have hmaj_eq : (∑' m : ℤ, C * (N' : ℝ)⁻¹ * A m) = C * (N' : ℝ)⁻¹ * ∑' m : ℤ, A m :=
      Summable.tsum_mul_left _ hA_sum
    have hA_eq : (∑' m : ℤ, A m) = (N' : ℝ) * (ε * D) := by
      rw [hA, hD]
      rw [tsum_finset_jbDecay_shift J hε0]
      have hJcard : (J.card : ℝ) = (N' : ℝ) := by
        rw [hJ, Nat.card_Icc]
        have : N' + 1 - 1 = N' := by omega
        rw [this]
      rw [hJcard]
    calc (∑' m : ℤ, ‖lipWeight ψ ε N' m‖)
        ≤ ∑' m : ℤ, C * (N' : ℝ)⁻¹ * A m := hle
      _ = C * (N' : ℝ)⁻¹ * ∑' m : ℤ, A m := hmaj_eq
      _ = C * (N' : ℝ)⁻¹ * ((N' : ℝ) * (ε * D)) := by rw [hA_eq]
      _ = C * (ε * D) := by
            have h : (N' : ℝ)⁻¹ * (N' : ℝ) = 1 := inv_mul_cancel₀ hN'ne
            have h2 : C * (N' : ℝ)⁻¹ * ((N' : ℝ) * (ε * D))
                = C * ((N' : ℝ)⁻¹ * (N' : ℝ)) * (ε * D) := by ring
            rw [h2, h, mul_one]
      _ ≤ C * (2 : ℝ) ^ 61 := by
            refine mul_le_mul_of_nonneg_left ?_ hC0
            rw [hD]
            exact eps_tsum_jbDecay_twelve_int_le hε0 hε1

end Work.KMTAreas.A4
