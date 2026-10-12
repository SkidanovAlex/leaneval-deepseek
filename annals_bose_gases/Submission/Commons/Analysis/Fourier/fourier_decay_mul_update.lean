import Mathlib.Order.CompletePartialOrder
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Topology.UniformSpace.Uniformizable
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Submission.Commons.Analysis.Calculus.contDiff_update_apply
import Submission.Commons.Analysis.Calculus.norm_iteratedFDeriv_update_le
import Submission.Commons.Analysis.Fourier.norm_fourier_le_of_integral_third_deriv
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Commons.Analysis.Fourier

open MeasureTheory
open scoped FourierTransform

/-- If `f` is supported in the closed ball of radius `R` and is bounded by `B` there, then
`∫ ‖f‖ ≤ B * volume.real (closedBall 0 R)`. -/
private lemma integral_norm_le_of_support_closedBall
    {F : Type*} [NormedAddCommGroup F]
    (f : EuclideanSpace ℝ (Fin 3) → F) (R B : ℝ)
    (hsupp : ∀ z, f z ≠ 0 → ‖z‖ ≤ R)
    (hb : ∀ z, ‖z‖ ≤ R → ‖f z‖ ≤ B) :
    ∫ z, ‖f z‖ ≤ B * volume.real (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) R) := by
  have hzero : ∀ z ∉ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) R, ‖f z‖ = 0 := by
    intro z hz
    have hz' : ¬ ‖z‖ ≤ R := by
      simpa only [Metric.mem_closedBall, dist_eq_norm, sub_zero] using hz
    have hfz : f z = 0 := by
      by_contra h
      exact hz' (hsupp z h)
    rw [hfz, norm_zero]
  have hfin : volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) R) < ⊤ :=
    (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin 3)) R).measure_lt_top
  have h1 : ‖∫ z in Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) R, ‖f z‖‖
      ≤ B * volume.real (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) R) := by
    refine norm_setIntegral_le_of_norm_le_const hfin (fun z hz => ?_)
    rw [Real.norm_of_nonneg (norm_nonneg _)]
    exact hb z (by simpa only [Metric.mem_closedBall, dist_eq_norm, sub_zero] using hz)
  have hnn : 0 ≤ ∫ z in Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) R, ‖f z‖ :=
    setIntegral_nonneg measurableSet_closedBall (fun z _ => norm_nonneg _)
  rw [Real.norm_of_nonneg hnn] at h1
  calc ∫ z, ‖f z‖
      = ∫ z in Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) R, ‖f z‖ :=
        (setIntegral_eq_integral_of_forall_compl_eq_zero hzero).symm
    _ ≤ B * volume.real (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) R) := h1

/-- The zeroth term of a sum over `range 4` is at most the whole sum, for nonnegative terms. -/
private lemma sum_range4_zero_le (G : ℕ → ℝ) (hG : ∀ k, k ≤ 3 → 0 ≤ G k) :
    G 0 ≤ ∑ k ∈ Finset.range 4, G k := by
  apply Finset.single_le_sum
  · intro k hk
    exact hG k (by have := Finset.mem_range.mp hk; omega)
  · simp

/-- Any term of a sum over `range 4` is at most the whole sum, for nonnegative terms. -/
private lemma sum_range4_le (G : ℕ → ℝ) (hG : ∀ k, k ≤ 3 → 0 ≤ G k) {j : ℕ} (hj : j ≤ 3) :
    G j ≤ ∑ k ∈ Finset.range 4, G k := by
  apply Finset.single_le_sum
  · intro k hk
    exact hG k (by have := Finset.mem_range.mp hk; omega)
  · exact Finset.mem_range.mpr (by omega)

/-- A sum over `range 4` of nonnegative terms is nonnegative. -/
private lemma sum_range4_nonneg (G : ℕ → ℝ) (hG : ∀ k, k ≤ 3 → 0 ≤ G k) :
    0 ≤ ∑ k ∈ Finset.range 4, G k := by
  apply Finset.sum_nonneg
  intro k hk
  exact hG k (by have := Finset.mem_range.mp hk; omega)

theorem fourier_decay_mul_update (n : ℕ) (R S : ℝ) (hR : 0 < R) (hRS : R ≤ S) : ∃ C : ℝ, 0 ≤ C ∧ ∀ (g : EuclideanSpace ℝ (Fin 3) → ℂ) (G : ℕ → ℝ), ContDiff ℝ 3 g → (∀ z, g z ≠ 0 → ‖z‖ ≤ R) → (∀ k ≤ 3, ∀ z, ‖iteratedFDeriv ℝ k g z‖ ≤ G k) → ∀ (Φ : (Fin n → EuclideanSpace ℝ (Fin 3)) → ℂ) (M : ℕ → ℝ), ContDiff ℝ 3 Φ → (∀ k ≤ 3, ∀ y : Fin n → EuclideanSpace ℝ (Fin 3), (∀ j, ‖y j‖ ≤ S) → ‖iteratedFDeriv ℝ k Φ y‖ ≤ M k) → ∀ (x : Fin n → EuclideanSpace ℝ (Fin 3)), (∀ j, ‖x j‖ ≤ S) → ∀ (i : Fin n) (ξ : EuclideanSpace ℝ (Fin 3)), ‖FourierTransform.fourier (fun z => g z * Φ (Function.update x i z)) ξ‖ ≤ C * (1 + ∑ k ∈ Finset.range 4, |G k|) * (1 + ∑ k ∈ Finset.range 4, |M k|) * (1 + ‖ξ‖) ^ (-(3 : ℤ)) := by
  refine ⟨128 * volume.real (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) R),
    mul_nonneg (by norm_num) measureReal_nonneg, ?_⟩
  intro g G hg hgsupp hGbd Φ M hΦ hMbd x hx i ξ
  set vol : ℝ := volume.real (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) R) with hvol
  have hvolnn : 0 ≤ vol := by rw [hvol]; exact measureReal_nonneg
  have hSnn : 0 ≤ S := le_of_lt (lt_of_lt_of_le hR hRS)
  let F : EuclideanSpace ℝ (Fin 3) → ℂ := fun z => Φ (Function.update x i z)
  let h : EuclideanSpace ℝ (Fin 3) → ℂ := fun z => g z * F z
  have hFcd : ContDiff ℝ 3 F :=
    hΦ.comp (Commons.Analysis.Calculus.contDiff_update_apply 3 x i)
  have hhcd : ContDiff ℝ 3 h := hg.mul hFcd
  have hsupp : ∀ z, h z ≠ 0 → ‖z‖ ≤ R := by
    intro z hz
    refine hgsupp z (fun hgz => hz ?_)
    simp only [h, hgz, zero_mul]
  have hsub : Function.support h ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) R := by
    intro z hz
    rw [Function.mem_support] at hz
    simp only [Metric.mem_closedBall, dist_eq_norm, sub_zero]
    exact hsupp z hz
  have hsub' : tsupport h ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) R :=
    closure_minimal hsub Metric.isClosed_closedBall
  have hcs : HasCompactSupport h :=
    HasCompactSupport.of_support_subset_isCompact
      (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin 3)) R) hsub
  have hGnn : ∀ k, k ≤ 3 → 0 ≤ G k := fun k hk => le_trans (norm_nonneg _) (hGbd k hk 0)
  have hMnn : ∀ k, k ≤ 3 → 0 ≤ M k := by
    intro k hk
    refine le_trans (norm_nonneg _) (hMbd k hk 0 (fun j => ?_))
    simp only [Pi.zero_apply, norm_zero]
    exact hSnn
  have hcoord : ∀ z, ‖z‖ ≤ R → ∀ j : Fin n, ‖(Function.update x i z) j‖ ≤ S := by
    intro z hz j
    rcases eq_or_ne j i with rfl | hj
    · rw [Function.update_self]
      exact le_trans hz hRS
    · rw [Function.update_of_ne hj]
      exact hx j
  have hkey : ∀ k, k ≤ 3 → ∀ z, ‖z‖ ≤ R →
      ‖iteratedFDeriv ℝ k h z‖ ≤
        ∑ j ∈ Finset.range (k + 1), (Nat.choose k j : ℝ) * G j * M (k - j) := by
    intro k hk z hz
    have hprod := norm_iteratedFDeriv_mul_le (𝕜 := ℝ) (f := g) (g := F) hg hFcd z
      (n := k) (by exact_mod_cast hk)
    refine hprod.trans ?_
    apply Finset.sum_le_sum
    intro j hj
    rw [Finset.mem_range] at hj
    have hjle3 : j ≤ 3 := by omega
    have hkj3 : k - j ≤ 3 := by omega
    have h1 : ‖iteratedFDeriv ℝ j g z‖ ≤ G j := hGbd j hjle3 z
    have h2 : ‖iteratedFDeriv ℝ (k - j) F z‖ ≤ M (k - j) := by
      refine le_trans (Commons.Analysis.Calculus.norm_iteratedFDeriv_update_le Φ
        (hΦ.of_le (by exact_mod_cast hkj3)) x i z) ?_
      exact hMbd (k - j) hkj3 _ (hcoord z hz)
    have hch : (0 : ℝ) ≤ (Nat.choose k j : ℝ) := by positivity
    have hGj : 0 ≤ G j := hGnn j hjle3
    have hMnj : 0 ≤ M (k - j) := hMnn (k - j) hkj3
    calc (Nat.choose k j : ℝ) * ‖iteratedFDeriv ℝ j g z‖ * ‖iteratedFDeriv ℝ (k - j) F z‖
        ≤ (Nat.choose k j : ℝ) * G j * ‖iteratedFDeriv ℝ (k - j) F z‖ :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 hch) (norm_nonneg _)
      _ ≤ (Nat.choose k j : ℝ) * G j * M (k - j) :=
          mul_le_mul_of_nonneg_left h2 (mul_nonneg hch hGj)
  -- define the auxiliary quantities
  set S3 : ℝ := ∑ j ∈ Finset.range 4, (Nat.choose 3 j : ℝ) * G j * M (3 - j) with hS3def
  set A : ℝ := (G 0 * M 0 + S3) * vol with hAdef
  have hS3nn : 0 ≤ S3 := by
    rw [hS3def]
    apply Finset.sum_nonneg
    intro j hj
    rw [Finset.mem_range] at hj
    exact mul_nonneg (mul_nonneg (by positivity) (hGnn j (by omega))) (hMnn (3 - j) (by omega))
  have hAnn : 0 ≤ A := by
    rw [hAdef]
    exact mul_nonneg (add_nonneg (mul_nonneg (hGnn 0 (by norm_num)) (hMnn 0 (by norm_num)))
      hS3nn) hvolnn
  -- integral bounds
  have hint0 : ∫ z, ‖h z‖ ≤ (G 0 * M 0) * vol := by
    rw [hvol]
    refine integral_norm_le_of_support_closedBall h R (G 0 * M 0) hsupp (fun z hz => ?_)
    have hk := hkey 0 (by norm_num) z hz
    rw [show (0:ℕ) + 1 = 1 from rfl, Finset.sum_range_one] at hk
    simpa using hk
  have hint3 : ∫ z, ‖iteratedFDeriv ℝ 3 h z‖ ≤ S3 * vol := by
    rw [hvol, hS3def]
    refine integral_norm_le_of_support_closedBall (iteratedFDeriv ℝ 3 h) R
      (∑ j ∈ Finset.range 4, (Nat.choose 3 j : ℝ) * G j * M (3 - j))
      (fun z hz => ?_) (fun z hz => hkey 3 (by norm_num) z hz)
    have hz' : z ∈ Function.support (iteratedFDeriv ℝ 3 h) := by
      rw [Function.mem_support]; exact hz
    have h1 := support_iteratedFDeriv_subset (𝕜 := ℝ) (f := h) 3 hz'
    have h2 := hsub' h1
    simpa only [Metric.mem_closedBall, dist_eq_norm, sub_zero] using h2
  have hI0 : ∫ z, ‖h z‖ ≤ A := by
    have : (G 0 * M 0) * vol ≤ (G 0 * M 0 + S3) * vol := by
      apply mul_le_mul_of_nonneg_right _ hvolnn
      linarith [hS3nn]
    rw [hAdef]
    exact le_trans hint0 this
  have hI3 : ∫ z, ‖iteratedFDeriv ℝ 3 h z‖ ≤ A := by
    have : S3 * vol ≤ (G 0 * M 0 + S3) * vol := by
      apply mul_le_mul_of_nonneg_right _ hvolnn
      linarith [mul_nonneg (hGnn 0 (by norm_num)) (hMnn 0 (by norm_num))]
    rw [hAdef]
    exact le_trans hint3 this
  have hmain := norm_fourier_le_of_integral_third_deriv h A hAnn hhcd hcs hI0 hI3 ξ
  -- arithmetic
  have hG0M0 : G 0 * M 0 ≤ (∑ k ∈ Finset.range 4, G k) * (∑ k ∈ Finset.range 4, M k) := by
    apply mul_le_mul
    · exact sum_range4_zero_le G hGnn
    · exact sum_range4_zero_le M hMnn
    · exact hMnn 0 (by norm_num)
    · exact sum_range4_nonneg G hGnn
  have hS3le : S3 ≤ 8 * (∑ k ∈ Finset.range 4, G k) * (∑ k ∈ Finset.range 4, M k) := by
    rw [hS3def]
    calc (∑ j ∈ Finset.range 4, (Nat.choose 3 j : ℝ) * G j * M (3 - j))
        ≤ ∑ j ∈ Finset.range 4, (8 * G j * M (3 - j)) := by
          apply Finset.sum_le_sum
          intro j hj
          rw [Finset.mem_range] at hj
          have hc : (Nat.choose 3 j : ℝ) ≤ 8 := by
            interval_cases j <;> norm_num [Nat.choose]
          have hGj : 0 ≤ G j := hGnn j (by omega)
          have hMj : 0 ≤ M (3 - j) := hMnn (3 - j) (by omega)
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc hGj) hMj
      _ = 8 * ∑ j ∈ Finset.range 4, (G j * M (3 - j)) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j _; ring
      _ ≤ 8 * ((∑ k ∈ Finset.range 4, G k) * (∑ k ∈ Finset.range 4, M k)) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          calc (∑ j ∈ Finset.range 4, G j * M (3 - j))
              ≤ ∑ j ∈ Finset.range 4, G j * (∑ k ∈ Finset.range 4, M k) := by
                apply Finset.sum_le_sum
                intro j hj
                rw [Finset.mem_range] at hj
                exact mul_le_mul_of_nonneg_left (sum_range4_le M hMnn (by omega))
                  (hGnn j (by omega))
            _ = (∑ j ∈ Finset.range 4, G j) * (∑ k ∈ Finset.range 4, M k) := by
                rw [Finset.sum_mul]
      _ = 8 * (∑ k ∈ Finset.range 4, G k) * (∑ k ∈ Finset.range 4, M k) := by ring
  have h9 : G 0 * M 0 + S3
      ≤ 9 * ((∑ k ∈ Finset.range 4, G k) * (∑ k ∈ Finset.range 4, M k)) := by
    have := add_le_add hG0M0 hS3le
    nlinarith [this]
  -- final bound on 8 A
  have h8A : 8 * A ≤ 128 * vol * (1 + ∑ k ∈ Finset.range 4, |G k|)
      * (1 + ∑ k ∈ Finset.range 4, |M k|) := by
    have hX : (0:ℝ) ≤ 1 + ∑ k ∈ Finset.range 4, |G k| := by positivity
    have hY : (0:ℝ) ≤ 1 + ∑ k ∈ Finset.range 4, |M k| := by positivity
    have hSGle : (∑ k ∈ Finset.range 4, G k) ≤ 1 + ∑ k ∈ Finset.range 4, |G k| := by
      have : ∑ k ∈ Finset.range 4, G k ≤ ∑ k ∈ Finset.range 4, |G k| :=
        Finset.sum_le_sum (fun k _ => le_abs_self (G k))
      linarith
    have hSMle : (∑ k ∈ Finset.range 4, M k) ≤ 1 + ∑ k ∈ Finset.range 4, |M k| := by
      have : ∑ k ∈ Finset.range 4, M k ≤ ∑ k ∈ Finset.range 4, |M k| :=
        Finset.sum_le_sum (fun k _ => le_abs_self (M k))
      linarith
    have hSGnn : (0:ℝ) ≤ ∑ k ∈ Finset.range 4, G k := sum_range4_nonneg G hGnn
    have hSMnn : (0:ℝ) ≤ ∑ k ∈ Finset.range 4, M k := sum_range4_nonneg M hMnn
    have hXYnn : (0:ℝ) ≤ (1 + ∑ k ∈ Finset.range 4, |G k|) * (1 + ∑ k ∈ Finset.range 4, |M k|) :=
      mul_nonneg hX hY
    have hXY : (∑ k ∈ Finset.range 4, G k) * (∑ k ∈ Finset.range 4, M k)
        ≤ (1 + ∑ k ∈ Finset.range 4, |G k|) * (1 + ∑ k ∈ Finset.range 4, |M k|) :=
      mul_le_mul hSGle hSMle hSMnn hX
    rw [hAdef]
    calc 8 * ((G 0 * M 0 + S3) * vol)
        ≤ 8 * ((9 * ((∑ k ∈ Finset.range 4, G k) * (∑ k ∈ Finset.range 4, M k))) * vol) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          exact mul_le_mul_of_nonneg_right h9 hvolnn
      _ ≤ 8 * ((9 * ((1 + ∑ k ∈ Finset.range 4, |G k|) * (1 + ∑ k ∈ Finset.range 4, |M k|))) * vol) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          apply mul_le_mul_of_nonneg_right _ hvolnn
          exact mul_le_mul_of_nonneg_left hXY (by norm_num)
      _ ≤ 128 * vol * (1 + ∑ k ∈ Finset.range 4, |G k|) * (1 + ∑ k ∈ Finset.range 4, |M k|) := by
          nlinarith [hvolnn, hXYnn, hX, hY]
  have hzpow_pos : (0:ℝ) < (1 + ‖ξ‖) ^ (-(3 : ℤ)) := by
    rw [zpow_neg]
    exact inv_pos.mpr (by positivity)
  calc ‖FourierTransform.fourier (fun z => g z * Φ (Function.update x i z)) ξ‖
      = ‖FourierTransform.fourier h ξ‖ := rfl
    _ ≤ 8 * A / (1 + ‖ξ‖) ^ 3 := hmain
    _ = 8 * A * (1 + ‖ξ‖) ^ (-(3 : ℤ)) := by
        rw [div_eq_mul_inv]
        rw [show (1 + ‖ξ‖) ^ (-(3 : ℤ)) = ((1 + ‖ξ‖) ^ 3)⁻¹ from by
          rw [zpow_neg]; norm_num]
    _ ≤ 128 * vol * (1 + ∑ k ∈ Finset.range 4, |G k|) * (1 + ∑ k ∈ Finset.range 4, |M k|)
          * (1 + ‖ξ‖) ^ (-(3 : ℤ)) :=
        mul_le_mul_of_nonneg_right h8A hzpow_pos.le

end Commons.Analysis.Fourier