import Mathlib
import Submission.Work.Mostow.BCGDefs
import Submission.Work.Mostow.N2Eigen
import Submission.Work.Mostow.LinAlgTriangular
import Submission.Work.Mostow.LinAlgMatrixIneq
import Submission.Work.Mostow.LinAlgIsom

namespace Work.Mostow

open scoped BigOperators

/-- The determinant of a composition of continuous linear endomorphisms is the product of the
determinants. -/
lemma clm_det_comp {𝕜 : Type*} [CommRing 𝕜] {M : Type*} [TopologicalSpace M] [AddCommGroup M]
    [Module 𝕜 M] (f g : M →L[𝕜] M) : (f ∘L g).det = f.det * g.det := by
  change LinearMap.det ((f ∘L g : M →L[𝕜] M) : M →ₗ[𝕜] M)
    = LinearMap.det (f : M →ₗ[𝕜] M) * LinearMap.det (g : M →ₗ[𝕜] M)
  rw [show ((f ∘L g : M →L[𝕜] M) : M →ₗ[𝕜] M) = (f : M →ₗ[𝕜] M) ∘ₗ (g : M →ₗ[𝕜] M) from rfl,
    LinearMap.det_comp]

/-- **Determinant bound.**  For `N = (1 - H) ∘ DF` with `⟪N v, w⟫ ≤ c √⟪H w, w⟫ ‖v‖`,
`c = (n-1)/√n`, and `(1 - H)` invertible, `|det DF| ≤ c^n √(det H) / det (1 - H)`. -/
lemma det_abs_le_of_tri (n : ℕ) (hn : 3 ≤ n)
    (H N DF : Submission.Mostow.E n →L[ℝ] Submission.Mostow.E n)
    (hkey : (1 - H) ∘L DF = N)
    (htri : ∀ v w : Submission.Mostow.E n,
      inner ℝ (N v) w ≤ (((n : ℝ) - 1) / Real.sqrt n) * Real.sqrt (inner ℝ (H w) w) * ‖v‖)
    (hsym : ∀ v w : Submission.Mostow.E n, inner ℝ (H v) w = inner ℝ v (H w))
    (hpsd : ∀ v : Submission.Mostow.E n, 0 ≤ inner ℝ (H v) v)
    (hpos : 0 < (1 - H).det) :
    |DF.det| ≤ (((n : ℝ) - 1) / Real.sqrt n) ^ n * Real.sqrt H.det / (1 - H).det := by
  have hnR3 : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hc : 0 ≤ ((n : ℝ) - 1) / Real.sqrt n :=
    div_nonneg (by linarith) (Real.sqrt_nonneg _)
  have hT := LinAlgTriangular n finrank_euclideanSpace_fin N.toLinearMap H.toLinearMap
    hsym hpsd (((n : ℝ) - 1) / Real.sqrt n) hc htri
  have hT' : |N.det| ≤ (((n : ℝ) - 1) / Real.sqrt n) ^ n * Real.sqrt H.det := hT
  have hdetN : N.det = (1 - H).det * DF.det := by
    rw [← hkey]; exact clm_det_comp (1 - H) DF
  rw [hdetN] at hT'
  rw [abs_mul, abs_of_pos hpos] at hT'
  rw [le_div_iff₀ hpos]
  have hcomm : (1 - H).det * |DF.det| = |DF.det| * (1 - H).det :=
    mul_comm ((1 - H).det) |DF.det|
  linarith [hT', hcomm]

/-- **Contraction in the equality case.**  If additionally `H = (1/n) • 1`, then
`N = ((n-1)/n) • DF` and the one-sided bound forces `DF` to be a contraction. -/
lemma norm_le_of_scalar_H (n : ℕ) (hn : 3 ≤ n)
    (H N DF : Submission.Mostow.E n →L[ℝ] Submission.Mostow.E n)
    (hkey : (1 - H) ∘L DF = N)
    (htri : ∀ v w : Submission.Mostow.E n,
      inner ℝ (N v) w ≤ (((n : ℝ) - 1) / Real.sqrt n) * Real.sqrt (inner ℝ (H w) w) * ‖v‖)
    (hH : H = (1 / (n : ℝ)) • 1) :
    ∀ v : Submission.Mostow.E n, ‖DF v‖ ≤ ‖v‖ := by
  intro v
  have hnR3 : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  have hn1 : (0 : ℝ) < (n : ℝ) - 1 := by linarith
  have hrnn : 0 ≤ ((n : ℝ) - 1) / (n : ℝ) := div_nonneg (by linarith) (by linarith)
  have hsc : (1 : ℝ) - 1 / (n : ℝ) = ((n : ℝ) - 1) / (n : ℝ) := by
    have hnne : (n : ℝ) ≠ 0 := ne_of_gt hn0
    have h1 : (1 : ℝ) = (n : ℝ) / (n : ℝ) := (div_self hnne).symm
    nth_rewrite 1 [h1, ← sub_div]
    ring
  -- `1 - H = ((n-1)/n) • 1`
  have hsub : (1 : Submission.Mostow.E n →L[ℝ] Submission.Mostow.E n)
      - (1 / (n : ℝ)) • (1 : Submission.Mostow.E n →L[ℝ] Submission.Mostow.E n)
      = (1 - 1 / (n : ℝ)) • (1 : Submission.Mostow.E n →L[ℝ] Submission.Mostow.E n) :=
    ((sub_smul 1 (1 / (n : ℝ)) (1 : Submission.Mostow.E n →L[ℝ] Submission.Mostow.E n)).trans
      (by rw [one_smul])).symm
  have h1H : (1 - H : Submission.Mostow.E n →L[ℝ] Submission.Mostow.E n)
      = (((n : ℝ) - 1) / (n : ℝ)) • 1 := by
    rw [hH, hsub, hsc]
  -- `N v = ((n-1)/n) • DF v`
  have hNv : N v = (((n : ℝ) - 1) / (n : ℝ)) • DF v := by
    have h1 : N v = (1 - H) (DF v) := (DFunLike.congr_fun hkey v).symm
    rw [h1, h1H]
    simp
  have hNnorm : ‖N v‖ = (((n : ℝ) - 1) / (n : ℝ)) * ‖DF v‖ := by
    rw [hNv, norm_smul, Real.norm_eq_abs, abs_of_nonneg hrnn]
  -- the pointwise hypothesis, evaluated at the unit-`H` point
  have hHw : ∀ w : Submission.Mostow.E n, inner ℝ (H w) w = (1 / (n : ℝ)) * ‖w‖ ^ 2 := by
    intro w
    rw [hH]
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply,
      real_inner_smul_left, real_inner_self_eq_norm_sq]
  have hsqrtH : ∀ w : Submission.Mostow.E n,
      Real.sqrt (inner ℝ (H w) w) = ‖w‖ / Real.sqrt (n : ℝ) := by
    intro w
    rw [hHw w,
      Real.sqrt_mul (div_nonneg (by norm_num) (le_of_lt hn0)),
      Real.sqrt_sq (norm_nonneg w),
      Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 1), Real.sqrt_one]
    ring
  -- the bound `‖N v‖ ≤ ((n-1)/n) ‖v‖`
  have hcc : (((n : ℝ) - 1) / Real.sqrt n) / Real.sqrt n = ((n : ℝ) - 1) / (n : ℝ) := by
    rw [div_div, Real.mul_self_sqrt (by linarith : (0 : ℝ) ≤ (n : ℝ))]
  have hNb : ‖N v‖ ≤ (((n : ℝ) - 1) / (n : ℝ)) * ‖v‖ := by
    have hcs := htri v (N v)
    rw [hsqrtH (N v), real_inner_self_eq_norm_sq] at hcs
    have hcs2 : (((n : ℝ) - 1) / Real.sqrt n) * (‖N v‖ / Real.sqrt n) * ‖v‖
        = (((n : ℝ) - 1) / (n : ℝ)) * ‖N v‖ * ‖v‖ := by
      rw [← hcc]; ring
    rw [hcs2] at hcs
    have hprod : ‖N v‖ * ‖N v‖ ≤ ‖N v‖ * ((((n : ℝ) - 1) / (n : ℝ)) * ‖v‖) := by
      have hsq : ‖N v‖ * ‖N v‖ = ‖N v‖ ^ 2 := by ring
      rw [hsq]
      calc ‖N v‖ ^ 2 ≤ (((n : ℝ) - 1) / (n : ℝ)) * ‖N v‖ * ‖v‖ := hcs
        _ = ‖N v‖ * ((((n : ℝ) - 1) / (n : ℝ)) * ‖v‖) := by ring
    rcases eq_or_lt_of_le (norm_nonneg (N v)) with hz | hz
    · rw [← hz]; exact mul_nonneg hrnn (norm_nonneg v)
    · exact le_of_mul_le_mul_left hprod hz
  -- convert back to `DF`
  have hratio : ((n : ℝ) / ((n : ℝ) - 1)) * (((n : ℝ) - 1) / (n : ℝ)) = 1 := by
    rw [div_mul_div_comm, mul_comm ((n : ℝ) - 1) (n : ℝ),
      div_self (mul_ne_zero (by linarith) (by linarith))]
  have hDF : ‖DF v‖ = ((n : ℝ) / ((n : ℝ) - 1)) * ‖N v‖ := by
    rw [hNnorm, ← mul_assoc, hratio, one_mul]
  rw [hDF]
  calc ((n : ℝ) / ((n : ℝ) - 1)) * ‖N v‖
      ≤ ((n : ℝ) / ((n : ℝ) - 1)) * ((((n : ℝ) - 1) / (n : ℝ)) * ‖v‖) :=
        mul_le_mul_of_nonneg_left hNb (div_nonneg (by linarith) (by linarith))
    _ = ‖v‖ := by rw [← mul_assoc, hratio, one_mul]

/-- The pure linear-algebra heart of the BCG Jacobian inequality: if `N = (1 - H) ∘ DF` and
`⟪N v, w⟫ ≤ ((n-1)/√n) √⟪H w, w⟫ ‖v‖` with `H` symmetric, positive semidefinite, `1 - H` positive
definite and `trace H = 1`, then `|det DF| ≤ 1`; equality forces `H = (1/n) • 1` and `‖DF v‖ ≤ ‖v‖`. -/
theorem JacLinAlg (n : ℕ) (hn : 3 ≤ n) (H N DF : Submission.Mostow.E n →L[ℝ] Submission.Mostow.E n)
    (hkey : (1 - H) ∘L DF = N)
    (htri : ∀ v w : Submission.Mostow.E n,
      inner ℝ (N v) w ≤ (((n : ℝ) - 1) / Real.sqrt n) * Real.sqrt (inner ℝ (H w) w) * ‖v‖)
    (hsym : ∀ v w : Submission.Mostow.E n, inner ℝ (H v) w = inner ℝ v (H w))
    (hpsd : ∀ v : Submission.Mostow.E n, 0 ≤ inner ℝ (H v) v)
    (hpd : ∀ v : Submission.Mostow.E n, v ≠ 0 → 0 < inner ℝ v v - inner ℝ (H v) v)
    (htr : LinearMap.trace ℝ (Submission.Mostow.E n) H.toLinearMap = 1) :
    |DF.det| ≤ 1 ∧
      (|DF.det| = 1 → H = (1 / (n : ℝ)) • 1 ∧ ∀ v : Submission.Mostow.E n, ‖DF v‖ ≤ ‖v‖) := by
  classical
  obtain ⟨lam, h0, h1, hsum, hdet1H, hdetH, hall⟩ := HEigenId n H hsym hpsd hpd htr
  have hnR : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  have hn1 : (0 : ℝ) < (n : ℝ) - 1 := by linarith
  have hRn : (0 : ℝ) < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hn0
  have hc : 0 ≤ ((n : ℝ) - 1) / Real.sqrt n := div_nonneg (by linarith) (Real.sqrt_nonneg _)
  have hcpos : 0 < ((n : ℝ) - 1) / Real.sqrt n := div_pos hn1 hRn
  have hdet1H' : (1 - H).det = ∏ i, (1 - lam i) := by
    rw [show (1 - H).det = (1 - H.toLinearMap).det from rfl, hdet1H]
  have hdetH' : H.det = ∏ i, lam i := by
    rw [show H.det = H.toLinearMap.det from rfl, hdetH]
  have hpos1H : 0 < (1 - H).det := by
    rw [hdet1H']
    exact Finset.prod_pos (fun i _ => by linarith [h1 i])
  have hsqrtH : Real.sqrt H.det = ∏ i, Real.sqrt (lam i) := by
    rw [hdetH']
    exact Real.sqrt_prod Finset.univ (fun i _ => h0 i)
  have hA := det_abs_le_of_tri n hn H N DF hkey htri hsym hpsd hpos1H
  set d : ℝ := Real.sqrt n / ((n : ℝ) - 1) with hd_def
  have hdpos : 0 < d := div_pos hRn hn1
  have hcd : ((n : ℝ) - 1) / Real.sqrt n = d⁻¹ := by
    rw [hd_def, inv_div]
  have hcdpow : (((n : ℝ) - 1) / Real.sqrt n) ^ n * d ^ n = 1 := by
    rw [hcd, ← mul_pow, inv_mul_cancel₀ (ne_of_gt hdpos), one_pow]
  have hB : (∏ i, Real.sqrt (lam i)) / (∏ i, (1 - lam i)) ≤ d ^ n := by
    have h := (LinAlgMatrixIneq n hn lam h0 h1 hsum).1
    rwa [← hd_def] at h
  have hchain : |DF.det| ≤ (((n : ℝ) - 1) / Real.sqrt n) ^ n
      * ((∏ i, Real.sqrt (lam i)) / (∏ i, (1 - lam i))) := by
    calc |DF.det| ≤ (((n : ℝ) - 1) / Real.sqrt n) ^ n * Real.sqrt H.det / (1 - H).det := hA
      _ = (((n : ℝ) - 1) / Real.sqrt n) ^ n
            * ((∏ i, Real.sqrt (lam i)) / (∏ i, (1 - lam i))) := by
            rw [hsqrtH, hdet1H']; ring
  refine ⟨?_, fun hEq => ?_⟩
  · calc |DF.det| ≤ (((n : ℝ) - 1) / Real.sqrt n) ^ n
          * ((∏ i, Real.sqrt (lam i)) / (∏ i, (1 - lam i))) := hchain
      _ ≤ (((n : ℝ) - 1) / Real.sqrt n) ^ n * d ^ n :=
          mul_le_mul_of_nonneg_left hB (pow_nonneg hc n)
      _ = 1 := hcdpow
  · have hPeq : (∏ i, Real.sqrt (lam i)) / (∏ i, (1 - lam i)) = d ^ n := by
      refine le_antisymm hB ?_
      have h1le : (1 : ℝ) ≤ (((n : ℝ) - 1) / Real.sqrt n) ^ n
          * ((∏ i, Real.sqrt (lam i)) / (∏ i, (1 - lam i))) := by
        calc (1 : ℝ) = |DF.det| := hEq.symm
          _ ≤ (((n : ℝ) - 1) / Real.sqrt n) ^ n
              * ((∏ i, Real.sqrt (lam i)) / (∏ i, (1 - lam i))) := hchain
      have h2 : (((n : ℝ) - 1) / Real.sqrt n) ^ n * d ^ n
          ≤ (((n : ℝ) - 1) / Real.sqrt n) ^ n
            * ((∏ i, Real.sqrt (lam i)) / (∏ i, (1 - lam i))) := by
        rw [hcdpow]; exact h1le
      exact le_of_mul_le_mul_left h2 (pow_pos hcpos n)
    have hlam : ∀ i, lam i = 1 / (n : ℝ) := by
      rw [hd_def] at hPeq
      exact (LinAlgMatrixIneq n hn lam h0 h1 hsum).2.mp hPeq
    exact ⟨hall hlam, norm_le_of_scalar_H n hn H N DF hkey htri (hall hlam)⟩

end Work.Mostow
