import Mathlib
import Submission.Work.CR.Flat.Polydisc
import Submission.Work.CR.Flat.Cauchy.fderiv_eq_dzC_add_dbarC
import Submission.Work.CR.Flat.Cauchy.holderNorm_le_sup_of_holomorphic
import Submission.Work.CR.Flat.Polydisc.dbarCoord_comm

set_option maxHeartbeats 1000000

noncomputable section

open scoped NNReal ENNReal Topology
open Filter Metric MeasureTheory Set

namespace Work.CR.Flat.Cauchy

open Work.CR.Flat

namespace DCoordGlobal

/-! ## Slices of a holomorphic function -/

/-- The insertion continuous linear map `ℂ → ℂⁿ`, `w ↦ w · e_j`. -/
def ins {n : ℕ} (j : Fin n) : ℂ →L[ℝ] (Fin n → ℂ) :=
  ContinuousLinearMap.single ℝ (fun _ : Fin n => ℂ) j

@[simp] lemma ins_apply {n : ℕ} (j : Fin n) (w : ℂ) : ins j w = Pi.single j w :=
  congrFun (ContinuousLinearMap.single_apply ℝ (fun _ : Fin n => ℂ) j) w

lemma hasFDerivAt_update {n : ℕ} (j : Fin n) (z : Fin n → ℂ) (w : ℂ) :
    HasFDerivAt (fun t : ℂ => Function.update z j t) (ins j) w := by
  have hfun : (fun t : ℂ => Function.update z j t)
      = fun t : ℂ => Function.update z j 0 + ins j t := by
    funext t
    rw [ins_apply]
    ext i
    by_cases h : i = j <;> simp [h]
  rw [hfun]
  exact ((ins j).hasFDerivAt (x := w)).const_add (Function.update z j 0)

lemma fderiv_slice {n : ℕ} (j : Fin n) {u : (Fin n → ℂ) → ℂ} {z : Fin n → ℂ} {w : ℂ}
    (hu : DifferentiableAt ℝ u (Function.update z j w)) :
    fderiv ℝ (fun t : ℂ => u (Function.update z j t)) w
      = (fderiv ℝ u (Function.update z j w)).comp (ins j) :=
  (hu.hasFDerivAt.comp w (hasFDerivAt_update j z w)).fderiv

/-- Complex linearity of the real differential in the `j`-th coordinate direction,
from the vanishing `(0,1)`-derivative. -/
lemma fderiv_single_I_eq_mul {n : ℕ} {u : (Fin n → ℂ) → ℂ} {y : Fin n → ℂ} {j : Fin n}
    (h : dbarCoord j u y = 0) :
    fderiv ℝ u y (Pi.single j Complex.I) = Complex.I * fderiv ℝ u y (Pi.single j 1) :=
  fderiv_single_eq_mul j h Complex.I

/-- The real differential applied to `e_j` is the `(1,0)`-derivative. -/
lemma fderiv_single_one_eq_dCoord {n : ℕ} {u : (Fin n → ℂ) → ℂ} {y : Fin n → ℂ} {j : Fin n}
    (h : dbarCoord j u y = 0) :
    fderiv ℝ u y (Pi.single j (1 : ℂ)) = dCoord j u y := by
  have hB := fderiv_single_I_eq_mul (j := j) h
  rw [dCoord, hB]
  rw [show Complex.I * (Complex.I * fderiv ℝ u y (Pi.single j (1 : ℂ)))
      = - fderiv ℝ u y (Pi.single j (1 : ℂ)) by
        rw [← mul_assoc, Complex.I_mul_I, neg_one_mul]]
  ring

/-- The `(0,1)`-derivative of the `j`-th slice is the `j`-th `(0,1)`-derivative of `u`. -/
lemma dbarC_slice {n : ℕ} (j : Fin n) {u : (Fin n → ℂ) → ℂ} {z : Fin n → ℂ} {w : ℂ}
    (hu : DifferentiableAt ℝ u (Function.update z j w)) :
    dbarC (fun t : ℂ => u (Function.update z j t)) w = dbarCoord j u (Function.update z j w) := by
  simp only [dbarC, dbarCoord, fderiv_slice j hu, ContinuousLinearMap.comp_apply, ins_apply]

/-- A slice at a point where `∂̄` vanishes is complex differentiable. -/
lemma differentiableAt_complex_slice {n : ℕ} (j : Fin n) {u : (Fin n → ℂ) → ℂ}
    {z : Fin n → ℂ} {w : ℂ} (hu : DifferentiableAt ℝ u (Function.update z j w))
    (h : dbarCoord j u (Function.update z j w) = 0) :
    DifferentiableAt ℂ (fun t : ℂ => u (Function.update z j t)) w := by
  have hℝ : DifferentiableAt ℝ (fun t : ℂ => u (Function.update z j t)) w :=
    (hu.hasFDerivAt.comp w (hasFDerivAt_update j z w)).differentiableAt
  rw [differentiableAt_complex_iff_differentiableAt_real]
  refine ⟨hℝ, ?_⟩
  rw [fderiv_slice j hu, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    ins_apply, ins_apply, smul_eq_mul]
  exact fderiv_single_I_eq_mul h

/-- The complex derivative of a slice is the `(1,0)`-derivative of `u`. -/
lemma deriv_slice_eq_dCoord {n : ℕ} (j : Fin n) {u : (Fin n → ℂ) → ℂ}
    {z : Fin n → ℂ} {w : ℂ} (hu : DifferentiableAt ℝ u (Function.update z j w))
    (h : dbarCoord j u (Function.update z j w) = 0) :
    deriv (fun t : ℂ => u (Function.update z j t)) w = dCoord j u (Function.update z j w) := by
  have hcd := differentiableAt_complex_slice j hu h
  have h1 : deriv (fun t : ℂ => u (Function.update z j t)) w
      = fderiv ℝ (fun t : ℂ => u (Function.update z j t)) w 1 := by
    rw [show deriv (fun t : ℂ => u (Function.update z j t)) w
        = (fderiv ℂ (fun t : ℂ => u (Function.update z j t)) w) 1 from rfl]
    calc (fderiv ℂ (fun t : ℂ => u (Function.update z j t)) w) 1
        = ((fderiv ℂ (fun t : ℂ => u (Function.update z j t)) w).restrictScalars ℝ) 1 := rfl
      _ = (fderiv ℝ (fun t : ℂ => u (Function.update z j t)) w) 1 := by
          rw [hcd.fderiv_restrictScalars ℝ]
  rw [h1, fderiv_slice j hu, ContinuousLinearMap.comp_apply, ins_apply]
  exact fderiv_single_one_eq_dCoord h

lemma dCoord_eq_deriv_slice {n : ℕ} (j : Fin n) {u : (Fin n → ℂ) → ℂ} {y : Fin n → ℂ}
    (hu : DifferentiableAt ℝ u y) (h : dbarCoord j u y = 0) :
    dCoord j u y = deriv (fun t : ℂ => u (Function.update y j t)) (y j) := by
  have hu' : DifferentiableAt ℝ u (Function.update y j (y j)) := by
    rwa [Function.update_eq_self]
  have h' : dbarCoord j u (Function.update y j (y j)) = 0 := by
    rwa [Function.update_eq_self]
  have hmain : deriv (fun t : ℂ => u (Function.update y j t)) (y j) = dCoord j u y := by
    rw [deriv_slice_eq_dCoord j hu' h', Function.update_eq_self]
  exact hmain.symm

/-! ## The Cauchy formula for the derivative of a slice -/

lemma deriv_eq_smul_circleIntegral {R : ℝ} {c w : ℂ} {f : ℂ → ℂ}
    (hc : DiffContOnCl ℂ f (Metric.ball c R)) (hw : w ∈ Metric.ball c R) :
    (∮ z in C(c, R), (z - w) ^ (-2 : ℤ) • f z)
      = (2 * (Real.pi : ℂ) * Complex.I) • deriv f w := by
  have hR : 0 < R := lt_of_le_of_lt dist_nonneg (Metric.mem_ball.mp hw)
  have hci : CircleIntegrable f c R :=
    (hc.continuousOn_ball.mono sphere_subset_closedBall).circleIntegrable hR.le
  have hderiv : HasDerivAt (fun t : ℂ => ∮ z in C(c, R), (z - t)⁻¹ • f z)
      (∮ z in C(c, R), (z - w) ^ (-2 : ℤ) • f z) w :=
    Complex.hasDerivAt_circleIntegral_sub_inv_smul hci (by
      rw [Metric.mem_sphere, abs_of_pos hR]
      exact ne_of_lt (Metric.mem_ball.mp hw))
  have hev : (fun t : ℂ => ∮ z in C(c, R), (z - t)⁻¹ • f z)
      =ᶠ[𝓝 w] (fun t : ℂ => (2 * (Real.pi : ℂ) * Complex.I) • f t) := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hw] with t ht
    exact hc.circleIntegral_sub_inv_smul ht
  have hf2 : HasDerivAt (fun t : ℂ => (2 * (Real.pi : ℂ) * Complex.I) • f t)
      ((2 * (Real.pi : ℂ) * Complex.I) • deriv f w) w := by
    have hfd : DifferentiableAt ℂ f w := hc.differentiableAt Metric.isOpen_ball hw
    exact hfd.hasDerivAt.const_smul (2 * (Real.pi : ℂ) * Complex.I)
  rw [← hderiv.deriv, hev.deriv_eq, hf2.deriv]

lemma two_pi_I_inv_smul_circleIntegral_deriv {R : ℝ} {c w : ℂ} {f : ℂ → ℂ}
    (hc : DiffContOnCl ℂ f (Metric.ball c R)) (hw : w ∈ Metric.ball c R) :
    ((2 * (Real.pi : ℂ) * Complex.I)⁻¹) • (∮ z in C(c, R), (z - w) ^ (-2 : ℤ) • f z)
      = deriv f w := by
  have hne : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero (by norm_num) ?_) Complex.I_ne_zero
    exact_mod_cast Real.pi_ne_zero
  rw [deriv_eq_smul_circleIntegral hc hw, inv_smul_smul₀ hne]

/-- The `j`-th slice of a function which is differentiable and holomorphic on a ball is
`DiffContOnCl` on the disc centred at the `j`-th coordinate of the point itself. -/
lemma diffContOnCl_slice {n : ℕ} {u : (Fin n → ℂ) → ℂ} {j : Fin n}
    {y₀ y : Fin n → ℂ} {ρ R : ℝ} (hR : 0 < R) (hyR : ‖y - y₀‖ + R < ρ)
    (hgd : ∀ z ∈ Metric.ball y₀ ρ, DifferentiableAt ℝ u z)
    (hhol : ∀ z ∈ Metric.ball y₀ ρ, dbarCoord j u z = 0) :
    DiffContOnCl ℂ (fun t : ℂ => u (Function.update y j t)) (Metric.ball (y j) R) := by
  have hρ : 0 < ρ := by linarith [norm_nonneg (y - y₀), hR]
  refine DifferentiableOn.diffContOnCl ?_
  rw [closure_ball _ (ne_of_gt hR)]
  intro t ht
  have ht' : ‖t - y j‖ ≤ R := by
    rw [Metric.mem_closedBall, dist_eq_norm] at ht; exact ht
  have hmem : Function.update y j t ∈ Metric.ball y₀ ρ := by
    rw [Metric.mem_ball, dist_eq_norm, pi_norm_lt_iff hρ]
    intro k
    rw [Pi.sub_apply]
    by_cases hk : k = j
    · subst hk
      rw [Function.update_self]
      calc ‖t - y₀ k‖ ≤ ‖t - y k‖ + ‖y k - y₀ k‖ := by
            rw [show t - y₀ k = (t - y k) + (y k - y₀ k) by ring]
            exact norm_add_le _ _
        _ ≤ R + ‖y - y₀‖ := add_le_add ht' (norm_le_pi_norm (y - y₀) k)
        _ < ρ := by linarith
    · rw [Function.update_of_ne hk]
      exact lt_of_le_of_lt (by simpa [Pi.sub_apply] using norm_le_pi_norm (y - y₀) k)
        (by linarith [norm_nonneg (y - y₀)])
  exact (differentiableAt_complex_slice j (hgd _ hmem) (hhol _ hmem)).differentiableWithinAt

/-- The Cauchy representation of `dCoord j u` with the contour centred at `y j`. -/
lemma dCoord_eq_circleIntegral_self {n : ℕ} {j : Fin n} {u : (Fin n → ℂ) → ℂ}
    {y₀ y : Fin n → ℂ} {ρ R : ℝ} (hR : 0 < R) (hyR : ‖y - y₀‖ + R < ρ)
    (hgd : ∀ z ∈ Metric.ball y₀ ρ, DifferentiableAt ℝ u z)
    (hhol : ∀ z ∈ Metric.ball y₀ ρ, dbarCoord j u z = 0) :
    dCoord j u y = ((2 * (Real.pi : ℂ) * Complex.I)⁻¹) •
        ∮ ζ in C(y j, R), (ζ - y j) ^ (-2 : ℤ) • u (Function.update y j ζ) := by
  have hρ : 0 < ρ := by linarith [norm_nonneg (y - y₀), hR]
  have hmem : y ∈ Metric.ball y₀ ρ := by
    rw [Metric.mem_ball, dist_eq_norm]; linarith [hR]
  rw [dCoord_eq_deriv_slice j (hgd y hmem) (hhol y hmem)]
  refine (two_pi_I_inv_smul_circleIntegral_deriv (diffContOnCl_slice hR hyR hgd hhol) ?_).symm
  rw [Metric.mem_ball, dist_eq_norm, sub_self, norm_zero]; exact hR

/-! ## The parametrised integral -/

lemma circleMap_sub_center (c : ℂ) (R θ : ℝ) : circleMap c R θ - c = circleMap 0 R θ := by
  simp [circleMap]

lemma update_circleMap {n : ℕ} (j : Fin n) (y : Fin n → ℂ) (R θ : ℝ) :
    Function.update y j (circleMap (y j) R θ)
      = y + circleMap 0 R θ • (Pi.single j (1 : ℂ) : Fin n → ℂ) := by
  ext k
  by_cases hk : k = j
  · subst hk
    simp only [Pi.add_apply, Pi.smul_apply, Pi.single_eq_same, Function.update_self, circleMap,
      smul_eq_mul, mul_one]
    ring
  · rw [Function.update_of_ne hk, Pi.add_apply, Pi.smul_apply,
      Pi.single_eq_of_ne (i := j) (i' := k) hk, smul_zero, add_zero]

lemma mul_I_zpow_neg_two_mul (z w : ℂ) (hz : z ≠ 0) :
    (z * Complex.I) * (z ^ (-2 : ℤ) * w) = (Complex.I * z⁻¹) * w := by
  have h : z * z ^ (-2 : ℤ) = z⁻¹ := by
    rw [show (-2 : ℤ) = -((2 : ℕ) : ℤ) from rfl, zpow_neg, zpow_natCast, sq, mul_inv,
      ← mul_assoc, mul_inv_cancel₀ hz, one_mul]
  calc (z * Complex.I) * (z ^ (-2 : ℤ) * w)
      = (z * z ^ (-2 : ℤ)) * (Complex.I * w) := by ring
    _ = z⁻¹ * (Complex.I * w) := by rw [h]
    _ = (Complex.I * z⁻¹) * w := by ring

lemma smul_I_mul_smul (z w : ℂ) (hz : z ≠ 0) :
    (z * Complex.I) • (z ^ (-2 : ℤ) • w) = (Complex.I * z⁻¹) • w := by
  simp only [smul_eq_mul]
  exact mul_I_zpow_neg_two_mul z w hz

lemma circleIntegral_reparam {n : ℕ} (j : Fin n) (u : (Fin n → ℂ) → ℂ) {R : ℝ} (hR : R ≠ 0)
    (y : Fin n → ℂ) :
    (∮ ζ in C(y j, R), (ζ - y j) ^ (-2 : ℤ) • u (Function.update y j ζ))
      = ∫ θ in (0 : ℝ)..(2 * Real.pi),
          (Complex.I * (circleMap 0 R θ)⁻¹) *
            u (y + (circleMap 0 R θ) • (Pi.single j (1 : ℂ) : Fin n → ℂ)) := by
  rw [circleIntegral]
  refine intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
  intro hθ
  rw [deriv_circleMap, circleMap_sub_center, update_circleMap]
  exact smul_I_mul_smul _ _ (circleMap_ne_center hR)

/-- The `(1,0)`-derivative of a holomorphic function, as a parametrised integral. -/
def phi2 {n : ℕ} (j : Fin n) (u : (Fin n → ℂ) → ℂ) (R : ℝ) (y : Fin n → ℂ) : ℂ :=
  ((2 * (Real.pi : ℂ) * Complex.I)⁻¹) •
    ∫ θ in (0 : ℝ)..(2 * Real.pi),
      (Complex.I * (circleMap 0 R θ)⁻¹) *
        u (y + (circleMap 0 R θ) • (Pi.single j (1 : ℂ) : Fin n → ℂ))

lemma dCoord_eq_phi2 {n : ℕ} {j : Fin n} {u : (Fin n → ℂ) → ℂ} {y₀ y : Fin n → ℂ} {ρ R : ℝ}
    (hR : 0 < R) (hyR : ‖y - y₀‖ + R < ρ)
    (hgd : ∀ z ∈ Metric.ball y₀ ρ, DifferentiableAt ℝ u z)
    (hhol : ∀ z ∈ Metric.ball y₀ ρ, dbarCoord j u z = 0) :
    dCoord j u y = phi2 j u R y := by
  rw [dCoord_eq_circleIntegral_self hR hyR hgd hhol,
    circleIntegral_reparam j u (ne_of_gt hR) y]
  rfl


/-! ## Differentiation of the parametrised integral -/

lemma mem_ball_shift {n : ℕ} {j : Fin n} {y₀ : Fin n → ℂ} {ρ R : ℝ}
    (hR : 0 < R) (hRρ : R < ρ) (θ : ℝ) :
    y₀ + (circleMap 0 R θ) • (Pi.single j (1 : ℂ) : Fin n → ℂ) ∈ Metric.ball y₀ ρ := by
  rw [Metric.mem_ball, dist_eq_norm, pi_norm_lt_iff (lt_trans hR hRρ)]
  intro k
  rw [Pi.sub_apply, Pi.add_apply, Pi.smul_apply]
  by_cases hk : k = j
  · subst hk
    rw [Pi.single_eq_same, smul_eq_mul, mul_one, add_sub_cancel_left, norm_circleMap_zero,
      abs_of_pos hR]
    exact hRρ
  · rw [Pi.single_eq_of_ne (i := j) (i' := k) hk, smul_zero, add_zero, sub_self, norm_zero]
    exact lt_trans hR hRρ

lemma hasFDerivAt_phi2 {n : ℕ} {j : Fin n} {u : (Fin n → ℂ) → ℂ} {y₀ : Fin n → ℂ}
    {ρ R M Mg : ℝ} (hR : 0 < R) (hRρ : R < ρ)
    (hgd : ∀ z ∈ Metric.ball y₀ ρ, DifferentiableAt ℝ u z)
    (hM : ∀ z ∈ Metric.ball y₀ ρ, ‖fderiv ℝ u z‖ ≤ M)
    (hgM : ∀ z ∈ Metric.ball y₀ ρ, ‖u z‖ ≤ Mg) :
    HasFDerivAt (phi2 j u R)
      (((2 * (Real.pi : ℂ) * Complex.I)⁻¹) •
        ∫ θ in (0 : ℝ)..(2 * Real.pi),
          (Complex.I * (circleMap 0 R θ)⁻¹) •
            fderiv ℝ u (y₀ + (circleMap 0 R θ) • (Pi.single j (1 : ℂ) : Fin n → ℂ))) y₀ := by
  set σ : ℝ := min R (ρ - R) / 2 with hσ
  have hσpos : 0 < σ := by
    rw [hσ]; exact div_pos (lt_min hR (by linarith)) (by norm_num)
  have hσltρ : σ + R < ρ := by
    rw [hσ]; have := min_le_right R (ρ - R); linarith
  have hρpos : 0 < ρ := lt_trans hR hRρ
  have hgc : ContinuousOn u (Metric.ball y₀ ρ) :=
    fun z hz => (hgd z hz).continuousAt.continuousWithinAt
  have hcont_shift : ∀ y : Fin n → ℂ, Continuous fun θ : ℝ =>
      y + (circleMap 0 R θ) • (Pi.single j (1 : ℂ) : Fin n → ℂ) :=
    fun y => continuous_const.add ((continuous_circleMap 0 R).smul continuous_const)
  have hmem : ∀ y ∈ Metric.ball y₀ σ, ∀ θ : ℝ,
      y + (circleMap 0 R θ) • (Pi.single j (1 : ℂ) : Fin n → ℂ) ∈ Metric.ball y₀ ρ := by
    intro y hy θ
    have hy' : ‖y - y₀‖ < σ := by rwa [Metric.mem_ball, dist_eq_norm] at hy
    have hsub : y + (circleMap 0 R θ) • (Pi.single j (1 : ℂ) : Fin n → ℂ) - y₀
        = (y - y₀) + (circleMap 0 R θ) • (Pi.single j (1 : ℂ) : Fin n → ℂ) := by abel
    rw [Metric.mem_ball, dist_eq_norm, hsub, pi_norm_lt_iff hρpos]
    intro k
    rw [Pi.add_apply, Pi.smul_apply]
    by_cases hk : k = j
    · subst hk
      rw [Pi.single_eq_same, smul_eq_mul, mul_one]
      have hle : ‖y k - y₀ k‖ ≤ ‖y - y₀‖ := by
        have h := norm_le_pi_norm (y - y₀) k
        rwa [Pi.sub_apply] at h
      calc ‖(y k - y₀ k) + circleMap 0 R θ‖
          ≤ ‖y k - y₀ k‖ + ‖circleMap 0 R θ‖ := norm_add_le _ _
        _ = ‖y k - y₀ k‖ + R := by rw [norm_circleMap_zero, abs_of_pos hR]
        _ ≤ ‖y - y₀‖ + R := by linarith
        _ < σ + R := by linarith
        _ < ρ := hσltρ
    · rw [Pi.single_eq_of_ne (i := j) (i' := k) hk, smul_zero, add_zero]
      have hle : ‖y k - y₀ k‖ ≤ ‖y - y₀‖ := by
        have h := norm_le_pi_norm (y - y₀) k
        rwa [Pi.sub_apply] at h
      exact lt_of_le_of_lt hle (lt_trans hy' (by linarith))
  have hcontF : ∀ y ∈ Metric.ball y₀ σ, ContinuousOn
      (fun θ : ℝ => (Complex.I * (circleMap 0 R θ)⁻¹) *
        u (y + (circleMap 0 R θ) • (Pi.single j (1 : ℂ) : Fin n → ℂ)))
      (Set.uIcc 0 (2 * Real.pi)) := by
    intro y hy
    have h1 : ContinuousOn (fun θ : ℝ => Complex.I * (circleMap 0 R θ)⁻¹)
        (Set.uIcc 0 (2 * Real.pi)) :=
      continuousOn_const.mul (((continuous_circleMap 0 R).continuousOn).inv₀
        (fun θ _ => circleMap_ne_center (ne_of_gt hR)))
    have h2 : ContinuousOn (fun θ : ℝ =>
        u (y + (circleMap 0 R θ) • (Pi.single j (1 : ℂ) : Fin n → ℂ)))
        (Set.uIcc 0 (2 * Real.pi)) :=
      (hgc.comp_continuous (hcont_shift y) (fun θ => hmem y hy θ)).continuousOn
    exact h1.mul h2
  have hmain : HasFDerivAt
      (fun y : Fin n → ℂ => ∫ θ in (0 : ℝ)..(2 * Real.pi),
        (Complex.I * (circleMap 0 R θ)⁻¹) *
          u (y + (circleMap 0 R θ) • (Pi.single j (1 : ℂ) : Fin n → ℂ)))
      (∫ θ in (0 : ℝ)..(2 * Real.pi),
        (Complex.I * (circleMap 0 R θ)⁻¹) •
          fderiv ℝ u (y₀ + (circleMap 0 R θ) • (Pi.single j (1 : ℂ) : Fin n → ℂ))) y₀ := by
    refine intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le
      (𝕜 := ℝ) (μ := volume)
      (F := fun y θ => (Complex.I * (circleMap 0 R θ)⁻¹) *
        u (y + (circleMap 0 R θ) • (Pi.single j (1 : ℂ) : Fin n → ℂ)))
      (F' := fun y θ => (Complex.I * (circleMap 0 R θ)⁻¹) •
        fderiv ℝ u (y + (circleMap 0 R θ) • (Pi.single j (1 : ℂ) : Fin n → ℂ)))
      (bound := fun _ => M / R) (s := Metric.ball y₀ σ) (x₀ := y₀) (a := 0)
      (b := 2 * Real.pi)
      (Metric.ball_mem_nhds y₀ hσpos) ?_ ?_ ?_ ?_ ?_ ?_
    · filter_upwards [Metric.ball_mem_nhds y₀ hσpos] with y hy
      exact ((hcontF y hy).mono Set.uIoc_subset_uIcc).aestronglyMeasurable measurableSet_uIoc
    · exact (hcontF y₀ (Metric.mem_ball_self hσpos)).intervalIntegrable
    · refine Measurable.aestronglyMeasurable ?_
      have h1 : Measurable fun θ : ℝ => Complex.I * (circleMap 0 R θ)⁻¹ :=
        measurable_const.mul ((continuous_circleMap 0 R).measurable.inv)
      have h2 : Measurable fun θ : ℝ =>
          fderiv ℝ u (y₀ + (circleMap 0 R θ) • (Pi.single j (1 : ℂ) : Fin n → ℂ)) :=
        (measurable_fderiv ℝ u).comp (hcont_shift y₀).measurable
      exact h1.smul h2
    · refine Filter.Eventually.of_forall fun θ hθ y hy => ?_
      calc ‖(Complex.I * (circleMap 0 R θ)⁻¹) •
              fderiv ℝ u (y + (circleMap 0 R θ) • (Pi.single j (1 : ℂ) : Fin n → ℂ))‖
          = ‖Complex.I * (circleMap 0 R θ)⁻¹‖ *
              ‖fderiv ℝ u (y + (circleMap 0 R θ) • (Pi.single j (1 : ℂ) : Fin n → ℂ))‖ :=
            norm_smul _ _
        _ = R⁻¹ * ‖fderiv ℝ u (y + (circleMap 0 R θ) • (Pi.single j (1 : ℂ) : Fin n → ℂ))‖ := by
            rw [norm_mul, Complex.norm_I, one_mul, norm_inv, norm_circleMap_zero, abs_of_pos hR]
        _ ≤ R⁻¹ * M := mul_le_mul_of_nonneg_left (hM _ (hmem y hy θ)) (by positivity)
        _ = M / R := by rw [div_eq_inv_mul]
    · exact continuousOn_const.intervalIntegrable
    · refine Filter.Eventually.of_forall fun θ hθ y hy => ?_
      have h1 : HasFDerivAt (fun y : Fin n → ℂ =>
            y + (circleMap 0 R θ) • (Pi.single j (1 : ℂ) : Fin n → ℂ))
          (ContinuousLinearMap.id ℝ (Fin n → ℂ)) y := (hasFDerivAt_id y).add_const _
      have h2 : HasFDerivAt (fun y : Fin n → ℂ =>
            u (y + (circleMap 0 R θ) • (Pi.single j (1 : ℂ) : Fin n → ℂ)))
          (fderiv ℝ u (y + (circleMap 0 R θ) • (Pi.single j (1 : ℂ) : Fin n → ℂ))) y := by
        have h := ((hgd _ (hmem y hy θ)).hasFDerivAt).comp y h1
        rwa [ContinuousLinearMap.comp_id] at h
      exact h2.const_smul (Complex.I * (circleMap 0 R θ)⁻¹)
  have hfun : phi2 j u R = fun y : Fin n → ℂ =>
      ((2 * (Real.pi : ℂ) * Complex.I)⁻¹) •
        ∫ θ in (0 : ℝ)..(2 * Real.pi),
          (Complex.I * (circleMap 0 R θ)⁻¹) *
            u (y + (circleMap 0 R θ) • (Pi.single j (1 : ℂ) : Fin n → ℂ)) := rfl
  rw [hfun]
  exact hmain.const_smul ((2 * (Real.pi : ℂ) * Complex.I)⁻¹)

lemma phi2_fderiv_eq {n : ℕ} {j : Fin n} {u : (Fin n → ℂ) → ℂ} {y₀ : Fin n → ℂ}
    {ρ R M Mg : ℝ} (hR : 0 < R) (hRρ : R < ρ)
    (hgd : ∀ z ∈ Metric.ball y₀ ρ, DifferentiableAt ℝ u z)
    (hM : ∀ z ∈ Metric.ball y₀ ρ, ‖fderiv ℝ u z‖ ≤ M)
    (hgM : ∀ z ∈ Metric.ball y₀ ρ, ‖u z‖ ≤ Mg) :
    fderiv ℝ (phi2 j u R) y₀ =
      ((2 * (Real.pi : ℂ) * Complex.I)⁻¹) •
        ∫ θ in (0 : ℝ)..(2 * Real.pi),
          (Complex.I * (circleMap 0 R θ)⁻¹) •
            fderiv ℝ u (y₀ + (circleMap 0 R θ) • (Pi.single j (1 : ℂ) : Fin n → ℂ)) :=
  (hasFDerivAt_phi2 hR hRρ hgd hM hgM).fderiv

/-! ## Continuity of the derivative, and complex linearity -/

lemma intervalIntegrable_phi2_deriv {n : ℕ} {j : Fin n} {u : (Fin n → ℂ) → ℂ}
    {y₀ : Fin n → ℂ} {ρ R : ℝ} (hR : 0 < R) (hRρ : R < ρ)
    (hgc : ContinuousOn (fderiv ℝ u) (Metric.ball y₀ ρ)) :
    IntervalIntegrable (fun θ : ℝ => (Complex.I * (circleMap 0 R θ)⁻¹ : ℂ) •
      fderiv ℝ u (y₀ + (circleMap 0 R θ) • (Pi.single j (1 : ℂ) : Fin n → ℂ))) volume
      0 (2 * Real.pi) := by
  refine ContinuousOn.intervalIntegrable ?_
  have h1 : ContinuousOn (fun θ : ℝ => (Complex.I * (circleMap 0 R θ)⁻¹ : ℂ))
      (Set.uIcc 0 (2 * Real.pi)) :=
    continuousOn_const.mul (((continuous_circleMap 0 R).continuousOn).inv₀
      (fun θ _ => circleMap_ne_center (ne_of_gt hR)))
  have h2 : ContinuousOn (fun θ : ℝ =>
      fderiv ℝ u (y₀ + (circleMap 0 R θ) • (Pi.single j (1 : ℂ) : Fin n → ℂ)))
      (Set.uIcc 0 (2 * Real.pi)) :=
    hgc.comp ((continuous_const.add
      ((continuous_circleMap 0 R).smul continuous_const)).continuousOn)
      (fun θ _ => mem_ball_shift hR hRρ θ)
  exact h1.smul h2

lemma fderiv_integral_smul_I {n : ℕ} {j : Fin n} {u : (Fin n → ℂ) → ℂ} {y₀ : Fin n → ℂ}
    {ρ R : ℝ} (hR : 0 < R) (hRρ : R < ρ)
    (hgc : ContinuousOn (fderiv ℝ u) (Metric.ball y₀ ρ))
    (hhol : ∀ k, ∀ z ∈ Metric.ball y₀ ρ, dbarCoord k u z = 0) (v : Fin n → ℂ) :
    (∫ θ in (0 : ℝ)..(2 * Real.pi), (Complex.I * (circleMap 0 R θ)⁻¹) •
        fderiv ℝ u (y₀ + (circleMap 0 R θ) • (Pi.single j (1 : ℂ) : Fin n → ℂ)))
      (Complex.I • v)
      = Complex.I * (∫ θ in (0 : ℝ)..(2 * Real.pi), (Complex.I * (circleMap 0 R θ)⁻¹) •
        fderiv ℝ u (y₀ + (circleMap 0 R θ) • (Pi.single j (1 : ℂ) : Fin n → ℂ))) v := by
  have hint := intervalIntegrable_phi2_deriv (j := j) hR hRρ hgc
  rw [ContinuousLinearMap.intervalIntegral_apply hint]
  rw [show (fun θ : ℝ => ((Complex.I * (circleMap 0 R θ)⁻¹) •
        fderiv ℝ u (y₀ + (circleMap 0 R θ) • (Pi.single j (1 : ℂ) : Fin n → ℂ)))
          (Complex.I • v))
      = fun θ : ℝ => Complex.I * (((Complex.I * (circleMap 0 R θ)⁻¹) •
        fderiv ℝ u (y₀ + (circleMap 0 R θ) • (Pi.single j (1 : ℂ) : Fin n → ℂ))) v) from by
        funext θ
        rw [ContinuousLinearMap.smul_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
          smul_eq_mul]
        rw [show fderiv ℝ u (y₀ + (circleMap 0 R θ) • (Pi.single j (1 : ℂ) : Fin n → ℂ))
              (Complex.I • v)
            = Complex.I * fderiv ℝ u
                (y₀ + (circleMap 0 R θ) • (Pi.single j (1 : ℂ) : Fin n → ℂ)) v from
              fderiv_smul_I (u := u)
                (y := y₀ + (circleMap 0 R θ) • (Pi.single j (1 : ℂ) : Fin n → ℂ))
                (fun k => hhol k _ (mem_ball_shift hR hRρ θ)) v]
        ring]
  rw [intervalIntegral.integral_const_mul]
  rw [ContinuousLinearMap.intervalIntegral_apply hint]

lemma continuousOn_phi2_fderiv {n : ℕ} {j : Fin n} {u : (Fin n → ℂ) → ℂ} {c : Fin n → ℂ}
    {ρ R M : ℝ} (hR : 0 < R) (hRρ : R < ρ)
    (hgd : ∀ z ∈ Metric.ball c ρ, DifferentiableAt ℝ u z)
    (hgc : ContinuousOn (fderiv ℝ u) (Metric.ball c ρ))
    (hM : ∀ z ∈ Metric.ball c ρ, ‖fderiv ℝ u z‖ ≤ M) :
    ContinuousOn (fun y : Fin n → ℂ =>
      ∫ θ in (0 : ℝ)..(2 * Real.pi),
        (Complex.I * (circleMap 0 R θ)⁻¹) •
          fderiv ℝ u (y + (circleMap 0 R θ) • (Pi.single j (1 : ℂ) : Fin n → ℂ)))
      (Metric.ball c (ρ - R)) := by
  have hρpos : 0 < ρ := lt_trans hR hRρ
  intro y hy
  have hmem : ∀ z ∈ Metric.ball c (ρ - R), ∀ θ : ℝ,
      z + (circleMap 0 R θ) • (Pi.single j (1 : ℂ) : Fin n → ℂ) ∈ Metric.ball c ρ := by
    intro z hz θ
    have hz' : ‖z - c‖ < ρ - R := by rwa [Metric.mem_ball, dist_eq_norm] at hz
    have hsub : z + (circleMap 0 R θ) • (Pi.single j (1 : ℂ) : Fin n → ℂ) - c
        = (z - c) + (circleMap 0 R θ) • (Pi.single j (1 : ℂ) : Fin n → ℂ) := by abel
    rw [Metric.mem_ball, dist_eq_norm, hsub, pi_norm_lt_iff hρpos]
    intro k
    rw [Pi.add_apply, Pi.smul_apply]
    by_cases hk : k = j
    · subst hk
      rw [Pi.single_eq_same, smul_eq_mul, mul_one]
      have hle : ‖z k - c k‖ ≤ ‖z - c‖ := by
        have h := norm_le_pi_norm (z - c) k
        rwa [Pi.sub_apply] at h
      calc ‖(z k - c k) + circleMap 0 R θ‖
          ≤ ‖z k - c k‖ + ‖circleMap 0 R θ‖ := norm_add_le _ _
        _ = ‖z k - c k‖ + R := by rw [norm_circleMap_zero, abs_of_pos hR]
        _ ≤ ‖z - c‖ + R := by linarith
        _ < (ρ - R) + R := by linarith
        _ = ρ := by ring
    · rw [Pi.single_eq_of_ne (i := j) (i' := k) hk, smul_zero, add_zero]
      have hle : ‖z k - c k‖ ≤ ‖z - c‖ := by
        have h := norm_le_pi_norm (z - c) k
        rwa [Pi.sub_apply] at h
      exact lt_of_le_of_lt hle (lt_of_lt_of_le hz' (by linarith))
  have hcont_coeff : ContinuousOn (fun θ : ℝ => Complex.I * (circleMap 0 R θ)⁻¹)
      (Set.uIcc 0 (2 * Real.pi)) :=
    continuousOn_const.mul (((continuous_circleMap 0 R).continuousOn).inv₀
      (fun θ _ => circleMap_ne_center (ne_of_gt hR)))
  refine intervalIntegral.continuousWithinAt_of_dominated_interval
    (F := fun z θ => (Complex.I * (circleMap 0 R θ)⁻¹) •
      fderiv ℝ u (z + (circleMap 0 R θ) • (Pi.single j (1 : ℂ) : Fin n → ℂ)))
    (bound := fun _ => M / R) (s := Metric.ball c (ρ - R)) (x₀ := y) ?_ ?_ ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with z hz
    have hcontθ : ContinuousOn (fun θ : ℝ => (Complex.I * (circleMap 0 R θ)⁻¹) •
        fderiv ℝ u (z + (circleMap 0 R θ) • (Pi.single j (1 : ℂ) : Fin n → ℂ)))
        (Set.uIoc 0 (2 * Real.pi)) :=
      (hcont_coeff.smul (hgc.comp
        ((continuous_const.add ((continuous_circleMap 0 R).smul continuous_const)).continuousOn)
        (fun θ _ => hmem z hz θ))).mono Set.uIoc_subset_uIcc
    exact hcontθ.aestronglyMeasurable measurableSet_uIoc
  · filter_upwards [self_mem_nhdsWithin] with z hz
    filter_upwards with t ht
    calc ‖(Complex.I * (circleMap 0 R t)⁻¹) •
            fderiv ℝ u (z + (circleMap 0 R t) • (Pi.single j (1 : ℂ) : Fin n → ℂ))‖
        = ‖Complex.I * (circleMap 0 R t)⁻¹‖ *
            ‖fderiv ℝ u (z + (circleMap 0 R t) • (Pi.single j (1 : ℂ) : Fin n → ℂ))‖ :=
          norm_smul _ _
      _ = R⁻¹ * ‖fderiv ℝ u (z + (circleMap 0 R t) • (Pi.single j (1 : ℂ) : Fin n → ℂ))‖ := by
          rw [norm_mul, Complex.norm_I, one_mul, norm_inv, norm_circleMap_zero, abs_of_pos hR]
      _ ≤ R⁻¹ * M := mul_le_mul_of_nonneg_left (hM _ (hmem z hz t)) (by positivity)
      _ = M / R := by rw [div_eq_inv_mul]
  · exact continuousOn_const.intervalIntegrable
  · filter_upwards with t ht
    have hshift : ContinuousWithinAt (fun z : Fin n → ℂ =>
        z + (circleMap 0 R t) • (Pi.single j (1 : ℂ) : Fin n → ℂ))
        (Metric.ball c (ρ - R)) y :=
      (continuous_id.add continuous_const).continuousAt.continuousWithinAt
    have hca : ContinuousAt (fderiv ℝ u)
        (y + (circleMap 0 R t) • (Pi.single j (1 : ℂ) : Fin n → ℂ)) :=
      hgc.continuousAt (Metric.isOpen_ball.mem_nhds (hmem y hy t))
    have h1 : ContinuousWithinAt (fun z : Fin n → ℂ => fderiv ℝ u
        (z + (circleMap 0 R t) • (Pi.single j (1 : ℂ) : Fin n → ℂ)))
        (Metric.ball c (ρ - R)) y :=
      ContinuousAt.comp_continuousWithinAt
        (f := fun z : Fin n → ℂ => z + (circleMap 0 R t) • (Pi.single j (1 : ℂ) : Fin n → ℂ))
        (x := y) hca hshift
    exact h1.const_smul (Complex.I * (circleMap 0 R t)⁻¹)

/-! ## The local step -/

lemma local_step {n : ℕ} {Ω : Set (Fin n → ℂ)} {g : (Fin n → ℂ) → ℂ} (hΩ : IsOpen Ω)
    (hg : ContDiffOn ℝ 1 g Ω) (hhol : ∀ j, ∀ z ∈ Ω, dbarCoord j g z = 0)
    {z₀ : Fin n → ℂ} {ρ : ℝ} (hρ : 0 < ρ) (hball : Metric.ball z₀ ρ ⊆ Ω) (j : Fin n) :
    ContDiffAt ℝ 1 (fun z => dCoord j g z) z₀ ∧
      (∀ k, dbarCoord k (fun z => dCoord j g z) z₀ = 0) := by
  have hgdΩ : ∀ z ∈ Ω, DifferentiableAt ℝ g z := fun z hz =>
    (hg.differentiableOn (by norm_num)).differentiableAt (hΩ.mem_nhds hz)
  have hfderivΩ : ContinuousOn (fun z => fderiv ℝ g z) Ω :=
    (hg.fderiv_of_isOpen (m := (0 : WithTop ℕ∞)) hΩ (by norm_num)).continuousOn
  have hKsub : Metric.closedBall z₀ (ρ / 2) ⊆ Ω := fun z hz => hball (by
    rw [Metric.mem_closedBall, dist_eq_norm] at hz
    rw [Metric.mem_ball, dist_eq_norm]; linarith)
  obtain ⟨M, hM⟩ := (isCompact_closedBall z₀ (ρ / 2)).exists_bound_of_continuousOn
    (hfderivΩ.mono hKsub)
  obtain ⟨Mg, hMg⟩ := (isCompact_closedBall z₀ (ρ / 2)).exists_bound_of_continuousOn
    (hg.continuousOn.mono hKsub)
  have hgdρ : ∀ z ∈ Metric.ball z₀ ρ, DifferentiableAt ℝ g z := fun z hz => hgdΩ z (hball hz)
  have hholρ : ∀ z ∈ Metric.ball z₀ ρ, dbarCoord j g z = 0 := fun z hz => hhol j z (hball hz)
  set R : ℝ := ρ / 16 with hRdef
  have hRpos : 0 < R := by rw [hRdef]; linarith
  have hR4 : R < ρ / 4 := by rw [hRdef]; linarith
  have hball4 : Metric.ball z₀ (ρ / 4) ⊆ Ω := fun z hz =>
    hball (Metric.ball_subset_ball (by linarith) hz)
  have hgd4 : ∀ z ∈ Metric.ball z₀ (ρ / 4), DifferentiableAt ℝ g z :=
    fun z hz => hgdΩ z (hball4 hz)
  have hhol4 : ∀ z ∈ Metric.ball z₀ (ρ / 4), dbarCoord j g z = 0 :=
    fun z hz => hhol j z (hball4 hz)
  have hgc4 : ContinuousOn (fderiv ℝ g) (Metric.ball z₀ (ρ / 4)) := hfderivΩ.mono hball4
  have h44 : Metric.ball z₀ (ρ / 4) ⊆ Metric.closedBall z₀ (ρ / 2) := by
    intro z hz
    rw [Metric.mem_ball, dist_eq_norm] at hz
    rw [Metric.mem_closedBall, dist_eq_norm]; linarith
  have hM4 : ∀ z ∈ Metric.ball z₀ (ρ / 4), ‖fderiv ℝ g z‖ ≤ M := fun z hz => hM z (h44 hz)
  have hRsub : Metric.ball z₀ R ⊆ Metric.ball z₀ (ρ / 4 - R) := by
    apply Metric.ball_subset_ball; rw [hRdef]; linarith
  have hderiv_eq : ∀ y ∈ Metric.ball z₀ R,
      HasFDerivAt (phi2 j g R)
        (((2 * (Real.pi : ℂ) * Complex.I)⁻¹) •
          ∫ θ in (0 : ℝ)..(2 * Real.pi), (Complex.I * (circleMap 0 R θ)⁻¹) •
            fderiv ℝ g (y + (circleMap 0 R θ) • (Pi.single j (1 : ℂ) : Fin n → ℂ))) y := by
    intro y hy
    have hyR : ‖y - z₀‖ < R := by
      rw [Metric.mem_ball, dist_eq_norm] at hy; exact hy
    have hsub4 : Metric.ball y (ρ / 4) ⊆ Metric.closedBall z₀ (ρ / 2) := by
      intro z hz
      rw [Metric.mem_ball, dist_eq_norm] at hz
      rw [Metric.mem_closedBall, dist_eq_norm]
      have h2 : ‖z - z₀‖ ≤ ‖z - y‖ + ‖y - z₀‖ := by
        rw [show z - z₀ = (z - y) + (y - z₀) by ring]; exact norm_add_le _ _
      rw [hRdef] at hyR; linarith
    exact hasFDerivAt_phi2 (j := j) (u := g) (y₀ := y) (ρ := ρ / 4) (R := R) (M := M)
      (Mg := Mg) hRpos hR4 (fun z hz => hgdΩ z (hKsub (hsub4 hz)))
      (fun z hz => hM z (hsub4 hz)) (fun z hz => hMg z (hsub4 hz))
  have hEqOn : ∀ y ∈ Metric.ball z₀ R, (fun z => dCoord j g z) =ᶠ[𝓝 y] phi2 j g R := by
    intro y hy
    filter_upwards [Metric.isOpen_ball.mem_nhds hy] with z hz
    have hzR : ‖z - z₀‖ + R < ρ := by
      rw [Metric.mem_ball, dist_eq_norm] at hz
      rw [hRdef] at *; linarith
    exact dCoord_eq_phi2 (j := j) (u := g) (y₀ := z₀) (y := z) (ρ := ρ) (R := R)
      hRpos hzR hgdρ hholρ
  have hcontA : ContinuousOn (fun y : Fin n → ℂ =>
      ∫ θ in (0 : ℝ)..(2 * Real.pi), (Complex.I * (circleMap 0 R θ)⁻¹) •
        fderiv ℝ g (y + (circleMap 0 R θ) • (Pi.single j (1 : ℂ) : Fin n → ℂ)))
      (Metric.ball z₀ (ρ / 4 - R)) :=
    continuousOn_phi2_fderiv (j := j) (u := g) (c := z₀) (ρ := ρ / 4) (R := R) (M := M)
      hRpos hR4 hgd4 hgc4 hM4
  have hz₀R : z₀ ∈ Metric.ball z₀ R := Metric.mem_ball_self hRpos
  have hhol4all : ∀ k, ∀ z ∈ Metric.ball z₀ (ρ / 4), dbarCoord k g z = 0 :=
    fun k z hz => hhol k z (hball4 hz)
  have hlin := fderiv_integral_smul_I (j := j) (u := g) (y₀ := z₀) (ρ := ρ / 4) (R := R)
    hRpos hR4 hgc4 hhol4all
  refine ⟨?_, ?_⟩
  · refine contDiffAt_one_iff.mpr ⟨fun y => ((2 * (Real.pi : ℂ) * Complex.I)⁻¹) •
        (∫ θ in (0 : ℝ)..(2 * Real.pi), (Complex.I * (circleMap 0 R θ)⁻¹) •
          fderiv ℝ g (y + (circleMap 0 R θ) • (Pi.single j (1 : ℂ) : Fin n → ℂ))),
      Metric.ball z₀ R, Metric.isOpen_ball.mem_nhds hz₀R, ?_, ?_⟩
    · exact (hcontA.mono hRsub).const_smul ((2 * (Real.pi : ℂ) * Complex.I)⁻¹)
    · intro y hy
      exact (hderiv_eq y hy).congr_of_eventuallyEq (hEqOn y hy)
  · intro k
    set G : (Fin n → ℂ) →L[ℝ] ℂ :=
      ∫ θ in (0 : ℝ)..(2 * Real.pi), (Complex.I * (circleMap 0 R θ)⁻¹) •
        fderiv ℝ g (z₀ + (circleMap 0 R θ) • (Pi.single j (1 : ℂ) : Fin n → ℂ)) with hG
    have hfd : fderiv ℝ (fun z => dCoord j g z) z₀
        = ((2 * (Real.pi : ℂ) * Complex.I)⁻¹) • G := by
      rw [hG]
      exact ((hderiv_eq z₀ hz₀R).congr_of_eventuallyEq (hEqOn z₀ hz₀R)).fderiv
    have hlinG : G (Complex.I • (Pi.single k (1 : ℂ))) = Complex.I * G (Pi.single k (1 : ℂ)) := by
      rw [hG]; exact hlin (Pi.single k (1 : ℂ))
    have hsingle : (Pi.single k (Complex.I) : Fin n → ℂ)
        = Complex.I • (Pi.single k (1 : ℂ) : Fin n → ℂ) := by
      ext i
      by_cases hi : i = k
      · subst hi; simp
      · rw [Pi.single_eq_of_ne (i := k) (i' := i) hi, Pi.smul_apply,
          Pi.single_eq_of_ne (i := k) (i' := i) hi, smul_zero]
    rw [dbarCoord, hfd, hsingle]
    simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
    rw [hlinG]
    set Gp : ℂ := G (Pi.single k (1 : ℂ)) with hGp
    have key : ∀ B : ℂ, (1 / 2 : ℂ) * (B + Complex.I * (Complex.I * B)) = 0 := by
      intro B
      rw [show Complex.I * (Complex.I * B) = -B by
        rw [← mul_assoc, Complex.I_mul_I, neg_one_mul]]
      ring
    have hconv : Complex.I * (((2 * (Real.pi : ℂ) * Complex.I)⁻¹) * (Complex.I * Gp))
        = Complex.I * (Complex.I * (((2 * (Real.pi : ℂ) * Complex.I)⁻¹) * Gp)) := by ring
    rw [hconv]
    exact key _

end DCoordGlobal

/-- **The elliptic-regularity step**: on an open set, the `(1,0)`-derivative `∂_j g = dCoord j g`
of a `C¹` holomorphic function `g` is again `C¹` and again holomorphic.

This is the `step` input required by `Work.CR.Flat.Holder.contDiffOn_holomorphic_of_step`
(module `Submission.Work.CR.Flat.Holder.contDiffOn_holomorphic_of_step`), which together with
`Work.CR.Flat.Holder.contDiffOn_succ_of_wirtinger` (module
`Submission.Work.CR.Flat.Holder.contDiffOn_succ_of_wirtinger`) yields the smoothness upgrade
"`C¹` holomorphic ⟹ `C^N` for every `N`".

The proof is local: on a small ball around each point the slice Cauchy integral formula exhibits
`dCoord j g` as a parametrised integral whose parameter derivative exists and is continuous, so
`ContDiffAt ℝ 1` and the vanishing of `∂̄_k` hold pointwise; `ContDiffOn` is local. -/
theorem dCoord_contDiffOn_one_of_holomorphic_global {n : ℕ} {Ω : Set (Fin n → ℂ)}
    (hΩ : IsOpen Ω) {g : (Fin n → ℂ) → ℂ} (hg : ContDiffOn ℝ 1 g Ω)
    (hhol : ∀ j, ∀ z ∈ Ω, Work.CR.Flat.dbarCoord j g z = 0) (j : Fin n) :
    ContDiffOn ℝ 1 (fun z => Work.CR.Flat.dCoord j g z) Ω ∧
      (∀ k, ∀ z ∈ Ω, Work.CR.Flat.dbarCoord k (fun z => Work.CR.Flat.dCoord j g z) z = 0) := by
  have hstep : ∀ z₀ ∈ Ω, ContDiffAt ℝ 1 (fun z => dCoord j g z) z₀ ∧
      (∀ k, dbarCoord k (fun z => dCoord j g z) z₀ = 0) := by
    intro z₀ hz₀
    obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.mp hΩ z₀ hz₀
    exact DCoordGlobal.local_step hΩ hg hhol hρ hball j
  exact ⟨(IsOpen.contDiffOn_iff hΩ).mpr (fun z hz => (hstep z hz).1),
    fun k z hz => (hstep z hz).2 k⟩

end Work.CR.Flat.Cauchy
