import Mathlib
import Submission.Work.NN.Newton.pushforward_setup
import Submission.Work.NN.Newton.holderNorm_one_le_of_pointwise_bounds
import Submission.Work.NN.Newton.DvCLM_data_le
import Submission.Work.CR.Flat.Holder
import Submission.Work.NN.Core.CnPert

/-!
# `C^{1,α}` bounds for the inverse family `Minv v z = (1 - dv(z))⁻¹`

The main result of this file is `Work.NN.Newton.Minv_holderNorm_one_le`: if the correction
`v : Fin n → ℂⁿ → ℂ` is smooth on the polydisc `Pd n R` with `holderNorm 2 α v ≤ b` for a
small `b ≤ 1/8`, then for every `w` with `‖w‖ ≤ 1` and every coordinate `k`, the function

  `z ↦ (Minv v z w) k`,  where `Minv v z = (1 - DvCLM v z)⁻¹`,

is `C¹` on `Pd n R` and has `holderNorm 1 α ≤ 1024`.

The proof is a general statement about the map `z ↦ Ring.inverse (1 - A z)` for a family of
continuous linear endomorphisms `A` that is `C¹`, small (`‖A z‖ ≤ b`), Hölder (`‖A x - A y‖ ≤
b ‖x - y‖^α`) and whose derivative is small and Hölder:

* Since `‖A z‖ < 1`, `1 - A z` is a unit of the Banach algebra `ℂⁿ →L[ℝ] ℂⁿ`, its inverse is
  the sum of the geometric series `∑' i, (A z)^i`, and `‖(1 - A z)⁻¹‖ ≤ (1 - b)⁻¹ ≤ 2`.
* The resolvent identity `(1 - A x)⁻¹ - (1 - A y)⁻¹ = (1 - A x)⁻¹ (A x - A y) (1 - A y)⁻¹`
  together with `‖A x - A y‖ ≤ b‖x - y‖^α` makes `z ↦ (1 - A z)⁻¹` Hölder of order `α`.
* The derivative of `z ↦ (1 - A z)⁻¹` is `-L ∘ (dA)`, where `L = mulLeftRight (M z) (M z)`
  is (left- and right-)multiplication by `(1 - A z)⁻¹`; differentiating once more, the difference
  of derivatives at `x` and `y` is bounded by `(16 b² + 4 b) ‖x - y‖^α`.

The last estimate gives the `C^{1,α}` bound `12` for the `C¹`-data `(M₀, M₁, M₂) = (2, 1, 2)`
through `holderNorm_one_le_of_pointwise_bounds`; the constant `1024` of the statement is far
larger than needed.
-/

set_option maxHeartbeats 4000000

noncomputable section

open scoped NNReal ENNReal ContDiff
open Set ContinuousLinearMap

namespace Work.NN.Newton

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

/-- The inverse family `z ↦ (1 - A z)⁻¹` in the Banach algebra `X →L[ℝ] X`. -/
def Mfam (A : X → (X →L[ℝ] X)) (z : X) : X →L[ℝ] X := Ring.inverse (1 - A z)

/-- The derivative of `A`, with a sign: `-(fderiv ℝ A z)`. -/
def Efam (A : X → (X →L[ℝ] X)) (z : X) : X →L[ℝ] (X →L[ℝ] X) := -(fderiv ℝ A z)

/-- Left-and-right multiplication by `(1 - A z)⁻¹`, the derivative of `Ring.inverse` at `1 - A z`. -/
def Kfam (A : X → (X →L[ℝ] X)) (z : X) : (X →L[ℝ] X) →L[ℝ] (X →L[ℝ] X) :=
  -(mulLeftRight ℝ (X →L[ℝ] X) (Mfam A z) (Mfam A z))

/-- The derivative of the scalar function `z ↦ Pw ((1 - A z)⁻¹)`. -/
def Dfam (A : X → (X →L[ℝ] X)) (Pw : (X →L[ℝ] X) →L[ℝ] ℂ) (z : X) : X →L[ℝ] ℂ :=
  Pw ∘SL (Kfam A z ∘SL Efam A z)

/-- If `x` and `c` are such that `1 - x` and `1 - c` are units, the difference of their inverses
is the conjugation of `x - c` by them (the resolvent identity). -/
lemma ring_inverse_sub_eq {R : Type*} [Ring R] {a c : R}
    (ha : IsUnit (1 - a)) (hc : IsUnit (1 - c)) :
    Ring.inverse (1 - a) - Ring.inverse (1 - c)
      = Ring.inverse (1 - a) * (a - c) * Ring.inverse (1 - c) := by
  have hX : Ring.inverse (1 - a) * (1 - a) = 1 := Ring.inverse_mul_cancel _ ha
  have hY : (1 - c) * Ring.inverse (1 - c) = 1 := Ring.mul_inverse_cancel _ hc
  have hkey : Ring.inverse (1 - a) * ((1 - c) - (1 - a)) * Ring.inverse (1 - c)
      = Ring.inverse (1 - a) - Ring.inverse (1 - c) := by
    rw [mul_sub, sub_mul]
    rw [mul_assoc (Ring.inverse (1 - a)) (1 - c) (Ring.inverse (1 - c)), hY, mul_one]
    rw [hX, one_mul]
  have h2 : (1 - c) - (1 - a) = a - c := by abel
  rw [h2] at hkey
  exact hkey.symm

lemma Mfam_sub {A : X → (X →L[ℝ] X)} {x y : X}
    (hx : IsUnit (1 - A x : X →L[ℝ] X)) (hy : IsUnit (1 - A y : X →L[ℝ] X)) :
    Mfam A x - Mfam A y = Mfam A x * (A x - A y) * Mfam A y := by
  simp only [Mfam]
  exact ring_inverse_sub_eq hx hy

/-- If `‖A z‖ ≤ b ≤ 1/8` on `P`, then `1 - A z` is a unit for `z ∈ P` and the inverse family is
bounded by `2` there. -/
lemma Mfam_basic {b : ℝ} {P : Set X} (hb0 : 0 ≤ b) (hb1 : b ≤ 1 / 8)
    {A : X → (X →L[ℝ] X)} (hAnorm : ∀ z ∈ P, ‖A z‖ ≤ b) :
    (∀ z ∈ P, IsUnit (1 - A z : X →L[ℝ] X)) ∧ (∀ z ∈ P, ‖Mfam A z‖ ≤ 2) := by
  have hlt : ∀ z ∈ P, ‖A z‖ < 1 := by
    intro z hz; have h := hAnorm z hz; linarith
  have hu : ∀ z ∈ P, IsUnit (1 - A z : X →L[ℝ] X) :=
    fun z hz => IsUnit.one_sub_of_norm_lt_one (hlt z hz)
  refine ⟨hu, fun z hz => ?_⟩
  have h1 : ‖Ring.inverse (1 - A z)‖ ≤ (1 - ‖A z‖)⁻¹ := by
    rw [← geom_series_eq_inverse (A z) (hlt z hz)]
    have h2 := tsum_geometric_le_of_norm_lt_one (A z) (hlt z hz)
    have h3 : ‖(1 : X →L[ℝ] X)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
    linarith
  have h4 : (1 - ‖A z‖)⁻¹ ≤ 2 := by
    have hlt' : (1 / 2 : ℝ) ≤ 1 - ‖A z‖ := by have h := hAnorm z hz; linarith
    calc (1 - ‖A z‖)⁻¹ ≤ ((1 / 2 : ℝ))⁻¹ := inv_anti₀ (by norm_num) hlt'
      _ = 2 := by norm_num
  have h5 : ‖Mfam A z‖ = ‖Ring.inverse (1 - A z)‖ := by simp only [Mfam]
  rw [h5]; linarith

/-- Chain rule for `Ring.inverse`: if `B` is differentiable at `z` with derivative `B'` and
`B z` is a unit of the Banach algebra `R`, then `Ring.inverse ∘ B` is differentiable at `z` with
derivative `-(mulLeftRight (B z)⁻¹ (B z)⁻¹) ∘ B'`. -/
theorem hasFDerivAt_ringInverse_comp
    {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {Y R : Type*} [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    [NormedRing R] [NormedAlgebra 𝕜 R] [HasSummableGeomSeries R]
    {B : Y → R} {B' : Y →L[𝕜] R} {z : Y} (hB : HasFDerivAt B B' z) (hu : IsUnit (B z)) :
    HasFDerivAt (fun y => Ring.inverse (B y))
      ((-(mulLeftRight 𝕜 R (Ring.inverse (B z)) (Ring.inverse (B z)))) ∘SL B') z := by
  obtain ⟨u, hu_eq⟩ := hu
  have hthis : HasFDerivAt Ring.inverse
      (-(mulLeftRight 𝕜 R (Ring.inverse (B z)) (Ring.inverse (B z)))) (B z) := by
    have h := hasFDerivAt_ringInverse (𝕜 := 𝕜) u
    rw [← Ring.inverse_unit u] at h
    rw [hu_eq] at h
    exact h
  exact HasFDerivAt.comp z hthis hB

/-- **The abstract inverse-family estimate.** Let `P` be an open convex set, `A : X → (X →L[ℝ] X)`
a `C¹` family of endomorphisms which is small (`‖A z‖ ≤ b`, `‖fderiv A z‖ ≤ b`, `b ≤ 1/8`),
Hölder (`‖A x - A y‖ ≤ b‖x - y‖^α`) with Hölder derivative. Then for every contraction `Pw`
the function `z ↦ Pw ((1 - A z)⁻¹)` is `C¹` on `P` with `holderNorm 1 α ≤ 1024`. -/
theorem inverseFam_le {α b : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    {P : Set X} (hP : IsOpen P) (hconv : Convex ℝ P)
    {A : X → (X →L[ℝ] X)} (hAcd : ContDiffOn ℝ 1 A P)
    (hb0 : 0 ≤ b) (hb1 : b ≤ 1 / 8)
    (hAnorm : ∀ z ∈ P, ‖A z‖ ≤ b)
    (hA'norm : ∀ z ∈ P, ‖fderiv ℝ A z‖ ≤ b)
    (hAhold : ∀ x ∈ P, ∀ y ∈ P, ‖A x - A y‖ ≤ b * ‖x - y‖ ^ α)
    (hA'hold : ∀ x ∈ P, ∀ y ∈ P, ‖fderiv ℝ A x - fderiv ℝ A y‖ ≤ b * ‖x - y‖ ^ α)
    {Pw : (X →L[ℝ] X) →L[ℝ] ℂ} (hPw : ‖Pw‖ ≤ 1) :
    ContDiffOn ℝ 1 (fun z => Pw (Mfam A z)) P ∧
    Work.CR.Flat.holderNorm 1 α (fun z => Pw (Mfam A z)) P ≤ ENNReal.ofReal 1024 := by
  obtain ⟨hunit, hMnorm⟩ := Mfam_basic hb0 hb1 hAnorm
  have hAdiff : ∀ z ∈ P, HasFDerivAt A (fderiv ℝ A z) z := by
    intro z hz
    have h2 : DifferentiableWithinAt ℝ A P z := (hAcd z hz).differentiableWithinAt (by norm_num)
    have h3 : HasFDerivAt A (fderivWithin ℝ A P z) z :=
      (h2.hasFDerivWithinAt).hasFDerivAt (hP.mem_nhds hz)
    rwa [fderivWithin_of_mem_nhds (hP.mem_nhds hz)] at h3
  have hMdiff : ∀ z ∈ P, HasFDerivAt (fun y => Ring.inverse (1 - A y))
      ((-(mulLeftRight ℝ (X →L[ℝ] X) (Ring.inverse (1 - A z))
            (Ring.inverse (1 - A z)))) ∘SL (-(fderiv ℝ A z))) z := by
    intro z hz
    have hB : HasFDerivAt (fun y => (1 : X →L[ℝ] X) - A y) (-(fderiv ℝ A z)) z :=
      HasFDerivAt.const_sub (hAdiff z hz) 1
    exact hasFDerivAt_ringInverse_comp hB (hunit z hz)
  have hgdiff : ∀ z ∈ P, HasFDerivAt (fun z => Pw (Mfam A z)) (Dfam A Pw z) z := by
    intro z hz
    have h := HasFDerivAt.comp z Pw.hasFDerivAt (hMdiff z hz)
    have hfun : (⇑Pw ∘ fun y => Ring.inverse (1 - A y))
        = fun z => Pw (Ring.inverse (1 - A z)) := rfl
    rw [hfun] at h
    simpa only [Dfam, Kfam, Efam, Mfam] using h
  have hgb : ∀ z ∈ P, ‖Pw (Mfam A z)‖ ≤ 2 := by
    intro z hz
    calc ‖Pw (Mfam A z)‖ ≤ ‖Pw‖ * ‖Mfam A z‖ := Pw.le_opNorm _
      _ ≤ 1 * 2 := mul_le_mul hPw (hMnorm z hz) (norm_nonneg _) (by norm_num)
      _ = 2 := by ring
  have hEnorm : ∀ z ∈ P, ‖Efam A z‖ ≤ b := by
    intro z hz
    calc ‖Efam A z‖ = ‖fderiv ℝ A z‖ := by simp only [Efam, norm_neg (fderiv ℝ A z)]
      _ ≤ b := hA'norm z hz
  have hKnorm : ∀ z ∈ P, ‖Kfam A z‖ ≤ 4 := by
    intro z hz
    have h1 := ContinuousLinearMap.opNorm_mulLeftRight_apply_apply_le ℝ (X →L[ℝ] X)
      (Mfam A z) (Mfam A z)
    have h2 : ‖Mfam A z‖ ≤ 2 := hMnorm z hz
    have h3 : ‖Kfam A z‖
        = ‖(mulLeftRight ℝ (X →L[ℝ] X) (Mfam A z)) (Mfam A z)‖ := by
      simp only [Kfam,
        norm_neg ((mulLeftRight ℝ (X →L[ℝ] X) (Mfam A z)) (Mfam A z))]
    rw [h3]
    nlinarith [h1, h2, norm_nonneg (Mfam A z)]
  have hDgnorm : ∀ z ∈ P, ‖Dfam A Pw z‖ ≤ 1 := by
    intro z hz
    have h1 : ‖Dfam A Pw z‖ ≤ ‖Pw‖ * ‖Kfam A z ∘SL Efam A z‖ := by
      simp only [Dfam]; exact ContinuousLinearMap.opNorm_comp_le _ _
    have h2 : ‖Kfam A z ∘SL Efam A z‖ ≤ 4 * b := by
      refine le_trans (ContinuousLinearMap.opNorm_comp_le _ _) ?_
      exact mul_le_mul (hKnorm z hz) (hEnorm z hz) (norm_nonneg (Efam A z)) (by norm_num)
    calc ‖Dfam A Pw z‖ ≤ ‖Pw‖ * ‖Kfam A z ∘SL Efam A z‖ := h1
      _ ≤ 1 * (4 * b) := mul_le_mul hPw h2 (norm_nonneg (Kfam A z ∘SL Efam A z)) (by norm_num)
      _ ≤ 1 := by nlinarith [hb1, hb0]
  have hEsub : ∀ x ∈ P, ∀ y ∈ P, ‖Efam A x - Efam A y‖ ≤ b * ‖x - y‖ ^ α := by
    intro x hx y hy
    have h1 : Efam A x - Efam A y = -(fderiv ℝ A x - fderiv ℝ A y) := by
      simp only [Efam]; abel
    rw [h1, norm_neg (fderiv ℝ A x - fderiv ℝ A y)]
    exact hA'hold x hx y hy
  have hMsub : ∀ x ∈ P, ∀ y ∈ P, ‖Mfam A x - Mfam A y‖ ≤ 4 * b * ‖x - y‖ ^ α := by
    intro x hx y hy
    rw [Mfam_sub (hunit x hx) (hunit y hy)]
    have hAxy := hAhold x hx y hy
    have hnn : 0 ≤ ‖x - y‖ ^ α := Real.rpow_nonneg (norm_nonneg _) α
    calc ‖Mfam A x * (A x - A y) * Mfam A y‖
        ≤ ‖Mfam A x * (A x - A y)‖ * ‖Mfam A y‖ := norm_mul_le _ _
      _ ≤ (‖Mfam A x‖ * ‖A x - A y‖) * ‖Mfam A y‖ :=
          mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
      _ ≤ (2 * (b * ‖x - y‖ ^ α)) * 2 := by
          have h1 : ‖Mfam A x‖ * ‖A x - A y‖ ≤ 2 * (b * ‖x - y‖ ^ α) :=
            mul_le_mul (hMnorm x hx) hAxy (norm_nonneg (A x - A y)) (by norm_num)
          exact mul_le_mul h1 (hMnorm y hy) (norm_nonneg _) (by nlinarith [hb0, hnn])
      _ = 4 * b * ‖x - y‖ ^ α := by ring
  have hKsub : ∀ x ∈ P, ∀ y ∈ P, ‖Kfam A x - Kfam A y‖ ≤ 16 * b * ‖x - y‖ ^ α := by
    intro x hx y hy
    have e1 : (mulLeftRight ℝ (X →L[ℝ] X) (Mfam A y - Mfam A x)) (Mfam A y)
        = (mulLeftRight ℝ (X →L[ℝ] X) (Mfam A y)) (Mfam A y)
          - (mulLeftRight ℝ (X →L[ℝ] X) (Mfam A x)) (Mfam A y) := by
      rw [map_sub (mulLeftRight ℝ (X →L[ℝ] X)) (Mfam A y) (Mfam A x), sub_apply]
    have e2 : (mulLeftRight ℝ (X →L[ℝ] X) (Mfam A x)) (Mfam A y - Mfam A x)
        = (mulLeftRight ℝ (X →L[ℝ] X) (Mfam A x)) (Mfam A y)
          - (mulLeftRight ℝ (X →L[ℝ] X) (Mfam A x)) (Mfam A x) :=
      map_sub (mulLeftRight ℝ (X →L[ℝ] X) (Mfam A x)) (Mfam A y) (Mfam A x)
    have hyx := hMsub y hy x hx
    have hyx' : ‖Mfam A y - Mfam A x‖ ≤ 4 * b * ‖x - y‖ ^ α := by
      simpa only [norm_sub_rev y x] using hyx
    have hb1' : ‖(mulLeftRight ℝ (X →L[ℝ] X) (Mfam A y - Mfam A x)) (Mfam A y)‖
        ≤ 4 * b * ‖x - y‖ ^ α * 2 := by
      refine le_trans (ContinuousLinearMap.opNorm_mulLeftRight_apply_apply_le ℝ (X →L[ℝ] X) _ _) ?_
      exact mul_le_mul hyx' (hMnorm y hy) (norm_nonneg (Mfam A y)) (by positivity)
    have hb2' : ‖(mulLeftRight ℝ (X →L[ℝ] X) (Mfam A x)) (Mfam A y - Mfam A x)‖
        ≤ 2 * (4 * b * ‖x - y‖ ^ α) := by
      refine le_trans (ContinuousLinearMap.opNorm_mulLeftRight_apply_apply_le ℝ (X →L[ℝ] X) _ _) ?_
      exact mul_le_mul (hMnorm x hx) hyx' (norm_nonneg (Mfam A y - Mfam A x)) (by norm_num)
    have h1 : Kfam A x - Kfam A y
        = mulLeftRight ℝ (X →L[ℝ] X) (Mfam A y - Mfam A x) (Mfam A y)
          + mulLeftRight ℝ (X →L[ℝ] X) (Mfam A x) (Mfam A y - Mfam A x) := by
      simp only [Kfam]
      rw [e1, e2]
      abel
    rw [h1]
    calc ‖mulLeftRight ℝ (X →L[ℝ] X) (Mfam A y - Mfam A x) (Mfam A y)
            + mulLeftRight ℝ (X →L[ℝ] X) (Mfam A x) (Mfam A y - Mfam A x)‖
        ≤ ‖(mulLeftRight ℝ (X →L[ℝ] X) (Mfam A y - Mfam A x)) (Mfam A y)‖
          + ‖(mulLeftRight ℝ (X →L[ℝ] X) (Mfam A x)) (Mfam A y - Mfam A x)‖ :=
          norm_add_le _ _
      _ ≤ 4 * b * ‖x - y‖ ^ α * 2 + 2 * (4 * b * ‖x - y‖ ^ α) := add_le_add hb1' hb2'
      _ ≤ 16 * b * ‖x - y‖ ^ α := by
            nlinarith [hb0, Real.rpow_nonneg (norm_nonneg (x - y)) α]
  have hDghold : ∀ x ∈ P, ∀ y ∈ P, ‖Dfam A Pw x - Dfam A Pw y‖ ≤ 2 * ‖x - y‖ ^ α := by
    intro x hx y hy
    have hsub : Dfam A Pw x - Dfam A Pw y
        = Pw ∘SL ((Kfam A x ∘SL Efam A x) - (Kfam A y ∘SL Efam A y)) := by
      simp only [Dfam, ContinuousLinearMap.comp_sub]
    have hexp : (Kfam A x ∘SL Efam A x) - (Kfam A y ∘SL Efam A y)
        = (Kfam A x - Kfam A y) ∘SL Efam A x + Kfam A y ∘SL (Efam A x - Efam A y) := by
      rw [ContinuousLinearMap.sub_comp, ContinuousLinearMap.comp_sub]
      abel
    rw [hsub, hexp]
    have hA1 : ‖(Kfam A x - Kfam A y) ∘SL Efam A x‖ ≤ 16 * b * ‖x - y‖ ^ α * b := by
      refine le_trans (ContinuousLinearMap.opNorm_comp_le _ _) ?_
      exact mul_le_mul (hKsub x hx y hy) (hEnorm x hx) (norm_nonneg (Efam A x)) (by positivity)
    have hB1 : ‖Kfam A y ∘SL (Efam A x - Efam A y)‖ ≤ 4 * (b * ‖x - y‖ ^ α) := by
      refine le_trans (ContinuousLinearMap.opNorm_comp_le _ _) ?_
      exact mul_le_mul (hKnorm y hy) (hEsub x hx y hy)
        (norm_nonneg (Efam A x - Efam A y)) (by norm_num)
    have hnn : 0 ≤ ‖x - y‖ ^ α := Real.rpow_nonneg (norm_nonneg _) α
    calc ‖Pw ∘SL ((Kfam A x - Kfam A y) ∘SL Efam A x + Kfam A y ∘SL (Efam A x - Efam A y))‖
        ≤ ‖Pw‖ * ‖(Kfam A x - Kfam A y) ∘SL Efam A x
            + Kfam A y ∘SL (Efam A x - Efam A y)‖ :=
          ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ 1 * (‖(Kfam A x - Kfam A y) ∘SL Efam A x‖
            + ‖Kfam A y ∘SL (Efam A x - Efam A y)‖) := by
            have hna : ‖(Kfam A x - Kfam A y) ∘SL Efam A x
                  + Kfam A y ∘SL (Efam A x - Efam A y)‖
                ≤ ‖(Kfam A x - Kfam A y) ∘SL Efam A x‖
                  + ‖Kfam A y ∘SL (Efam A x - Efam A y)‖ :=
              norm_add_le ((Kfam A x - Kfam A y) ∘SL Efam A x)
                (Kfam A y ∘SL (Efam A x - Efam A y))
            exact mul_le_mul hPw hna
              (norm_nonneg ((Kfam A x - Kfam A y) ∘SL Efam A x
                + Kfam A y ∘SL (Efam A x - Efam A y))) (by norm_num)
      _ ≤ 1 * (16 * b * ‖x - y‖ ^ α * b + 4 * (b * ‖x - y‖ ^ α)) := by gcongr
      _ ≤ 2 * ‖x - y‖ ^ α := by
            have hbb : 16 * b * b + 4 * b ≤ 2 := by nlinarith [hb1, hb0]
            have := mul_le_mul_of_nonneg_right hbb hnn
            linarith [this]
  have hcd : ContDiffOn ℝ 1 (fun z => Pw (Mfam A z)) P := by
    intro z hz
    have hInvc : ContDiffAt ℝ 1 Ring.inverse ((1 : X →L[ℝ] X) - A z) := by
      obtain ⟨u, hu_eq⟩ := hunit z hz
      have h := contDiffAt_ringInverse (𝕜 := ℝ) (n := (1 : WithTop ℕ∞)) u
      rw [hu_eq] at h
      exact h
    have hBcd : ContDiffWithinAt ℝ 1 (fun y => (1 : X →L[ℝ] X) - A y) P z :=
      contDiffWithinAt_const.sub (hAcd z hz)
    have hMcd : ContDiffWithinAt ℝ 1 (Mfam A) P z :=
      (hInvc.contDiffWithinAt).comp z hBcd (fun y _ => mem_univ _)
    have hPwcd : ContDiffWithinAt ℝ 1 (⇑Pw) Set.univ (Mfam A z) :=
      ContDiffAt.contDiffWithinAt (Pw.contDiff.contDiffAt)
    exact hPwcd.comp z hMcd (fun y _ => mem_univ _)
  have hhn : Work.CR.Flat.holderNorm 1 α (fun z => Pw (Mfam A z)) P ≤ ENNReal.ofReal 1024 := by
    refine le_trans (holderNorm_one_le_of_pointwise_bounds (Ω := P) (g := fun z => Pw (Mfam A z))
      (M₀ := 2) (M₁ := 1) (M₂ := 2) hP hconv hα0 hα1 (by norm_num) (by norm_num) (by norm_num)
      (fun z hz => (hgdiff z hz).differentiableAt) hgb ?_ ?_) ?_
    · intro z hz
      rw [(hgdiff z hz).fderiv]
      exact hDgnorm z hz
    · intro x hx y hy
      rw [(hgdiff x hx).fderiv, (hgdiff y hy).fderiv]
      exact hDghold x hx y hy
    · exact ENNReal.ofReal_le_ofReal (by norm_num)
  exact ⟨hcd, hhn⟩

/-- The coordinate functional `L ↦ (L w) k` on endomorphisms of `ℂⁿ` is a contraction for
`‖w‖ ≤ 1`. -/
lemma norm_proj_comp_apply_le {n : ℕ} {w : Work.NN.Core.Cn n} (hw : ‖w‖ ≤ 1) (k : Fin n) :
    ‖(ContinuousLinearMap.proj k : Work.NN.Core.Cn n →L[ℝ] ℂ) ∘SL
      (ContinuousLinearMap.apply ℝ (Work.NN.Core.Cn n) w)‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by norm_num) fun L => ?_
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply,
    ContinuousLinearMap.apply_apply]
  calc ‖(L w) k‖ ≤ ‖L w‖ := norm_le_pi_norm _ k
    _ ≤ ‖L‖ * ‖w‖ := L.le_opNorm w
    _ ≤ ‖L‖ * 1 := by nlinarith [norm_nonneg L, hw]
    _ = 1 * ‖L‖ := by ring

theorem Minv_holderNorm_one_le {n : ℕ} {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    {R : ℝ} (hR : 0 < R) (hR4 : R ≤ 4)
    {v : Fin n → Work.NN.Core.Cn n → ℂ}
    (hv : ∀ l, ∀ m : ℕ, ContDiffOn ℝ m (v l) (Work.NN.Newton.Pd n R))
    {b : ℝ} (hb0 : 0 ≤ b) (hb1 : b ≤ 1 / 8)
    (hb : ∀ l, Work.CR.Flat.holderNorm 2 α (v l) (Work.NN.Newton.Pd n R) ≤ ENNReal.ofReal b) :
    (∀ (w : Work.NN.Core.Cn n), ‖w‖ ≤ 1 → ∀ k : Fin n,
      ContDiffOn ℝ 1 (fun z => (Work.NN.Newton.Minv v z w) k) (Work.NN.Newton.Pd n R) ∧
      Work.CR.Flat.holderNorm 1 α (fun z => (Work.NN.Newton.Minv v z w) k)
          (Work.NN.Newton.Pd n R) ≤ ENNReal.ofReal 1024) := by
  obtain ⟨hAcd, hAnorm, hA'norm, hAhold, hA'hold⟩ := DvCLM_data_le hα0 hR hv hb0 hb
  intro w hw k
  have hmain := inverseFam_le (X := Work.NN.Core.Cn n) (α := α) (b := b)
    (P := Work.NN.Newton.Pd n R) (A := Work.NN.Newton.DvCLM v)
    (Pw := (ContinuousLinearMap.proj k : Work.NN.Core.Cn n →L[ℝ] ℂ) ∘SL
      (ContinuousLinearMap.apply ℝ (Work.NN.Core.Cn n) w))
    hα0 hα1 (Work.NN.Newton.isOpen_Pd n R) (Work.NN.Newton.convex_Pd n R)
    hAcd hb0 hb1 hAnorm hA'norm hAhold hA'hold (norm_proj_comp_apply_le hw k)
  simpa only [Work.NN.Newton.Minv, Work.NN.Newton.Mfam, Work.NN.Newton.DvCLM,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply,
    ContinuousLinearMap.apply_apply] using hmain

end Work.NN.Newton
