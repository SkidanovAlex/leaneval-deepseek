import ChallengeDeps
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseBoxFock.qmqDefs
import Submission.Work.BoseBoxFock.rowShape_congr_box
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.qmqRowKernelChain` — the kernel-value chain of the `Q₂` row

The row `rowPairSubC a Θ A KI KII` is an integral functional of the two kernels `KI`, `KII`.  This
module carries out the *value* replacement

    rowPairSubC a Θ A (K1lim ℓ W₁) (K1lim ℓ W₂)
      = rowPairSubC a Θ A (qmqKernel ℓ k₁) (qmqKernel ℓ k₂)         (kᵢ := wPair ℓ hᵢ + imgKernel ℓ Wᵢ)

in three steps, each of which is a `sorry`-free plumbing fact:

* `rowPairSubC_congr_box` — `rowShape_congr_box` summed over `pairSet n`: two kernels that agree on
  `acube ℓ × acube ℓ` give the same row (`Θ` supported in the box);
* `qmqKCθ_eq_qmqKC_of_mem` — the sharp `θ_Λ`-rows of `qmqKCθ` are those of `qmqKC` on the box
  (`θ_Λ = 1_{acube ℓ}`);
* the identity `K1lim ℓ W = qmqKCθ ℓ kPer(W)` with `kPer(W) = wPair ℓ h + imgKernel ℓ W`
  (`K1lim_eq_qmqKCtheta_L1` + `kPer_eq_wPair_add_img`) is taken as a hypothesis, so that this
  module is independent of the two modules proving it.

Everything here is `sorry`-free.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "Xn" => Work.BoseDict.Xn

set_option linter.unusedVariables false

/-! ## 1. The row is a function of the two kernels on `acube ℓ × acube ℓ` -/

/-- The three `rowShape`'s agree when the kernels agree on `acube ℓ × acube ℓ` (`rowShape_congr_box`
at every `p ∈ pairSet n`, hence the same for the `pairSet n`-sums and for `rowPairSubC`). -/
theorem rowPairSubC_congr_box {n : ℕ} {ℓ a : ℝ} (hℓ : 0 < ℓ) {Θ : Xn n → ℂ} {A : E3 → ℂ}
    {KI KI' KII KII' : E3 → E3 → ℂ}
    (hΘs : Function.support Θ ⊆ Work.MB.boxPow n ℓ)
    (hI : ∀ w y, w ∈ Submission.BoseGases.acube ℓ → y ∈ Submission.BoseGases.acube ℓ →
      KI w y = KI' w y)
    (hII : ∀ w y, w ∈ Submission.BoseGases.acube ℓ → y ∈ Submission.BoseGases.acube ℓ →
      KII w y = KII' w y) :
    rowPairSubC a Θ A KI KII = rowPairSubC a Θ A KI' KII' := by
  have h13 : rowSum13 Θ A A KI = rowSum13 Θ A A KI' := by
    rw [rowSum13, rowSum13]
    exact Finset.sum_congr rfl (fun p hp =>
      (rowShape_congr_box (A := A) (B := A) hℓ hΘs hI (mem_pairSet_iff.mp hp)).1)
  have h21 : rowSum21 Θ A KII = rowSum21 Θ A KII' := by
    rw [rowSum21, rowSum21]
    exact Finset.sum_congr rfl (fun p hp =>
      (rowShape_congr_box (A := A) (B := A) hℓ hΘs hII (mem_pairSet_iff.mp hp)).2.1)
  have h23 : rowSum23 Θ A A KII = rowSum23 Θ A A KII' := by
    rw [rowSum23, rowSum23]
    exact Finset.sum_congr rfl (fun p hp =>
      (rowShape_congr_box (A := A) (B := A) hℓ hΘs hII (mem_pairSet_iff.mp hp)).2.2)
  rw [rowPairSubC, rowPairSubC, h13, h21, h23]

/-! ## 2. `qmqKCθ` and `qmqKC` agree on the box -/

/-- On the box, FS's `θ_Λ = 1_{acube ℓ}`, so the three sharp `θ`-rows of `qmqKCθ` collapse onto
those of `qmqKC`. -/
theorem qmqKCθ_eq_qmqKC_of_mem {ℓ : ℝ} (hℓ : 0 < ℓ) {m : E3 → E3 → ℂ} {w y : E3}
    (hw : w ∈ Submission.BoseGases.acube ℓ) (hy : y ∈ Submission.BoseGases.acube ℓ) :
    qmqKCθ ℓ m w y = qmqKC ℓ m w y := by
  have hw1 : Work.BoseK15.corpusBox.thetaFun ℓ w = 1 :=
    thetaFun_eq_one_of_mem (acube_subset_boxL hℓ hw)
  have hy1 : Work.BoseK15.corpusBox.thetaFun ℓ y = 1 :=
    thetaFun_eq_one_of_mem (acube_subset_boxL hℓ hy)
  rw [qmqKCθ, qmqKC, hw1, hy1]
  ring

/-! ## 3. The kernel-value chain -/

/-- **The kernel-value chain of the row.**  If the two limit kernels are the `qmqKCθ`'s of the
periodised kernels `mᵢ`, and `mᵢ` is the `ℂ`-coercion of the honest `m = 0` plus images kernel
`kᵢ = wPair ℓ hᵢ + imgKernel ℓ Wᵢ`, then the row at the limit kernels is the row at the
`qmqKernel`'s of the honest kernels. -/
theorem rowPairSubC_K1lim_eq_qmqKernel {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    {Θ : Xn n → ℂ} {A : E3 → ℂ}
    (hΘs : Function.support Θ ⊆ Work.MB.boxPow n ℓ)
    {W₁ W₂ : E3 → ℝ} {h₁ h₂ : E3 → ℝ} {m₁ m₂ : E3 → E3 → ℂ}
    (hK₁ : K1lim ℓ W₁ = qmqKCθ ℓ m₁) (hK₂ : K1lim ℓ W₂ = qmqKCθ ℓ m₂)
    (hm₁ : m₁ = fun a b =>
      ((Submission.BoseGases.wPair ℓ h₁ a b + imgKernel ℓ W₁ a b : ℝ) : ℂ))
    (hm₂ : m₂ = fun a b =>
      ((Submission.BoseGases.wPair ℓ h₂ a b + imgKernel ℓ W₂ a b : ℝ) : ℂ)) :
    rowPairSubC ((ℓ ^ 3)⁻¹) Θ A (K1lim ℓ W₁) (K1lim ℓ W₂)
      = rowPairSubC ((ℓ ^ 3)⁻¹) Θ A
          (qmqKernel ℓ (fun a b => Submission.BoseGases.wPair ℓ h₁ a b + imgKernel ℓ W₁ a b))
          (qmqKernel ℓ (fun a b => Submission.BoseGases.wPair ℓ h₂ a b + imgKernel ℓ W₂ a b)) := by
  subst hm₁
  subst hm₂
  rw [hK₁, hK₂]
  have hKC₁ : qmqKC ℓ (fun a b =>
      ((Submission.BoseGases.wPair ℓ h₁ a b + imgKernel ℓ W₁ a b : ℝ) : ℂ))
      = qmqKernel ℓ (fun a b => Submission.BoseGases.wPair ℓ h₁ a b + imgKernel ℓ W₁ a b) :=
    funext fun w => funext fun y =>
      (qmqKernel_eq_qmqKC ℓ (fun a b => Submission.BoseGases.wPair ℓ h₁ a b
        + imgKernel ℓ W₁ a b) w y).symm
  have hKC₂ : qmqKC ℓ (fun a b =>
      ((Submission.BoseGases.wPair ℓ h₂ a b + imgKernel ℓ W₂ a b : ℝ) : ℂ))
      = qmqKernel ℓ (fun a b => Submission.BoseGases.wPair ℓ h₂ a b + imgKernel ℓ W₂ a b) :=
    funext fun w => funext fun y =>
      (qmqKernel_eq_qmqKC ℓ (fun a b => Submission.BoseGases.wPair ℓ h₂ a b
        + imgKernel ℓ W₂ a b) w y).symm
  calc rowPairSubC ((ℓ ^ 3)⁻¹) Θ A
          (qmqKCθ ℓ fun a b =>
            ((Submission.BoseGases.wPair ℓ h₁ a b + imgKernel ℓ W₁ a b : ℝ) : ℂ))
          (qmqKCθ ℓ fun a b =>
            ((Submission.BoseGases.wPair ℓ h₂ a b + imgKernel ℓ W₂ a b : ℝ) : ℂ))
      = rowPairSubC ((ℓ ^ 3)⁻¹) Θ A
          (qmqKC ℓ fun a b =>
            ((Submission.BoseGases.wPair ℓ h₁ a b + imgKernel ℓ W₁ a b : ℝ) : ℂ))
          (qmqKC ℓ fun a b =>
            ((Submission.BoseGases.wPair ℓ h₂ a b + imgKernel ℓ W₂ a b : ℝ) : ℂ)) := by
        refine rowPairSubC_congr_box (a := (ℓ ^ 3)⁻¹) hℓ hΘs ?_ ?_
        · intro w y hw hy
          exact qmqKCθ_eq_qmqKC_of_mem hℓ hw hy
        · intro w y hw hy
          exact qmqKCθ_eq_qmqKC_of_mem hℓ hw hy
    _ = rowPairSubC ((ℓ ^ 3)⁻¹) Θ A
          (qmqKernel ℓ (fun a b => Submission.BoseGases.wPair ℓ h₁ a b + imgKernel ℓ W₁ a b))
          (qmqKernel ℓ
            (fun a b => Submission.BoseGases.wPair ℓ h₂ a b + imgKernel ℓ W₂ a b)) := by
        rw [hKC₁, hKC₂]


/-! ## 4. The summability of a shifted compactly supported weight -/

/-- A weight vanishing outside the ball of radius `R` has `ℓℤ³`-summable shifts: for every shift
`z` only the finitely many lattice points with `‖ℓ•m‖ ≤ R + ‖z‖` contribute. -/
theorem summable_shift_of_support {ℓ : ℝ} (hℓ : 0 < ℓ) {R : ℝ} {W : E3 → ℝ}
    (hWs : ∀ x : E3, R < ‖x‖ → W x = 0) (z : E3) :
    Summable (fun m : Fin 3 → ℤ => ((W (z + ℓ • latVec m) : ℝ) : ℂ)) := by
  refine summable_of_ne_finset_zero (s := LatFourier.latBall ((R + ‖z‖) / ℓ)) (fun m hm => ?_)
  have hm' : (R + ‖z‖) / ℓ < ‖latVec m‖ := by
    rw [LatFourier.mem_latBall] at hm
    exact not_le.mp hm
  have hmul : R + ‖z‖ < ℓ * ‖latVec m‖ := by
    rw [div_lt_iff₀ hℓ] at hm'
    linarith
  have hnorm : ‖z + ℓ • latVec m‖ ≥ ℓ * ‖latVec m‖ - ‖z‖ := by
    have h := norm_sub_le (z + ℓ • latVec m) z
    rw [add_sub_cancel_left] at h
    have h2 : ‖ℓ • latVec m‖ = ℓ * ‖latVec m‖ := LatFourier.latVec_norm_smul ℓ hℓ.le m
    linarith [h, h2.ge, h2.le]
  have h0 : W (z + ℓ • latVec m) = 0 := hWs _ (by linarith)
  simp [h0]


/-! ## 5. Symmetry of the two honest kernels -/

/-- `latVec` is odd. -/
theorem latVec_neg' (m : Fin 3 → ℤ) : latVec (-m) = -latVec m := by
  ext i
  simp [latVec]

/-- `wPair ℓ h` is symmetric when its numerator `h` is even. -/
theorem wPair_symm {ℓ : ℝ} {h : E3 → ℝ} (hh : ∀ z, h (-z) = h z) (a b : E3) :
    Submission.BoseGases.wPair ℓ h a b = Submission.BoseGases.wPair ℓ h b a :=
  Submission.BoseGases.wPairC_sym hh ℓ a b

/-- The lattice-images kernel is symmetric when its weight `W` is even. -/
theorem imgKernel_symm {ℓ : ℝ} {W : E3 → ℝ} (hWe : ∀ z, W (-z) = W z) (a b : E3) :
    imgKernel ℓ W a b = imgKernel ℓ W b a := by
  have hterm : ∀ m : Fin 3 → ℤ,
      (if m = 0 then (0 : ℝ) else W (b - a + ℓ • latVec m))
        = (if (-m) = 0 then (0 : ℝ) else W (a - b + ℓ • latVec (-m))) := by
    intro m
    by_cases hm : m = 0
    · simp [hm]
    · have hneg : (-m) ≠ 0 := by simpa using hm
      rw [if_neg hm, if_neg hneg, latVec_neg']
      rw [show a - b + ℓ • (-(latVec m)) = -(b - a + ℓ • latVec m) by
        rw [smul_neg]; abel]
      exact (hWe _).symm
  have htsum : (∑' m : Fin 3 → ℤ, if m = 0 then (0 : ℝ) else W (a - b + ℓ • latVec m))
      = ∑' m : Fin 3 → ℤ, if m = 0 then (0 : ℝ) else W (b - a + ℓ • latVec m) := by
    rw [show (∑' m : Fin 3 → ℤ, if m = 0 then (0 : ℝ) else W (b - a + ℓ • latVec m))
        = ∑' m : Fin 3 → ℤ,
            (if (-m) = 0 then (0 : ℝ) else W (a - b + ℓ • latVec (-m))) from
      tsum_congr (fun m => hterm m)]
    let e : (Fin 3 → ℤ) ≃ (Fin 3 → ℤ) :=
      { toFun := fun m => -m, invFun := fun m => -m,
        left_inv := fun m => by simp, right_inv := fun m => by simp }
    exact (Equiv.tsum_eq e _).symm
  rw [imgKernel, imgKernel, htsum]
  ring


/-! ## 6. `errKafz` is nonnegative -/

/-- `errKafz v R μ C ≥ 0` for `0 < μ`, `0 < a v`, `0 ≤ C` (a public copy of the `private`
lemma of `pairRowS2Bound`). -/
theorem errKafz_nonneg' {v : ℝ³ → ℝ} {R μ C : ℝ} (hμ : 0 < μ) (hav : 0 < BoseGases.a v)
    (hC : 0 ≤ C) : 0 ≤ Work.BoseFixR.errKafz v R μ C := by
  have hside : 0 < Work.BoseBox.sideAt μ (BoseGases.a v) := Work.BoseBox.sideAt_pos hμ hav
  have hell3 : 0 ≤ Work.BoseFixR.ell3 v μ := by
    unfold Work.BoseFixR.ell3 Work.BoseFixR.ell
    exact pow_nonneg hside.le 3
  have hdil : 0 ≤ Work.BoseFixR.dil v μ := by
    unfold Work.BoseFixR.dil
    positivity
  have hbr : 0 ≤ (Work.BoseBox.paramsAt μ (BoseGases.a v)).Kl ^ (-(3 : ℝ))
      + Work.BoseFixR.fsX v μ ^ 2
      + (R / BoseGases.a v) ^ 2 * Real.sqrt (Work.BoseFixR.dil v μ)
      + Work.BoseFixR.errExp v μ := by
    have h1 : 0 ≤ (Work.BoseBox.paramsAt μ (BoseGases.a v)).Kl ^ (-(3 : ℝ)) := by
      have ht : 0 < μ * (BoseGases.a v) ^ 3 := by positivity
      simp only [Work.BoseBox.paramsAt, Work.BoseBox.fsParams]
      exact Real.rpow_nonneg (Work.BoseBox.fsXp_pos ht).le _
    have h2 : 0 ≤ Work.BoseFixR.fsX v μ ^ 2 := sq_nonneg _
    have h3 : 0 ≤ (R / BoseGases.a v) ^ 2 * Real.sqrt (Work.BoseFixR.dil v μ) :=
      mul_nonneg (sq_nonneg _) (Real.sqrt_nonneg _)
    have h4 : 0 ≤ Work.BoseFixR.errExp v μ := by
      unfold Work.BoseFixR.errExp
      exact Real.rpow_nonneg hdil _
    linarith
  unfold Work.BoseFixR.errKafz
  exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hC (sq_nonneg μ)) hav.le)
    hell3) (Real.sqrt_nonneg _)) hbr

end Work.BoseBoxFock
