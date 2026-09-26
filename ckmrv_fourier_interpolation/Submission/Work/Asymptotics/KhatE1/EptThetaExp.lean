import Mathlib
import Submission.Work.Asymptotics.KhatE1.EptSmallDefs
import Submission.Work.Asymptotics.thetaC00_second_order
import Submission.Work.Asymptotics.ratio_second_order
import Submission.Work.Kernels.TildeFacts.theta_quartic

/-!
# The first-order cusp expansions of the theta quartics
-/

namespace Work.Asymptotics.KhatE1

open UpperHalfPlane

noncomputable section

/-- A function dominated by a constant is `IsSmall _ 0`. -/
lemma isSmall_of_const {f : UpperHalfPlane → ℂ} {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ τ : UpperHalfPlane, 1 ≤ τ.im → ‖f τ‖ ≤ C) : IsSmall f 0 := by
  refine ⟨C + 1, 0, by linarith, le_rfl, fun τ hτ => ?_⟩
  rw [Real.rpow_zero, mul_one]
  linarith [h τ hτ]

/-- A continuous function of `ℂ` is bounded on the closed unit ball. -/
lemma exists_bound_continuous_closedBall (P : ℂ → ℂ) (hcont : Continuous P) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, ‖z‖ ≤ 1 → ‖P z‖ ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0:ℂ) 1).exists_bound_of_continuousOn
    hcont.continuousOn
  exact ⟨max C 0, le_max_right _ _, fun z hz => le_trans
    (hC z (by rw [Metric.mem_closedBall, dist_zero_right]; exact hz)) (le_max_left _ _)⟩

/-- Bounded explicit polynomial in `Ept`. -/
lemma isSmall_ept_poly (P : ℂ → ℂ) (hcont : Continuous P) :
    IsSmall (fun τ : UpperHalfPlane => P (Work.Residues.Ept τ)) 0 := by
  obtain ⟨C, hC, hb⟩ := exists_bound_continuous_closedBall P hcont
  exact isSmall_of_const hC (fun τ _ => hb _ (norm_Ept_le_one τ))

/-! ## The atoms -/

/-- `θ₂(τ/2,τ)/2`. -/
noncomputable def ratioFn (τ : UpperHalfPlane) : ℂ :=
  jacobiTheta₂ ((τ : ℂ) / 2) (τ : ℂ) / 2

/-- The remainder `θ₂(τ/2,τ)/2 - 1 - Ept²`. -/
noncomputable def ratioSigma (τ : UpperHalfPlane) : ℂ :=
  ratioFn τ - 1 - Work.Residues.Ept τ ^ 2

/-- The model `1 + 8 Ept + 24 Ept² + 32 Ept³` for `U`. -/
noncomputable def uModel (τ : UpperHalfPlane) : ℂ :=
  1 + 8 * Work.Residues.Ept τ + 24 * Work.Residues.Ept τ ^ 2 + 32 * Work.Residues.Ept τ ^ 3

/-- The model `16 Ept + 64 Ept³` for `V`. -/
noncomputable def vModel (τ : UpperHalfPlane) : ℂ :=
  16 * Work.Residues.Ept τ + 64 * Work.Residues.Ept τ ^ 3

/-- The remainder `θ₀₀ - 1 - 2 Ept`. -/
noncomputable def thetaC00Rem (τ : UpperHalfPlane) : ℂ :=
  Work.Kernels.LogLambda.thetaC00 (τ : ℂ) - 1 - 2 * Work.Residues.Ept τ

/-- The model expression of `ratio⁴ - 1 - 4 Ept²` decomposed. -/
noncomputable def ratio4Main (τ : UpperHalfPlane) : ℂ :=
  (6 * Work.Residues.Ept τ ^ 4 + 4 * Work.Residues.Ept τ ^ 6 + Work.Residues.Ept τ ^ 8)
    + (4 * (1 + Work.Residues.Ept τ ^ 2) ^ 3
        + 6 * (1 + Work.Residues.Ept τ ^ 2) ^ 2 * ratioSigma τ
        + 4 * (1 + Work.Residues.Ept τ ^ 2) * ratioSigma τ ^ 2
        + ratioSigma τ ^ 3) * ratioSigma τ

/-- The binomial expansion of the `U`-remainder. -/
noncomputable def uRemMain (τ : UpperHalfPlane) : ℂ :=
  (16 * Work.Residues.Ept τ ^ 4)
    + (4 * (1 + 2 * Work.Residues.Ept τ) ^ 3) * thetaC00Rem τ
    + (6 * (1 + 2 * Work.Residues.Ept τ) ^ 2) * thetaC00Rem τ ^ 2
    + (4 * (1 + 2 * Work.Residues.Ept τ)) * thetaC00Rem τ ^ 3
    + thetaC00Rem τ ^ 4

/-- The model polynomial of the `ξ₄`-expansion. -/
noncomputable def xi4Model (τ : UpperHalfPlane) : ℂ :=
  2 * uModel τ ^ 2 - 2 * uModel τ * vModel τ - vModel τ ^ 2

/-! ## The expansions -/

lemma isSmall_thetaC00Rem : IsSmall thetaC00Rem 4 := by
  refine ⟨4, 0, by norm_num, le_rfl, fun τ hτ => ?_⟩
  have h := thetaC00_second_order (τ : ℂ) (by simpa using hτ)
  rw [Real.rpow_zero, mul_one]
  simpa [thetaC00Rem, Work.Residues.Ept] using h

lemma isSmall_ratioSigma : IsSmall ratioSigma 3 := by
  refine ⟨4, 0, by norm_num, le_rfl, fun τ hτ => ?_⟩
  have h := ratio_second_order (τ : ℂ) (by simpa using hτ)
  rw [Real.rpow_zero, mul_one]
  simpa [ratioSigma, ratioFn, Work.Residues.Ept] using h

lemma isSmall_uModel : IsSmall uModel 0 :=
  isSmall_ept_poly (fun z : ℂ => 1 + 8*z + 24*z^2 + 32*z^3) (by fun_prop)

lemma isSmall_vModel : IsSmall vModel 0 :=
  isSmall_ept_poly (fun z : ℂ => 16*z + 64*z^3) (by fun_prop)

/-- The model difference for `U`. -/
lemma isSmall_URem : IsSmall (fun τ : UpperHalfPlane => Work.Kernels.UFun τ - uModel τ) 4 := by
  have hρ : IsSmall thetaC00Rem 4 := isSmall_thetaC00Rem
  have hEq : (fun τ : UpperHalfPlane => ((1 + 2 * Work.Residues.Ept τ) + thetaC00Rem τ) ^ 4
      - uModel τ) = uRemMain := by
    funext τ; simp only [uRemMain, uModel]; ring
  suffices hmain : IsSmall (fun τ : UpperHalfPlane =>
      ((1 + 2 * Work.Residues.Ept τ) + thetaC00Rem τ) ^ 4 - uModel τ) 4 by
    refine hmain.congr (fun τ => ?_)
    simp only [thetaC00Rem, Work.Kernels.UFun, Work.Kernels.theta00Fun,
      Work.Kernels.LogLambda.thetaC00, uModel]
    ring
  rw [hEq]
  have hept : IsSmall (fun τ : UpperHalfPlane => Work.Residues.Ept τ) 1 := isSmall_ept
  have h2 : IsSmall (fun τ : UpperHalfPlane => (1 + 2 * Work.Residues.Ept τ)) 0 :=
    (IsSmall.one.add (hept.const_mul 2)).mono_of 0 (by decide)
  have h1 : IsSmall (fun τ : UpperHalfPlane => (16:ℂ) * Work.Residues.Ept τ ^ 4) 4 :=
    (hept.pow 4).const_mul (16:ℂ)
  have hterm2 : IsSmall (fun τ : UpperHalfPlane => (4 * (1 + 2 * Work.Residues.Ept τ) ^ 3)
      * thetaC00Rem τ) 4 := IsSmall.mul ((h2.pow 3).const_mul 4) hρ
  have hterm3 : IsSmall (fun τ : UpperHalfPlane => (6 * (1 + 2 * Work.Residues.Ept τ) ^ 2)
      * thetaC00Rem τ ^ 2) 4 :=
    (IsSmall.mul ((h2.pow 2).const_mul 6) (hρ.pow 2)).mono_of 4 (by decide)
  have hterm4 : IsSmall (fun τ : UpperHalfPlane => (4 * (1 + 2 * Work.Residues.Ept τ))
      * thetaC00Rem τ ^ 3) 4 :=
    (IsSmall.mul (h2.const_mul 4) (hρ.pow 3)).mono_of 4 (by decide)
  have hterm5 : IsSmall (fun τ : UpperHalfPlane => thetaC00Rem τ ^ 4) 4 :=
    (hρ.pow 4).mono_of 4 (by decide)
  have hsum : IsSmall (fun τ : UpperHalfPlane => (16 * Work.Residues.Ept τ ^ 4)
        + (4 * (1 + 2 * Work.Residues.Ept τ) ^ 3) * thetaC00Rem τ
        + (6 * (1 + 2 * Work.Residues.Ept τ) ^ 2) * thetaC00Rem τ ^ 2
        + (4 * (1 + 2 * Work.Residues.Ept τ)) * thetaC00Rem τ ^ 3
        + thetaC00Rem τ ^ 4) 4 :=
    (((h1.add hterm2).add hterm3).add hterm4).add hterm5
  exact hsum

/-- `ratio⁴ = 1 + 4 Ept² + O(Ept³)`. -/
lemma isSmall_ratio4 :
    IsSmall (fun τ : UpperHalfPlane => ratioFn τ ^ 4 - (1 + 4 * Work.Residues.Ept τ ^ 2)) 3 := by
  have hσ : IsSmall ratioSigma 3 := isSmall_ratioSigma
  have hEq : (fun τ : UpperHalfPlane => ratioFn τ ^ 4
      - (1 + 4 * Work.Residues.Ept τ ^ 2)) = ratio4Main := by
    funext τ; simp only [ratio4Main, ratioFn, ratioSigma]; ring
  suffices hmain : IsSmall ratio4Main 3 by
    refine hmain.congr (fun τ => ?_)
    simp only [ratio4Main, ratioFn, ratioSigma]; ring
  have h1 : IsSmall (fun τ : UpperHalfPlane =>
      6 * Work.Residues.Ept τ ^ 4 + 4 * Work.Residues.Ept τ ^ 6 + Work.Residues.Ept τ ^ 8) 4 :=
    (((isSmall_ept.pow 4).const_mul 6).add
      ((isSmall_ept.pow 6).const_mul 4)).add (isSmall_ept.pow 8)
  have hb0 : IsSmall (fun τ : UpperHalfPlane =>
      (1 : ℂ) + Work.Residues.Ept τ ^ 2) 0 :=
    (IsSmall.one.add (isSmall_ept.pow 2)).mono_of 0 (by decide)
  have t1 : IsSmall (fun τ : UpperHalfPlane => 4 * (1 + Work.Residues.Ept τ ^ 2) ^ 3) 0 :=
    (hb0.pow 3).const_mul 4
  have t2 : IsSmall (fun τ : UpperHalfPlane =>
      6 * (1 + Work.Residues.Ept τ ^ 2) ^ 2 * ratioSigma τ) 0 :=
    (IsSmall.mul ((hb0.pow 2).const_mul 6) hσ).mono_of 0 (by decide)
  have t3 : IsSmall (fun τ : UpperHalfPlane =>
      4 * (1 + Work.Residues.Ept τ ^ 2) * ratioSigma τ ^ 2) 0 :=
    (IsSmall.mul (hb0.const_mul 4) (hσ.pow 2)).mono_of 0 (by decide)
  have t4 : IsSmall (fun τ : UpperHalfPlane => ratioSigma τ ^ 3) 0 :=
    (hσ.pow 3).mono_of 0 (by decide)
  have s1 : IsSmall (fun τ : UpperHalfPlane =>
      4 * (1 + Work.Residues.Ept τ ^ 2) ^ 3
        + 6 * (1 + Work.Residues.Ept τ ^ 2) ^ 2 * ratioSigma τ) 0 := t1.add t2
  have s2 : IsSmall (fun τ : UpperHalfPlane =>
      4 * (1 + Work.Residues.Ept τ ^ 2) * ratioSigma τ ^ 2 + ratioSigma τ ^ 3) 0 := t3.add t4
  have h2raw : IsSmall (fun τ : UpperHalfPlane =>
      (4 * (1 + Work.Residues.Ept τ ^ 2) ^ 3
        + 6 * (1 + Work.Residues.Ept τ ^ 2) ^ 2 * ratioSigma τ
        + 4 * (1 + Work.Residues.Ept τ ^ 2) * ratioSigma τ ^ 2
        + ratioSigma τ ^ 3)) 0 :=
    (s1.add s2).congr (fun τ => by ring)
  have h3 : IsSmall (fun τ : UpperHalfPlane =>
      (4 * (1 + Work.Residues.Ept τ ^ 2) ^ 3
        + 6 * (1 + Work.Residues.Ept τ ^ 2) ^ 2 * ratioSigma τ
        + 4 * (1 + Work.Residues.Ept τ ^ 2) * ratioSigma τ ^ 2
        + ratioSigma τ ^ 3) * ratioSigma τ) 3 :=
    IsSmall.mul h2raw hσ
  have h13 : IsSmall (fun τ : UpperHalfPlane =>
      (6 * Work.Residues.Ept τ ^ 4 + 4 * Work.Residues.Ept τ ^ 6 + Work.Residues.Ept τ ^ 8)
        + (4 * (1 + Work.Residues.Ept τ ^ 2) ^ 3
            + 6 * (1 + Work.Residues.Ept τ ^ 2) ^ 2 * ratioSigma τ
            + 4 * (1 + Work.Residues.Ept τ ^ 2) * ratioSigma τ ^ 2
            + ratioSigma τ ^ 3) * ratioSigma τ) 3 :=
    (h1.add h3).mono_of 3 (by decide)
  exact h13

lemma isSmall_VRem : IsSmall (fun τ : UpperHalfPlane => Work.Kernels.VFun τ - vModel τ) 4 := by
  have h4 : IsSmall (fun τ : UpperHalfPlane => ratioFn τ ^ 4
      - (1 + 4 * Work.Residues.Ept τ ^ 2)) 3 := isSmall_ratio4
  suffices hmain : IsSmall (fun τ : UpperHalfPlane =>
      (16 : ℂ) * Work.Residues.Ept τ * (ratioFn τ ^ 4 - (1 + 4 * Work.Residues.Ept τ ^ 2))) 4 by
    refine hmain.congr (fun τ => ?_)
    have hpow : (Complex.exp (Real.pi * Complex.I * (τ : ℂ) / 4)) ^ 4
        = Work.Residues.Ept τ := by
      rw [Work.Residues.Ept, ← Complex.exp_nat_mul]
      congr 1; push_cast; ring
    simp only [Work.Kernels.VFun, Work.Kernels.theta10Fun, mul_pow, vModel, ratioFn, hpow]
    ring
  exact (IsSmall.const_mul 16 (IsSmall.mul isSmall_ept h4)).congr (fun τ => by ring)

lemma isSmall_WRem :
    IsSmall (fun τ : UpperHalfPlane => Work.Kernels.WFun τ
      - (1 - 8 * Work.Residues.Ept τ + 24 * Work.Residues.Ept τ ^ 2
          - 32 * Work.Residues.Ept τ ^ 3)) 4 := by
  have h : IsSmall (fun τ : UpperHalfPlane => (Work.Kernels.UFun τ - uModel τ)
      - (Work.Kernels.VFun τ - vModel τ)) 4 :=
    (isSmall_URem.sub isSmall_VRem).mono_of 4 (by decide)
  refine h.congr (fun τ => ?_)
  simp only [uModel, vModel]
  have hq := Work.Kernels.TildeFacts.theta_quartic τ
  rw [hq]; ring

lemma isSmall_xi2 :
    IsSmall (fun τ : UpperHalfPlane =>
      (Work.Kernels.UFun τ + Work.Kernels.WFun τ)
        - (2 + 48 * Work.Kernels.qParamFun τ)) 4 := by
  have h : IsSmall (fun τ : UpperHalfPlane =>
      (Work.Kernels.UFun τ - uModel τ)
        + (Work.Kernels.WFun τ - (1 - 8 * Work.Residues.Ept τ
            + 24 * Work.Residues.Ept τ ^ 2 - 32 * Work.Residues.Ept τ ^ 3))) 4 :=
    (isSmall_URem.add isSmall_WRem).mono_of 4 (by decide)
  refine h.congr (fun τ => ?_)
  simp only [uModel]
  rw [← ept_sq_apply τ]
  ring

lemma isSmall_xi4 :
    IsSmall (fun τ : UpperHalfPlane =>
      Work.Kernels.xi4Fun τ - (2 - 288 * Work.Kernels.qParamFun τ)) 4 := by
  have hU0 : IsSmall (fun τ : UpperHalfPlane => Work.Kernels.UFun τ) 0 :=
    ((isSmall_URem.mono_of 0 (by decide)).add isSmall_uModel).congr (fun τ => by ring)
  have hV0 : IsSmall (fun τ : UpperHalfPlane => Work.Kernels.VFun τ) 0 :=
    ((isSmall_VRem.mono_of 0 (by decide)).add isSmall_vModel).congr (fun τ => by ring)
  have hA : IsSmall (fun τ : UpperHalfPlane => xi4Model τ
      - (2 - 288 * Work.Residues.Ept τ ^ 2)) 4 := by
    have hb : IsSmall (fun τ : UpperHalfPlane =>
        Work.Residues.Ept τ ^ 4 * (-1920 - 6144 * Work.Residues.Ept τ ^ 2)) 4 :=
      ((IsSmall.mul (isSmall_ept.pow 4)
        ((IsSmall.const (-1920)).add ((isSmall_ept.pow 2).const_mul (-6144)))).mono_of 4
          (by omega)).congr (fun τ => by ring)
    refine hb.congr (fun τ => ?_)
    simp only [xi4Model, uModel, vModel]; ring
  have hfac1 : IsSmall (fun τ : UpperHalfPlane =>
      2 * (Work.Kernels.UFun τ + uModel τ) - 2 * Work.Kernels.VFun τ) 0 :=
    ((((isSmall_uModel.const_mul 2).add (hU0.const_mul 2)).sub (hV0.const_mul 2)).mono_of 0
      (by decide)).congr (fun τ => by ring)
  have hfac2 : IsSmall (fun τ : UpperHalfPlane =>
      2 * uModel τ + Work.Kernels.VFun τ + vModel τ) 0 :=
    ((((isSmall_uModel.const_mul 2).add hV0).add isSmall_vModel).mono_of 0
      (by decide)).congr (fun τ => by ring)
  have hdec : IsSmall (fun τ : UpperHalfPlane =>
      (Work.Kernels.UFun τ ^ 2 + (Work.Kernels.UFun τ - Work.Kernels.VFun τ) ^ 2
          - 2 * Work.Kernels.VFun τ ^ 2) - xi4Model τ) 4 := by
    have hp1 : IsSmall (fun τ : UpperHalfPlane => (Work.Kernels.UFun τ - uModel τ)
        * (2 * (Work.Kernels.UFun τ + uModel τ) - 2 * Work.Kernels.VFun τ)) 4 :=
      (isSmall_URem.mul hfac1).mono_of 4 (by decide)
    have hp2 : IsSmall (fun τ : UpperHalfPlane => (Work.Kernels.VFun τ - vModel τ)
        * (2 * uModel τ + Work.Kernels.VFun τ + vModel τ)) 4 :=
      (isSmall_VRem.mul hfac2).mono_of 4 (by decide)
    refine ((hp1.sub hp2).mono_of 4 (by decide)).congr (fun τ => ?_)
    simp only [xi4Model, uModel, vModel]; ring
  have htot : IsSmall (fun τ : UpperHalfPlane =>
      ((Work.Kernels.UFun τ ^ 2 + (Work.Kernels.UFun τ - Work.Kernels.VFun τ) ^ 2
          - 2 * Work.Kernels.VFun τ ^ 2) - xi4Model τ)
      + (xi4Model τ - (2 - 288 * Work.Residues.Ept τ ^ 2))) 4 :=
    (hdec.add hA).mono_of 4 (by decide)
  refine htot.congr (fun τ => ?_)
  rw [← ept_sq_apply τ]
  simp only [Work.Kernels.xi4Fun]
  have hq := Work.Kernels.TildeFacts.theta_quartic τ
  rw [hq]; ring

end

end Work.Asymptotics.KhatE1
