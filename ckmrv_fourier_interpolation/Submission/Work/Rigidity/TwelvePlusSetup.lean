/-
# Setup for the weight-twelve rigidity lemma at eigenvalue `-1`

This file introduces the auxiliary functions used in the proof of
`Work.Rigidity.SingleRigidityP 12 (-1) 1` (the `S`-anti-invariant, weight-twelve case
of CKMRV's `lem:noPsolutions` with the moderate-growth hypothesis).

For a holomorphic `f : ℍ → ℂ` annihilated by `(T - I)²` and anti-invariant under `|₁₂ S`
we set

* `A = fstDiff f = f(·+1) - f`,
* `B = qzero f = f - τ · A`,
* `h₂ = h2fun f = A |₁₂ S - τ² A - 2 τ B` (this is the modular form `h₂` of the paper),
* `m = mfun f = 2B - (πi/3) h₂ E₂` (modular of weight `12`),
* `F₀ = F0fun f = A - (πi/6) m E₂ + (π²/36) h₂ E₂²` (modular of weight `14`),

together with their transformation laws under `T` and under `S` and the two identities

`A = F₀ + (πi/6) m E₂ - (π²/36) h₂ E₂²`, `B = (πi/6) h₂ E₂ + m/2`.
-/
import Mathlib
import Submission.Work.Rigidity.Basic
import Submission.Work.Rigidity.Diff
import Submission.Work.Modular.Basic
import Submission.Work.Modular.E2_S_smul
import Submission.Work.Modular.E2_T_smul
import Submission.Work.Kernels.ClassicalFacts.E2Fun_mem_InP
import Submission.Work.Modular.E2_qExpansion_coeff
import Submission.Work.Kernels.ModerateGrowth
import Submission.Work.Kernels.Slash

noncomputable section

open UpperHalfPlane ModularForm ModularGroup Matrix Filter
open scoped MatrixGroups ModularForm Modular Manifold Bundle Topology

namespace Work.Rigidity

/-! ## Slash computations -/

lemma slash_T_app (k : ℤ) (F : ℍ → ℂ) (τ : ℍ) :
    (F ∣[k] ModularGroup.T) τ = F ((1 : ℝ) +ᵥ τ) := by
  rw [Work.Kernels.slash_apply', modular_T_smul]
  have h1 : Work.Kernels.jFun ModularGroup.T (τ : ℂ) = 1 := by
    rw [Work.Kernels.jFun_apply]
    have h10 : (ModularGroup.T : SL(2, ℤ)) 1 0 = 0 := by decide
    have h11 : (ModularGroup.T : SL(2, ℤ)) 1 1 = 1 := by decide
    rw [h10, h11]
    ring
  rw [h1, _root_.one_zpow, mul_one]

lemma slash_S_app (F : ℍ → ℂ) (k : ℤ) (τ : ℍ) :
    (F ∣[k] ModularGroup.S) τ = (τ : ℂ) ^ (-k) * F (ModularGroup.S • τ) := by
  rw [ModularForm.SL_slash_apply, ModularGroup.denom_S, mul_comm]

/-- `(F ∣[k] S) τ = τ^{-k} F (S • τ)` specialized to weight `12`. -/
lemma slash_S_app_twelve (F : ℍ → ℂ) (τ : ℍ) :
    (F ∣[(12 : ℤ)] ModularGroup.S) τ = (τ : ℂ) ^ (-12 : ℤ) * F (ModularGroup.S • τ) :=
  slash_S_app F 12 τ


/-! ## Elementary slash lemmas for `T`, `S` and the group relation `TST = -S T⁻¹ S` -/

lemma slash_neg_one {k : ℤ} (hk : Even k) (F : ℍ → ℂ) :
    F ∣[k] (-1 : SL(2, ℤ)) = F := by
  funext τ
  rw [ModularForm.SL_slash_apply]
  have h1 : ((-1 : SL(2, ℤ)) • τ : ℍ) = τ := by
    apply UpperHalfPlane.ext
    simp
  have h2 : UpperHalfPlane.denom (Work.Kernels.glOf (-1 : SL(2, ℤ))) (τ : ℂ) = -1 := by
    rw [show UpperHalfPlane.denom (Work.Kernels.glOf (-1 : SL(2, ℤ))) (τ : ℂ)
        = (Work.Kernels.glOf (-1 : SL(2, ℤ))) 1 0 * (τ : ℂ)
          + (Work.Kernels.glOf (-1 : SL(2, ℤ))) 1 1 from rfl]
    rw [Work.Kernels.glOf_apply, Work.Kernels.glOf_apply]
    simp
  rw [h1, h2]
  have h3 : ((-1 : ℂ)) ^ (-k) = 1 := by simpa using hk.neg_zpow (1 : ℂ)
  rw [h3, mul_one]

lemma slash_neg {k : ℤ} (hk : Even k) (F : ℍ → ℂ) (γ : SL(2, ℤ)) :
    F ∣[k] (-γ) = F ∣[k] γ := by
  rw [show (-γ : SL(2, ℤ)) = (-1 : SL(2, ℤ)) * γ from by rw [neg_one_mul],
    SlashAction.slash_mul, slash_neg_one hk]

lemma fstDiff_eq_slash_T_sub (f : ℍ → ℂ) :
    fstDiff f = f ∣[(12 : ℤ)] ModularGroup.T - f := by
  funext τ
  simp only [Pi.sub_apply]
  rw [slash_T_app]
  simp [fstDiff]

lemma slash_T_eq (f : ℍ → ℂ) :
    f ∣[(12 : ℤ)] ModularGroup.T = f + fstDiff f := by
  funext τ
  simp only [Pi.add_apply]
  rw [slash_T_app]
  simp [fstDiff]

/-- The `(T - I)²` relation in slash form: `f ∣[12] T⁻¹ = 2 f - f ∣[12] T`. -/
lemma slash_T_inv_twelve {f : ℍ → ℂ} (hf : AnnT2 f) :
    f ∣[(12 : ℤ)] ModularGroup.T⁻¹ = (2 : ℂ) • f - f ∣[(12 : ℤ)] ModularGroup.T := by
  have hT : f ∣[(12 : ℤ)] ModularGroup.T = fun τ : ℍ => f ((1 : ℝ) +ᵥ τ) := by
    funext τ; rw [slash_T_app]
  have hT2 : f ∣[(12 : ℤ)] (ModularGroup.T * ModularGroup.T) =
      fun τ : ℍ => f ((2 : ℝ) +ᵥ τ) := by
    rw [SlashAction.slash_mul, hT]
    funext τ
    rw [slash_T_app]
    congr 1
    rw [Work.Kernels.vadd_one_add_one]
  have hzero : f ∣[(12 : ℤ)] (ModularGroup.T * ModularGroup.T)
      - (2 : ℂ) • (f ∣[(12 : ℤ)] ModularGroup.T) + f = 0 := by
    rw [hT2, hT]
    funext τ
    have h := congrFun hf τ
    simpa [Work.Kernels.T2op, Work.Kernels.vadd_one_add_one, Pi.add_apply, Pi.sub_apply,
      Pi.smul_apply, smul_eq_mul] using h
  have h1 : (f ∣[(12 : ℤ)] (ModularGroup.T * ModularGroup.T)
      - (2 : ℂ) • (f ∣[(12 : ℤ)] ModularGroup.T) + f) ∣[(12 : ℤ)] ModularGroup.T⁻¹ = 0 := by
    rw [hzero]; simp
  have h2 : ((f ∣[(12 : ℤ)] (ModularGroup.T * ModularGroup.T)) ∣[(12 : ℤ)] ModularGroup.T⁻¹
      - (2 : ℂ) • ((f ∣[(12 : ℤ)] ModularGroup.T) ∣[(12 : ℤ)] ModularGroup.T⁻¹)
      + f ∣[(12 : ℤ)] ModularGroup.T⁻¹) = 0 := by
    simpa only [sub_eq_add_neg, SlashAction.add_slash, SlashAction.neg_slash, SL_smul_slash]
      using h1
  have hTT : ModularGroup.T * ModularGroup.T * ModularGroup.T⁻¹ = ModularGroup.T := by decide
  have hT1 : ModularGroup.T * ModularGroup.T⁻¹ = 1 := by decide
  rw [← SlashAction.slash_mul, ← SlashAction.slash_mul, hTT, hT1,
    SlashAction.slash_one] at h2
  linear_combination h2

/-- `(f ∣[12] (T*S)) ∣[12] T = f ∣[12] (T*S) + 2 f`, the consequence of `TST = -S T⁻¹ S`. -/
lemma slash_TS_T {f : ℍ → ℂ} (hT2 : AnnT2 f) (hS : SlashEigen 12 (-1 : ℂ) f) :
    (f ∣[(12 : ℤ)] (ModularGroup.T * ModularGroup.S)) ∣[(12 : ℤ)] ModularGroup.T
      = f ∣[(12 : ℤ)] (ModularGroup.T * ModularGroup.S) + (2 : ℂ) • f := by
  have hgrp : ModularGroup.T * ModularGroup.S * ModularGroup.T
      = -(ModularGroup.S * ModularGroup.T⁻¹ * ModularGroup.S) := by decide
  have hSl : f ∣[(12 : ℤ)] ModularGroup.S = -f := by
    funext τ; simpa using hS τ
  have hTinv : f ∣[(12 : ℤ)] ModularGroup.T⁻¹ = (2 : ℂ) • f - f ∣[(12 : ℤ)] ModularGroup.T :=
    slash_T_inv_twelve hT2
  have key : (f ∣[(12 : ℤ)] (ModularGroup.T * ModularGroup.S)) ∣[(12 : ℤ)] ModularGroup.T
      = - ((f ∣[(12 : ℤ)] ModularGroup.T⁻¹) ∣[(12 : ℤ)] ModularGroup.S) := by
    rw [← SlashAction.slash_mul, hgrp, slash_neg (by norm_num),
      SlashAction.slash_mul, SlashAction.slash_mul, hSl, SlashAction.neg_slash,
      SlashAction.neg_slash]
  rw [key, hTinv, sub_eq_add_neg, SlashAction.add_slash, SlashAction.neg_slash,
    SL_smul_slash, SlashAction.slash_mul, hSl]
  ext τ
  simp only [Pi.neg_apply, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- `(fstDiff f) ∣[12] S = f ∣[12] (T*S) + f`. -/
lemma fstDiff_slash_S {f : ℍ → ℂ} (hS : SlashEigen 12 (-1 : ℂ) f) :
    fstDiff f ∣[(12 : ℤ)] ModularGroup.S
      = f ∣[(12 : ℤ)] (ModularGroup.T * ModularGroup.S) + f := by
  have hSl : f ∣[(12 : ℤ)] ModularGroup.S = -f := by
    funext τ; simpa using hS τ
  rw [fstDiff_eq_slash_T_sub, sub_eq_add_neg, SlashAction.add_slash, SlashAction.neg_slash,
    SlashAction.slash_mul, hSl]
  simp


/-! ## The auxiliary functions `B`, `h₂` and their laws -/

/-- `B = f - τ · fstDiff f`, the `τ`-free part of `f`. -/
def qzero (f : ℍ → ℂ) : ℍ → ℂ := fun τ => f τ - (τ : ℂ) * fstDiff f τ

/-- `h₂ = A ∣[12] S - τ² A - 2 τ B`, the weight-ten modular form attached to `f`. -/
def h2fun (f : ℍ → ℂ) : ℍ → ℂ :=
  fstDiff f ∣[(12 : ℤ)] ModularGroup.S
    - (fun τ : ℍ => (τ : ℂ) ^ 2 * fstDiff f τ)
    - (fun τ : ℍ => (2 : ℂ) * (τ : ℂ) * qzero f τ)

lemma qzero_apply (f : ℍ → ℂ) (τ : ℍ) :
    qzero f τ = f τ - (τ : ℂ) * fstDiff f τ := rfl

lemma h2fun_apply (f : ℍ → ℂ) (τ : ℍ) :
    h2fun f τ = (fstDiff f ∣[(12 : ℤ)] ModularGroup.S) τ
      - (τ : ℂ) ^ 2 * fstDiff f τ - (2 : ℂ) * (τ : ℂ) * qzero f τ := rfl

/-- The defining identity of `h₂`, as an identity of functions. -/
lemma h2fun_eq (f : ℍ → ℂ) :
    fstDiff f ∣[(12 : ℤ)] ModularGroup.S
      = h2fun f + (fun τ : ℍ => (τ : ℂ) ^ 2 * fstDiff f τ)
        + (fun τ : ℍ => (2 : ℂ) * (τ : ℂ) * qzero f τ) := by
  rw [h2fun]
  abel

lemma fstDiff_vadd_one {f : ℍ → ℂ} (hT2 : AnnT2 f) (τ : ℍ) :
    fstDiff f ((1 : ℝ) +ᵥ τ) = fstDiff f τ :=
  (fstDiff_vadd_one_iff f).mp hT2 τ

lemma qzero_vadd_one {f : ℍ → ℂ} (hT2 : AnnT2 f) (τ : ℍ) :
    qzero f ((1 : ℝ) +ᵥ τ) = qzero f τ := by
  have h := sub_smul_fstDiff_periodic hT2 τ
  simpa [qzero] using h

lemma zpow_mul_zpow_neg_twelve (z : ℂ) (hz : z ≠ 0) :
    z ^ 12 * z ^ (-12 : ℤ) = 1 := by
  rw [show (-12 : ℤ) = -((12 : ℕ) : ℤ) by norm_num, _root_.zpow_neg, zpow_natCast,
    mul_inv_cancel₀ (pow_ne_zero 12 hz)]

lemma zpow_neg_twelve_mul_zpow (z : ℂ) (hz : z ≠ 0) :
    z ^ (-12 : ℤ) * z ^ 12 = 1 := by
  rw [show (-12 : ℤ) = -((12 : ℕ) : ℤ) by norm_num, _root_.zpow_neg, zpow_natCast,
    inv_mul_cancel₀ (pow_ne_zero 12 hz)]

lemma zpow_neg_ten_mul_zpow_ten (z : ℂ) (hz : z ≠ 0) :
    z ^ (-10 : ℤ) * z ^ 10 = 1 := by
  rw [show (-10 : ℤ) = -((10 : ℕ) : ℤ) by norm_num, _root_.zpow_neg, zpow_natCast,
    inv_mul_cancel₀ (pow_ne_zero 10 hz)]

/-- The pointwise form of the defining identity of `h₂` at the point `S • τ`. -/
lemma h2fun_gives_A_S (f : ℍ → ℂ) (τ : ℍ) :
    fstDiff f (ModularGroup.S • τ)
      = (τ : ℂ) ^ 12 *
        (h2fun f τ + (τ : ℂ) ^ 2 * fstDiff f τ + (2 : ℂ) * (τ : ℂ) * qzero f τ) := by
  have hτ : (τ : ℂ) ≠ 0 := coe_ne_zero τ
  have h := congrFun (h2fun_eq f) τ
  rw [slash_S_app] at h
  have h' : (τ : ℂ) ^ (-12 : ℤ) * fstDiff f (ModularGroup.S • τ)
      = h2fun f τ + (τ : ℂ) ^ 2 * fstDiff f τ + (2 : ℂ) * (τ : ℂ) * qzero f τ := by
    simpa only [Pi.add_apply] using h
  have h2 := congrArg (fun z : ℂ => (τ : ℂ) ^ 12 * z) h'
  rw [← mul_assoc, zpow_mul_zpow_neg_twelve (τ : ℂ) hτ, one_mul] at h2
  exact h2

/-- The `S`-relation for `B`: `B ∣[12] S = B + τ⁻¹ h₂`. -/
lemma qzero_slash_S {f : ℍ → ℂ} (hS : SlashEigen 12 (-1 : ℂ) f) :
    qzero f ∣[(12 : ℤ)] ModularGroup.S
      = qzero f + (fun τ : ℍ => (τ : ℂ)⁻¹ * h2fun f τ) := by
  funext τ
  have hτ : (τ : ℂ) ≠ 0 := coe_ne_zero τ
  have hf : f (ModularGroup.S • τ) = -((τ : ℂ) ^ 12) * f τ := by
    have h := hS τ
    rw [slash_S_app] at h
    have h' : (τ : ℂ) ^ (-12 : ℤ) * f (ModularGroup.S • τ) = -f τ := by simpa using h
    have h2 := congrArg (fun z : ℂ => (τ : ℂ) ^ 12 * z) h'
    rw [← mul_assoc, zpow_mul_zpow_neg_twelve (τ : ℂ) hτ, one_mul] at h2
    rw [h2]
    ring
  have hA := h2fun_gives_A_S f τ
  have hSc : (((ModularGroup.S • τ : ℍ)) : ℂ) = -(τ : ℂ)⁻¹ := coe_S_smul τ
  rw [slash_S_app, Pi.add_apply]
  simp only [qzero_apply]
  rw [hf, hA, hSc]
  simp only [qzero_apply]
  rw [show (-12 : ℤ) = -((12 : ℕ) : ℤ) by norm_num, _root_.zpow_neg, zpow_natCast]
  field_simp
  ring

lemma qzero_gives_B_S {f : ℍ → ℂ} (hS : SlashEigen 12 (-1 : ℂ) f) (τ : ℍ) :
    qzero f (ModularGroup.S • τ)
      = (τ : ℂ) ^ 12 * (qzero f τ + (τ : ℂ)⁻¹ * h2fun f τ) := by
  have hτ : (τ : ℂ) ≠ 0 := coe_ne_zero τ
  have hB := congrFun (qzero_slash_S hS) τ
  rw [slash_S_app, Pi.add_apply] at hB
  have h' : (τ : ℂ) ^ (-12 : ℤ) * qzero f (ModularGroup.S • τ)
      = qzero f τ + (τ : ℂ)⁻¹ * h2fun f τ := by
    simpa only [Pi.add_apply] using hB
  have h2 := congrArg (fun z : ℂ => (τ : ℂ) ^ 12 * z) h'
  rw [← mul_assoc, zpow_mul_zpow_neg_twelve (τ : ℂ) hτ, one_mul] at h2
  exact h2

/-- `h₂` at `S • τ`. -/
lemma h2fun_S_smul_S {f : ℍ → ℂ} (hS : SlashEigen 12 (-1 : ℂ) f) (τ : ℍ) :
    h2fun f (ModularGroup.S • τ) = (τ : ℂ) ^ 10 * h2fun f τ := by
  have hτ : (τ : ℂ) ≠ 0 := coe_ne_zero τ
  have hA := h2fun_gives_A_S f τ
  have hB := qzero_gives_B_S hS τ
  have hcoef : (((ModularGroup.S • τ : ℍ)) : ℂ) ^ (-12 : ℤ) = (τ : ℂ) ^ 12 := by
    rw [coe_S_smul, zpow_neg_inv (τ : ℂ) (by norm_num : Even (12 : ℤ))]
    rfl
  have hcA : (fstDiff f ∣[(12 : ℤ)] ModularGroup.S) (ModularGroup.S • τ)
      = (τ : ℂ) ^ 12 * fstDiff f τ := by
    rw [slash_S_app, S_smul_S_smul, hcoef]
  have hSc : (((ModularGroup.S • τ : ℍ)) : ℂ) = -(τ : ℂ)⁻¹ := coe_S_smul τ
  rw [h2fun_apply, h2fun_apply, hcA, hSc, hA, hB]
  field_simp
  rw [h2fun_apply]
  ring

/-- `h₂` is invariant under `S` at weight `10`. -/
lemma h2fun_slash_S {f : ℍ → ℂ} (hS : SlashEigen 12 (-1 : ℂ) f) :
    h2fun f ∣[(10 : ℤ)] ModularGroup.S = h2fun f := by
  funext τ
  have hτ : (τ : ℂ) ≠ 0 := coe_ne_zero τ
  rw [slash_S_app, h2fun_S_smul_S hS τ, ← mul_assoc,
    zpow_neg_ten_mul_zpow_ten (τ : ℂ) hτ, one_mul]

/-- `(fstDiff f ∣[12] S) ∣[12] T = fstDiff f ∣[12] S + fstDiff f + 2 f`. -/
lemma fstDiff_slash_S_T {f : ℍ → ℂ} (hT2 : AnnT2 f) (hS : SlashEigen 12 (-1 : ℂ) f) :
    (fstDiff f ∣[(12 : ℤ)] ModularGroup.S) ∣[(12 : ℤ)] ModularGroup.T
      = fstDiff f ∣[(12 : ℤ)] ModularGroup.S + fstDiff f + (2 : ℂ) • f := by
  rw [fstDiff_slash_S hS, SlashAction.add_slash, slash_TS_T hT2 hS, slash_T_eq]
  abel

/-- `h₂` is invariant under `T`. -/
lemma h2fun_vadd_one {f : ℍ → ℂ} (hT2 : AnnT2 f) (hS : SlashEigen 12 (-1 : ℂ) f)
    (τ : ℍ) :
    h2fun f ((1 : ℝ) +ᵥ τ) = h2fun f τ := by
  have h1 : (fstDiff f ∣[(12 : ℤ)] ModularGroup.S) ((1 : ℝ) +ᵥ τ)
      = (fstDiff f ∣[(12 : ℤ)] ModularGroup.S) τ + fstDiff f τ + 2 * f τ := by
    have h := congrFun (fstDiff_slash_S_T hT2 hS) τ
    rw [slash_T_app] at h
    simpa [Pi.add_apply, Pi.smul_apply, smul_eq_mul] using h
  have h2 : fstDiff f ((1 : ℝ) +ᵥ τ) = fstDiff f τ := fstDiff_vadd_one hT2 τ
  have h3 : qzero f ((1 : ℝ) +ᵥ τ) = qzero f τ := qzero_vadd_one hT2 τ
  have hc : (((1 : ℝ) +ᵥ τ : ℍ) : ℂ) = 1 + (τ : ℂ) := by
    rw [UpperHalfPlane.coe_vadd]
    push_cast
    ring
  rw [h2fun_apply, h2fun_apply, h1, h2, h3, hc, qzero_apply]
  ring


/-! ## The quasimodular parts `m` and `F₀` -/

/-- The weight-twelve modular form attached to `f`: `m = 2B - (πi/3) h₂ E₂`. -/
def mfun (f : ℍ → ℂ) : ℍ → ℂ :=
  (fun τ : ℍ => (2 : ℂ) * qzero f τ)
    - (fun τ : ℍ => ((Real.pi : ℂ) * Complex.I / 3) * (h2fun f τ * Work.Modular.E2 τ))

/-- The weight-fourteen modular form attached to `f`:
`F₀ = A - (πi/6) m E₂ + (π²/36) h₂ E₂²`. -/
def F0fun (f : ℍ → ℂ) : ℍ → ℂ :=
  fstDiff f
    - (fun τ : ℍ => ((Real.pi : ℂ) * Complex.I / 6) * (mfun f τ * Work.Modular.E2 τ))
    + (fun τ : ℍ => ((Real.pi : ℂ) ^ 2 / 36) * (h2fun f τ * Work.Modular.E2 τ ^ 2))

lemma qzero_eq_mfun (f : ℍ → ℂ) :
    qzero f
      = (fun τ : ℍ => ((Real.pi : ℂ) * Complex.I / 6) * (h2fun f τ * Work.Modular.E2 τ))
        + (fun τ : ℍ => (1 / 2 : ℂ) * mfun f τ) := by
  funext τ
  simp only [mfun, Pi.add_apply, Pi.sub_apply, qzero_apply]
  ring

lemma fstDiff_eq_F0fun (f : ℍ → ℂ) :
    fstDiff f
      = F0fun f
        + (fun τ : ℍ => ((Real.pi : ℂ) * Complex.I / 6) * (mfun f τ * Work.Modular.E2 τ))
        - (fun τ : ℍ => ((Real.pi : ℂ) ^ 2 / 36) * (h2fun f τ * Work.Modular.E2 τ ^ 2)) := by
  rw [F0fun]
  abel

lemma qzero_slash_T {f : ℍ → ℂ} (hT2 : AnnT2 f) :
    qzero f ∣[(12 : ℤ)] ModularGroup.T = qzero f := by
  funext τ
  rw [slash_T_app]
  exact qzero_vadd_one hT2 τ

lemma h2fun_slash_T {f : ℍ → ℂ} (hT2 : AnnT2 f) (hS : SlashEigen 12 (-1 : ℂ) f) :
    h2fun f ∣[(10 : ℤ)] ModularGroup.T = h2fun f := by
  funext τ
  rw [slash_T_app]
  exact h2fun_vadd_one hT2 hS τ

lemma E2_slash_T : Work.Modular.E2 ∣[(2 : ℤ)] ModularGroup.T = Work.Modular.E2 := by
  funext τ
  rw [slash_T_app, ← modular_T_smul]
  exact Work.Modular.E2_T_smul τ

lemma mfun_slash_T {f : ℍ → ℂ} (hT2 : AnnT2 f) (hS : SlashEigen 12 (-1 : ℂ) f) :
    mfun f ∣[(12 : ℤ)] ModularGroup.T = mfun f := by
  funext τ
  rw [slash_T_app]
  simp only [mfun, Pi.sub_apply, Pi.mul_apply]
  rw [qzero_vadd_one hT2 τ, h2fun_vadd_one hT2 hS τ, ← modular_T_smul,
    Work.Modular.E2_T_smul τ]

/-- `m` is invariant under `S` at weight `12`. -/
lemma mfun_slash_S {f : ℍ → ℂ} (hS : SlashEigen 12 (-1 : ℂ) f) :
    mfun f ∣[(12 : ℤ)] ModularGroup.S = mfun f := by
  funext τ
  have hτ : (τ : ℂ) ≠ 0 := coe_ne_zero τ
  have hB := qzero_gives_B_S hS τ
  have hH := h2fun_S_smul_S hS τ
  have hE := Work.Modular.E2_S_smul τ
  rw [slash_S_app]
  simp only [mfun, Pi.sub_apply, Pi.mul_apply]
  rw [hB, hH, hE]
  rw [show (-12 : ℤ) = -((12 : ℕ) : ℤ) by norm_num, _root_.zpow_neg, zpow_natCast]
  field_simp
  ring_nf
  simp only [Complex.I_mul_I, Complex.I_sq, Complex.I_pow_three, Complex.I_pow_four]
  ring

lemma F0fun_slash_T {f : ℍ → ℂ} (hT2 : AnnT2 f) (hS : SlashEigen 12 (-1 : ℂ) f) :
    F0fun f ∣[(14 : ℤ)] ModularGroup.T = F0fun f := by
  funext τ
  have hm : mfun f ((1 : ℝ) +ᵥ τ) = mfun f τ := by
    have h := congrFun (mfun_slash_T hT2 hS) τ
    rwa [slash_T_app] at h
  rw [slash_T_app]
  simp only [F0fun, Pi.add_apply, Pi.sub_apply, Pi.mul_apply]
  rw [fstDiff_vadd_one hT2 τ, hm, h2fun_vadd_one hT2 hS τ, ← modular_T_smul,
    Work.Modular.E2_T_smul τ]

/-- The pointwise form of the `S`-behaviour of `m`. -/
lemma mfun_gives_at_S {f : ℍ → ℂ} (hS : SlashEigen 12 (-1 : ℂ) f) (τ : ℍ) :
    mfun f (ModularGroup.S • τ) = (τ : ℂ) ^ 12 * mfun f τ := by
  have hτ : (τ : ℂ) ≠ 0 := coe_ne_zero τ
  have hm := congrFun (mfun_slash_S hS) τ
  rw [slash_S_app] at hm
  have h' : (τ : ℂ) ^ (-12 : ℤ) * mfun f (ModularGroup.S • τ) = mfun f τ := by
    simpa using hm
  have h2 := congrArg (fun z : ℂ => (τ : ℂ) ^ 12 * z) h'
  rw [← mul_assoc, zpow_mul_zpow_neg_twelve (τ : ℂ) hτ, one_mul] at h2
  exact h2

/-- `F₀` is invariant under `S` at weight `14`. -/
lemma F0fun_slash_S {f : ℍ → ℂ} (hT2 : AnnT2 f) (hS : SlashEigen 12 (-1 : ℂ) f) :
    F0fun f ∣[(14 : ℤ)] ModularGroup.S = F0fun f := by
  funext τ
  have hτ : (τ : ℂ) ≠ 0 := coe_ne_zero τ
  have hA := h2fun_gives_A_S f τ
  have hm := mfun_gives_at_S hS τ
  have hH := h2fun_S_smul_S hS τ
  have hE := Work.Modular.E2_S_smul τ
  rw [slash_S_app]
  simp only [F0fun, Pi.add_apply, Pi.sub_apply, Pi.mul_apply]
  rw [hA, hm, hH, hE]
  simp only [mfun, Pi.sub_apply, Pi.mul_apply]
  rw [show (-14 : ℤ) = -((14 : ℕ) : ℤ) by norm_num, _root_.zpow_neg, zpow_natCast]
  field_simp
  ring_nf
  simp only [Complex.I_mul_I, Complex.I_sq, Complex.I_pow_three, Complex.I_pow_four]
  ring

/-! ## Membership in `𝒫` -/

lemma inP_coe : Work.Kernels.InP (fun τ : ℍ => (τ : ℂ)) := by
  refine ⟨UpperHalfPlane.mdifferentiable_coe, ?_⟩
  refine ⟨1, 0, 1, by norm_num, by norm_num, by norm_num, fun τ _ => ?_⟩
  simp only [Real.rpow_zero, Real.rpow_one, mul_one, inv_one]
  linarith [norm_nonneg (τ : ℂ)]

lemma inP_fstDiff {f : ℍ → ℂ} (hf : Work.Kernels.InP f) : Work.Kernels.InP (fstDiff f) := by
  have h := hf.slash (12 : ℤ) ModularGroup.T
  rw [fstDiff_eq_slash_T_sub]
  exact h.sub hf

lemma inP_qzero {f : ℍ → ℂ} (hf : Work.Kernels.InP f) : Work.Kernels.InP (qzero f) := by
  have h1 : Work.Kernels.InP (fstDiff f) := inP_fstDiff hf
  have h2 : Work.Kernels.InP (fun τ : ℍ => (τ : ℂ) * fstDiff f τ) := inP_coe.mul h1
  have h3 : Work.Kernels.InP (fun τ : ℍ => f τ - (τ : ℂ) * fstDiff f τ) := hf.sub h2
  exact h3

lemma inP_h2fun {f : ℍ → ℂ} (hf : Work.Kernels.InP f) : Work.Kernels.InP (h2fun f) := by
  have hA := inP_fstDiff hf
  have hB := inP_qzero hf
  have h1 : Work.Kernels.InP (fstDiff f ∣[(12 : ℤ)] ModularGroup.S) :=
    hA.slash (12 : ℤ) ModularGroup.S
  have h2 : Work.Kernels.InP (fun τ : ℍ => (τ : ℂ) ^ 2 * fstDiff f τ) := (inP_coe.pow 2).mul hA
  have h3 : Work.Kernels.InP (fun τ : ℍ => (2 : ℂ) * (τ : ℂ) * qzero f τ) :=
    (inP_coe.const_mul 2).mul hB
  have h4 : Work.Kernels.InP (fun τ : ℍ => (fstDiff f ∣[(12 : ℤ)] ModularGroup.S) τ
      - (τ : ℂ) ^ 2 * fstDiff f τ - (2 : ℂ) * (τ : ℂ) * qzero f τ) := (h1.sub h2).sub h3
  exact h4

lemma inP_E2 : Work.Kernels.InP Work.Modular.E2 :=
  Work.Kernels.ClassicalFacts.E2Fun_mem_InP

lemma inP_mfun {f : ℍ → ℂ} (hf : Work.Kernels.InP f) : Work.Kernels.InP (mfun f) := by
  have hB := inP_qzero hf
  have hH := inP_h2fun hf
  have h3 : Work.Kernels.InP
      (fun τ : ℍ => ((Real.pi : ℂ) * Complex.I / 3) * (h2fun f τ * Work.Modular.E2 τ)) :=
    (hH.mul inP_E2).const_mul _
  have h4 : Work.Kernels.InP (fun τ : ℍ => (2 : ℂ) * qzero f τ
      - ((Real.pi : ℂ) * Complex.I / 3) * (h2fun f τ * Work.Modular.E2 τ)) :=
    (hB.const_mul 2).sub h3
  exact h4

lemma inP_F0fun {f : ℍ → ℂ} (hf : Work.Kernels.InP f) : Work.Kernels.InP (F0fun f) := by
  have hA := inP_fstDiff hf
  have hm := inP_mfun hf
  have hH := inP_h2fun hf
  have h2 : Work.Kernels.InP
      (fun τ : ℍ => ((Real.pi : ℂ) * Complex.I / 6) * (mfun f τ * Work.Modular.E2 τ)) :=
    (hm.mul inP_E2).const_mul _
  have h3 : Work.Kernels.InP
      (fun τ : ℍ => ((Real.pi : ℂ) ^ 2 / 36) * (h2fun f τ * Work.Modular.E2 τ ^ 2)) :=
    ((hH.mul (inP_E2.pow 2))).const_mul _
  have h4 : Work.Kernels.InP (fun τ : ℍ => fstDiff f τ
      - ((Real.pi : ℂ) * Complex.I / 6) * (mfun f τ * Work.Modular.E2 τ)
      + ((Real.pi : ℂ) ^ 2 / 36) * (h2fun f τ * Work.Modular.E2 τ ^ 2)) :=
    (hA.sub h2).add h3
  exact h4


/-! ## Periodicity bridges and closure of analyticity at the cusp -/

lemma periodic_comp_ofComplex_of_vadd_one {F : ℍ → ℂ}
    (hper : ∀ τ : ℍ, F ((1 : ℝ) +ᵥ τ) = F τ) :
    Function.Periodic (F ∘ UpperHalfPlane.ofComplex) 1 := by
  intro z
  by_cases hz : 0 < z.im
  · have hz' : 0 < (z + 1).im := by simpa [Complex.add_im] using hz
    have hv : UpperHalfPlane.ofComplex (z + 1) = (1 : ℝ) +ᵥ UpperHalfPlane.ofComplex z := by
      apply UpperHalfPlane.ext
      rw [UpperHalfPlane.ofComplex_apply_of_im_pos hz',
        UpperHalfPlane.ofComplex_apply_of_im_pos hz, UpperHalfPlane.coe_vadd]
      push_cast
      ring
    rw [Function.comp_apply, Function.comp_apply, hv, hper]
  · have hz' : ¬ 0 < (z + 1).im := by simpa [Complex.add_im] using hz
    rw [Function.comp_apply, Function.comp_apply,
      UpperHalfPlane.ofComplex_apply_eq_of_im_nonpos (not_lt.mp hz') (not_lt.mp hz)]

lemma mfun_vadd_one {f : ℍ → ℂ} (hT2 : AnnT2 f) (hS : SlashEigen 12 (-1 : ℂ) f) (τ : ℍ) :
    mfun f ((1 : ℝ) +ᵥ τ) = mfun f τ := by
  have h := congrFun (mfun_slash_T hT2 hS) τ
  rwa [slash_T_app] at h

lemma F0fun_vadd_one {f : ℍ → ℂ} (hT2 : AnnT2 f) (hS : SlashEigen 12 (-1 : ℂ) f) (τ : ℍ) :
    F0fun f ((1 : ℝ) +ᵥ τ) = F0fun f τ := by
  have h := congrFun (F0fun_slash_T hT2 hS) τ
  rwa [slash_T_app] at h

lemma analyticAt_cuspFunction_add {F G : ℍ → ℂ}
    (hF : AnalyticAt ℂ (UpperHalfPlane.cuspFunction 1 F) 0)
    (hG : AnalyticAt ℂ (UpperHalfPlane.cuspFunction 1 G) 0) :
    AnalyticAt ℂ (UpperHalfPlane.cuspFunction 1 (F + G)) 0 := by
  have hcomp : (F + G) ∘ UpperHalfPlane.ofComplex
      = (F ∘ UpperHalfPlane.ofComplex) + (G ∘ UpperHalfPlane.ofComplex) := rfl
  have h := Function.Periodic.cuspFunction_add (h := (1 : ℝ)) hF.continuousAt hG.continuousAt
  rw [UpperHalfPlane.cuspFunction, hcomp, h]
  exact hF.add hG

lemma analyticAt_cuspFunction_neg {F : ℍ → ℂ}
    (hF : AnalyticAt ℂ (UpperHalfPlane.cuspFunction 1 F) 0) :
    AnalyticAt ℂ (UpperHalfPlane.cuspFunction 1 (-F)) 0 := by
  have hcomp : (-F) ∘ UpperHalfPlane.ofComplex
      = -(F ∘ UpperHalfPlane.ofComplex) := rfl
  have h := Function.Periodic.cuspFunction_neg (h := (1 : ℝ)) hF.continuousAt
  rw [UpperHalfPlane.cuspFunction, hcomp, h]
  exact hF.neg

lemma analyticAt_cuspFunction_smul (c : ℂ) {F : ℍ → ℂ}
    (hF : AnalyticAt ℂ (UpperHalfPlane.cuspFunction 1 F) 0) :
    AnalyticAt ℂ (UpperHalfPlane.cuspFunction 1 (c • F)) 0 := by
  have hcomp : (c • F) ∘ UpperHalfPlane.ofComplex
      = c • (F ∘ UpperHalfPlane.ofComplex) := rfl
  have h := Function.Periodic.cuspFunction_smul (h := (1 : ℝ)) hF.continuousAt c
  rw [UpperHalfPlane.cuspFunction, hcomp, h]
  exact hF.const_smul

lemma analyticAt_cuspFunction_of_modularForm {k : ℤ} (G : ModularForm 𝒮ℒ k) :
    AnalyticAt ℂ (UpperHalfPlane.cuspFunction 1 (⇑G)) 0 :=
  ModularFormClass.analyticAt_cuspFunction_zero (f := G) one_pos one_mem_strictPeriods_SL

lemma analyticAt_cuspFunction_E2 :
    AnalyticAt ℂ (UpperHalfPlane.cuspFunction 1 Work.Modular.E2) 0 :=
  UpperHalfPlane.analyticAt_cuspFunction_zero one_pos Work.Modular.E2_periodic_one
    E2_mdifferentiable EisensteinSeries.isBoundedAtImInfty_E2


lemma f_eq_qzero_add (f : ℍ → ℂ) :
    f = qzero f + (fun τ : ℍ => (τ : ℂ) * fstDiff f τ) := by
  funext τ
  simp only [Pi.add_apply, qzero_apply]
  ring

lemma qzero_eq_mfun_smul (f : ℍ → ℂ) :
    qzero f = ((Real.pi : ℂ) * Complex.I / 6) • (h2fun f * Work.Modular.E2)
      + (1 / 2 : ℂ) • mfun f := by
  rw [qzero_eq_mfun f]
  funext τ
  simp only [Pi.add_apply, Pi.smul_apply, Pi.mul_apply, smul_eq_mul]

lemma fstDiff_eq_F0fun_smul (f : ℍ → ℂ) :
    fstDiff f = F0fun f + ((Real.pi : ℂ) * Complex.I / 6) • (mfun f * Work.Modular.E2)
      - ((Real.pi : ℂ) ^ 2 / 36) • (h2fun f * Work.Modular.E2 ^ 2) := by
  funext τ
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.mul_apply, Pi.pow_apply,
    smul_eq_mul, F0fun]
  ring

end Work.Rigidity
