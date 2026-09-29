import Mathlib
import Submission.Work.TMContract.Defs
import Submission.Work.TMComp.RedProj.Basic

/-!
# C11 (`P_Reducibility`), Claim B: an analytic coboundary makes `E` reducible

Given the analytic conjugacy `C` of the almost Mathieu cocycle at energy `E` to the rotations
`rot (φ x)` (the output of component C9) and an analytic 1-periodic solution `ψ` of the
cohomological equation `φ x - ∫φ = ψ (x+α) - ψ x`, the gauge
`B x = rot (-(ψ x)) * C x` conjugates the cocycle to the *constant* rotation `rot (∫φ)`, and
`B` is analytic, 1-periodic, of determinant 1 and of degree 0.  Hence `E ∈ RedSet α λ`
(AJ (4.18)–(4.20)).
-/

open LeanEval.Analysis.TenMartini

set_option autoImplicit false

noncomputable section

namespace Work.TMComp.RedProj

open Work.TMContract

/-! ## Analyticity helpers for the gauge `x ↦ rot (-ψ x) * C x` -/

theorem analyticOnNhd_cos_comp (ψ : ℝ → ℝ) (hψ : AnalyticOnNhd ℝ ψ Set.univ) (c : ℝ) :
    AnalyticOnNhd ℝ (fun x => Real.cos (c * ψ x)) Set.univ :=
  (Real.analyticOnNhd_cos (s := Set.univ)).comp (analyticOnNhd_const.mul hψ)
    (fun x _ => trivial)

theorem analyticOnNhd_sin_comp (ψ : ℝ → ℝ) (hψ : AnalyticOnNhd ℝ ψ Set.univ) (c : ℝ) :
    AnalyticOnNhd ℝ (fun x => Real.sin (c * ψ x)) Set.univ :=
  (Real.analyticOnNhd_sin (s := Set.univ)).comp (analyticOnNhd_const.mul hψ)
    (fun x _ => trivial)

/-- Entrywise analyticity of `x ↦ rot (g x)` for analytic `g`. -/
theorem analyticOnNhd_rot_comp {g : ℝ → ℝ} (hg : AnalyticOnNhd ℝ g Set.univ) :
    ∀ i j, AnalyticOnNhd ℝ (fun x => rot (g x) i j) Set.univ := by
  have h1 : AnalyticOnNhd ℝ (fun x => 2 * Real.pi * g x) Set.univ :=
    analyticOnNhd_const.mul hg
  have hc : AnalyticOnNhd ℝ (fun x => Real.cos (2 * Real.pi * g x)) Set.univ :=
    (Real.analyticOnNhd_cos (s := Set.univ)).comp h1 (fun x _ => trivial)
  have hs : AnalyticOnNhd ℝ (fun x => Real.sin (2 * Real.pi * g x)) Set.univ :=
    (Real.analyticOnNhd_sin (s := Set.univ)).comp h1 (fun x _ => trivial)
  intro i j
  fin_cases i <;> fin_cases j <;>
    first
      | exact hc
      | exact hs.neg
      | exact hs
      | exact hc

/-- Entrywise analyticity of the product of two matrix-valued analytic functions. -/
theorem analyticOnNhd_matrix_mul {A B : ℝ → Matrix (Fin 2) (Fin 2) ℝ}
    (hA : ∀ i j, AnalyticOnNhd ℝ (fun x => A x i j) Set.univ)
    (hB : ∀ i j, AnalyticOnNhd ℝ (fun x => B x i j) Set.univ) :
    ∀ i j, AnalyticOnNhd ℝ (fun x => (A x * B x) i j) Set.univ := by
  intro i j
  have h : (fun x => (A x * B x) i j)
      = fun x => A x i 0 * B x 0 j + A x i 1 * B x 1 j := by
    funext x
    rw [Matrix.mul_apply, Fin.sum_univ_two]
  rw [h]
  exact ((hA i 0).mul (hB 0 j)).add ((hA i 1).mul (hB 1 j))

/-! ## Claim B -/

/-- **Claim B** (AJ (4.18)–(4.20)): an analytic 1-periodic coboundary `ψ` for the rotation
angle `φ` makes the energy `E` reducible. -/
theorem mem_RedSet_of_coboundary (α lam E : ℝ)
    (C : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (φ ψ : ℝ → ℝ)
    (hCan : ∀ i j, AnalyticOnNhd ℝ (fun x => C x i j) Set.univ)
    (hCp : ∀ x, C (x + 1) = C x) (hCdet : ∀ x, (C x).det = 1)
    (hCdeg : HasDegree C 0)
    (hconj : ∀ x, C (x + α) * tmR lam E x = rot (φ x) * C x)
    (hψan : AnalyticOnNhd ℝ ψ Set.univ) (hψp : ∀ x, ψ (x + 1) = ψ x)
    (hψeq : ∀ x, φ x - (∫ t in (0 : ℝ)..1, φ t) = ψ (x + α) - ψ x) :
    E ∈ RedSet α lam := by
  refine ⟨fun x => rot (-(ψ x)) * C x, ∫ t in (0 : ℝ)..1, φ t, ?_, ?_, ?_, ?_, ?_⟩
  · exact analyticOnNhd_matrix_mul (analyticOnNhd_rot_comp (hψan.neg)) hCan
  · intro x
    change rot (-(ψ (x + 1))) * C (x + 1) = rot (-(ψ x)) * C x
    rw [hψp x, hCp x]
  · intro x
    rw [Matrix.det_mul]
    simp [rot_det, hCdet x]
  · exact hasDegree_rot_mul hCdeg (hψan.continuous.neg) (fun x => by rw [hψp x])
  · intro x
    have hrot : rot (-(ψ (x + α))) * rot (φ x)
        = rot (∫ t in (0 : ℝ)..1, φ t) * rot (-(ψ x)) := by
      rw [rot_mul, rot_mul]
      congr 1
      linarith [hψeq x]
    calc rot (-(ψ (x + α))) * C (x + α) * tmR lam E x
        = rot (-(ψ (x + α))) * (C (x + α) * tmR lam E x) := by rw [mul_assoc]
      _ = rot (-(ψ (x + α))) * (rot (φ x) * C x) := by rw [hconj x]
      _ = (rot (-(ψ (x + α))) * rot (φ x)) * C x := by rw [mul_assoc]
      _ = (rot (∫ t in (0 : ℝ)..1, φ t) * rot (-(ψ x))) * C x := by rw [hrot]
      _ = rot (∫ t in (0 : ℝ)..1, φ t) * (rot (-(ψ x)) * C x) := by rw [mul_assoc]

end Work.TMComp.RedProj
