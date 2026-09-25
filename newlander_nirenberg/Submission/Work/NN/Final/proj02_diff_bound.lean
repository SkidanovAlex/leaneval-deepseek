import Mathlib
import Submission.Work.NN.Final.Defs

/-!
Copyright: none.  Part of the `Newlander-Nirenberg` formalisation project.

# The Lipschitz bound for the `(0,2)`-projection under perturbation of `J`

The `(0,2)`-projection of a `2`-form at a point,

  `proj02 J Ω z V W = (1/4)(Ω z V W + i·Ω z (J z V) W + i·Ω z V (J z W) - Ω z (J z V) (J z W))`,

is a *bilinear* expression in the values `J z v`.  Consequently, when the complex structure is
perturbed from the standard one `JstdCn n` (multiplication by `i`) by a field `A` which is small of
size `ε`, the projections differ by `O(ε·‖Ω z‖·(‖V‖+1)(‖W‖+1))`, with a constant independent of
`n`, `A`, `ε`, `Ω`, `z`, `V`, `W`.  This is the estimate `proj02_diff_bound` used in the
perturbation argument of the assembly chapter.
-/

noncomputable section

open scoped NNReal ENNReal ContDiff
open Set

namespace Work.NN.Final

/-- **The algebraic decomposition of the perturbation of the `(0,2)`-projection.**  Differences of
the `(0,2)`-projections with respect to `Jstd + A` and `Jstd` involve only `A`, and are *linear* in
`Ω`; the multilinearity of `Ω z` expands the difference into five elementary terms. -/
lemma proj02_pert_diff {n : ℕ} (A : (Fin n → ℂ) → (Fin n → ℂ) →L[ℝ] (Fin n → ℂ))
    (Ω : (Fin n → ℂ) → (Fin n → ℂ) →L[ℝ] (Fin n → ℂ) →L[ℝ] ℂ) (z V W : Fin n → ℂ) :
    proj02 (Work.NN.Core.JstdCn n + A) (fun z' a b => (Ω z') a b) z V W
      - proj02 (Work.NN.Core.JstdCn n) (fun z' a b => (Ω z') a b) z V W
    = (1/4 : ℂ) * (Complex.I * ((Ω z) (A z V)) W + Complex.I * ((Ω z) V) (A z W)
        - ((Ω z) (Work.NN.Core.JstdCn n z V)) (A z W)
        - ((Ω z) (A z V)) (Work.NN.Core.JstdCn n z W)
        - ((Ω z) (A z V)) (A z W)) := by
  simp only [proj02, Pi.add_apply, map_add, add_apply]
  ring

/-- Norm bound for the two-fold evaluation of a continuous bilinear form. -/
lemma norm_clm_clm_apply_le {n : ℕ} (T : (Fin n → ℂ) →L[ℝ] (Fin n → ℂ) →L[ℝ] ℂ)
    (u w : Fin n → ℂ) : ‖(T u) w‖ ≤ ‖T‖ * ‖u‖ * ‖w‖ := by
  calc ‖(T u) w‖ ≤ ‖T u‖ * ‖w‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ (‖T‖ * ‖u‖) * ‖w‖ :=
        mul_le_mul_of_nonneg_right (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg w)
    _ = ‖T‖ * ‖u‖ * ‖w‖ := by ring

/-- **The Lipschitz bound for `proj02` under a small perturbation `A` of the complex structure.**
There is an absolute constant `C` (here `C = 2`) such that for every field `A` with `‖A z‖ ≤ ε`
and every `2`-form `Ω` the two `(0,2)`-projections differ by at most
`C·ε·‖Ω z‖·(‖V‖+1)(‖W‖+1)`. -/
theorem proj02_diff_bound {n : ℕ} : ∃ C : ℝ, 0 < C ∧ ∀ (A : (Fin n → ℂ) → (Fin n → ℂ) →L[ℝ] (Fin n → ℂ)) (ε : ℝ), 0 ≤ ε → ε ≤ 1 → (∀ z, ‖A z‖ ≤ ε) → ∀ (Ω : (Fin n → ℂ) → (Fin n → ℂ) →L[ℝ] (Fin n → ℂ) →L[ℝ] ℂ) (z V W : Fin n → ℂ), ‖Work.NN.Final.proj02 (Work.NN.Core.JstdCn n + A) (fun z' a b => (Ω z') a b) z V W - Work.NN.Final.proj02 (Work.NN.Core.JstdCn n) (fun z' a b => (Ω z') a b) z V W‖ ≤ C * ε * ‖Ω z‖ * ((‖V‖ + 1) * (‖W‖ + 1)) := by
  refine ⟨2, by norm_num, ?_⟩
  intro A ε hε0 hε1 hA Ω z V W
  rw [proj02_pert_diff A Ω z V W]
  have hΩnn : (0:ℝ) ≤ ‖Ω z‖ := norm_nonneg (Ω z)
  have hVnn : (0:ℝ) ≤ ‖V‖ := norm_nonneg V
  have hWnn : (0:ℝ) ≤ ‖W‖ := norm_nonneg W
  have hAV : ‖A z V‖ ≤ ε * ‖V‖ := by
    calc ‖A z V‖ ≤ ‖A z‖ * ‖V‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ ε * ‖V‖ := mul_le_mul_of_nonneg_right (hA z) hVnn
  have hAW : ‖A z W‖ ≤ ε * ‖W‖ := by
    calc ‖A z W‖ ≤ ‖A z‖ * ‖W‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ ε * ‖W‖ := mul_le_mul_of_nonneg_right (hA z) hWnn
  have hJV : ‖(Work.NN.Core.JstdCn n z) V‖ = ‖V‖ := by
    rw [Work.NN.Core.JstdCn_apply, norm_smul, Complex.norm_I, one_mul]
  have hJW : ‖(Work.NN.Core.JstdCn n z) W‖ = ‖W‖ := by
    rw [Work.NN.Core.JstdCn_apply, norm_smul, Complex.norm_I, one_mul]
  have hM : (0:ℝ) ≤ ε * ‖Ω z‖ * ‖V‖ * ‖W‖ :=
    mul_nonneg (mul_nonneg (mul_nonneg hε0 hΩnn) hVnn) hWnn
  have ht1 : ‖(Ω z (A z V)) W‖ ≤ ε * ‖Ω z‖ * ‖V‖ * ‖W‖ := by
    calc ‖(Ω z (A z V)) W‖ ≤ ‖Ω z‖ * ‖A z V‖ * ‖W‖ := norm_clm_clm_apply_le (Ω z) _ _
      _ ≤ ‖Ω z‖ * (ε * ‖V‖) * ‖W‖ :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hAV hΩnn) hWnn
      _ = ε * ‖Ω z‖ * ‖V‖ * ‖W‖ := by ring
  have ht2 : ‖(Ω z V) (A z W)‖ ≤ ε * ‖Ω z‖ * ‖V‖ * ‖W‖ := by
    calc ‖(Ω z V) (A z W)‖ ≤ ‖Ω z‖ * ‖V‖ * ‖A z W‖ := norm_clm_clm_apply_le (Ω z) _ _
      _ ≤ ‖Ω z‖ * ‖V‖ * (ε * ‖W‖) :=
            mul_le_mul_of_nonneg_left hAW (mul_nonneg hΩnn hVnn)
      _ = ε * ‖Ω z‖ * ‖V‖ * ‖W‖ := by ring
  have ht3 : ‖(Ω z ((Work.NN.Core.JstdCn n z) V)) (A z W)‖ ≤ ε * ‖Ω z‖ * ‖V‖ * ‖W‖ := by
    calc ‖(Ω z ((Work.NN.Core.JstdCn n z) V)) (A z W)‖
        ≤ ‖Ω z‖ * ‖(Work.NN.Core.JstdCn n z) V‖ * ‖A z W‖ := norm_clm_clm_apply_le (Ω z) _ _
      _ = ‖Ω z‖ * ‖V‖ * ‖A z W‖ := by rw [hJV]
      _ ≤ ‖Ω z‖ * ‖V‖ * (ε * ‖W‖) :=
            mul_le_mul_of_nonneg_left hAW (mul_nonneg hΩnn hVnn)
      _ = ε * ‖Ω z‖ * ‖V‖ * ‖W‖ := by ring
  have ht4 : ‖(Ω z (A z V)) ((Work.NN.Core.JstdCn n z) W)‖ ≤ ε * ‖Ω z‖ * ‖V‖ * ‖W‖ := by
    calc ‖(Ω z (A z V)) ((Work.NN.Core.JstdCn n z) W)‖
        ≤ ‖Ω z‖ * ‖A z V‖ * ‖(Work.NN.Core.JstdCn n z) W‖ := norm_clm_clm_apply_le (Ω z) _ _
      _ = ‖Ω z‖ * ‖A z V‖ * ‖W‖ := by rw [hJW]
      _ ≤ ‖Ω z‖ * (ε * ‖V‖) * ‖W‖ :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hAV hΩnn) hWnn
      _ = ε * ‖Ω z‖ * ‖V‖ * ‖W‖ := by ring
  have ht5 : ‖(Ω z (A z V)) (A z W)‖ ≤ ε * ‖Ω z‖ * ‖V‖ * ‖W‖ := by
    calc ‖(Ω z (A z V)) (A z W)‖ ≤ ‖Ω z‖ * ‖A z V‖ * ‖A z W‖ := norm_clm_clm_apply_le (Ω z) _ _
      _ ≤ ‖Ω z‖ * (ε * ‖V‖) * (ε * ‖W‖) :=
            mul_le_mul (mul_le_mul_of_nonneg_left hAV hΩnn) hAW (norm_nonneg (A z W))
              (mul_nonneg hΩnn (mul_nonneg hε0 hVnn))
      _ = ε * (ε * ‖Ω z‖ * ‖V‖ * ‖W‖) := by ring
      _ ≤ 1 * (ε * ‖Ω z‖ * ‖V‖ * ‖W‖) := mul_le_mul_of_nonneg_right hε1 hM
      _ = ε * ‖Ω z‖ * ‖V‖ * ‖W‖ := by ring
  have htri : ‖Complex.I * ((Ω z (A z V)) W) + Complex.I * ((Ω z V) (A z W))
      - (Ω z ((Work.NN.Core.JstdCn n z) V)) (A z W)
      - (Ω z (A z V)) ((Work.NN.Core.JstdCn n z) W)
      - (Ω z (A z V)) (A z W)‖
      ≤ 5 * (ε * ‖Ω z‖ * ‖V‖ * ‖W‖) := by
    have h1 : ‖Complex.I * ((Ω z (A z V)) W)‖ ≤ ε * ‖Ω z‖ * ‖V‖ * ‖W‖ := by
      rw [norm_mul, Complex.norm_I, one_mul]; exact ht1
    have h2 : ‖Complex.I * ((Ω z V) (A z W))‖ ≤ ε * ‖Ω z‖ * ‖V‖ * ‖W‖ := by
      rw [norm_mul, Complex.norm_I, one_mul]; exact ht2
    have hh1 := norm_sub_le (Complex.I * ((Ω z (A z V)) W) + Complex.I * ((Ω z V) (A z W))
        - (Ω z ((Work.NN.Core.JstdCn n z) V)) (A z W)
        - (Ω z (A z V)) ((Work.NN.Core.JstdCn n z) W))
        ((Ω z (A z V)) (A z W))
    have hh2 := norm_sub_le (Complex.I * ((Ω z (A z V)) W) + Complex.I * ((Ω z V) (A z W))
        - (Ω z ((Work.NN.Core.JstdCn n z) V)) (A z W))
        ((Ω z (A z V)) ((Work.NN.Core.JstdCn n z) W))
    have hh3 := norm_sub_le (Complex.I * ((Ω z (A z V)) W) + Complex.I * ((Ω z V) (A z W)))
        ((Ω z ((Work.NN.Core.JstdCn n z) V)) (A z W))
    have hh4 := norm_add_le (Complex.I * ((Ω z (A z V)) W)) (Complex.I * ((Ω z V) (A z W)))
    linarith [hh1, hh2, hh3, hh4, h1, h2, ht3, ht4, ht5]
  rw [norm_mul, show ‖(1/4 : ℂ)‖ = (1/4 : ℝ) by norm_num]
  have hb : (5/4 : ℝ) * (‖V‖ * ‖W‖) ≤ 2 * ((‖V‖ + 1) * (‖W‖ + 1)) := by
    nlinarith [hVnn, hWnn]
  have h0 : (0:ℝ) ≤ ε * ‖Ω z‖ := mul_nonneg hε0 hΩnn
  have step2 : (5/4) * (ε * ‖Ω z‖ * ‖V‖ * ‖W‖) ≤ 2 * ε * ‖Ω z‖ * ((‖V‖ + 1) * (‖W‖ + 1)) := by
    have h := mul_le_mul_of_nonneg_left hb h0
    have h' : (ε * ‖Ω z‖) * ((5/4) * (‖V‖ * ‖W‖))
        ≤ (ε * ‖Ω z‖) * (2 * ((‖V‖ + 1) * (‖W‖ + 1))) := h
    nlinarith [h']
  calc (1/4 : ℝ) * ‖Complex.I * ((Ω z (A z V)) W) + Complex.I * ((Ω z V) (A z W))
        - (Ω z ((Work.NN.Core.JstdCn n z) V)) (A z W)
        - (Ω z (A z V)) ((Work.NN.Core.JstdCn n z) W)
        - (Ω z (A z V)) (A z W)‖
      ≤ (5/4) * (ε * ‖Ω z‖ * ‖V‖ * ‖W‖) := by linarith [htri]
    _ ≤ 2 * ε * ‖Ω z‖ * ((‖V‖ + 1) * (‖W‖ + 1)) := step2

end Work.NN.Final
