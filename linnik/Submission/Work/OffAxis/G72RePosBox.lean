/-
# OffAxis/G72RePosBox

`2/5 ≤ Re G72(s + iσ)` for `0 ≤ s ≤ 1`, `0 ≤ σ ≤ 3/2`.

The proof reduces to the corner `(s, σ) = (1, 3/2)`:

* `σ ↦ Re G72(s + iσ)` is non-increasing on `[0, 3/2]` because `cos (σ y) ≥ cos (3y/2)`
  pointwise on `[0,2]` (both arguments lie in `[0, π]`);
* `s ↦ Re G72(s + 3i/2)` is non-increasing on `[0,1]`: here the derivative is
  `-∫₀² y e^{-sy} cos(3y/2) g72 y dy`, which is non-positive by `G72YCosNonneg`;
* the corner value satisfies `2/5 ≤ Re G72(1 + 3i/2)` (`G72ReCornerGe`).
-/
import Mathlib
import Submission.Work.ZeroFreeTables.OffAxis.G72Base
import Submission.Work.ZeroFreeTables.OffAxis.G72Defs
import Submission.Work.OffAxis.G72RePosBoxAux

noncomputable section
namespace Work.OffAxis

open Work.ZeroFreeTables
open Work.ZeroFreeTables.OffAxis
open scoped Topology

/-- `cos (3y/2) ≤ cos (σy)` for `0 ≤ y ≤ 2`, `0 ≤ σ ≤ 3/2`. -/
lemma cos_three_halves_le_cos (y σ : ℝ) (hy0 : 0 ≤ y) (hy2 : y ≤ 2) (hσ0 : 0 ≤ σ)
    (hσ32 : σ ≤ 3/2) : Real.cos (3*y/2) ≤ Real.cos (σ*y) := by
  refine Real.cos_le_cos_of_nonneg_of_le_pi (mul_nonneg hσ0 hy0) ?_ ?_
  · nlinarith [Real.pi_gt_three]
  · nlinarith

/-- `K s = ∫₀² (1 - e^{-sy}) cos(3y/2) g72 y dy`. -/
def K (s : ℝ) : ℝ :=
  ∫ y in (0:ℝ)..2, (1 - Real.exp (-(s*y))) * Real.cos (3*y/2) * g72 y

/-- Parametric differentiation of `K`. -/
lemma hasDerivAt_K (t : ℝ) (ht : t ∈ Set.Icc (0:ℝ) 1) :
    HasDerivAt K (∫ y in (0:ℝ)..2,
        y * Real.exp (-(t*y)) * Real.cos (3*y/2) * g72 y) t := by
  have hmain : HasDerivAt (fun s : ℝ => ∫ y in (0:ℝ)..2,
      (1 - Real.exp (-(s*y))) * Real.cos (3*y/2) * g72 y)
      (∫ y in (0:ℝ)..2, y * Real.exp (-(t*y)) * Real.cos (3*y/2) * g72 y) t := by
    have hmem : Set.Ioo (-1:ℝ) 2 ∈ 𝓝 t := by
      apply IsOpen.mem_nhds isOpen_Ioo
      constructor <;> linarith [ht.1, ht.2]
    have hcont : ∀ s : ℝ, Continuous (fun y : ℝ =>
        (1 - Real.exp (-(s*y))) * Real.cos (3*y/2) * g72 y) := by
      intro s; simp only [g72]; fun_prop
    have hcont' : Continuous (fun y : ℝ =>
        y * Real.exp (-(t*y)) * Real.cos (3*y/2) * g72 y) := by
      simp only [g72]; fun_prop
    have hbcont : Continuous (fun y : ℝ => 20 * g72 y) := by
      simp only [g72]; fun_prop
    refine (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
        (a := (0:ℝ)) (b := 2) (μ := MeasureTheory.volume)
        (bound := fun y => 20 * g72 y)
        (F := fun s y => (1 - Real.exp (-(s*y))) * Real.cos (3*y/2) * g72 y)
        (F' := fun s y => y * Real.exp (-(s*y)) * Real.cos (3*y/2) * g72 y)
        hmem ?_ ((hcont t).intervalIntegrable 0 2) ?_ ?_
        (hbcont.intervalIntegrable 0 2) ?_).2
    · filter_upwards with s
      exact (hcont s).aestronglyMeasurable
    · exact hcont'.aestronglyMeasurable
    · filter_upwards with y
      intro hy x hx
      have hy' : y ∈ Set.Ioc (0:ℝ) 2 := by
        simpa [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 2)] using hy
      have hy0 : 0 ≤ y := le_of_lt hy'.1
      have hg : 0 ≤ g72 y := g72_nonneg hy0 hy'.2
      have hexp : Real.exp (-(x*y)) ≤ 9 := by
        have h1 : -(x*y) ≤ 2 := by nlinarith [hx.1, hx.2, hy0, hy'.2]
        have h2 : Real.exp (-(x*y)) ≤ Real.exp (2:ℝ) := Real.exp_le_exp.mpr h1
        have h2' : Real.exp (2:ℝ) = Real.exp 1 * Real.exp 1 := by
          rw [show (2:ℝ) = 1 + 1 by norm_num, Real.exp_add]
        have h3 : Real.exp (2:ℝ) ≤ 9 := by
          rw [h2']; nlinarith [Real.exp_one_lt_three, Real.exp_pos (1:ℝ)]
        linarith
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul,
        abs_of_nonneg (Real.exp_pos (-(x*y))).le, abs_of_nonneg hg]
      have hy2 : |y| ≤ 2 := by rw [abs_of_nonneg hy0]; exact hy'.2
      have hcos : |Real.cos (3*y/2)| ≤ 1 := Real.abs_cos_le_one _
      have step1 : |y| * Real.exp (-(x*y)) ≤ 2 * 9 :=
        mul_le_mul hy2 hexp (Real.exp_pos _).le (by norm_num)
      have step2 : |y| * Real.exp (-(x*y)) * |Real.cos (3*y/2)| ≤ 2 * 9 * 1 :=
        mul_le_mul step1 hcos (abs_nonneg _) (by norm_num)
      calc |y| * Real.exp (-(x*y)) * |Real.cos (3*y/2)| * g72 y
          ≤ (2 * 9 * 1) * g72 y := mul_le_mul_of_nonneg_right step2 hg
        _ ≤ 20 * g72 y := by nlinarith
    · filter_upwards with y
      intro hy x hx
      have h1 : HasDerivAt (fun s : ℝ => s*y) (1*y) x := (hasDerivAt_id x).mul_const y
      have h2 : HasDerivAt (fun s : ℝ => -(s*y)) (-(1*y)) x := h1.neg
      have h3 : HasDerivAt (fun s : ℝ => Real.exp (-(s*y)))
          (Real.exp (-(x*y)) * (-(1*y))) x := h2.exp
      have h4 : HasDerivAt (fun s : ℝ => 1 - Real.exp (-(s*y)))
          (0 - Real.exp (-(x*y)) * (-(1*y))) x := (hasDerivAt_const x 1).sub h3
      have h5 : HasDerivAt (fun s : ℝ => (1 - Real.exp (-(s*y))) * Real.cos (3*y/2) * g72 y)
          ((0 - Real.exp (-(x*y)) * (-(1*y))) * Real.cos (3*y/2) * g72 y) x :=
        (h4.mul_const (Real.cos (3*y/2))).mul_const (g72 y)
      have h6 : (0 - Real.exp (-(x*y)) * (-(1*y))) = y * Real.exp (-(x*y)) := by ring
      rw [h6] at h5
      exact h5
  exact hmain

/-- `K` is monotone on `[0,1]`. -/
lemma K_mono : MonotoneOn K (Set.Icc (0:ℝ) 1) := by
  have hdiff : DifferentiableOn ℝ K (Set.Icc (0:ℝ) 1) := fun t ht =>
    (hasDerivAt_K t ht).differentiableAt.differentiableWithinAt
  refine monotoneOn_of_deriv_nonneg (convex_Icc 0 1) hdiff.continuousOn ?_ ?_
  · exact hdiff.mono interior_subset
  · intro x hx
    rw [interior_Icc] at hx
    rw [(hasDerivAt_K x ⟨le_of_lt hx.1, le_of_lt hx.2⟩).deriv]
    exact G72YCosNonneg x (le_of_lt hx.1) (le_of_lt hx.2)

/-- `∫₀² e^{-sy} cos(3y/2) g72 y dy = ∫₀² cos(3y/2) g72 y dy - K s`. -/
lemma exp_cos_eq_sub_K (s : ℝ) :
    (∫ y in (0:ℝ)..2, Real.exp (-(s*y)) * Real.cos (3*y/2) * g72 y)
      = (∫ y in (0:ℝ)..2, Real.cos (3*y/2) * g72 y) - K s := by
  rw [K, ← intervalIntegral.integral_sub]
  · apply intervalIntegral.integral_congr
    intro y _
    ring
  · apply Continuous.intervalIntegrable; simp only [g72]; fun_prop
  · apply Continuous.intervalIntegrable; simp only [g72]; fun_prop

/-- The `s = 1` value is the minimum on `[0,1]`. -/
lemma h_one_le (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    (∫ y in (0:ℝ)..2, Real.exp (-y) * Real.cos (3*y/2) * g72 y)
      ≤ ∫ y in (0:ℝ)..2, Real.exp (-(s*y)) * Real.cos (3*y/2) * g72 y := by
  have h1 : (∫ y in (0:ℝ)..2, Real.exp (-y) * Real.cos (3*y/2) * g72 y)
      = (∫ y in (0:ℝ)..2, Real.cos (3*y/2) * g72 y) - K 1 := by
    rw [← exp_cos_eq_sub_K 1]
    apply intervalIntegral.integral_congr
    intro y _
    ring_nf
  have h2 : (∫ y in (0:ℝ)..2, Real.exp (-(s*y)) * Real.cos (3*y/2) * g72 y)
      = (∫ y in (0:ℝ)..2, Real.cos (3*y/2) * g72 y) - K s := exp_cos_eq_sub_K s
  have hmono : K s ≤ K 1 :=
    K_mono ⟨hs0, hs1⟩ ⟨by norm_num, by norm_num⟩ hs1
  rw [h1, h2]
  linarith

/-- `Re G72(1 + 3i/2)` is the integral of `e^{-y} cos(3y/2) g72`. -/
lemma G72_re_one_three_halves :
    (Work.ZeroFreeTables.G72 ((1:ℂ) + ((3:ℂ)/2) * Complex.I)).re
      = ∫ y in (0:ℝ)..2, Real.exp (-y) * Real.cos (3*y/2) * g72 y := by
  rw [G72_re_eq_integral]
  apply intervalIntegral.integral_congr
  intro y _
  have h1 : (((1:ℂ) + ((3:ℂ)/2) * Complex.I)).re = 1 := by simp
  have h2 : (((1:ℂ) + ((3:ℂ)/2) * Complex.I)).im = 3/2 := by simp
  rw [h1, h2]
  ring_nf

theorem G72RePosBox : ∀ s σ : ℝ, 0 ≤ s → s ≤ 1 → 0 ≤ σ → σ ≤ 3/2 →
    2/5 ≤ (Work.ZeroFreeTables.G72 ((s : ℂ) + (σ : ℂ) * Complex.I)).re := by
  intro s σ hs0 hs1 hσ0 hσ32
  have key : (∫ y in (0:ℝ)..2, Real.exp (-(s*y)) * Real.cos (3*y/2) * g72 y)
      ≤ (Work.ZeroFreeTables.G72 ((s : ℂ) + (σ : ℂ) * Complex.I)).re := by
    rw [G72_re_eq_integral]
    apply intervalIntegral.integral_mono_on (by norm_num) ?_ ?_ ?_
    · apply Continuous.intervalIntegrable; simp only [g72]; fun_prop
    · apply Continuous.intervalIntegrable; simp only [g72]; fun_prop
    · intro y hy
      have hy0 : 0 ≤ y := hy.1
      have hy2 : y ≤ 2 := hy.2
      have hre : (((s : ℂ) + (σ : ℂ) * Complex.I)).re = s := by simp
      have him : (((s : ℂ) + (σ : ℂ) * Complex.I)).im = σ := by simp
      rw [hre, him]
      have hg := g72_nonneg hy0 hy2
      have he : 0 ≤ Real.exp (-(s*y)) := (Real.exp_pos _).le
      have hcos := cos_three_halves_le_cos y σ hy0 hy2 hσ0 hσ32
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcos he) hg
  have hmono := h_one_le s hs0 hs1
  have hcorner : (2/5 : ℝ)
      ≤ (Work.ZeroFreeTables.G72 ((1:ℂ) + ((3:ℂ)/2) * Complex.I)).re := G72ReCornerGe
  rw [G72_re_one_three_halves] at hcorner
  linarith

end Work.OffAxis
