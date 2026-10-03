import Mathlib
import Submission.Work.Interfaces.Parabolic
import Submission.Work.Pert.Ksub2.Setup
import Submission.Work.Pert.pert2v2.XcV2_deep_legit
import Submission.Work.Pert.pert2v2.Xc_ray_aux

/-!
# `Work.Pert.pert2v2.Xc_ray_mem`

The datum's curve `u ↦ Xc d u = τ₀ (d.φ u)` over the *vertical ray* `t + i y₀` (`t ≤ x < 1`)
enters the lower cone `Qreg none (some (-Ξ')) = {z | Re z + Ξ' < |Im z|}` as soon as `y₀` is
large, **uniformly in `t ≤ x`**, and the same holds for the translate `u + 1`.

This is the "large positive height" counterpart of `XcV2_deep_legit` (which treats `Re u → -∞`).
The only input is the datum's asymptotic `τ₀ (φ₀ w) = w + a log(-w) + b + o(1)` on the repelling
sector `QLeft ξ₀` (`d.φ_asymp`, used at the fixed accuracy `1`), which is available because
`t + i y₀ ∈ QLeft ξ₀` for `y₀ > 2 (t + ξ₀)`.  Writing `z := Xc d u`, `A := a log(-u) + b`,
`x := -u.re + |u.im|` and `c := ‖A‖ + 1`:

* `z.re < (u + A).re + 1 ≤ u.re + c` and `|z.im| > |(u + A).im| - 1 ≥ |u.im| - c`
  (the two Lipschitz bounds of `Work.Pert.pert2v2.mem_Qreg_of_deep_close`), so the cone condition
  follows from the single scalar inequality `2c + Ξ' < x`;
* `‖u‖ ≤ x + 2B` when `u.re ≤ B` and `B ≥ 0`, so
  `c ≤ ‖a‖ log(x+1) + (‖a‖ log(2B+1) + ‖a‖ π + ‖b‖ + 1)` — the logarithmic error is dominated by
  `x` at infinity (`Work.Pert.pert2v2.threshold_arith`), which is exactly the scalar inequality.

Everything is assembled in `Work.Pert.pert2v2.Xc_ray_aux` (a single-point statement, applied twice:
at `u` and at `u + 1`); this file contains only the geometric input `t + i y₀ ∈ QLeft ξ₀` and the
quantifier bookkeeping.
-/

namespace Work.Pert.pert2v2

open Complex

/-- A point of the vertical ray `t + i y₀` lies in the repelling sector `QLeft ξ` as soon as
`2 (t + ξ) < y₀` (the imaginary part dominates the real part, which sits strictly to the right of
the vertex `-ξ`). -/
theorem mem_QLeft_ray {ξ t y₀ : ℝ} (h : 2 * (t + ξ) < y₀) :
    ((t : ℂ) + (y₀ : ℂ) * Complex.I) ∈ MandelDim.QLeft ξ := by
  rw [Work.Parab.QLeft_iff]
  have hre : ((t : ℂ) + (y₀ : ℂ) * Complex.I + (ξ : ℂ)).re = t + ξ := by simp
  have him : ((t : ℂ) + (y₀ : ℂ) * Complex.I + (ξ : ℂ)).im = y₀ := by simp
  have hnorm := Complex.abs_im_le_norm ((t : ℂ) + (y₀ : ℂ) * Complex.I + (ξ : ℂ))
  rw [him] at hnorm
  have h2 : y₀ ≤ |y₀| := le_abs_self y₀
  rw [hre]
  linarith

theorem Xc_ray_mem {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : MandelDim.ParabData f₀ D₀) :
    ∃ Ξ₀ : ℝ, 0 < Ξ₀ ∧ ∀ Ξ' : ℝ, Ξ₀ ≤ Ξ' → ∃ Y : ℝ, ∀ y₀ : ℝ, Y ≤ y₀ →
      ∀ x t : ℝ, 0 ≤ x → x < 1 → t ≤ x →
        ((t : ℂ) + (y₀ : ℂ) * Complex.I) ∈ d.Dφ ∧
        (((t : ℂ) + (y₀ : ℂ) * Complex.I) + 1) ∈ d.Dφ ∧
        Work.Pert.Xc d ((t : ℂ) + (y₀ : ℂ) * Complex.I)
          ∈ MandelDim.Qreg none (some (-(Ξ' : ℂ))) ∧
        Work.Pert.Xc d (((t : ℂ) + (y₀ : ℂ) * Complex.I) + 1)
          ∈ MandelDim.Qreg none (some (-(Ξ' : ℂ))) := by
  obtain ⟨a, b, hasym⟩ := d.φ_asymp
  obtain ⟨Ra, hRa⟩ := hasym 1 one_pos
  refine ⟨1, one_pos, ?_⟩
  intro Ξ' hΞ'1
  have hΞ'pos : 0 < Ξ' := lt_of_lt_of_le one_pos hΞ'1
  -- the two constants of the argument: a bound `B` for `Re u` and the threshold `N` of the
  -- logarithmic-vs-linear comparison.
  set B : ℝ := 2 with hBdef
  have hB0 : (0 : ℝ) ≤ B := by rw [hBdef]; norm_num
  obtain ⟨N, hNpos, thr⟩ := threshold_arith (K := ‖a‖)
    (L := ‖a‖ * Real.log (2 * B + 1) + (‖a‖ * Real.pi + ‖b‖ + 1)) (Ξ := Ξ') (norm_nonneg a)
  have hN0 : (0 : ℝ) ≤ N := le_of_lt hNpos
  refine ⟨max (N + B + 1) (max (2 * (2 + d.ξ₀)) (max Ra 1)) + 1, ?_⟩
  intro y₀ hy x t hx0 hx1 htx
  have ht1 : t < 1 := lt_of_le_of_lt htx hx1
  -- consequences of `y₀ ≥ Y`
  have hy' : max (N + B + 1) (max (2 * (2 + d.ξ₀)) (max Ra 1)) < y₀ := by linarith
  obtain ⟨hN3lt, hrest⟩ := max_lt_iff.mp hy'
  obtain ⟨hξ2lt, hrest2⟩ := max_lt_iff.mp hrest
  obtain ⟨hRalt, h1lt⟩ := max_lt_iff.mp hrest2
  have hN3 : N + B + 1 ≤ y₀ := le_of_lt hN3lt
  have hξ2 : 2 * (2 + d.ξ₀) ≤ y₀ := le_of_lt hξ2lt
  have hRale : Ra < y₀ := hRalt
  have hy0 : (0 : ℝ) ≤ y₀ := by linarith
  -- the two points `u` and `u + 1` in the standard form
  set u : ℂ := (t : ℂ) + (y₀ : ℂ) * Complex.I with hudef
  have hure : u.re = t := by rw [hudef]; simp
  have huim : u.im = y₀ := by rw [hudef]; simp
  have hu1re : (u + 1).re = t + 1 := by rw [hudef]; simp
  have hu1im : (u + 1).im = y₀ := by rw [hudef]; simp
  have habsim : |u.im| = y₀ := by rw [huim]; exact abs_of_nonneg hy0
  have habs1im : |(u + 1).im| = y₀ := by rw [hu1im]; exact abs_of_nonneg hy0
  -- sector membership (the geometric input)
  have hQ1 : u ∈ MandelDim.QLeft d.ξ₀ := by
    rw [hudef]
    exact mem_QLeft_ray (by linarith)
  have hQ2 : u + 1 ∈ MandelDim.QLeft d.ξ₀ := by
    have heq : u + 1 = ((t + 1 : ℝ) : ℂ) + (y₀ : ℂ) * Complex.I := by
      rw [hudef]; push_cast; ring
    rw [heq]
    exact mem_QLeft_ray (by linarith)
  -- the hypotheses of `Xc_ray_aux` at the two points
  have hre1 : u.re ≤ B := by rw [hure, hBdef]; linarith
  have hre2 : (u + 1).re ≤ B := by rw [hu1re, hBdef]; linarith
  have him1 : N + B + 1 ≤ |u.im| := by rw [habsim]; exact hN3
  have him2 : N + B + 1 ≤ |(u + 1).im| := by rw [habs1im]; exact hN3
  have hra1 : Ra < |u.im| := by rw [habsim]; exact hRale
  have hra2 : Ra < |(u + 1).im| := by rw [habs1im]; exact hRale
  have hN' : ∀ z : ℝ, N ≤ z → 2 * ‖a‖ * Real.log (z + 1) +
      2 * (‖a‖ * Real.log (2 * B + 1) + (‖a‖ * Real.pi + ‖b‖ + 1)) + Ξ' < z :=
    fun z hz => by have h := thr z hz; linarith
  have hmain1 := Xc_ray_aux d (a := a) (b := b) (Ra := Ra) (hasym1 := hRa)
    (Ξ' := Ξ') (B := B) (N := N) hB0 hN0 hN' hre1 him1 hQ1 hra1
  have hmain2 := Xc_ray_aux d (a := a) (b := b) (Ra := Ra) (hasym1 := hRa)
    (Ξ' := Ξ') (B := B) (N := N) hB0 hN0 hN' hre2 him2 hQ2 hra2
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [hudef] using hmain1.1
  · simpa [hudef] using hmain2.1
  · simpa [hudef] using hmain1.2
  · simpa [hudef] using hmain2.2

end Work.Pert.pert2v2
