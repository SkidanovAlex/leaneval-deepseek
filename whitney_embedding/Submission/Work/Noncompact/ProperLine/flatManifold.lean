import Mathlib
import Submission.Work.Noncompact.ProperLine.flatGlue2

/-!
# Localisation of a `C^∞` germ

Mathlib's `ContDiffAt ℝ ∞ f 0` (with `∞ = ((⊤ : ℕ∞) : WithTop ℕ∞)`) only says that for every
finite `m` there is an `m`-dependent neighbourhood of `0` on which `f` is `C^m`; it does *not*
imply that `f` is `C^∞` on a fixed neighbourhood.  The lemma below therefore takes the local
`C^∞` hypothesis explicitly and produces a globally `C^∞` function agreeing with `f` near `0`
and inheriting the one-sided flatness.

This is the tool that lets the vector-valued flat gluing `contDiffAt_flatGlue_top` (which needs
*globally* smooth functions) be applied to the *local* chart expressions of two smooth arcs.
-/

open Set Filter Topology
open scoped Manifold ContDiff

namespace Work.Noncompact.ProperLine

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **Localisation of a `C^∞` germ.** -/
theorem exists_contDiff_flat_of_contDiffAt {f : ℝ → F} {δ : ℝ} (hδ : 0 < δ)
    (hf : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f (Metric.ball 0 δ))
    (hfl : ∀ k : ℕ, 0 < k → iteratedDerivWithin k f (Set.Iic 0) 0 = 0)
    (hfl' : ∀ k : ℕ, 0 < k → iteratedDerivWithin k f (Set.Ici 0) 0 = 0) :
    ∃ g : ℝ → F, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g ∧
      Filter.EventuallyEq (nhds 0) g f ∧
      (∀ k : ℕ, 0 < k → iteratedDerivWithin k g (Set.Iic 0) 0 = 0) ∧
      (∀ k : ℕ, 0 < k → iteratedDerivWithin k g (Set.Ici 0) 0 = 0) := by
  set χ : ℝ → ℝ :=
    fun s => Real.smoothTransition (2 - 4 * s / δ) * Real.smoothTransition (2 + 4 * s / δ)
    with hχdef
  have hχsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ := by
    rw [hχdef]
    exact ((Real.smoothTransition.contDiff (n := (⊤ : ℕ∞))).comp
        (by fun_prop : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun s : ℝ => 2 - 4 * s / δ)).mul
      ((Real.smoothTransition.contDiff (n := (⊤ : ℕ∞))).comp
        (by fun_prop : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun s : ℝ => 2 + 4 * s / δ))
  have hχnn : ∀ s, 0 ≤ χ s := fun s => by
    rw [hχdef]; exact mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _)
  have hχle : ∀ s, χ s ≤ 1 := fun s => by
    rw [hχdef]
    calc Real.smoothTransition (2 - 4 * s / δ) * Real.smoothTransition (2 + 4 * s / δ)
        ≤ 1 * 1 := mul_le_mul (Real.smoothTransition.le_one _) (Real.smoothTransition.le_one _)
            (Real.smoothTransition.nonneg _) zero_le_one
      _ = 1 := by norm_num
  have hχone : ∀ s, |s| ≤ δ / 4 → χ s = 1 := by
    intro s hs
    rw [abs_le] at hs
    have h1 : 4 * s / δ ≤ 1 := by
      rw [div_le_one hδ]; linarith [hs.2]
    have h2 : -(1 : ℝ) ≤ 4 * s / δ := by
      rw [le_div_iff₀ hδ]; linarith [hs.1]
    rw [hχdef]
    change Real.smoothTransition (2 - 4 * s / δ) * Real.smoothTransition (2 + 4 * s / δ) = 1
    rw [Real.smoothTransition.one_of_one_le (by linarith : (1:ℝ) ≤ 2 - 4 * s / δ),
      Real.smoothTransition.one_of_one_le (by linarith : (1:ℝ) ≤ 2 + 4 * s / δ), mul_one]
  have hχzero : ∀ s, δ / 2 ≤ |s| → χ s = 0 := by
    intro s hs
    rw [hχdef]
    change Real.smoothTransition (2 - 4 * s / δ) * Real.smoothTransition (2 + 4 * s / δ) = 0
    by_cases h : 0 ≤ s
    · rw [abs_of_nonneg h] at hs
      have h5 : (2 : ℝ) ≤ 4 * s / δ := by
        rw [le_div_iff₀ hδ]; linarith [hs]
      rw [Real.smoothTransition.zero_of_nonpos (by linarith : 2 - 4 * s / δ ≤ 0), zero_mul]
    · rw [abs_of_neg (not_le.mp h)] at hs
      have h5 : 4 * s / δ ≤ -(2 : ℝ) := by
        rw [div_le_iff₀ hδ]; linarith [hs]
      rw [Real.smoothTransition.zero_of_nonpos (by linarith : 2 + 4 * s / δ ≤ 0), mul_zero]
  have hφid : ∀ s : ℝ, |s| ≤ δ / 4 → (fun s : ℝ => s * χ s) s = s := by
    intro s hs
    simp only
    rw [hχone s hs, mul_one]
  have hφbound : ∀ s : ℝ, |(fun s : ℝ => s * χ s) s| < δ := by
    intro s
    simp only
    rw [abs_mul]
    rcases lt_or_ge |s| δ with h | h
    · calc |s| * |χ s| ≤ |s| * 1 :=
            mul_le_mul_of_nonneg_left
              (by rw [abs_of_nonneg (hχnn s)]; exact hχle s) (abs_nonneg s)
        _ = |s| := by ring
        _ < δ := h
    · rw [hχzero s (by linarith), abs_zero, mul_zero]
      exact hδ
  have hge : Filter.EventuallyEq (nhds 0) (f ∘ fun s : ℝ => s * χ s) f := by
    filter_upwards [Metric.ball_mem_nhds 0 (by positivity : (0:ℝ) < δ / 4)] with s hs
    rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at hs
    exact congrArg f (hφid s (le_of_lt hs))
  refine ⟨f ∘ (fun s => s * χ s), ?_, hge, ?_, ?_⟩
  · refine hf.comp_contDiff (contDiff_id.mul hχsm) (fun s => ?_)
    rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs]
    exact hφbound s
  · intro k hk
    exact (hge.filter_mono nhdsWithin_le_nhds).iteratedDerivWithin_eq_of_nhds_insert k ▸ hfl k hk
  · intro k hk
    exact (hge.filter_mono nhdsWithin_le_nhds).iteratedDerivWithin_eq_of_nhds_insert k ▸ hfl' k hk

end Work.Noncompact.ProperLine
