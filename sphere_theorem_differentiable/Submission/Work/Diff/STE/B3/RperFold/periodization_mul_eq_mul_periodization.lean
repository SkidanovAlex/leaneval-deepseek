import Mathlib
import Submission.Work.Diff.STE.B3.VarCoef.perMatDefs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Multiplicativity of the periodization sums

If `f` is supported in the closed ball of radius `1/4` around the origin and `g` is supported in the
open unit cube `(-1/2,1/2)^n`, then for every `z` the two periodizations of `f` and `g` along the
lattice `ℤ^n ↪ ℝ^n` multiply:

`∑' m, f (z+m) g (z+m) = (∑' m, f (z+m)) * (∑' m, g (z+m))`.

The reason is that for a fixed `z` there is **at most one** lattice point `m` with `f (z+m) ≠ 0`, and
**at most one** lattice point `m` with `g (z+m) ≠ 0`, and -- crucially -- these two lattice points,
when they exist, coincide: if `f (z+m₁) ≠ 0` and `g (z+m₂) ≠ 0` then
`|(m₁-m₂) j| ≤ 1/4 + 1/2 < 1` for every coordinate `j`, so `m₁ = m₂`.  Hence either `f` vanishes on
the whole lattice orbit of `z`, in which case both sides vanish, or there is a single index carrying
the whole mass of both sums, and the identity is a one-term computation.
-/

noncomputable section

namespace Work.Diff.STE.B3.RperFold

/-- **Geometric core of the periodization identity.**  A lattice translate `z + m₁` of norm `≤ 1/4`
and a lattice translate `z + m₂` all of whose coordinates lie in the open cube `(-1/2,1/2)` must be
the same translate.  (Each coordinate of `m₁ - m₂` is an integer with absolute value
`≤ 1/4 + 1/2 < 1`.) -/
lemma iVec_eq_of_norm_le_of_abs_lt {n : ℕ} {z : Fin n → ℝ} {m₁ m₂ : Fin n → ℤ}
    (h₁ : ‖z + Work.Diff.STE.iVec m₁‖ ≤ 1 / 4)
    (h₂ : ∀ j, |(z + Work.Diff.STE.iVec m₂) j| < 1 / 2) : m₁ = m₂ := by
  funext j
  have h₁j : |(z + Work.Diff.STE.iVec m₁) j| ≤ 1 / 4 := by
    have := norm_le_pi_norm (z + Work.Diff.STE.iVec m₁) j
    rw [Real.norm_eq_abs] at this
    linarith
  have hsub : ((m₁ - m₂) j : ℝ)
      = (z + Work.Diff.STE.iVec m₁) j - (z + Work.Diff.STE.iVec m₂) j := by
    simp only [Work.Diff.STE.iVec_apply, Pi.add_apply, Pi.sub_apply]
    push_cast
    ring
  have hlt : |((m₁ - m₂) j : ℤ)| < 1 := by
    have h3 : |(((m₁ - m₂) j : ℤ) : ℝ)| < 1 := by
      rw [hsub]
      calc |(z + Work.Diff.STE.iVec m₁) j - (z + Work.Diff.STE.iVec m₂) j|
          ≤ |(z + Work.Diff.STE.iVec m₁) j| + |(z + Work.Diff.STE.iVec m₂) j| := abs_sub _ _
        _ < 1 / 4 + 1 / 2 := by linarith [h₁j, h₂ j]
        _ < 1 := by norm_num
    rw [← Int.cast_abs] at h3
    exact_mod_cast h3
  have h0 : (m₁ - m₂) j = 0 := Int.abs_lt_one_iff.mp hlt
  have : m₁ j - m₂ j = 0 := by rwa [Pi.sub_apply] at h0
  exact sub_eq_zero.mp this

theorem periodization_mul_eq_mul_periodization {n : ℕ} (f g : (Fin n → ℝ) → ℂ)
    (hf : Function.support f ⊆ Metric.closedBall (0 : Fin n → ℝ) (1 / 4))
    (hg : Function.support g ⊆ Set.pi Set.univ
      (fun _ : Fin n => Set.Ioo (-(1 / 2 : ℝ)) (1 / 2)))
    (z : Fin n → ℝ) :
    (∑' m : Fin n → ℤ, f (z + Work.Diff.STE.iVec m) * g (z + Work.Diff.STE.iVec m))
      = (∑' m : Fin n → ℤ, f (z + Work.Diff.STE.iVec m))
        * (∑' m : Fin n → ℤ, g (z + Work.Diff.STE.iVec m)) := by
  have hball : ∀ m : Fin n → ℤ, f (z + Work.Diff.STE.iVec m) ≠ 0 →
      ‖z + Work.Diff.STE.iVec m‖ ≤ 1 / 4 := by
    intro m hm
    have h := hf (Function.mem_support.mpr hm)
    rwa [Metric.mem_closedBall, dist_eq_norm, sub_zero] at h
  have hcube : ∀ m : Fin n → ℤ, g (z + Work.Diff.STE.iVec m) ≠ 0 →
      ∀ j, |(z + Work.Diff.STE.iVec m) j| < 1 / 2 := by
    intro m hm j
    have h := (Set.mem_pi.mp (hg (Function.mem_support.mpr hm))) j (Set.mem_univ j)
    rw [Set.mem_Ioo] at h
    exact abs_lt.mpr h
  rcases em (∃ m₀, f (z + Work.Diff.STE.iVec m₀) ≠ 0) with hcase | hcase
  · obtain ⟨m₀, hm₀⟩ := hcase
    have hlt_half : ∀ m : Fin n → ℤ, f (z + Work.Diff.STE.iVec m) ≠ 0 → m = m₀ := by
      intro m hm
      refine iVec_eq_of_norm_le_of_abs_lt (hball m hm) (fun j => ?_)
      have h4 := norm_le_pi_norm (z + Work.Diff.STE.iVec m₀) j
      rw [Real.norm_eq_abs] at h4
      linarith [hball m₀ hm₀]
    have hfz : ∀ m, m ≠ m₀ → f (z + Work.Diff.STE.iVec m) = 0 := by
      intro m hm
      by_contra hne
      exact hm (hlt_half m hne)
    have hgz : ∀ m, m ≠ m₀ → g (z + Work.Diff.STE.iVec m) = 0 := by
      intro m hm
      by_contra hne
      exact hm ((iVec_eq_of_norm_le_of_abs_lt (hball m₀ hm₀) (hcube m hne)).symm)
    rw [tsum_eq_single m₀ (fun m hm => by rw [hfz m hm, zero_mul]),
      tsum_eq_single m₀ hfz, tsum_eq_single m₀ hgz]
  · simp only [not_exists, not_not] at hcase
    simp [hcase]

end Work.Diff.STE.B3.RperFold
