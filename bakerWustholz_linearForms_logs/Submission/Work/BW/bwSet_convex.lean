import Mathlib
import Submission.Work.BW.lcDefs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- The superlevel set `{x | c ≤ h x}` of a function `h : ℝ → ℝ` that is even and
antitone on `[0,∞)` is convex: it is symmetric about `0` and downward closed in `|·|`. -/
lemma convex_setOf_le_even_antitone {h : ℝ → ℝ}
    (heven : ∀ x, h (-x) = h x) (hanti : AntitoneOn h (Set.Ici 0)) (c : ℝ) :
    Convex ℝ {x : ℝ | c ≤ h x} := by
  have h_abs : ∀ x, h |x| = h x := by
    intro x
    by_cases hx : 0 ≤ x
    · rw [abs_of_nonneg hx]
    · rw [abs_of_neg (lt_of_not_ge hx), heven]
  intro x hx y hy a b ha hb hab
  simp only [Set.mem_setOf_eq] at hx hy ⊢
  have hM : c ≤ h (max |x| |y|) := by
    rcases max_cases |x| |y| with ⟨h1, _⟩ | ⟨h1, _⟩
    · rw [h1, h_abs]; exact hx
    · rw [h1, h_abs]; exact hy
  have hle : |a * x + b * y| ≤ max |x| |y| := by
    have h1 : |a * x + b * y| ≤ a * |x| + b * |y| := by
      have h2 := abs_add_le (a * x) (b * y)
      rwa [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb] at h2
    have hax : a * |x| ≤ a * max |x| |y| := mul_le_mul_of_nonneg_left (le_max_left _ _) ha
    have hby : b * |y| ≤ b * max |x| |y| := mul_le_mul_of_nonneg_left (le_max_right _ _) hb
    have hsum : a * max |x| |y| + b * max |x| |y| = max |x| |y| := by
      rw [← add_mul, hab, one_mul]
    linarith
  have hmono : h (max |x| |y|) ≤ h |a * x + b * y| :=
    hanti (Set.mem_Ici.mpr (abs_nonneg _)) (Set.mem_Ici.mpr (le_trans (abs_nonneg _) hle)) hle
  show c ≤ h (a • x + b • y)
  rw [smul_eq_mul, smul_eq_mul, ← h_abs (a * x + b * y)]
  exact le_trans hM hmono

theorem bwSet_convex {n : ℕ} (C : Set (Fin (n+1) → ℝ)) (k : Fin (n+1)) (h : Fin n → ℝ → ℝ)
    (hh_even : ∀ i x, h i (-x) = h i x) (hh_anti : ∀ i, AntitoneOn (h i) (Set.Ici 0))
    (hconv : Convex ℝ C) (u : Fin n → ℝ) : Convex ℝ (Work.BW.bwSet C k h u) := by
  by_cases hu : ∀ i, 0 ≤ u i
  · rw [bwSet_of_forall_nonneg _ _ _ hu]
    refine hconv.inter ?_
    refine convex_iInter (fun i => ?_)
    have := (convex_setOf_le_even_antitone (hh_even i) (hh_anti i) (u i)).linear_preimage
      (LinearMap.proj (R := ℝ) (φ := fun _ : Fin (n+1) => ℝ) (k.succAbove i))
    simpa [LinearMap.proj_apply] using this
  · rw [bwSet_of_not _ _ _ hu]
    exact convex_empty

end Work.BW
