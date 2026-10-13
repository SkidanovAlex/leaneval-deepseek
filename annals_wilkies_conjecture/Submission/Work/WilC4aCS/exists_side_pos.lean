/-
  WilC4aCS -- the dimension-one / `F =ᶠ 0` end of the curve-selection induction step.

  The claim: let `g_1, …, g_l` be real functions, each analytic at `0`, vanishing at `0`, and not
  identically zero on any neighbourhood of `0`.  If `0` lies in the closure of the set where *all*
  of them are positive, then one whole side of `0` is contained in that set.

  The mathematics is the classical isolated-zeros principle: an analytic function which does not
  vanish identically on a neighbourhood of `0` vanishes nowhere on a punctured neighbourhood of
  `0`, hence has constant (nonzero) sign on `(0, δ)` and on `(-δ, 0)`.  Taking `δ` smaller than all
  the individual thresholds, the closure hypothesis produces a witness `x₀` with `|x₀| < δ` and
  `g_j(x₀) > 0` for every `j`; the side on which `x₀` lies is then positive for all the `g_j`.

  The two analytic ingredients are proved by colleagues in
  `Submission.Work.WilC4aCS.analyticAt_punctured_ne_zero` (isolated zeros, `ε`-ball form) and
  `Submission.Work.WilC4aCS.sign_const_Ioo` (constant sign of a continuous non-vanishing function
  on an interval).
-/
import Mathlib
import Submission.Work.WilC4aCS.analyticAt_punctured_ne_zero
import Submission.Work.WilC4aCS.sign_const_Ioo

set_option autoImplicit false
noncomputable section
open Classical Topology Filter
open Set

namespace Work.WilC4aCS

/-- An analytic function at `0` which is not identically zero near `0` has constant sign on each
of the two sides of `0`, with a common radius. -/
theorem exists_sign_side {g : ℝ → ℝ} (hg : AnalyticAt ℝ g 0)
    (hnz : ¬ (∀ᶠ x in nhds (0 : ℝ), g x = 0)) :
    ∃ ε > (0 : ℝ),
      ((∀ x : ℝ, 0 < x → x < ε → 0 < g x) ∨ (∀ x : ℝ, 0 < x → x < ε → g x < 0)) ∧
      ((∀ x : ℝ, -ε < x → x < 0 → 0 < g x) ∨ (∀ x : ℝ, -ε < x → x < 0 → g x < 0)) := by
  obtain ⟨ε₀, hε₀pos, hε₀⟩ := analyticAt_punctured_ne_zero hg hnz
  obtain ⟨r, hrpos, hran⟩ := hg.exists_ball_analyticOnNhd
  -- A radius small enough both for punctured non-vanishing and for the analyticity ball.
  set ε := min ε₀ (r / 2) with hεdef
  have hεpos : 0 < ε := lt_min hε₀pos (by linarith)
  have hεle₀ : ε ≤ ε₀ := min_le_left _ _
  have hεler : ε < r := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  have hcont : ContinuousOn g (Set.Icc (-ε) ε) :=
    hran.continuousOn.mono (fun x hx => by
      rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_lt]
      exact ⟨by linarith [hx.1], by linarith [hx.2]⟩)
  refine ⟨ε, hεpos, ?_, ?_⟩
  · have hdisj : (∀ x ∈ Set.Ioo (0 : ℝ) ε, 0 < g x) ∨ (∀ x ∈ Set.Ioo (0 : ℝ) ε, g x < 0) := by
      refine sign_const_Ioo (hcont.mono (Set.Icc_subset_Icc (by linarith : -ε ≤ 0) le_rfl)) ?_
      intro x hx
      exact hε₀ x (ne_of_gt hx.1) (by rw [abs_of_pos hx.1]; exact lt_of_lt_of_le hx.2 hεle₀)
    rcases hdisj with h | h
    · exact Or.inl (fun x hx hx' => h x ⟨hx, hx'⟩)
    · exact Or.inr (fun x hx hx' => h x ⟨hx, hx'⟩)
  · have hdisj : (∀ x ∈ Set.Ioo (-ε) (0 : ℝ), 0 < g x) ∨ (∀ x ∈ Set.Ioo (-ε) (0 : ℝ), g x < 0) := by
      refine sign_const_Ioo (hcont.mono (Set.Icc_subset_Icc le_rfl (by linarith : (0 : ℝ) ≤ ε))) ?_
      intro x hx
      exact hε₀ x (ne_of_lt hx.2) (by rw [abs_of_neg hx.2]; linarith [hx.1, hεle₀])
    rcases hdisj with h | h
    · exact Or.inl (fun x hx hx' => h x ⟨hx, hx'⟩)
    · exact Or.inr (fun x hx hx' => h x ⟨hx, hx'⟩)

theorem exists_side_pos {l : ℕ} (g : Fin l → ℝ → ℝ) (hg : ∀ j, AnalyticAt ℝ (g j) 0)
    (h0 : ∀ j, g j 0 = 0) (hnz : ∀ j, ¬ (∀ᶠ x in nhds (0 : ℝ), g j x = 0))
    (hcl : (0 : ℝ) ∈ closure {x : ℝ | ∀ j, 0 < g j x}) :
    ∃ δ > (0 : ℝ),
      (∀ x : ℝ, 0 < x → x < δ → ∀ j, 0 < g j x) ∨
      (∀ x : ℝ, -δ < x → x < 0 → ∀ j, 0 < g j x) := by
  by_cases hl : l = 0
  · -- no functions at all: the first alternative holds vacuously
    refine ⟨1, one_pos, Or.inl ?_⟩
    intro x hx hx' j
    exact absurd j.isLt (by omega)
  · have hlpos : 0 < l := Nat.pos_of_ne_zero hl
    haveI : Nonempty (Fin l) := ⟨⟨0, hlpos⟩⟩
    -- a common radius for all the `g j`
    have hspec : ∀ j, ∃ ε : ℝ, 0 < ε ∧
        ((∀ x : ℝ, 0 < x → x < ε → 0 < g j x) ∨ (∀ x : ℝ, 0 < x → x < ε → g j x < 0)) ∧
        ((∀ x : ℝ, -ε < x → x < 0 → 0 < g j x) ∨ (∀ x : ℝ, -ε < x → x < 0 → g j x < 0)) :=
      fun j => exists_sign_side (hg j) (hnz j)
    choose ε hε using hspec
    set δ := (Finset.univ.image (fun j : Fin l => ε j)).min'
        (Finset.image_nonempty.mpr Finset.univ_nonempty) with hδdef
    have hδpos : 0 < δ := by
      rw [hδdef, Finset.lt_min'_iff]
      intro y hy
      obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hy
      exact (hε j).1
    have hδle : ∀ j, δ ≤ ε j := fun j => by
      rw [hδdef]
      exact Finset.min'_le _ _ (Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩)
    -- a closure witness strictly inside the common radius
    obtain ⟨x0, hx0mem, hx0dist⟩ := (Metric.mem_closure_iff).1 hcl (δ / 2) (by linarith)
    have hx0abs : |x0| < δ := by
      have h : dist (0 : ℝ) x0 = |x0| := by simp [Real.dist_eq]
      rw [h] at hx0dist
      linarith
    have hx0ne : x0 ≠ 0 := by
      intro hx0eq
      have hmem := hx0mem ⟨0, hlpos⟩
      rw [hx0eq, h0 ⟨0, hlpos⟩] at hmem
      exact lt_irrefl 0 hmem
    refine ⟨δ, hδpos, ?_⟩
    rcases lt_trichotomy x0 0 with hlt | heq | hgt
    · -- the witness is on the left, so the whole left side works
      right
      intro x hxl xh0 j
      have hle : δ ≤ ε j := hδle j
      have hx0in : -ε j < x0 := (abs_lt.1 (lt_of_lt_of_le hx0abs hle)).1
      rcases (hε j).2.2 with hpos | hneg
      · exact hpos x (by linarith [hxl, hle]) xh0
      · exact absurd (hx0mem j) (not_lt.2 (le_of_lt (hneg x0 hx0in hlt)))
    · exact absurd heq hx0ne
    · -- the witness is on the right, so the whole right side works
      left
      intro x hx0 hxl j
      have hle : δ ≤ ε j := hδle j
      have hx0in : x0 < ε j := (abs_lt.1 (lt_of_lt_of_le hx0abs hle)).2
      rcases (hε j).2.1 with hpos | hneg
      · exact hpos x hx0 (by linarith [hxl, hle])
      · exact absurd (hx0mem j) (not_lt.2 (le_of_lt (hneg x0 hgt hx0in)))

end Work.WilC4aCS
