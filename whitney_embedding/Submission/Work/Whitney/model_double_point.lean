import Mathlib
import Submission.Work.Whitney.LocalModel

namespace Work.Whitney

open scoped BigOperators
open Set Filter Topology

/-- `uu n x = ∏ᵢ (1 + xᵢ²)` is positive. -/
lemma uu_pos (n : ℕ) (x : Fin n → ℝ) : 0 < uu n x := by
  unfold uu
  exact Finset.prod_pos (fun i _ => by positivity)

/-- `uu n (e0 n) = 2`. -/
lemma uu_e0 (n : ℕ) [NeZero n] : uu n (e0 n) = 2 := by
  unfold uu e0
  rw [Finset.prod_eq_single (0 : Fin n)]
  · norm_num
  · intro b _ hb; rw [Pi.single_eq_of_ne hb]; ring
  · intro h; exact absurd (Finset.mem_univ 0) h

/-- `uu n (-(e0 n)) = 2`. -/
lemma uu_nege0 (n : ℕ) [NeZero n] : uu n (-(e0 n)) = 2 := by
  unfold uu e0
  rw [Finset.prod_eq_single (0 : Fin n)]
  · norm_num
  · intro b _ hb; rw [Pi.neg_apply, Pi.single_eq_of_ne hb]; ring
  · intro h; exact absurd (Finset.mem_univ 0) h

/-- The scalar germ `φ t = (t - 2t/(1+t²), 1/(1+t²))` that governs the model on the `e₀`-axis is
injective away from the pair `{1, -1}`. -/
lemma phi_eq_pair (t s : ℝ)
    (h1 : t - 2*t/(1+t^2) = s - 2*s/(1+s^2))
    (h2 : (1:ℝ)/(1+t^2) = 1/(1+s^2)) :
    t = s ∨ (t = 1 ∧ s = -1) ∨ (t = -1 ∧ s = 1) := by
  have ht2 : t^2 = s^2 := by
    rw [one_div, one_div] at h2
    have := inv_inj.mp h2
    linarith
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp ht2 with hts | hts
  · exact Or.inl hts
  · have hst : s = -t := by linarith
    have hprod : t * (t^2 - 1) = 0 := by
      have hh := h1
      rw [hst] at hh
      have h2pos : (1 + t^2) ≠ 0 := by positivity
      field_simp at hh
      nlinarith only [hh]
    rcases eq_or_ne t 0 with ht0 | ht0
    · exact Or.inl (by rw [ht0, hst, ht0, neg_zero])
    · right
      have key : t^2 = 1 := by
        rcases mul_eq_zero.mp hprod with h | h
        · exact absurd h ht0
        · linarith
      rcases sq_eq_one_iff.mp key with h | h
      · left; exact ⟨h, by simp [hst, h]⟩
      · right; exact ⟨h, by simp [hst, h]⟩

/-- The only double point of Whitney's model `model n : ℝⁿ → ℝⁿ × ℝⁿ` (defined in `Submission/Work/Whitney/LocalModel.lean` with `uu n x = ∏ i, (1 + x i ^ 2)`) is the pair `±e₀`, where `e0 n = Pi.single 0 1`: `model n (e0 n) = model n (-(e0 n))`, and if `model n x = model n y` with `x ≠ y` then `{x, y} = {e0 n, -(e0 n)}`.  This is the "single self-intersection" of Whitney's local model. -/
theorem model_double_point (n : ℕ) [NeZero n] :
    Work.Whitney.model n (Work.Whitney.e0 n) = Work.Whitney.model n (-(Work.Whitney.e0 n)) ∧
      ∀ x y : Fin n → ℝ, Work.Whitney.model n x = Work.Whitney.model n y →
        x = y ∨ (x = Work.Whitney.e0 n ∧ y = -(Work.Whitney.e0 n)) ∨
          (x = -(Work.Whitney.e0 n) ∧ y = Work.Whitney.e0 n) := by
  constructor
  · refine Prod.ext ?_ ?_
    · funext i
      rw [model_fst, model_fst]
      by_cases hi : i = 0
      · subst hi
        simp only [↓reduceIte, uu_e0, uu_nege0]
        simp [e0]
      · rw [if_neg hi, if_neg hi, sub_zero, sub_zero]
        simp [e0, hi]
    · funext i
      rw [model_snd, model_snd]
      by_cases hi : i = 0
      · subst hi
        simp only [↓reduceIte, uu_e0, uu_nege0]
      · rw [if_neg hi, if_neg hi]
        simp [e0, hi]
  · intro x y h
    -- Coordinate equations of `model n x = model n y`.
    have e1 : x 0 - 2 * x 0 / uu n x = y 0 - 2 * y 0 / uu n y := by
      have := congrArg (fun z => z.1 0) h
      simpa [model_fst] using this
    have e2 : 1 / uu n x = 1 / uu n y := by
      have := congrArg (fun z => z.2 0) h
      simpa [model_snd] using this
    have hA : uu n x = uu n y := by
      rw [one_div, one_div] at e2
      exact inv_inj.mp e2
    have hfst : ∀ i, i ≠ 0 → x i = y i := by
      intro i hi
      have := congrArg (fun z => z.1 i) h
      simpa [model_fst, if_neg hi] using this
    have hsnd : ∀ i, i ≠ 0 → x 0 * x i = y 0 * y i := by
      intro i hi
      have hh := congrArg (fun z => z.2 i) h
      simp only [model_snd, if_neg hi] at hh
      rw [← hA] at hh
      exact (div_left_inj' (ne_of_gt (uu_pos n x))).mp hh
    by_cases hz : ∀ i, i ≠ 0 → x i = 0
    · -- All coordinates other than the `0`-th vanish: the two points lie on the `e₀`-axis.
      have hz' : ∀ i, i ≠ 0 → y i = 0 := fun i hi => by rw [← hfst i hi]; exact hz i hi
      have hux : uu n x = 1 + x 0 ^ 2 := by
        unfold uu
        rw [Finset.prod_eq_single (0 : Fin n) (by intro b _ hb; rw [hz b hb]; ring)
          (by intro hb; exact absurd (Finset.mem_univ 0) hb)]
      have huy : uu n y = 1 + y 0 ^ 2 := by
        unfold uu
        rw [Finset.prod_eq_single (0 : Fin n) (by intro b _ hb; rw [hz' b hb]; ring)
          (by intro hb; exact absurd (Finset.mem_univ 0) hb)]
      rw [hux, huy] at e1 e2
      rcases phi_eq_pair (x 0) (y 0) e1 e2 with h0 | ⟨h0, h1⟩ | ⟨h0, h1⟩
      · left
        funext i
        by_cases hi : i = 0
        · subst hi; exact h0
        · exact hfst i hi
      · right; left
        refine ⟨?_, ?_⟩
        · funext i
          by_cases hi : i = 0
          · subst hi; rw [h0]; simp [e0]
          · rw [hz i hi]; simp [e0, hi]
        · funext i
          by_cases hi : i = 0
          · subst hi; rw [h1]; simp [e0]
          · rw [hz' i hi]; simp [e0, hi]
      · right; right
        refine ⟨?_, ?_⟩
        · funext i
          by_cases hi : i = 0
          · subst hi; rw [h0]; simp [e0]
          · rw [hz i hi]; simp [e0, hi]
        · funext i
          by_cases hi : i = 0
          · subst hi; rw [h1]; simp [e0]
          · rw [hz' i hi]; simp [e0, hi]
    · -- Some `x i₀ ≠ 0` with `i₀ ≠ 0` forces `x 0 = y 0`, hence `x = y`.
      push Not at hz
      obtain ⟨i, hi, hxi⟩ := hz
      left
      have hx0y0 : x 0 = y 0 := by
        have hh := hsnd i hi
        rw [← hfst i hi] at hh
        exact mul_right_cancel₀ hxi hh
      funext j
      by_cases hj : j = 0
      · subst hj; exact hx0y0
      · exact hfst j hj

end Work.Whitney
