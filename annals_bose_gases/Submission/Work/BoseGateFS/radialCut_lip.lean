import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Submission.Work.BoseBoxFix.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseGateFS

/-- A function on `ℝ` whose derivative is bounded by `M` is `M`-Lipschitz.
The mean value inequality applied on the whole line, with a single real variable. -/
lemma abs_sub_le_of_deriv_bound {f : ℝ → ℝ} {M : ℝ}
    (hdiff : Differentiable ℝ f) (hζ' : ∀ s : ℝ, |deriv f s| ≤ M) :
    ∀ a b : ℝ, |f a - f b| ≤ M * |a - b| := by
  intro a b
  have hb : ∀ x ∈ (Set.univ : Set ℝ), ‖deriv f x‖ ≤ M := by
    intro x _
    simpa [Real.norm_eq_abs] using hζ' x
  have h := Convex.norm_image_sub_le_of_norm_deriv_le
    (s := (Set.univ : Set ℝ)) (x := b) (y := a) (C := M)
    (fun x _ => hdiff.differentiableAt) hb convex_univ (Set.mem_univ b) (Set.mem_univ a)
  simpa [Real.norm_eq_abs] using h

theorem radialCut_lip {fu : Work.BoseBoxFix.LowCut} {M Λ : ℝ} (hΛ : 1 ≤ Λ) (hM : 0 ≤ M)
    (hζ' : ∀ s : ℝ, |deriv fu.f s| ≤ M) :
    (∀ p q : EuclideanSpace ℝ (Fin 3),
        |fu.f (‖p‖ / Λ) - fu.f (‖q‖ / Λ)| ≤ M * ‖p - q‖)
      ∧ (∀ p : EuclideanSpace ℝ (Fin 3), |fu.f (‖p‖ / Λ)| ≤ 1) := by
  have hΛpos : 0 < Λ := lt_of_lt_of_le zero_lt_one hΛ
  have hdi : Differentiable ℝ fu.f := fu.smooth.differentiable (by simp)
  have hf_lip : ∀ a b : ℝ, |fu.f a - fu.f b| ≤ M * |a - b| :=
    abs_sub_le_of_deriv_bound hdi hζ'
  constructor
  · intro p q
    have h := hf_lip (‖p‖ / Λ) (‖q‖ / Λ)
    have h1 : |‖p‖ / Λ - ‖q‖ / Λ| = |‖p‖ - ‖q‖| / Λ := by
      rw [← sub_div, abs_div, abs_of_pos hΛpos]
    rw [h1] at h
    have h4 : |‖p‖ - ‖q‖| / Λ ≤ ‖p - q‖ := by
      have h5 : |‖p‖ - ‖q‖| / Λ ≤ |‖p‖ - ‖q‖| :=
        div_le_self (abs_nonneg _) hΛ
      have h6 := abs_norm_sub_norm_le p q
      linarith
    exact le_trans h (mul_le_mul_of_nonneg_left h4 hM)
  · intro p
    have hle1 : fu.f (‖p‖ / Λ) ≤ 1 := by
      rcases le_or_gt (‖p‖ / Λ) 1 with h | h
      · rw [fu.one _ h]
      · have h' : fu.f (‖p‖ / Λ) ≤ fu.f 1 := fu.anti (le_of_lt h)
        rwa [fu.one 1 le_rfl] at h'
    have hge0 : 0 ≤ fu.f (‖p‖ / Λ) := by
      rcases le_or_gt (‖p‖ / Λ) 2 with h | h
      · have h' : fu.f 2 ≤ fu.f (‖p‖ / Λ) := fu.anti h
        rwa [fu.zero 2 le_rfl] at h'
      · rw [fu.zero _ (le_of_lt h)]
    rw [abs_le]
    exact ⟨by linarith, hle1⟩

end Work.BoseGateFS
