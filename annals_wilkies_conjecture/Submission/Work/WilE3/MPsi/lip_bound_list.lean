import Mathlib
import Submission.Work.WilE3.eaEval_analytic
import Submission.Work.WilE3.Defs

set_option autoImplicit false
noncomputable section
open Classical Topology Filter
open WilkiesDesign.E
namespace Work.WilE3.MPsi

/-- For a finite list of EA polynomials and a point `y` there are `R > 0`, `Cb ≥ 1` and `Lip ≥ 0`
such that on the closed ball of radius `R` around `y` every `eaEval c g` (`g` in the list) is
bounded by `Cb` and is `Lip`-Lipschitz: `|g x - g x'| ≤ Lip * dist x x'`. -/
theorem lip_bound_list {k r : ℕ} (c : EAChain k r) (l : List (EAPoly k r)) (y : Fin k → ℝ) :
    ∃ R Cb Lip : ℝ, 0 < R ∧ 1 ≤ Cb ∧ 0 ≤ Lip ∧
      (∀ g ∈ l, ∀ x : Fin k → ℝ, dist x y ≤ R → |eaEval c g x| ≤ Cb) ∧
      (∀ g ∈ l, ∀ x x' : Fin k → ℝ, dist x y ≤ R → dist x' y ≤ R →
        |eaEval c g x - eaEval c g x'| ≤ Lip * dist x x') := by
  -- Each single EA polynomial is bounded and Lipschitz on the closed ball of radius `1`.
  have single : ∀ Q : EAPoly k r, ∃ Cb Lip : ℝ, 1 ≤ Cb ∧ 0 ≤ Lip ∧
      (∀ x : Fin k → ℝ, dist x y ≤ 1 → |eaEval c Q x| ≤ Cb) ∧
      (∀ x x' : Fin k → ℝ, dist x y ≤ 1 → dist x' y ≤ 1 →
        |eaEval c Q x - eaEval c Q x'| ≤ Lip * dist x x') := by
    intro Q
    set f : (Fin k → ℝ) → ℝ := fun x => eaEval c Q x with hf
    have hana : ∀ x, AnalyticAt ℝ f x := fun x => eaEval_analytic c Q x
    have hcont : Continuous f := continuous_iff_continuousAt.mpr (fun x => (hana x).continuousAt)
    have hcd : ContDiffOn ℝ 1 f (Metric.closedBall y 1) :=
      fun x _ => (hana x).contDiffAt.contDiffWithinAt
    obtain ⟨K, hK⟩ :=
      hcd.exists_lipschitzOnWith (by norm_num) (convex_closedBall y 1) (isCompact_closedBall y 1)
    obtain ⟨C, hC⟩ :=
      (isCompact_closedBall y (1:ℝ)).exists_bound_of_continuousOn hcont.continuousOn
    refine ⟨max C 1, (K:ℝ), le_max_right C 1, K.coe_nonneg, ?_, ?_⟩
    · intro x hx
      have h1 : |f x| ≤ C := by
        simpa [Real.norm_eq_abs] using hC x (by simpa [Metric.mem_closedBall] using hx)
      calc |eaEval c Q x| = |f x| := by rw [hf]
        _ ≤ C := h1
        _ ≤ max C 1 := le_max_left C 1
    · intro x x' hx hx'
      have hx'' : x ∈ Metric.closedBall y 1 := by simpa [Metric.mem_closedBall] using hx
      have hx''' : x' ∈ Metric.closedBall y 1 := by simpa [Metric.mem_closedBall] using hx'
      have h1 := hK.dist_le_mul x hx'' x' hx'''
      rw [Real.dist_eq] at h1
      simpa [hf] using h1
  -- The list version with radius `1`, by induction on the list.
  have hlist : ∃ Cb Lip : ℝ, 1 ≤ Cb ∧ 0 ≤ Lip ∧
      (∀ g ∈ l, ∀ x : Fin k → ℝ, dist x y ≤ 1 → |eaEval c g x| ≤ Cb) ∧
      (∀ g ∈ l, ∀ x x' : Fin k → ℝ, dist x y ≤ 1 → dist x' y ≤ 1 →
        |eaEval c g x - eaEval c g x'| ≤ Lip * dist x x') := by
    induction l with
    | nil => exact ⟨1, 0, le_refl 1, le_refl 0, by simp, by simp⟩
    | cons g t ih =>
      obtain ⟨Cb₁, Lip₁, hCb₁, hLip₁, hb₁, hl₁⟩ := single g
      obtain ⟨Cb₂, Lip₂, hCb₂, hLip₂, hb₂, hl₂⟩ := ih
      refine ⟨max Cb₁ Cb₂, max Lip₁ Lip₂, le_trans hCb₁ (le_max_left _ _),
        le_trans hLip₁ (le_max_left _ _), ?_, ?_⟩
      · intro h hm x hx
        rcases List.mem_cons.mp hm with rfl | hm
        · exact le_trans (hb₁ x hx) (le_max_left _ _)
        · exact le_trans (hb₂ h hm x hx) (le_max_right _ _)
      · intro h hm x x' hx hx'
        rcases List.mem_cons.mp hm with rfl | hm
        · exact le_trans (hl₁ x x' hx hx')
            (mul_le_mul_of_nonneg_right (le_max_left _ _) dist_nonneg)
        · exact le_trans (hl₂ h hm x x' hx hx')
            (mul_le_mul_of_nonneg_right (le_max_right _ _) dist_nonneg)
  obtain ⟨Cb, Lip, hCb, hLip, hb, hl⟩ := hlist
  exact ⟨1, Cb, Lip, one_pos, hCb, hLip, hb, hl⟩

end Work.WilE3.MPsi
