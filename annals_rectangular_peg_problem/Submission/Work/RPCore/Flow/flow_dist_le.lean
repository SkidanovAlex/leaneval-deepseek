import Mathlib
import Submission.Work.RPCore.Port.ODE.SmoothFlow

/-!
# The Grönwall estimate for a flow of a field with bounded derivative

If `X : E → E` is `C¹` with `‖fderiv ℝ X z‖ ≤ K` for all `z`, and `Φ` is *any* map such that
`Φ t y` is reached at time `t` by an integral curve of `X` starting at `y` (hypothesis `hΦ`),
then for `t ≥ 0`

`dist (Φ t y) (Φ t z) ≤ exp (K * t) * dist y z`.

The proof is Grönwall's inequality applied to the difference of the two integral curves: the
mean value inequality turns the bound on `fderiv ℝ X` into the Lipschitz bound
`‖X a - X b‖ ≤ K * ‖a - b‖`, so that the difference `s ↦ γ s - η s` satisfies
`‖(γ - η)' s‖ ≤ K * ‖(γ - η) s‖`.
-/

open Set

set_option autoImplicit false

namespace Work.RPCore.Flow

/-- The mean value inequality in the form used below: a `C¹` map whose derivative is bounded by
`K` is Lipschitz with constant `K`. -/
lemma norm_sub_le_of_norm_fderiv_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (X : E → E) (hX : ContDiff ℝ 1 X) {K : ℝ} (hK : ∀ z, ‖fderiv ℝ X z‖ ≤ K) :
    ∀ a b : E, ‖X a - X b‖ ≤ K * ‖a - b‖ := by
  have hdiff : Differentiable ℝ X := hX.differentiable_one
  intro a b
  exact convex_univ.norm_image_sub_le_of_norm_fderiv_le (f := X) (C := K) (s := univ)
    (fun x _ => hdiff x) (fun x _ => hK x) (mem_univ a) (mem_univ b)

theorem flow_dist_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E] (X : E → E) (hX : ContDiff ℝ 1 X) {K : ℝ}
    (hK : ∀ z, ‖fderiv ℝ X z‖ ≤ K) (Φ : ℝ → E → E)
    (hΦ : ∀ t y, ∃ γ : ℝ → E, γ 0 = y ∧ IsIntegralCurve γ (fun _ z => X z) ∧ γ t = Φ t y)
    {t : ℝ} (ht : 0 ≤ t) (y z : E) :
    dist (Φ t y) (Φ t z) ≤ Real.exp (K * t) * dist y z := by
  obtain ⟨γ, hγ0, hγic, hγt⟩ := hΦ t y
  obtain ⟨η, hη0, hηic, hηt⟩ := hΦ t z
  have hlip : ∀ a b : E, ‖X a - X b‖ ≤ K * ‖a - b‖ := norm_sub_le_of_norm_fderiv_le X hX hK
  -- Grönwall on the difference of the two integral curves
  have hcont : ContinuousOn (fun s : ℝ => γ s - η s) (Icc 0 t) :=
    (hγic.continuous.sub hηic.continuous).continuousOn
  have hder : ∀ s ∈ Ico (0 : ℝ) t,
      HasDerivWithinAt (fun s : ℝ => γ s - η s) (X (γ s) - X (η s)) (Ici s) s :=
    fun s _ => ((hγic s).hasDerivWithinAt).sub ((hηic s).hasDerivWithinAt)
  have hδ : ‖(fun s : ℝ => γ s - η s) 0‖ ≤ ‖y - z‖ := by simp [hγ0, hη0]
  have hbound : ∀ s ∈ Ico (0 : ℝ) t, ‖X (γ s) - X (η s)‖ ≤ K * ‖γ s - η s‖ + 0 :=
    fun s _ => by simpa using hlip (γ s) (η s)
  have hmain : ‖γ t - η t‖ ≤ ‖y - z‖ * Real.exp (K * t) := by
    have h := norm_le_gronwallBound_of_norm_deriv_right_le
      (f := fun s : ℝ => γ s - η s) (f' := fun s : ℝ => X (γ s) - X (η s))
      (a := 0) (b := t) (δ := ‖y - z‖) (K := K) (ε := 0)
      hcont hder hδ hbound t ⟨ht, le_rfl⟩
    rwa [gronwallBound_ε0, sub_zero] at h
  rw [dist_eq_norm, ← hγt, ← hηt]
  calc ‖γ t - η t‖ ≤ ‖y - z‖ * Real.exp (K * t) := hmain
    _ = Real.exp (K * t) * dist y z := by rw [dist_eq_norm]; ring

end Work.RPCore.Flow
