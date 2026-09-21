import Mathlib

namespace Work.OddVolterra.Window

open scoped ContDiff

/-!
# Uniform jet bounds on a compact convex box

`JetCurve_box` is the elementary analytic input of the odd Volterra construction: given a function
`F : E → ℝ` which is `C^∞` on an open set `U` and a compact **convex** set `Kc ⊆ U`, there is a
constant `C ≥ 0` such that for *any* pair of smooth curves `j₁, j₀ : ℝ → E` whose values at a point
`a` lie in `Kc`, with derivatives at `a` bounded by `B'`, and which are `δ`-close in value and in
derivative, the values `F (jᵢ a)`, the derivatives `deriv (F ∘ jᵢ) a` and their differences are all
bounded by `C` resp. `C * δ`.

The mathematics: `F` is bounded and has bounded gradient on the compact set `Kc`; the mean value
inequality on the convex set `Kc` turns the gradient bound into a Lipschitz bound for `F`; and the
gradient map `fderiv ℝ F` is `C^1` on `U` (with `F` smooth), hence Lipschitz on the convex compact
set `Kc` by `ContDiffOn.exists_lipschitzOnWith`.  The chain rule expresses `deriv (F ∘ j) a` as
`fderiv ℝ F (j a) (deriv j a)`, and the two estimates combine.
-/

/-- Auxiliary data attached to a `C^∞` function `F` on an open set `U` and a compact convex set
`Kc ⊆ U`: a bound `A` for `|F|` on `Kc`, a bound `L₁` for the gradient of `F` on `Kc`, a Lipschitz
constant `L₂` for the gradient map itself on `Kc`, and differentiability of `F` on `Kc`. -/
private lemma jet_box_constants {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : E → ℝ) {U : Set E} (hU : IsOpen U) {Kc : Set E} (hcvx : Convex ℝ Kc)
    (hcpt : IsCompact Kc) (hKU : Kc ⊆ U) (hF : ContDiffOn ℝ (⊤ : ℕ∞) F U) :
    ∃ A L₁ L₂ : ℝ, 0 ≤ A ∧ 0 ≤ L₁ ∧ 0 ≤ L₂ ∧
      (∀ x ∈ Kc, |F x| ≤ A) ∧
      (∀ x ∈ Kc, ‖fderiv ℝ F x‖ ≤ L₁) ∧
      (∀ x ∈ Kc, DifferentiableAt ℝ F x) ∧
      (∀ x ∈ Kc, ∀ y ∈ Kc, ‖fderiv ℝ F x - fderiv ℝ F y‖ ≤ L₂ * ‖x - y‖) := by
  have hcAt : ∀ x ∈ Kc, ContDiffAt ℝ (⊤ : ℕ∞) F x := fun x hx =>
    hF.contDiffAt (hU.mem_nhds (hKU hx))
  have hcAt' : ∀ x ∈ Kc, ContDiffAt ℝ (⊤ : ℕ∞) (fderiv ℝ F) x := fun x hx =>
    (hcAt x hx).fderiv_right (m := (⊤ : ℕ∞)) (by simp)
  have hcont1 : ContinuousOn (fun x => fderiv ℝ F x) Kc := fun x hx =>
    (hcAt' x hx).continuousAt.continuousWithinAt
  obtain ⟨A₀, hA₀⟩ := hcpt.exists_bound_of_continuousOn (hF.continuousOn.mono hKU)
  obtain ⟨L₁₀, hL₁₀⟩ := hcpt.exists_bound_of_continuousOn hcont1
  have hΦcd : ContDiffOn ℝ (⊤ : ℕ∞) (fun x => fderiv ℝ F x) Kc := fun x hx =>
    ((hcAt x hx).fderiv_right (m := (⊤ : ℕ∞)) (by simp)).contDiffWithinAt
  obtain ⟨K₂, hK₂⟩ := hΦcd.exists_lipschitzOnWith (n := (⊤ : ℕ∞)) (by simp) hcvx hcpt
  refine ⟨max A₀ 0, max L₁₀ 0, (K₂ : ℝ), le_max_right _ _, le_max_right _ _, K₂.coe_nonneg,
    ?_, ?_, ?_, ?_⟩
  · intro x hx
    calc |F x| = ‖F x‖ := (Real.norm_eq_abs _).symm
      _ ≤ A₀ := hA₀ x hx
      _ ≤ max A₀ 0 := le_max_left _ _
  · intro x hx
    exact le_trans (hL₁₀ x hx) (le_max_left _ _)
  · intro x hx
    exact (hcAt x hx).differentiableAt (by simp)
  · intro x hx y hy
    exact hK₂.norm_sub_le hx hy

theorem JetCurve_box {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : E → ℝ) {U : Set E} (hU : IsOpen U) {Kc : Set E} (hcvx : Convex ℝ Kc)
    (hcpt : IsCompact Kc) (hKU : Kc ⊆ U) (hF : ContDiffOn ℝ (⊤ : ℕ∞) F U)
    {B' : ℝ} (hB' : 0 ≤ B') :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (j₁ j₀ : ℝ → E) (a δ : ℝ), 0 ≤ δ →
      ContDiff ℝ (⊤ : ℕ∞) j₁ → ContDiff ℝ (⊤ : ℕ∞) j₀ →
      j₁ a ∈ Kc → j₀ a ∈ Kc →
      ‖deriv j₁ a‖ ≤ B' → ‖deriv j₀ a‖ ≤ B' →
      ‖j₁ a - j₀ a‖ ≤ δ → ‖deriv j₁ a - deriv j₀ a‖ ≤ δ →
      |F (j₁ a)| ≤ C ∧ |F (j₀ a)| ≤ C ∧
      |deriv (fun x => F (j₁ x)) a| ≤ C ∧ |deriv (fun x => F (j₀ x)) a| ≤ C ∧
      |F (j₁ a) - F (j₀ a)| ≤ C * δ ∧
      |deriv (fun x => F (j₁ x)) a - deriv (fun x => F (j₀ x)) a| ≤ C * δ := by
  obtain ⟨A, L₁, L₂, hA0, hL₁0, hL₂0, hA, hL₁, hdiff, hLip⟩ :=
    jet_box_constants F hU hcvx hcpt hKU hF
  set C : ℝ := max (max A (L₁ * B')) (max L₁ (L₁ + L₂ * B')) with hC
  have hAC : A ≤ C := le_trans (le_max_left _ _) (le_max_left _ _)
  have hvc : L₁ * B' ≤ C := le_trans (le_max_right _ _) (le_max_left _ _)
  have hMc : L₁ ≤ C := le_trans (le_max_left _ _) (le_max_right _ _)
  have hmc : L₁ + L₂ * B' ≤ C := le_trans (le_max_right _ _) (le_max_right _ _)
  refine ⟨C, le_trans hA0 hAC, ?_⟩
  intro j₁ j₀ a δ hδ hj₁ hj₀ hj₁a hj₀a hv₁ hv₀ hpos hvel
  have hdj₁ : DifferentiableAt ℝ j₁ a := (hj₁.contDiffAt).differentiableAt (by simp)
  have hdj₀ : DifferentiableAt ℝ j₀ a := (hj₀.contDiffAt).differentiableAt (by simp)
  have hchain₁ : deriv (fun x => F (j₁ x)) a = fderiv ℝ F (j₁ a) (deriv j₁ a) :=
    ((((hdiff (j₁ a) hj₁a).hasFDerivAt).comp_hasDerivAt a hdj₁.hasDerivAt)).deriv
  have hchain₀ : deriv (fun x => F (j₀ x)) a = fderiv ℝ F (j₀ a) (deriv j₀ a) :=
    ((((hdiff (j₀ a) hj₀a).hasFDerivAt).comp_hasDerivAt a hdj₀.hasDerivAt)).deriv
  have hMVT_F : ‖F (j₁ a) - F (j₀ a)‖ ≤ L₁ * ‖j₁ a - j₀ a‖ :=
    hcvx.norm_image_sub_le_of_norm_hasFDerivWithin_le
      (f := F) (f' := fun x => fderiv ℝ F x) (C := L₁)
      (fun x hx => ((hdiff x hx).hasFDerivAt).hasFDerivWithinAt)
      (fun x hx => hL₁ x hx) hj₀a hj₁a
  have hgrad : ‖fderiv ℝ F (j₁ a) - fderiv ℝ F (j₀ a)‖ ≤ L₂ * ‖j₁ a - j₀ a‖ :=
    hLip (j₁ a) hj₁a (j₀ a) hj₀a
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact le_trans (hA _ hj₁a) hAC
  · exact le_trans (hA _ hj₀a) hAC
  · rw [hchain₁]
    calc |fderiv ℝ F (j₁ a) (deriv j₁ a)|
        = ‖fderiv ℝ F (j₁ a) (deriv j₁ a)‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖fderiv ℝ F (j₁ a)‖ * ‖deriv j₁ a‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ L₁ * B' := mul_le_mul (hL₁ _ hj₁a) hv₁ (norm_nonneg _) hL₁0
      _ ≤ C := hvc
  · rw [hchain₀]
    calc |fderiv ℝ F (j₀ a) (deriv j₀ a)|
        = ‖fderiv ℝ F (j₀ a) (deriv j₀ a)‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖fderiv ℝ F (j₀ a)‖ * ‖deriv j₀ a‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ L₁ * B' := mul_le_mul (hL₁ _ hj₀a) hv₀ (norm_nonneg _) hL₁0
      _ ≤ C := hvc
  · calc |F (j₁ a) - F (j₀ a)| = ‖F (j₁ a) - F (j₀ a)‖ := (Real.norm_eq_abs _).symm
      _ ≤ L₁ * ‖j₁ a - j₀ a‖ := hMVT_F
      _ ≤ L₁ * δ := mul_le_mul_of_nonneg_left hpos hL₁0
      _ ≤ C * δ := mul_le_mul_of_nonneg_right hMc hδ
  · rw [hchain₁, hchain₀]
    have hsplit : fderiv ℝ F (j₁ a) (deriv j₁ a) - fderiv ℝ F (j₀ a) (deriv j₀ a)
        = fderiv ℝ F (j₁ a) (deriv j₁ a - deriv j₀ a) +
          (fderiv ℝ F (j₁ a) - fderiv ℝ F (j₀ a)) (deriv j₀ a) := by
      rw [map_sub, sub_apply]
      abel
    rw [hsplit]
    calc |fderiv ℝ F (j₁ a) (deriv j₁ a - deriv j₀ a) +
            (fderiv ℝ F (j₁ a) - fderiv ℝ F (j₀ a)) (deriv j₀ a)|
        = ‖fderiv ℝ F (j₁ a) (deriv j₁ a - deriv j₀ a) +
            (fderiv ℝ F (j₁ a) - fderiv ℝ F (j₀ a)) (deriv j₀ a)‖ :=
          (Real.norm_eq_abs _).symm
      _ ≤ ‖fderiv ℝ F (j₁ a) (deriv j₁ a - deriv j₀ a)‖ +
            ‖(fderiv ℝ F (j₁ a) - fderiv ℝ F (j₀ a)) (deriv j₀ a)‖ := norm_add_le _ _
      _ ≤ ‖fderiv ℝ F (j₁ a)‖ * ‖deriv j₁ a - deriv j₀ a‖ +
            ‖fderiv ℝ F (j₁ a) - fderiv ℝ F (j₀ a)‖ * ‖deriv j₀ a‖ :=
          add_le_add (ContinuousLinearMap.le_opNorm _ _) (ContinuousLinearMap.le_opNorm _ _)
      _ ≤ L₁ * δ + L₂ * δ * B' := by
          refine add_le_add ?_ ?_
          · exact mul_le_mul (hL₁ _ hj₁a) hvel (norm_nonneg _) hL₁0
          · refine mul_le_mul ?_ hv₀ (norm_nonneg _) (mul_nonneg hL₂0 hδ)
            calc ‖fderiv ℝ F (j₁ a) - fderiv ℝ F (j₀ a)‖
                ≤ L₂ * ‖j₁ a - j₀ a‖ := hgrad
              _ ≤ L₂ * δ := mul_le_mul_of_nonneg_left hpos hL₂0
      _ = (L₁ + L₂ * B') * δ := by ring
      _ ≤ C * δ := mul_le_mul_of_nonneg_right hmc hδ

end Work.OddVolterra.Window
