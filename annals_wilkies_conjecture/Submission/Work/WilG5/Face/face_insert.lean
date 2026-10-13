import Mathlib
import Submission.Work.WilG5.Face.Defs

namespace Work.WilG5.Face

/-- The open unit cube is open. -/
lemma isOpen_openCube (μ : ℕ) : IsOpen (WilkiesDesign.openCube μ) := by
  have h : WilkiesDesign.openCube μ =
      ⋂ i : Fin μ, {x : Fin μ → ℝ | x i ∈ Set.Ioo (0:ℝ) 1} := by
    ext x; simp [WilkiesDesign.openCube]
  rw [h]
  exact isOpen_iInter_of_finite (fun i => isOpen_Ioo.preimage (continuous_apply i))

theorem face_insert {μ n r : ℕ} (hn : 1 ≤ n) (i : Fin n) {c : ℝ} (hc : c ∈ Set.Icc (0:ℝ) 1)
    (f : (Fin μ → ℝ) → (Fin (n - 1) → ℝ))
    (hf : ContDiffOn ℝ r f (WilkiesDesign.openCube μ))
    (hbd : ∀ k ≤ r, ∀ t ∈ WilkiesDesign.openCube μ, ‖iteratedFDeriv ℝ k f t‖ ≤ 1)
    (hcube : ∀ t ∈ WilkiesDesign.openCube μ, f t ∈ WilkiesDesign.cube01 (n - 1)) :
    ContDiffOn ℝ r (fun t => (Work.WilG5.Face.insCoord i c (f t) : Fin n → ℝ))
        (WilkiesDesign.openCube μ) ∧
      ∀ k ≤ r, ∀ t ∈ WilkiesDesign.openCube μ,
        ‖iteratedFDeriv ℝ k (fun t => (Work.WilG5.Face.insCoord i c (f t) : Fin n → ℝ)) t‖ ≤ 1 := by
  have hU : IsOpen (WilkiesDesign.openCube μ) := isOpen_openCube μ
  let e : Fin n → ℝ := Pi.single i c
  constructor
  · -- `t ↦ insCoord i c (f t)` is `insCLM i ∘ f` plus the constant `Pi.single i c`.
    have h1 : ContDiffOn ℝ r (fun t => insCLM i (f t) + Pi.single i c)
        (WilkiesDesign.openCube μ) :=
      (hf.continuousLinearMap_comp (insCLM i)).add contDiffOn_const
    refine h1.congr ?_
    intro t _
    exact insCoord_eq_insCLM_add i c (f t)
  · intro k hk t ht
    rcases k with _ | j
    · -- zeroth derivative: the coordinates of `insCoord i c (f t)` all lie in `[0,1]`.
      simp only [norm_iteratedFDeriv_zero]
      refine (pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ) ≤ 1)).mpr fun l => ?_
      by_cases hl : l = i
      · subst hl
        rw [insCoord_self, Real.norm_eq_abs]
        exact abs_le.mpr ⟨by linarith [hc.1], hc.2⟩
      · rw [insCoord_of_ne i l c (f t) hl, Real.norm_eq_abs]
        have hl' := hcube t ht (splitIdx i l hl)
        exact abs_le.mpr ⟨by linarith [hl'.1], hl'.2⟩
    · -- The function agrees with `t ↦ insCLM i (f t) + e`.
      have hfun : (fun t => (insCoord i c (f t) : Fin n → ℝ)) = fun t => insCLM i (f t) + e := by
        funext t
        simpa [e] using insCoord_eq_insCLM_add i c (f t)
      rw [hfun]
      have hfAt : ContDiffAt ℝ r f t := hf.contDiffAt (hU.mem_nhds ht)
      have hLfAt : ContDiffAt ℝ (j + 1) (fun t => insCLM i (f t)) t :=
        (hfAt.continuousLinearMap_comp (insCLM i)).of_le (by exact_mod_cast hk)
      have hcAt : ContDiffAt ℝ (j + 1) (fun _ : Fin μ → ℝ => e) t :=
        contDiffAt_const (c := e)
      -- differentiating a constant does not contribute, since `j + 1 ≥ 1`.
      have hzero : iteratedFDeriv ℝ (j + 1) (fun _ : Fin μ → ℝ => e) t = 0 := by
        rw [iteratedFDeriv_const_of_ne (𝕜 := ℝ) (by omega : (j:ℕ) + 1 ≠ 0) e]
        rfl
      rw [show (fun t => insCLM i (f t) + e)
            = (fun t => insCLM i (f t)) + (fun _ : Fin μ → ℝ => e) from rfl]
      rw [iteratedFDeriv_add_apply hLfAt hcAt, hzero, add_zero]
      -- the derivative of `L ∘ f` is `L` applied to the derivative of `f`
      calc ‖iteratedFDeriv ℝ (j + 1) (fun t => insCLM i (f t)) t‖
          = ‖iteratedFDeriv ℝ (j + 1)
              ((insCLM i : (Fin (n - 1) → ℝ) →L[ℝ] (Fin n → ℝ)) ∘ f) t‖ := rfl
        _ ≤ ‖insCLM i‖ * ‖iteratedFDeriv ℝ (j + 1) f t‖ :=
            ContinuousLinearMap.norm_iteratedFDeriv_comp_left (insCLM i) hfAt
              (by exact_mod_cast hk)
        _ ≤ 1 * 1 :=
            mul_le_mul (norm_insCLM_le_one i) (hbd (j + 1) hk t ht) (norm_nonneg _) zero_le_one
        _ = 1 := one_mul 1

end Work.WilG5.Face
