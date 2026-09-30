import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW.isometricAux

open Matrix

theorem slab_convex_symm_closed {n m : ℕ} (Bp : Matrix (Fin n) (Fin m) ℝ) {δ : ℝ} (hδ : 0 < δ) :
    Convex ℝ {z : Fin n → ℝ | ∀ l, |(Bp.transpose.mulVec z) l| ≤ δ/2} ∧
    ({z : Fin n → ℝ | ∀ l, |(Bp.transpose.mulVec z) l| ≤ δ/2}
       = -{z : Fin n → ℝ | ∀ l, |(Bp.transpose.mulVec z) l| ≤ δ/2}) ∧
    IsClosed {z : Fin n → ℝ | ∀ l, |(Bp.transpose.mulVec z) l| ≤ δ/2} := by
  -- coordinate linearity of `z ↦ Bpᵀ *ᵥ z`
  have hlin : ∀ l : Fin m, ∀ (z w : Fin n → ℝ) (a b : ℝ),
      (Bp.transpose.mulVec (a • z + b • w)) l
        = a * (Bp.transpose.mulVec z) l + b * (Bp.transpose.mulVec w) l := by
    intro l z w a b
    rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul]
    simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  -- coordinate behaviour under negation
  have hneg : ∀ l : Fin m, ∀ z : Fin n → ℝ,
      (Bp.transpose.mulVec (-z)) l = -((Bp.transpose.mulVec z) l) := by
    intro l z
    rw [Matrix.mulVec_neg]
    rfl
  refine ⟨?_, ?_, ?_⟩
  · intro x hx y hy a b ha hb hab l
    rw [hlin l x y a b]
    calc |a * (Bp.transpose.mulVec x) l + b * (Bp.transpose.mulVec y) l|
        ≤ |a * (Bp.transpose.mulVec x) l| + |b * (Bp.transpose.mulVec y) l| := abs_add_le _ _
      _ = a * |(Bp.transpose.mulVec x) l| + b * |(Bp.transpose.mulVec y) l| := by
            rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
      _ ≤ a * (δ/2) + b * (δ/2) := by
            apply add_le_add
            · exact mul_le_mul_of_nonneg_left (hx l) ha
            · exact mul_le_mul_of_nonneg_left (hy l) hb
      _ = δ/2 := by rw [← add_mul, hab, one_mul]
  · ext x
    rw [Set.mem_neg]
    simp only [Set.mem_ofPred_eq]
    constructor
    · intro hx l
      rw [hneg l x, abs_neg]
      exact hx l
    · intro hx l
      have hxl := hx l
      rw [hneg l x, abs_neg] at hxl
      exact hxl
  · rw [Set.ofPred_forall]
    apply isClosed_iInter
    intro l
    have hcont : Continuous (fun z : Fin n → ℝ => |(Bp.transpose.mulVec z) l|) := by
      have h2 : Continuous (fun z : Fin n → ℝ => (Bp.transpose.mulVecLin z) l) :=
        (continuous_apply l).comp (LinearMap.continuous_of_finiteDimensional _)
      have h3 : Continuous (fun z : Fin n → ℝ => (Bp.transpose.mulVec z) l) := by
        simpa only [Matrix.mulVecLin_apply] using h2
      exact h3.abs
    exact isClosed_le hcont continuous_const

end Work.BW.isometricAux
