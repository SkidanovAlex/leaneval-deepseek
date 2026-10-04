import Mathlib
import Submission.Work.Diff.STE.flat.antisymN_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Elementary facts about `posSet`, `symMat` and the quadratic form

Supporting lemmas for `Work.Diff.STE.flat.antisymN_bound`: the admissible region `posSet` is closed,
bounded by the closed ball of radius `M` and convex, hence compact, and it is contained in the
domain `detNeZeroSet`; and the symmetrisation `symMat` is symmetric, preserves the quadratic form
and is `1/2`-close to the identity in each entry.

The import closure of this module is `Mathlib` plus `antisymN_defs` only (in particular it avoids
`Submission.Work.Diff.STE.flat.det_ne_zero_of_quadForm_le`, whose constant
`sum_sum_mul_eq_dotProduct` collides with the copy declared in `torus_uniqueness.lean`).
-/

namespace Work.Diff.STE.flat

open Work.Diff.STE.Flat

noncomputable section

variable {n : ℕ}

/-! ### Algebra of the symmetrisation -/

lemma symMat_symm (A : MatC n) : ∀ i j, symMat A i j = symMat A j i := by
  intro i j
  simp only [symMat]
  rw [add_comm]

lemma sub_symMat_apply (A : MatC n) (i j : Fin n) :
    (A - symMat A) i j = (A i j - A j i) / 2 := by
  simp only [Pi.sub_apply, symMat]
  ring

lemma norm_sub_symMat (A : MatC n) (i j : Fin n) :
    ‖(A - symMat A) i j‖ = ‖A i j - A j i‖ / 2 := by
  rw [sub_symMat_apply, norm_div]
  norm_num

lemma norm_symMat_le (A : MatC n) (i j : Fin n) :
    ‖symMat A i j‖ ≤ (‖A i j‖ + ‖A j i‖) / 2 := by
  rw [symMat, norm_div]
  have h2 : ‖(2 : ℂ)‖ = 2 := by norm_num
  rw [h2]
  exact div_le_div_of_nonneg_right (norm_add_le _ _) (by norm_num)

/-- The real part of `z / 2` for a complex number. -/
private lemma re_div_two (z : ℂ) : (z / 2).re = z.re / 2 := by
  rw [Complex.div_re]
  norm_num [Complex.normSq]
  ring

lemma symMat_re_apply (A : MatC n) (i j : Fin n) :
    (symMat A i j).re = ((A i j).re + (A j i).re) / 2 := by
  rw [symMat, re_div_two, Complex.add_re]

lemma quadForm_symMat (A : MatC n) (ξ : Fin n → ℝ) : quadForm (symMat A) ξ = quadForm A ξ := by
  have h2S : ∀ i j : Fin n, 2 * ((symMat A i j).re * ξ i * ξ j)
      = ((A i j).re + (A j i).re) * ξ i * ξ j := by
    intro i j
    rw [symMat_re_apply]
    ring
  have h2A : ∀ i j : Fin n, ((A i j).re + (A j i).re) * ξ i * ξ j
      = (A i j).re * ξ i * ξ j + (A j i).re * ξ i * ξ j := by
    intro i j
    ring
  have hswap : ∑ i, ∑ j, (A j i).re * ξ i * ξ j = ∑ i, ∑ j, (A i j).re * ξ i * ξ j := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have hL : 2 * (∑ i, ∑ j, (symMat A i j).re * ξ i * ξ j)
      = ∑ i, ∑ j, ((A i j).re + (A j i).re) * ξ i * ξ j := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => h2S i j
  have hR : ∑ i, ∑ j, ((A i j).re + (A j i).re) * ξ i * ξ j
      = 2 * (∑ i, ∑ j, (A i j).re * ξ i * ξ j) := by
    have e1 : ∑ i, ∑ j, ((A i j).re + (A j i).re) * ξ i * ξ j
        = ∑ i, ∑ j, ((A i j).re * ξ i * ξ j + (A j i).re * ξ i * ξ j) :=
      Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => h2A i j))
    rw [e1]
    simp only [Finset.sum_add_distrib]
    rw [hswap]
    ring
  show ∑ i, ∑ j, (symMat A i j).re * ξ i * ξ j = ∑ i, ∑ j, (A i j).re * ξ i * ξ j
  exact mul_left_cancel₀ two_ne_zero (hL.trans hR)

/-! ### Geometry of the admissible set -/

private lemma reMat_smul_add (a b : ℝ) (A B : MatC n) :
    reMat (a • A + b • B) = a • reMat A + b • reMat B := by
  ext i j
  simp only [reMat_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Matrix.add_apply,
    Matrix.smul_apply]
  simp [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]

private lemma continuous_quadForm (ξ : Fin n → ℝ) :
    Continuous fun w : MatC n × (Fin n → MatC n) => quadForm w.1 ξ := by
  have hfun : (fun w : MatC n × (Fin n → MatC n) => quadForm w.1 ξ)
      = fun w => ∑ i, ∑ j, reMat w.1 i j * ξ i * ξ j := rfl
  rw [hfun]
  refine continuous_finsetSum _ (fun i _ => continuous_finsetSum _ (fun j _ => ?_))
  have h1 : Continuous (fun w : MatC n × (Fin n → MatC n) => reMat w.1 i j) :=
    Complex.continuous_re.comp
      ((continuous_apply j).comp ((continuous_apply i).comp continuous_fst))
  exact (h1.mul continuous_const).mul continuous_const

private lemma isClosed_posSet (M lam : ℝ) : IsClosed (posSet (n := n) M lam) := by
  have h1 : IsClosed {w : MatC n × (Fin n → MatC n) | ∀ i j, ‖w.1 i j‖ ≤ M} := by
    rw [show {w : MatC n × (Fin n → MatC n) | ∀ i j, ‖w.1 i j‖ ≤ M}
        = ⋂ (i : Fin n), ⋂ (j : Fin n), {w | ‖w.1 i j‖ ≤ M} by ext w; simp]
    exact isClosed_iInter fun i => isClosed_iInter fun j =>
      isClosed_le (by fun_prop) continuous_const
  have h2 : IsClosed {w : MatC n × (Fin n → MatC n) | ∀ c i j, ‖w.2 c i j‖ ≤ M} := by
    rw [show {w : MatC n × (Fin n → MatC n) | ∀ c i j, ‖w.2 c i j‖ ≤ M}
        = ⋂ (c : Fin n), ⋂ (i : Fin n), ⋂ (j : Fin n), {w | ‖w.2 c i j‖ ≤ M} by ext w; simp]
    exact isClosed_iInter fun c => isClosed_iInter fun i => isClosed_iInter fun j =>
      isClosed_le (by fun_prop) continuous_const
  have h3 : IsClosed {w : MatC n × (Fin n → MatC n) |
      ∀ ξ : Fin n → ℝ, lam * ∑ i, (ξ i) ^ 2 ≤ quadForm w.1 ξ} := by
    rw [show {w : MatC n × (Fin n → MatC n) |
        ∀ ξ : Fin n → ℝ, lam * ∑ i, (ξ i) ^ 2 ≤ quadForm w.1 ξ}
        = ⋂ (ξ : Fin n → ℝ), {w | lam * ∑ i, (ξ i) ^ 2 ≤ quadForm w.1 ξ} by ext w; simp]
    exact isClosed_iInter fun ξ => isClosed_le continuous_const (continuous_quadForm ξ)
  have heq : posSet (n := n) M lam
      = {w : MatC n × (Fin n → MatC n) | ∀ i j, ‖w.1 i j‖ ≤ M} ∩
        {w : MatC n × (Fin n → MatC n) | ∀ c i j, ‖w.2 c i j‖ ≤ M} ∩
        {w : MatC n × (Fin n → MatC n) |
          ∀ ξ : Fin n → ℝ, lam * ∑ i, (ξ i) ^ 2 ≤ quadForm w.1 ξ} := by
    ext w
    simp [mem_posSet, and_assoc]
  rw [heq]
  exact (h1.inter h2).inter h3

private lemma posSet_subset_closedBall (M lam : ℝ) (hM : 0 ≤ M) :
    posSet (n := n) M lam ⊆ Metric.closedBall (0 : MatC n × (Fin n → MatC n)) M := by
  intro w hw
  rw [Metric.mem_closedBall, dist_zero_right, Prod.norm_def]
  refine max_le ?_ ?_
  · rw [pi_norm_le_iff_of_nonneg hM]
    intro i
    rw [pi_norm_le_iff_of_nonneg hM]
    exact hw.1 i
  · rw [pi_norm_le_iff_of_nonneg hM]
    intro c
    rw [pi_norm_le_iff_of_nonneg hM]
    intro i
    rw [pi_norm_le_iff_of_nonneg hM]
    exact hw.2.1 c i

private lemma convex_posSet (M lam : ℝ) : Convex ℝ (posSet (n := n) M lam) := by
  intro w₁ hw₁ w₂ hw₂ a b ha hb hab
  obtain ⟨hA₁, hL₁, hE₁⟩ := hw₁
  obtain ⟨hA₂, hL₂, hE₂⟩ := hw₂
  refine ⟨?_, ?_, ?_⟩
  · intro i j
    have hw : (a • w₁ + b • w₂).1 i j = a • w₁.1 i j + b • w₂.1 i j := rfl
    rw [hw]
    calc ‖a • w₁.1 i j + b • w₂.1 i j‖ ≤ ‖a • w₁.1 i j‖ + ‖b • w₂.1 i j‖ := norm_add_le _ _
      _ = a * ‖w₁.1 i j‖ + b * ‖w₂.1 i j‖ := by
          rw [norm_smul, norm_smul, Real.norm_of_nonneg ha, Real.norm_of_nonneg hb]
      _ ≤ a * M + b * M := add_le_add (mul_le_mul_of_nonneg_left (hA₁ i j) ha)
          (mul_le_mul_of_nonneg_left (hA₂ i j) hb)
      _ = M := by rw [← add_mul, hab, one_mul]
  · intro c i j
    have hw : (a • w₁ + b • w₂).2 c i j = a • w₁.2 c i j + b • w₂.2 c i j := rfl
    rw [hw]
    calc ‖a • w₁.2 c i j + b • w₂.2 c i j‖ ≤ ‖a • w₁.2 c i j‖ + ‖b • w₂.2 c i j‖ :=
          norm_add_le _ _
      _ = a * ‖w₁.2 c i j‖ + b * ‖w₂.2 c i j‖ := by
          rw [norm_smul, norm_smul, Real.norm_of_nonneg ha, Real.norm_of_nonneg hb]
      _ ≤ a * M + b * M := add_le_add (mul_le_mul_of_nonneg_left (hL₁ c i j) ha)
          (mul_le_mul_of_nonneg_left (hL₂ c i j) hb)
      _ = M := by rw [← add_mul, hab, one_mul]
  · intro ξ
    have hre : reMat (a • w₁ + b • w₂).1 = a • reMat w₁.1 + b • reMat w₂.1 := by
      have h1 : (a • w₁ + b • w₂).1 = a • w₁.1 + b • w₂.1 := rfl
      rw [h1, reMat_smul_add]
    simp only [quadForm]
    rw [hre]
    have hsplit : ∑ i, ∑ j, (a * reMat w₁.1 i j + b * reMat w₂.1 i j) * ξ i * ξ j
        = a * (∑ i, ∑ j, reMat w₁.1 i j * ξ i * ξ j)
          + b * (∑ i, ∑ j, reMat w₂.1 i j * ξ i * ξ j) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      ring
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    rw [hsplit]
    have h3 : a * (lam * ∑ i, (ξ i) ^ 2)
        ≤ a * (∑ i, ∑ j, reMat w₁.1 i j * ξ i * ξ j) := mul_le_mul_of_nonneg_left (hE₁ ξ) ha
    have h4 : b * (lam * ∑ i, (ξ i) ^ 2)
        ≤ b * (∑ i, ∑ j, reMat w₂.1 i j * ξ i * ξ j) := mul_le_mul_of_nonneg_left (hE₂ ξ) hb
    have h5 : a * (lam * ∑ i, (ξ i) ^ 2) + b * (lam * ∑ i, (ξ i) ^ 2)
        = lam * ∑ i, (ξ i) ^ 2 := by rw [← add_mul, hab, one_mul]
    linarith

/-- The admissible set is compact. -/
theorem posSet_isCompact (M lam : ℝ) (hM : 0 ≤ M) : IsCompact (posSet (n := n) M lam) :=
  (isCompact_closedBall (0 : MatC n × (Fin n → MatC n)) M).of_isClosed_subset
    (isClosed_posSet M lam) (posSet_subset_closedBall M lam hM)

/-- The admissible set is convex. -/
theorem posSet_convex (M lam : ℝ) : Convex ℝ (posSet (n := n) M lam) := convex_posSet M lam

/-- The admissible set consists of value matrices whose real part is invertible. -/
theorem posSet_subset_detNeZero (M lam : ℝ) (hlam : 0 < lam) :
    posSet (n := n) M lam ⊆ detNeZeroSet (n := n) := by
  intro w hw
  exact det_ne_zero_of_quadForm_bound (reMat w.1) hlam hw.2.2

end

end Work.Diff.STE.flat
