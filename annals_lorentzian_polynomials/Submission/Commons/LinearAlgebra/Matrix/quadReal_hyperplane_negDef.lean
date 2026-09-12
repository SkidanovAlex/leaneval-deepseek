import Mathlib
import Submission.Commons.LinearAlgebra.Matrix.quadratic_stable_iff_roots_card_le_one
import Submission.Commons.LinearAlgebra.Matrix.scalar_hyperplane_negSemidef

open Matrix
open scoped BigOperators

set_option linter.unusedVariables false

namespace Commons.LinearAlgebra.Matrix

noncomputable section

/-- If the bilinear form `(y,x) ↦ quadReal A y x` vanishes for every `y`, then `A x = 0`.
This is Rayleigh-quotient-free: it only uses symmetry and the nondegeneracy of the
Euclidean dot product. -/
lemma mulVec_eq_zero_of_quadReal_eq_zero {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.IsSymm) (x : Fin n → ℝ)
    (hq : ∀ y : Fin n → ℝ, quadReal A x y = 0) : A.mulVec x = 0 := by
  classical
  have hquad0 : ∀ y : Fin n → ℝ, quadReal A y x = 0 := by
    intro y
    rw [quadReal_symm A hA y x]
    exact hq y
  have hdot : ∀ y : Fin n → ℝ, y ⬝ᵥ (A.mulVec x) = 0 := by
    intro y
    rw [← quadReal_mulVec A y x]
    exact hquad0 y
  funext j
  have hj : ((fun i : Fin n => if i = j then (1 : ℝ) else 0) ⬝ᵥ (A.mulVec x)) = 0 := hdot _
  simpa [dotProduct] using hj

theorem quadReal_hyperplane_negDef {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.IsSymm) (hreg : A.det ≠ 0)
    (hidx : (A.charpoly.roots.filter (fun r : ℝ => 0 < r)).card ≤ 1)
    (w : Fin n → ℝ) (hwA : 0 < Commons.LinearAlgebra.Matrix.quadReal A w w)
    (x : Fin n → ℝ) (hx : Commons.LinearAlgebra.Matrix.quadReal A w x = 0) :
    Commons.LinearAlgebra.Matrix.quadReal A x x ≤ 0 ∧
      (Commons.LinearAlgebra.Matrix.quadReal A x x = 0 → Matrix.mulVec A x = 0) := by
  classical
  let lam : Fin n → ℝ := fun i =>
    (LinearMap.IsSymmetric.eigenvalues
      (T := A.toEuclideanLin)
      (by rw [Matrix.isSymmetric_toEuclideanLin_iff]; exact (Matrix.isHermitian_iff_isSymm).2 hA)
      (by simp [finrank_euclideanSpace]) i)
  have hlam_eq_apply : ∀ i : Fin n, symmEigenvalues A hA i = lam i := by
    intro i
    rfl
  let cw : Fin n → ℝ := fun i => ((symmBasis A hA).repr (WithLp.toLp 2 w)).ofLp i
  let cx : Fin n → ℝ := fun i => ((symmBasis A hA).repr (WithLp.toLp 2 x)).ofLp i
  have hq_ww : quadReal A w w = ∑ i : Fin n, lam i * (cw i * cw i) := by
    simpa [cw, hlam_eq_apply] using quadReal_eq_eigen_sum' A hA w w
  have hb_pos : 0 < ∑ i : Fin n, lam i * (cw i * cw i) := by
    rw [← hq_ww]
    exact hwA
  -- some positive weight: a coordinate `p` with `lam p > 0`
  have hex : ∃ p : Fin n, 0 < lam p * (cw p * cw p) := by
    by_contra hnot
    have hall : ∀ p : Fin n, lam p * (cw p * cw p) ≤ 0 := by
      intro p
      exact le_of_not_gt (fun h => hnot ⟨p, h⟩)
    have hsum_le : (∑ i : Fin n, lam i * (cw i * cw i)) ≤ 0 := Finset.sum_nonpos (fun i hi => hall i)
    linarith
  obtain ⟨p, hp_pos⟩ := hex
  have hlam_p : 0 < lam p := by
    by_contra hle
    have hneg : lam p * (cw p * cw p) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hle) (mul_self_nonneg (cw p))
    linarith
  -- at most one positive eigenvalue, and it must be `p`
  have hcard_lam : (Finset.univ.filter (fun i : Fin n => 0 < lam i)).card ≤ 1 := by
    dsimp [lam]
    rw [← charpoly_positive_roots_card_eq A hA]
    exact hidx
  have hlam_rest : ∀ i : Fin n, i ≠ p → lam i ≤ 0 := by
    intro i hi
    by_contra hnotpos
    have hpos : 0 < lam i := lt_of_not_ge hnotpos
    have hcard_le : ∀ a ∈ (Finset.univ.filter (fun j : Fin n => 0 < lam j)),
        ∀ b ∈ (Finset.univ.filter (fun j : Fin n => 0 < lam j)), a = b :=
      (Finset.card_le_one.mp hcard_lam)
    have hi_mem : i ∈ (Finset.univ.filter (fun j : Fin n => 0 < lam j)) := by simp [hpos]
    have hp_mem : p ∈ (Finset.univ.filter (fun j : Fin n => 0 < lam j)) := by simp [hlam_p]
    have : i = p := hcard_le i hi_mem p hp_mem
    exact hi this
  -- hyperplane condition in eigen coordinates
  have hq_wx : quadReal A w x = ∑ i : Fin n, lam i * (cw i * cx i) := by
    simpa [cw, cx, hlam_eq_apply] using quadReal_eq_eigen_sum' A hA w x
  have hcross : (∑ i : Fin n, lam i * (cx i * cw i)) = 0 := by
    calc
      (∑ i : Fin n, lam i * (cx i * cw i)) = ∑ i : Fin n, lam i * (cw i * cx i) := by
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = quadReal A w x := hq_wx.symm
      _ = 0 := hx
  -- scalar inequality on coordinates
  have hsc := scalar_hyperplane_negSemidef lam cw cx p hlam_p hlam_rest hb_pos hcross
  have hq_xx : quadReal A x x = ∑ i : Fin n, lam i * (cx i * cx i) := by
    simpa [cx, hlam_eq_apply] using quadReal_eq_eigen_sum' A hA x x
  constructor
  · rw [hq_xx]
    exact hsc.1
  · intro hxx0
    have hq0_sum : (∑ i : Fin n, lam i * (cx i * cx i)) = 0 := by
      simpa [hq_xx] using hxx0
    have hzero_coords : ∀ i : Fin n, lam i ≠ 0 → cx i = 0 := hsc.2 hq0_sum
    apply mulVec_eq_zero_of_quadReal_eq_zero A hA x
    intro y
    let cy : Fin n → ℝ := fun i => ((symmBasis A hA).repr (WithLp.toLp 2 y)).ofLp i
    have hq_xy : quadReal A x y = ∑ i : Fin n, lam i * (cx i * cy i) := by
      simpa [cx, cy, hlam_eq_apply] using quadReal_eq_eigen_sum' A hA x y
    rw [hq_xy]
    apply Finset.sum_eq_zero
    intro i hi
    by_cases hlam0 : lam i = 0
    · simp [lam, hlam0]
    · have hcx0 : cx i = 0 := hzero_coords i hlam0
      simp [cx, cy, hcx0]

end

end Commons.LinearAlgebra.Matrix
