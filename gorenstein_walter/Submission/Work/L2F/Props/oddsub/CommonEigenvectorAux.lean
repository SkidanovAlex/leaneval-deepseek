import Mathlib
import Submission.Work.L2F.Mat2.sq_eq_trace_smul_sub_det

/-!
# Auxiliary vocabulary for `fixes_line_of_normal_abelian_with_invariant_line`

* `IsCommonEigenvector Q u`: `u ≠ 0` and every element of `Q ≤ SL(2,F)` acts on `u` by a scalar.
* `eq_smul_of_mulVec_eq_zero_of_ne_zero`: a nonzero `2 × 2` matrix which annihilates a nonzero
  vector `v` has kernel contained in the line spanned by `v`.
* `not_scalar_coe_of_odd_orderOf`: a non-identity element of `SL(2,F)` of odd order is not a
  scalar matrix.
* `sq_sub_trace_mul_add_one_of_eigenvector`: the eigenvalue `c` of an eigenvector of an element
  `g ∈ SL(2,F)` satisfies the characteristic equation `c ^ 2 - tr g * c + 1 = 0`.
-/

open scoped MatrixGroups
open Matrix

namespace Work.L2F.Props.oddsub

variable {F : Type*} [Field F]

/-- `u` is a common eigenvector for the subgroup `Q ≤ SL(2,F)`: a nonzero vector on which every
element of `Q` acts by a scalar. -/
def IsCommonEigenvector (Q : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F))
    (u : Fin 2 → F) : Prop :=
  u ≠ 0 ∧ ∀ y ∈ Q, ∃ c : F,
    Matrix.mulVec ((y : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) u = c • u

/-- **Kernel of a nonzero `2 × 2` matrix.**  If `A ≠ 0` is a `2 × 2` matrix annihilating a
nonzero vector `v`, then every vector annihilated by `A` is a multiple of `v`. -/
theorem eq_smul_of_mulVec_eq_zero_of_ne_zero (A : Matrix (Fin 2) (Fin 2) F) (v : Fin 2 → F)
    (hA : A ≠ 0) (hv : v ≠ 0) (hAv : A *ᵥ v = 0) :
    ∀ u : Fin 2 → F, A *ᵥ u = 0 → ∃ c : F, u = c • v := by
  intro u hu
  have hker_ne : (Matrix.mulVecLin A).ker ≠ ⊤ := by
    intro h
    apply hA
    ext i j
    have hmem : (Pi.single j (1 : F)) ∈ (Matrix.mulVecLin A).ker := by
      rw [h]; exact Submodule.mem_top
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.mulVec_single_one] at hmem
    have := congrFun hmem i
    rwa [Matrix.col_apply] at this
  have hfin : Module.finrank F ↥(Matrix.mulVecLin A).ker ≤ 1 := by
    have hlt : (Matrix.mulVecLin A).ker < ⊤ := lt_top_iff_ne_top.mpr hker_ne
    have := Submodule.finrank_lt_finrank_of_lt hlt
    rw [finrank_top, Module.finrank_fin_fun F] at this
    omega
  have hle : F ∙ v ≤ (Matrix.mulVecLin A).ker := by
    rw [Submodule.span_le]
    intro w hw
    rw [Set.mem_singleton_iff] at hw
    rw [hw]
    simpa [LinearMap.mem_ker, Matrix.mulVecLin_apply] using hAv
  have heq : F ∙ v = (Matrix.mulVecLin A).ker := by
    apply Submodule.eq_of_le_of_finrank_le hle
    rw [finrank_span_singleton hv]
    exact hfin
  have hu' : u ∈ F ∙ v := by
    rw [heq]
    simpa [LinearMap.mem_ker, Matrix.mulVecLin_apply] using hu
  rw [Submodule.mem_span_singleton] at hu'
  obtain ⟨c, hc⟩ := hu'
  exact ⟨c, hc.symm⟩

/-- Two distinct lines: if `u` is not a multiple of `v`, then `v` is not a multiple of `u`. -/
theorem notMem_span_of_notMem_span {v u : Fin 2 → F} (hv : v ≠ 0) (hu : u ≠ 0)
    (h : u ∉ Submodule.span F ({v} : Set (Fin 2 → F))) :
    v ∉ Submodule.span F ({u} : Set (Fin 2 → F)) := by
  intro hvu
  obtain ⟨a, ha⟩ : ∃ a : F, a • u = v := Submodule.mem_span_singleton.mp hvu
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [zero_smul] at ha
    exact hv ha.symm
  apply h
  rw [Submodule.mem_span_singleton]
  exact ⟨a⁻¹, by rw [← ha, smul_smul, inv_mul_cancel₀ ha0, one_smul]⟩

/-- **A non-identity element of `SL(2,F)` of odd order is not a scalar matrix.** -/
theorem not_scalar_coe_of_odd_orderOf (x : Matrix.SpecialLinearGroup (Fin 2) F) (hx : x ≠ 1)
    (hodd : Odd (orderOf x)) :
    ∀ c : F, (x : Matrix (Fin 2) (Fin 2) F) ≠ c • (1 : Matrix (Fin 2) (Fin 2) F) := by
  intro c hc
  have hdet : c ^ 2 = 1 := by
    have h := Matrix.SpecialLinearGroup.det_coe x
    rw [hc, Matrix.det_smul, Fintype.card_fin] at h
    simpa using h
  have hcc : c * c = 1 := by rw [← pow_two, hdet]
  have hmul : (c • (1 : Matrix (Fin 2) (Fin 2) F)) * (c • 1) = 1 := by
    rw [show (c • (1 : Matrix (Fin 2) (Fin 2) F)) * (c • 1) = (c * c) • 1 by
          ext i j
          fin_cases i <;> fin_cases j <;>
            simp [Matrix.mul_apply, Matrix.one_apply],
      hcc, one_smul]
  have hsq : x * x = 1 := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one, hc]
    exact hmul
  have h2 : orderOf x ∣ 2 := by
    rw [orderOf_dvd_iff_pow_eq_one, pow_two]
    exact hsq
  obtain ⟨k, hk⟩ := hodd
  rcases (Nat.dvd_prime Nat.prime_two).mp h2 with h | h
  · exact hx (orderOf_eq_one_iff.mp h)
  · omega

/-- **Characteristic equation of an eigenvalue.**  If `z ≠ 0` and `g ∈ SL(2,F)` satisfies
`g *ᵥ z = c • z`, then `c ^ 2 - (tr g) * c + 1 = 0`. -/
theorem sq_sub_trace_mul_add_one_of_eigenvector (g : Matrix.SpecialLinearGroup (Fin 2) F)
    (z : Fin 2 → F) (c : F) (hz : z ≠ 0)
    (h : Matrix.mulVec ((g : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) z
      = c • z) :
    c ^ 2 - (((g : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)).trace * c
      + 1 = 0 := by
  set M : Matrix (Fin 2) (Fin 2) F := (g : Matrix (Fin 2) (Fin 2) F) with hM
  have hdet : M.det = 1 := Matrix.SpecialLinearGroup.det_coe g
  have hCH : M * M = M.trace • M - M.det • 1 := Work.L2F.Mat2.sq_eq_trace_smul_sub_det F M
  rw [hdet, one_smul] at hCH
  have h1 : Matrix.mulVec M (Matrix.mulVec M z) = (c * c) • z := by
    rw [h, Matrix.mulVec_smul, h, smul_smul]
  have h2 : Matrix.mulVec M (Matrix.mulVec M z) = (M.trace * c - 1) • z := by
    rw [Matrix.mulVec_mulVec, hCH, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, h,
      smul_smul, sub_smul, one_smul]
  have h3 : (c * c) • z = (M.trace * c - 1) • z := by rw [← h1, h2]
  have h4 : (c * c - (M.trace * c - 1)) • z = 0 := by rw [sub_smul, h3, sub_self]
  have h5 : c * c - (M.trace * c - 1) = 0 := by
    rcases smul_eq_zero.mp h4 with h | h
    · exact h
    · exact absurd h hz
  linear_combination h5

end Work.L2F.Props.oddsub
