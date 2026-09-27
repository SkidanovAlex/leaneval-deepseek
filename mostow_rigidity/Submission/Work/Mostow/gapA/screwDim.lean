/-
# Dimension of the normal space of the geodesic through two distinct boundary points

For `a ≠ b` in the boundary sphere `Sph 3`, `Nsub a b` is the subspace of the Minkowski space
`ℝ^{Fin 3 ⊕ Fin 1}` of vectors orthogonal to both null vectors `A = nullA a = (a,1)` and
`B = nullB b = (b,1)`.  Its dimension is `4 - 2 = 2`: the two linear functionals
`x ↦ ⟨x,A⟩` and `x ↦ ⟨x,B⟩` are linearly independent exactly because `a ≠ b`, and the ambient
space is 4-dimensional.

Concretely, `φ x = (⟨x,A⟩, ⟨x,B⟩) : ℝ × ℝ` is surjective (`x = (s/d)•A + (r/d)•B` maps to
`(r,s)`, where `d = ⟨A,B⟩ = ⟪a,b⟫ - 1 ≠ 0`), has `Nsub a b` as its kernel, and rank-nullity
gives `dim (Nsub a b) = finrank ℝ (Fin 3 ⊕ Fin 1 → ℝ) - 2 = 4 - 2 = 2`.
-/
import Mathlib
import Submission.Work.Mostow.gapA.screwDefs
import Submission.Work.Mostow.gapA.screwNorm

namespace Work.Mostow.gapA

open Submission.Mostow

noncomputable section

/-- The linear functional `x ↦ ⟨x,Y⟩` for the Minkowski form. -/
private def minkLin (Y : Fin 3 ⊕ Fin 1 → ℝ) : (Fin 3 ⊕ Fin 1 → ℝ) →ₗ[ℝ] ℝ where
  toFun x := Work.Mostow.mink x Y
  map_add' x y := sn_mink_add_left x y Y
  map_smul' c x := sn_mink_smul_left c x Y

@[simp] private lemma minkLin_apply (Y x : Fin 3 ⊕ Fin 1 → ℝ) :
    minkLin Y x = Work.Mostow.mink x Y := rfl

theorem screwDim {a b : Submission.Mostow.E 3} (ha : a ∈ Submission.Mostow.Sph 3) (hb : b ∈ Submission.Mostow.Sph 3) (hab : a ≠ b) :
    Module.finrank ℝ (Work.Mostow.gapA.Nsub a b) = 2 := by
  have hAA : Work.Mostow.mink (nullA a) (nullA a) = 0 := mink_nvec_self ha
  have hBB : Work.Mostow.mink (nullB b) (nullB b) = 0 := mink_nvec_self hb
  have hAB : Work.Mostow.mink (nullA a) (nullB b) = inner ℝ a b - 1 := mink_nvec_nvec a b
  have hBA : Work.Mostow.mink (nullB b) (nullA a) = inner ℝ a b - 1 := by
    rw [Work.Mostow.minkSeg_comm]; exact hAB
  have hne : inner ℝ a b - 1 ≠ 0 := by linarith [inner_lt_one ha hb hab]
  set φ : (Fin 3 ⊕ Fin 1 → ℝ) →ₗ[ℝ] (ℝ × ℝ) :=
    (minkLin (nullA a)).prod (minkLin (nullB b)) with hφ
  -- `Nsub a b` is the kernel of the pair of the two functionals
  have hker : Nsub a b = LinearMap.ker φ := by
    ext x
    rw [mem_Nsub, LinearMap.mem_ker, hφ, LinearMap.prod_apply, Prod.mk_eq_zero]
    simp
  have hφapply : ∀ x : Fin 3 ⊕ Fin 1 → ℝ,
      φ x = (Work.Mostow.mink x (nullA a), Work.Mostow.mink x (nullB b)) := by
    intro x
    rw [hφ, LinearMap.prod_apply]
    rfl
  -- and that pair of functionals is surjective
  have hsurj : Function.Surjective φ := by
    rintro ⟨r, s⟩
    refine ⟨(s / (inner ℝ a b - 1)) • nullA a + (r / (inner ℝ a b - 1)) • nullB b, ?_⟩
    have h1 : Work.Mostow.mink ((s / (inner ℝ a b - 1)) • nullA a
        + (r / (inner ℝ a b - 1)) • nullB b) (nullA a) = r := by
      rw [sn_mink_add_left, sn_mink_smul_left, sn_mink_smul_left, hAA, hBA]
      rw [mul_zero, zero_add, div_mul_cancel₀ r hne]
    have h2 : Work.Mostow.mink ((s / (inner ℝ a b - 1)) • nullA a
        + (r / (inner ℝ a b - 1)) • nullB b) (nullB b) = s := by
      rw [sn_mink_add_left, sn_mink_smul_left, sn_mink_smul_left, hBB, hAB]
      rw [mul_zero, add_zero, div_mul_cancel₀ s hne]
    rw [hφapply]
    exact Prod.ext h1 h2
  have hrange : Module.finrank ℝ (LinearMap.range φ) = 2 := by
    rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, Module.finrank_prod, Module.finrank_self]
  have hamb : Module.finrank ℝ (Fin 3 ⊕ Fin 1 → ℝ) = 4 := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin, Fintype.card_fin]
  have h := LinearMap.finrank_range_add_finrank_ker φ
  rw [hrange, hamb] at h
  rw [hker]
  omega

end

end Work.Mostow.gapA
