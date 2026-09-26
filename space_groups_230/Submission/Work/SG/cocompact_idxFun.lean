import Mathlib
import Submission.Work.SG.realize_defs

/-!
# Three independent translations in the realised group

`idxFun M P τ horth` is the (junk-valued off `P`) index function
`(A, n) ↦ (x ↦ M A M⁻¹ x + M (τ A + n))` of `Submission/Work/SG/realize_defs.lean`.

Because `1 ∈ P` and `oConj M 1 = 1`, the elements indexed by `A = 1` are honest translations
`x ↦ x + M (τ 1 + n)`, and since `τ 1 = n₀` they realise the whole lattice `M ℤ³`: for the
standard basis `eᵢ ∈ ℤ³` the index `n = eᵢ − n₀` gives the translation by `M eᵢ`.

As `M` is invertible (`M.det ≠ 0`) and the `eᵢ` are linearly independent, the images `M eᵢ`
are linearly independent.  This is precisely the "contains three linearly independent
translations" half of `IsCrystallographicGroup` needed to see that the realised group is
cocompact.
-/

namespace Work.SG

open LeanEval.Geometry.SpaceGroupsProblem
open Matrix

lemma idxFun_intVec_sub (a b : Fin 3 → ℤ) : intVec (a - b) = intVec a - intVec b := by
  funext i; simp [intVec]

lemma idxFun_intVec_single_one (i : Fin 3) :
    intVec (Pi.single i (1 : ℤ)) = (Pi.single i (1 : ℝ) : Fin 3 → ℝ) := by
  funext j; simp [intVec, Pi.single_apply]

theorem cocompact_idxFun (M : Work.SG.RMat) (hM : M.det ≠ 0) (P : Set Work.SG.IMat)
    (h1 : (1 : Work.SG.IMat) ∈ P) (τ : Work.SG.IMat → Fin 3 → ℝ)
    (horth : ∀ A ∈ P, Matrix.transpose (Work.SG.oConj M A) * (Work.SG.oConj M A) = 1)
    (n₀ : Fin 3 → ℤ) (hn₀ : τ 1 = Work.SG.intVec n₀) :
    ∃ v : Fin 3 → LeanEval.Geometry.SpaceGroupsProblem.E 3,
      LinearIndependent ℝ v ∧ ∀ i, ∃ g : LeanEval.Geometry.SpaceGroupsProblem.EuclideanIsom 3,
        (∃ j : Work.SG.IMat × (Fin 3 → ℤ), Work.SG.idxFun M P τ horth j = g) ∧
          LeanEval.Geometry.SpaceGroupsProblem.IsTranslationBy g (v i) := by
  have hu : IsUnit M.det := isUnit_iff_ne_zero.mpr hM
  have hMM : M * M⁻¹ = 1 := Matrix.mul_nonsing_inv M hu
  have hc1 : oConj M 1 = 1 := by rw [oConj, realMat_one, mul_one]; exact hMM
  refine ⟨fun i => WithLp.toLp 2 (M *ᵥ intVec (Pi.single i (1 : ℤ))), ?_, ?_⟩
  · -- the three translation vectors are linearly independent
    have hker1 : ((WithLp.linearEquiv 2 ℝ (Fin 3 → ℝ)).symm :
        (Fin 3 → ℝ) ≃ₗ[ℝ] E 3).toLinearMap.ker = ⊥ := by
      rw [LinearMap.ker_eq_bot]
      exact (WithLp.linearEquiv 2 ℝ (Fin 3 → ℝ)).symm.injective
    have step1 : LinearIndependent ℝ
        (fun i : Fin 3 => WithLp.toLp 2 ((Pi.basisFun ℝ (Fin 3)) i)) := by
      have h := LinearIndependent.map' (Pi.basisFun ℝ (Fin 3)).linearIndependent
        ((WithLp.linearEquiv 2 ℝ (Fin 3 → ℝ)).symm : (Fin 3 → ℝ) ≃ₗ[ℝ] E 3).toLinearMap hker1
      simpa [Function.comp_def, WithLp.coe_symm_linearEquiv, LinearEquiv.coe_toLinearMap] using h
    have hker2 : ((LinearEquiv.ofBijective (Matrix.toEuclideanLin M)
        (toEuclideanLin_bijective_of_det_ne_zero hM)) : E 3 ≃ₗ[ℝ] E 3).toLinearMap.ker = ⊥ := by
      rw [LinearMap.ker_eq_bot]
      exact (LinearEquiv.ofBijective (Matrix.toEuclideanLin M)
        (toEuclideanLin_bijective_of_det_ne_zero hM)).injective
    have step2 : LinearIndependent ℝ
        (fun i : Fin 3 => WithLp.toLp 2 (M *ᵥ ((Pi.basisFun ℝ (Fin 3)) i))) := by
      have h := LinearIndependent.map' step1
        ((LinearEquiv.ofBijective (Matrix.toEuclideanLin M)
          (toEuclideanLin_bijective_of_det_ne_zero hM)) : E 3 ≃ₗ[ℝ] E 3).toLinearMap hker2
      simpa [Function.comp_def, LinearEquiv.coe_toLinearMap, Matrix.toLpLin_apply] using h
    have hfin : (fun i : Fin 3 => WithLp.toLp 2 (M *ᵥ ((Pi.basisFun ℝ (Fin 3)) i)))
        = (fun i : Fin 3 => WithLp.toLp 2 (M *ᵥ intVec (Pi.single i (1 : ℤ)))) := by
      funext i
      rw [Pi.basisFun_apply, idxFun_intVec_single_one i]
    rwa [hfin] at step2
  · -- each standard basis vector is realised by a translation of the group
    intro i
    -- `k` is the index whose translation is `M (τ 1 + k) = M eᵢ`, namely `k = eᵢ - n₀`
    set k : Fin 3 → ℤ := Pi.single i (1 : ℤ) - n₀ with hk
    refine ⟨idxFun M P τ horth (1, k), ⟨(1, k), rfl⟩, ?_⟩
    intro x
    have harg : τ 1 + intVec k = intVec (Pi.single i (1 : ℤ)) := by
      rw [hk, hn₀, idxFun_intVec_sub]
      funext j
      simp only [Pi.add_apply, Pi.sub_apply, intVec]
      ring
    have hidx := idxFun_apply (M := M) (P := P) (τ := τ) (horth := horth) (A := (1 : IMat))
      (hA := h1) (n := k) (x := x)
    rw [hidx, hc1, Matrix.one_mulVec, WithLp.toLp_ofLp, harg]

end Work.SG
