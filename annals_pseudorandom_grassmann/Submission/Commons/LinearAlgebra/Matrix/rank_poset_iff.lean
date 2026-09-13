import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.TotallySplit
import Submission.Commons.LinearAlgebra.Submodule.finrank_map_mkQ_of_le
import Submission.Commons.LinearAlgebra.Matrix.rank_add_le

namespace Commons.LinearAlgebra.Matrix

open Module

/-- If `ker f ≤ ker g` then the rank of `g` is at most the rank of `f`:
the kernel of `g` is larger, hence its range is smaller. -/
theorem finrank_range_le_of_ker_le {K M N N' : Type*} [Field K]
    [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N] [AddCommGroup N'] [Module K N']
    [FiniteDimensional K M] (f : M →ₗ[K] N) (g : M →ₗ[K] N')
    (h : LinearMap.ker f ≤ LinearMap.ker g) :
    Module.finrank K (LinearMap.range g) ≤ Module.finrank K (LinearMap.range f) := by
  have hf := LinearMap.finrank_range_add_finrank_ker f
  have hg := LinearMap.finrank_range_add_finrank_ker g
  have hk : Module.finrank K (LinearMap.ker f) ≤ Module.finrank K (LinearMap.ker g) :=
    Submodule.finrank_mono h
  omega

theorem rank_poset_iff {m n : Type*} [Fintype m] [Fintype n] {K : Type*} [Field K]
    (X Y : Matrix m n K) :
    (Y.rank = X.rank + (Y - X).rank) ↔
      (LinearMap.range X.mulVecLin ≤ LinearMap.range Y.mulVecLin ∧
        ∀ w, Y.mulVec w ∈ LinearMap.range X.mulVecLin → X.mulVec w = Y.mulVec w) := by
  constructor
  · intro h
    let A : Submodule K (m → K) := LinearMap.range X.mulVecLin
    let B : Submodule K (m → K) := LinearMap.range (Y - X).mulVecLin
    have hsum : Y.mulVecLin = X.mulVecLin + (Y - X).mulVecLin := by
      ext w
      simp only [LinearMap.add_apply, Matrix.mulVecLin_apply, Matrix.sub_mulVec]
      rw [add_sub_cancel]
    have hsub : (Y - X).mulVecLin = Y.mulVecLin - X.mulVecLin := by
      ext w
      simp only [LinearMap.sub_apply, Matrix.mulVecLin_apply, Matrix.sub_mulVec]
    have hle : LinearMap.range Y.mulVecLin ≤ A ⊔ B := by
      rw [hsum]
      exact LinearMap.range_add_le _ _
    have hfinRY_le : Module.finrank K (LinearMap.range Y.mulVecLin) ≤
        Module.finrank K ↑(A ⊔ B) := Submodule.finrank_mono hle
    have hfin_sup_le : Module.finrank K ↑(A ⊔ B) ≤ Module.finrank K A + Module.finrank K B :=
      Submodule.finrank_add_le_finrank_add_finrank A B
    have hh : Module.finrank K (LinearMap.range Y.mulVecLin) =
        Module.finrank K A + Module.finrank K B := h
    have hsup : Module.finrank K ↑(A ⊔ B) = Module.finrank K A + Module.finrank K B :=
      le_antisymm hfin_sup_le (hh ▸ hfinRY_le)
    have hRY_eq : LinearMap.range Y.mulVecLin = A ⊔ B := by
      apply Submodule.eq_of_le_of_finrank_eq hle
      rw [hsup, ← hh]
    have hinf : A ⊓ B = ⊥ := by
      have hsd := Submodule.finrank_sup_add_finrank_inf_eq A B
      have h0 : Module.finrank K ↑(A ⊓ B) = 0 := by omega
      exact Submodule.finrank_eq_zero.mp h0
    refine ⟨?_, ?_⟩
    · rw [hRY_eq]
      exact le_sup_left
    · intro w hw
      have hzm : (Y - X).mulVecLin w ∈ B := LinearMap.mem_range_self _ w
      have hxA : X.mulVecLin w ∈ A := LinearMap.mem_range_self _ w
      have hYA : Y.mulVecLin w ∈ A := hw
      have hzA : (Y - X).mulVecLin w ∈ A := by
        rw [hsub, LinearMap.sub_apply]
        exact A.sub_mem hYA hxA
      have hz0 : (Y - X).mulVecLin w = 0 := by
        have hmem : (Y - X).mulVecLin w ∈ (A ⊓ B) := Submodule.mem_inf.mpr ⟨hzA, hzm⟩
        rw [hinf] at hmem
        simpa using hmem
      have h1 : Y.mulVecLin w = X.mulVecLin w := by
        have h1' : Y.mulVecLin w = X.mulVecLin w + (Y - X).mulVecLin w := by
          rw [hsum]; rfl
        rw [hz0, add_zero] at h1'
        exact h1'
      exact h1.symm
  · rintro ⟨hA, h2⟩
    let A : Submodule K (m → K) := LinearMap.range X.mulVecLin
    let ψ : (n → K) →ₗ[K] ((m → K) ⧸ A) := A.mkQ.comp Y.mulVecLin
    have hsub : (Y - X).mulVecLin = Y.mulVecLin - X.mulVecLin := by
      ext w
      simp only [LinearMap.sub_apply, Matrix.mulVecLin_apply, Matrix.sub_mulVec]
    have hker : LinearMap.ker ψ ≤ LinearMap.ker (Y - X).mulVecLin := by
      intro w hw
      rw [LinearMap.mem_ker] at hw ⊢
      have hmem : Y.mulVecLin w ∈ A := by
        have h0 : A.mkQ (Y.mulVecLin w) = 0 := by
          simpa only [ψ, LinearMap.comp_apply] using hw
        rwa [← LinearMap.mem_ker, Submodule.ker_mkQ] at h0
      have hXY : X.mulVecLin w = Y.mulVecLin w := h2 w hmem
      rw [hsub, LinearMap.sub_apply, hXY, sub_self]
    have hrangeψ : LinearMap.range ψ = Submodule.map A.mkQ (LinearMap.range Y.mulVecLin) := by
      show LinearMap.range (A.mkQ.comp Y.mulVecLin) = _
      rw [LinearMap.range_comp]
    have hfinψ : Module.finrank K (LinearMap.range ψ) =
        Module.finrank K (LinearMap.range Y.mulVecLin) - Module.finrank K A := by
      rw [hrangeψ]
      exact Commons.LinearAlgebra.Submodule.finrank_map_mkQ_of_le A
        (LinearMap.range Y.mulVecLin) hA
    have hle : Module.finrank K (LinearMap.range (Y - X).mulVecLin) ≤
        Module.finrank K (LinearMap.range ψ) :=
      finrank_range_le_of_ker_le ψ (Y - X).mulVecLin hker
    have hZY : (Y - X).rank ≤ Y.rank - X.rank := by
      calc (Y - X).rank
          = Module.finrank K (LinearMap.range (Y - X).mulVecLin) := rfl
        _ ≤ Module.finrank K (LinearMap.range ψ) := hle
        _ = Module.finrank K (LinearMap.range Y.mulVecLin) - Module.finrank K A := hfinψ
        _ = Y.rank - X.rank := rfl
    have hYX : X.rank ≤ Y.rank := by
      have h' : Module.finrank K (LinearMap.range X.mulVecLin) ≤
          Module.finrank K (LinearMap.range Y.mulVecLin) := Submodule.finrank_mono hA
      exact h'
    have hYle : Y.rank ≤ X.rank + (Y - X).rank := by
      have h' := rank_add_le X (Y - X)
      rwa [add_sub_cancel] at h'
    omega

end Commons.LinearAlgebra.Matrix