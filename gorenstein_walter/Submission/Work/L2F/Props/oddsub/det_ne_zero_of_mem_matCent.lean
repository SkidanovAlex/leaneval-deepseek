import Mathlib
import Submission.Work.L2F.Props.oddsub.NoUnipotentDefs

/-!
# A nonzero matrix commuting with a subgroup of `SL(2,F)` without common eigenvector is
invertible

Let `A ≤ SL(2,F)` be a subgroup with no common eigenvector in `F²` and let `M ∈ M₂(F)` commute
with every element of `A`.  If `M ≠ 0` then `det M ≠ 0`.

The proof is the standard one: if `det M = 0` and `M ≠ 0`, then the range of the linear map
`v ↦ M *ᵥ v` is a nonzero proper subspace of `F²`, hence a line; it is stable under `A`
because `M` commutes with `A`; and `A` acts on a stable line by scalars, which produces a common
eigenvector, contradicting the hypothesis.
-/

open scoped MatrixGroups
open Matrix

namespace Work.L2F.Props.oddsub

variable {F : Type*} [Field F]
variable {A : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)}
variable {M : Matrix (Fin 2) (Fin 2) F}

/-- The range of `v ↦ M *ᵥ v` is stable under every element of `A` when `M` commutes with `A`. -/
theorem smul_mem_range_mulVecLin_of_mem_matCent (hM : MatCent A M)
    {a : Matrix.SpecialLinearGroup (Fin 2) F} (ha : a ∈ A) {w : Fin 2 → F}
    (hw : w ∈ LinearMap.range M.mulVecLin) :
    (a : Matrix (Fin 2) (Fin 2) F) *ᵥ w ∈ LinearMap.range M.mulVecLin := by
  obtain ⟨v, hv⟩ := hw
  refine ⟨(a : Matrix (Fin 2) (Fin 2) F) *ᵥ v, ?_⟩
  rw [← hv]
  simp only [Matrix.mulVecLin_apply]
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hM a ha]

/-- The range of `v ↦ M *ᵥ v` is nonzero when `M ≠ 0`. -/
theorem range_mulVecLin_ne_bot_of_ne_zero (h : M ≠ 0) :
    LinearMap.range M.mulVecLin ≠ ⊥ := by
  intro hbot
  apply h
  have h0 : M.mulVecLin = 0 := LinearMap.range_eq_bot.mp hbot
  ext i j
  have h1 : M.mulVecLin (Pi.single j (1 : F)) = 0 := by rw [h0]; rfl
  rw [Matrix.mulVecLin_apply, Matrix.mulVec_single_one] at h1
  have h2 : M.col j i = 0 := congrFun h1 i
  simpa using h2

/-- The determinant of `M` vanishes exactly when the range of `v ↦ M *ᵥ v` is a proper
subspace of `F²`. -/
theorem range_mulVecLin_ne_top_of_det_eq_zero (h : M.det = 0) :
    LinearMap.range M.mulVecLin ≠ ⊤ := by
  have hdetf : LinearMap.det M.mulVecLin = 0 := by
    rw [← Matrix.toLin'_apply', LinearMap.det_toLin']
    exact h
  exact ne_of_lt (LinearMap.range_lt_top_of_det_eq_zero hdetf)

theorem det_ne_zero_of_mem_matCent (F : Type*) [Field F]
    (A : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F))
    (hirr : ¬ Work.L2F.Props.oddsub.HasCommonEigenvector A)
    {M : Matrix (Fin 2) (Fin 2) F} (hM : Work.L2F.Props.oddsub.MatCent A M) (hM0 : M ≠ 0) :
    M.det ≠ 0 := by
  intro hdet
  apply hirr
  have htop : LinearMap.range M.mulVecLin ≠ ⊤ := range_mulVecLin_ne_top_of_det_eq_zero hdet
  have hbot : LinearMap.range M.mulVecLin ≠ ⊥ := range_mulVecLin_ne_bot_of_ne_zero hM0
  obtain ⟨u, hu, hu0⟩ := (Submodule.ne_bot_iff _).mp hbot
  refine ⟨u, hu0, ?_⟩
  intro a ha
  have hmem : (a : Matrix (Fin 2) (Fin 2) F) *ᵥ u ∈ LinearMap.range M.mulVecLin :=
    smul_mem_range_mulVecLin_of_mem_matCent hM ha hu
  obtain ⟨c, hc⟩ := eq_smul_of_mem_of_ne_top hu hu0 htop _ hmem
  exact ⟨c, hc.symm⟩

end Work.L2F.Props.oddsub
