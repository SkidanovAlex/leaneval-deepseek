import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit

namespace Commons.LinearAlgebra.Matrix

theorem rank_le_one_iff {K : Type*} [Field K] {m n : ℕ} (B : Matrix (Fin m) (Fin n) K) :
    B.rank ≤ 1 ↔ ∃ b : Fin m → K, ∃ φ : Fin n → K, B = Matrix.vecMulVec b φ := by
  constructor
  · intro h
    let S : Submodule K (Fin m → K) := LinearMap.range B.mulVecLin
    have hS : Module.finrank K S ≤ 1 := h
    obtain ⟨v, hv⟩ := (finrank_le_one_iff).mp hS
    have hmem : ∀ j : Fin n, B.col j ∈ S := by
      intro j
      show B.col j ∈ LinearMap.range B.mulVecLin
      rw [Matrix.range_mulVecLin]
      exact Submodule.subset_span ⟨j, rfl⟩
    let φ : Fin n → K := fun j => Classical.choose (hv ⟨B.col j, hmem j⟩)
    have hφ : ∀ j, φ j • (v : Fin m → K) = B.col j := by
      intro j
      exact congrArg Subtype.val (Classical.choose_spec (hv ⟨B.col j, hmem j⟩))
    refine ⟨(v : Fin m → K), φ, ?_⟩
    ext i j
    have h2 : (φ j • (v : Fin m → K)) i = B i j := congrFun (hφ j) i
    simp only [Matrix.vecMulVec_apply]
    rw [← h2, Pi.smul_apply, smul_eq_mul, mul_comm]
  · rintro ⟨b, φ, rfl⟩
    exact Matrix.rank_vecMulVec_le b φ

end Commons.LinearAlgebra.Matrix