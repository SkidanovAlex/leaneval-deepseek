import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit

namespace Commons.LinearAlgebra.Matrix

theorem rank_vecMulVec {K : Type*} [Field K] {m n : ℕ} (b : Fin m → K) (φ : Fin n → K)
    (h : (b = 0 ∨ φ = 0) = False) : (Matrix.vecMulVec b φ).rank = 1 := by
  have hb : b ≠ 0 := fun hb => h ▸ (Or.inl hb)
  have hφ : φ ≠ 0 := fun hφ => h ▸ (Or.inr hφ)
  obtain ⟨i₀, hi₀⟩ : ∃ i, b i ≠ 0 := by
    by_contra hc
    exact hb (funext fun i => by simpa using not_exists.mp hc i)
  obtain ⟨j₀, hj₀⟩ : ∃ j, φ j ≠ 0 := by
    by_contra hc
    exact hφ (funext fun j => by simpa using not_exists.mp hc j)
  refine le_antisymm (Matrix.rank_vecMulVec_le b φ) ?_
  rw [Matrix.rank, Submodule.one_le_finrank_iff]
  intro hbot
  have hx : Matrix.mulVecLin (Matrix.vecMulVec b φ) (Pi.single j₀ (1 : K)) ≠ 0 := by
    intro hz
    have hval := congr_fun hz i₀
    simp only [Matrix.mulVecLin_apply, Matrix.mulVec_single_one, Matrix.col_apply,
      Matrix.vecMulVec_apply, Pi.zero_apply] at hval
    exact mul_ne_zero hi₀ hj₀ hval
  refine hx ?_
  have hmem : Matrix.mulVecLin (Matrix.vecMulVec b φ) (Pi.single j₀ (1 : K))
      ∈ LinearMap.range (Matrix.mulVecLin (Matrix.vecMulVec b φ)) :=
    LinearMap.mem_range_self _ _
  rw [hbot] at hmem
  simpa using hmem

end Commons.LinearAlgebra.Matrix