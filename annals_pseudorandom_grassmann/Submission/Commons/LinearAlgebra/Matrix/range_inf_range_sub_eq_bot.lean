import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit

namespace Commons.LinearAlgebra.Matrix

open Submodule Module

theorem range_inf_range_sub_eq_bot {m n : Type*} [Fintype m] [Fintype n] {K : Type*} [Field K]
    (X Y : Matrix m n K) (h : Y.rank = X.rank + (Y - X).rank) :
    LinearMap.range X.mulVecLin ⊓ LinearMap.range (Y - X).mulVecLin = ⊥ := by
  set A : Submodule K (m → K) := LinearMap.range X.mulVecLin with hA
  set B : Submodule K (m → K) := LinearMap.range (Y - X).mulVecLin with hB
  have hYX : Y.mulVecLin = X.mulVecLin + (Y - X).mulVecLin := by
    rw [← Matrix.mulVecLin_add]
    congr 1
    abel
  have hrange : LinearMap.range Y.mulVecLin ≤ A ⊔ B := by
    rw [hYX]
    exact LinearMap.range_add_le _ _
  have h1 : Y.rank ≤ finrank K ↑(A ⊔ B) := by
    rw [Matrix.rank]
    exact Submodule.finrank_mono hrange
  have h2 : finrank K ↑(A ⊔ B) ≤ X.rank + (Y - X).rank := by
    refine (Submodule.finrank_add_le_finrank_add_finrank A B).trans ?_
    rw [hA, hB]
    rfl
  have h3 : finrank K ↑(A ⊔ B) = X.rank + (Y - X).rank := le_antisymm h2 (h ▸ h1)
  have hA' : finrank K ↑A = X.rank := by rw [hA]; rfl
  have hB' : finrank K ↑B = (Y - X).rank := by rw [hB]; rfl
  have hfin : finrank K ↑(A ⊓ B) = 0 := by
    have hsup := Submodule.finrank_sup_add_finrank_inf_eq A B
    omega
  have hbot : A ⊓ B = ⊥ := Submodule.finrank_eq_zero.mp hfin
  simpa [hA, hB] using hbot

end Commons.LinearAlgebra.Matrix