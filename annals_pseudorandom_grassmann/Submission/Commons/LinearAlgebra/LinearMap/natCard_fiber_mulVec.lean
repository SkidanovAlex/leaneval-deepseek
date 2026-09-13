import Mathlib.Algebra.Field.ZMod
import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.RingTheory.PicardGroup

namespace Commons.LinearAlgebra.LinearMap

theorem natCard_fiber_mulVec {m n : ℕ} (X : Matrix (Fin n) (Fin m) (ZMod 2)) (u : Fin n → ZMod 2)
    (hu : u ∈ LinearMap.range (Matrix.mulVecLin X)) :
    Nat.card {b : Fin m → ZMod 2 // Matrix.mulVec X b = u} = 2 ^ (m - X.rank) := by
  obtain ⟨b₀, hb₀⟩ := LinearMap.mem_range.mp hu
  have hb₀' : Matrix.mulVec X b₀ = u := by rwa [Matrix.mulVecLin_apply] at hb₀
  -- The fiber is a coset of the kernel: b ↦ b - b₀ is a bijection onto the kernel.
  let e : {b : Fin m → ZMod 2 // Matrix.mulVec X b = u} ≃ LinearMap.ker (Matrix.mulVecLin X) :=
    { toFun := fun b => ⟨b.1 - b₀, by
        rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.mulVec_sub, b.2, hb₀', sub_self]⟩
      invFun := fun c => ⟨c.1 + b₀, by
        have hc : Matrix.mulVec X c.1 = 0 := by
          have := LinearMap.mem_ker.mp c.2
          rwa [Matrix.mulVecLin_apply] at this
        rw [Matrix.mulVec_add, hc, hb₀', zero_add]⟩
      left_inv := fun b => by ext; simp
      right_inv := fun c => by ext; simp }
  have hfin : Module.finrank (ZMod 2) ↥(LinearMap.ker (Matrix.mulVecLin X)) = m - X.rank := by
    have h := LinearMap.finrank_range_add_finrank_ker (Matrix.mulVecLin X)
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at h
    have hr : X.rank = Module.finrank (ZMod 2) (LinearMap.range (Matrix.mulVecLin X)) := rfl
    omega
  have hcard : Nat.card (ZMod 2) = 2 := by
    rw [Nat.card_eq_fintype_card]; exact ZMod.card 2
  rw [Nat.card_congr e,
    Module.natCard_eq_pow_finrank (K := ZMod 2) (V := ↥(LinearMap.ker (Matrix.mulVecLin X))),
    hfin, hcard]

end Commons.LinearAlgebra.LinearMap