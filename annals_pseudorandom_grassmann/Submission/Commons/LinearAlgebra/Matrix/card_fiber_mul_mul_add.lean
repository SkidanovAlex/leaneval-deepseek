import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.LinearAlgebra.Matrix.Bilinear
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.RingTheory.TotallySplit

open Matrix

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Commons.LinearAlgebra.Matrix

/-- **Cardinality of the fibres of `A ↦ ι * A * Q`.**

For matrices `Q : Matrix (Fin n') (Fin n) 𝔽₂` with `Q.mulVecLin` injective (i.e. the columns of
`Q` are linearly independent, `n ≤ n'`) and `ι : Matrix (Fin m) (Fin m') 𝔽₂` with `ι.mulVecLin`
surjective (i.e. the rows of `ι` span, `m ≤ m'`), the affine equation
`ι * A * Q + T = B` in the unknown `A : Matrix (Fin m') (Fin n') 𝔽₂` always has a solution, and
the solution set is a coset of the kernel of the linear map `A ↦ ι * A * Q`, of dimension
`m' * n' - m * n` over `𝔽₂`.  Hence its cardinality is `2 ^ (m' * n' - m * n)`.

The map `A ↦ ι * A * Q` is surjective: choosing a right inverse `P` of `ι` (`ι * P = 1`) and a
left inverse `S` of `Q` (`S * Q = 1`), the matrix `P * C * S` maps to `C`.  Rank–nullity then
gives the dimension of the kernel. -/
theorem card_fiber_mul_mul_add {m n m' n' : ℕ} (Q : Matrix (Fin n') (Fin n) (ZMod 2))
    (ι : Matrix (Fin m) (Fin m') (ZMod 2))
    (hQ : Function.Injective Q.mulVecLin) (hι : Function.Surjective ι.mulVecLin)
    (T : Matrix (Fin m) (Fin n) (ZMod 2)) (B : Matrix (Fin m) (Fin n) (ZMod 2)) :
    Nat.card {A : Matrix (Fin m') (Fin n') (ZMod 2) // ι * A * Q + T = B} =
      2 ^ (m' * n' - m * n) := by
  classical
  -- The linear map `φ A = ι * A * Q`.
  let φ : Matrix (Fin m') (Fin n') (ZMod 2) →ₗ[ZMod 2] Matrix (Fin m) (Fin n) (ZMod 2) :=
    (mulLeftLinearMap (Fin n) (ZMod 2) ι).comp (mulRightLinearMap (Fin m') (ZMod 2) Q)
  have hφ : ∀ A, φ A = ι * A * Q := by
    intro A
    simp only [φ, LinearMap.comp_apply, mulLeftLinearMap_apply, mulRightLinearMap_apply,
      Matrix.mul_assoc]
  -- `φ` is surjective: take a right inverse of `ι` and a left inverse of `Q`.
  have hsurj : Function.Surjective φ := by
    intro C
    have hkerQ : LinearMap.ker Q.mulVecLin = ⊥ := LinearMap.ker_eq_bot.mpr hQ
    obtain ⟨g', hg'⟩ := LinearMap.exists_leftInverse_of_injective Q.mulVecLin hkerQ
    have hS : (LinearMap.toMatrix' g') * Q = 1 := by
      apply Matrix.toLin'.injective
      rw [Matrix.toLin'_mul, Matrix.toLin'_toMatrix', Matrix.toLin'_one]
      exact hg'
    have hrangeι : LinearMap.range ι.mulVecLin = ⊤ := LinearMap.range_eq_top.mpr hι
    obtain ⟨g, hg⟩ := LinearMap.exists_rightInverse_of_surjective ι.mulVecLin hrangeι
    have hP : ι * (LinearMap.toMatrix' g) = 1 := by
      apply Matrix.toLin'.injective
      rw [Matrix.toLin'_mul, Matrix.toLin'_toMatrix', Matrix.toLin'_one]
      exact hg
    refine ⟨(LinearMap.toMatrix' g) * C * (LinearMap.toMatrix' g'), ?_⟩
    rw [hφ]
    calc ι * ((LinearMap.toMatrix' g) * C * (LinearMap.toMatrix' g')) * Q
        = (ι * (LinearMap.toMatrix' g)) * C * ((LinearMap.toMatrix' g') * Q) := by
          simp only [Matrix.mul_assoc]
      _ = C := by rw [hP, hS, Matrix.one_mul, Matrix.mul_one]
  -- A particular solution `A₀` of `ι * A * Q = B - T`.
  let A₀ : Matrix (Fin m') (Fin n') (ZMod 2) := (hsurj (B - T)).choose
  have hA₀ : φ A₀ = B - T := (hsurj (B - T)).choose_spec
  have hA₀'' : ι * A₀ * Q = B - T := (hφ A₀).symm.trans hA₀
  -- The fibre is a coset of the kernel: `A ↦ A - A₀` is a bijection onto `ker φ`.
  let e : {A : Matrix (Fin m') (Fin n') (ZMod 2) // ι * A * Q + T = B} ≃ ↥(LinearMap.ker φ) :=
    { toFun := fun A => ⟨A.1 - A₀, by
        rw [LinearMap.mem_ker, map_sub, hφ A.1, hφ A₀]
        have hA : ι * A.1 * Q = B - T := (eq_sub_iff_add_eq).mpr A.2
        rw [hA, hA₀'', sub_self]⟩
      invFun := fun c => ⟨c.1 + A₀, by
        have hc : φ c.1 = 0 := LinearMap.mem_ker.mp c.2
        have hs : φ (c.1 + A₀) = B - T := by rw [map_add, hc, hA₀, zero_add]
        rw [hφ (c.1 + A₀)] at hs
        exact (eq_sub_iff_add_eq).mp hs⟩
      left_inv := fun A => by apply Subtype.ext; simp [sub_add_cancel]
      right_inv := fun c => by apply Subtype.ext; simp [add_sub_cancel_right] }
  -- Dimensions.
  have hfin1 : Module.finrank (ZMod 2) (Matrix (Fin m') (Fin n') (ZMod 2)) = m' * n' := by
    rw [Module.finrank_matrix, Fintype.card_fin, Fintype.card_fin, Module.finrank_self, mul_one]
  have hfin2 : Module.finrank (ZMod 2) (Matrix (Fin m) (Fin n) (ZMod 2)) = m * n := by
    rw [Module.finrank_matrix, Fintype.card_fin, Fintype.card_fin, Module.finrank_self, mul_one]
  have hker : Module.finrank (ZMod 2) ↥(LinearMap.ker φ) = m' * n' - m * n := by
    have hrn := LinearMap.finrank_range_add_finrank_ker φ
    rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, hfin2, hfin1] at hrn
    omega
  have hcard : Nat.card (ZMod 2) = 2 := by
    rw [Nat.card_eq_fintype_card]; exact ZMod.card 2
  rw [Nat.card_congr e,
    Module.natCard_eq_pow_finrank (K := ZMod 2) (V := ↥(LinearMap.ker φ)),
    hcard, hker]

end Commons.LinearAlgebra.Matrix