import Mathlib.LinearAlgebra.Matrix.ToLin

open _root_.Matrix

namespace Commons.LinearAlgebra.Matrix

/-- Two injective matrices with the same range: the one with more columns is a right multiple of
the other by a surjective matrix. -/
theorem exists_mul_of_range_eq_inj {K : Type*} [Field K] {m n c : ℕ}
    (A : Matrix (Fin m) (Fin n) K) (B : Matrix (Fin m) (Fin c) K)
    (hrange : LinearMap.range A.mulVecLin = LinearMap.range B.mulVecLin)
    (hA : LinearMap.ker A.mulVecLin = ⊥) (hB : LinearMap.ker B.mulVecLin = ⊥) :
    ∃ S : Matrix (Fin n) (Fin c) K, Function.Surjective S.mulVecLin ∧ B = A * S := by
  -- The linear equivalence from `(Fin n → K)` onto the common range, inverse to `A.mulVecLin`.
  let eA : (Fin n → K) ≃ₗ[K] LinearMap.range A.mulVecLin :=
    LinearEquiv.ofInjective A.mulVecLin (LinearMap.ker_eq_bot.mp hA)
  -- The map `y ↦ ⟨B y, _⟩` from `(Fin c → K)` into the range of `A`.
  let fB : (Fin c → K) →ₗ[K] LinearMap.range A.mulVecLin :=
    B.mulVecLin.codRestrict _ (fun y => by rw [hrange]; exact ⟨y, rfl⟩)
  -- The composite inverse `T`.
  let T : (Fin c → K) →ₗ[K] (Fin n → K) := (eA.symm : _ →ₗ[K] _).comp fB
  have hvalB : ∀ y, ((fB y : LinearMap.range A.mulVecLin) : Fin m → K) = B.mulVecLin y :=
    fun _ => rfl
  -- `T` is a right inverse of `A.mulVecLin` on the range of `B`.
  have key : ∀ y, A.mulVecLin (T y) = B.mulVecLin y := by
    intro y
    change A.mulVecLin (eA.symm (fB y)) = B.mulVecLin y
    rw [LinearEquiv.ofInjective_symm_apply]
    exact hvalB y
  -- `fB` is surjective since it has the same range as `B`.
  have hfB_surj : Function.Surjective fB := by
    intro z
    have hz : (z : Fin m → K) ∈ LinearMap.range B.mulVecLin := hrange ▸ z.2
    obtain ⟨y, hy⟩ := hz
    exact ⟨y, Subtype.ext (by rw [hvalB]; exact hy)⟩
  have hT : Function.Surjective T := (eA.symm.surjective).comp hfB_surj
  refine ⟨LinearMap.toMatrix' T, ?_, ?_⟩
  · intro y
    obtain ⟨x, hx⟩ := hT y
    exact ⟨x, by rw [Matrix.mulVecLin_apply, LinearMap.toMatrix'_mulVec, hx]⟩
  · have hS : (LinearMap.toMatrix' T).mulVecLin = T :=
      LinearMap.ext (fun y => by rw [Matrix.mulVecLin_apply, LinearMap.toMatrix'_mulVec])
    have hkey : A.mulVecLin.comp T = B.mulVecLin := LinearMap.ext key
    have hmap : B.mulVecLin = (A * LinearMap.toMatrix' T).mulVecLin := by
      rw [Matrix.mulVecLin_mul, hS]
      exact hkey.symm
    have htoB : LinearMap.toMatrix' B.mulVecLin = B := by
      rw [← Matrix.toLin'_apply', LinearMap.toMatrix'_toLin']
    have htoAS : LinearMap.toMatrix' (A * LinearMap.toMatrix' T).mulVecLin
        = A * LinearMap.toMatrix' T := by
      rw [← Matrix.toLin'_apply', LinearMap.toMatrix'_toLin']
    have := congrArg LinearMap.toMatrix' hmap
    rw [htoB, htoAS] at this
    exact this

end Commons.LinearAlgebra.Matrix