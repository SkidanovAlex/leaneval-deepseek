import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.Matrix.ToLin

namespace Commons.LinearAlgebra.Matrix

/-- `Matrix.mulVecLin` agrees with `Matrix.toLin'` (both send `v` to `M *ᵥ v`). -/
private lemma mulVecLin_eq_toLin' {m n : ℕ} (M : Matrix (Fin m) (Fin n) (ZMod 2)) :
    M.mulVecLin = Matrix.toLin' M := by
  apply LinearMap.ext
  intro v
  simp [Matrix.toLin'_apply]

theorem exists_mul_invertible_of_range_eq {m n : ℕ} (A B : Matrix (Fin m) (Fin n) (ZMod 2))
    (hrange : LinearMap.range A.mulVecLin = LinearMap.range B.mulVecLin)
    (hA : LinearMap.ker A.mulVecLin = ⊥) (hB : LinearMap.ker B.mulVecLin = ⊥) :
    ∃ S : Matrix (Fin n) (Fin n) (ZMod 2), Function.Bijective S.mulVecLin ∧ B = A * S := by
  have hf_inj : Function.Injective A.mulVecLin := LinearMap.ker_eq_bot.mp hA
  have hg_inj : Function.Injective B.mulVecLin := LinearMap.ker_eq_bot.mp hB
  -- The map `gU : V → A.range` induced by `B`.
  let gU : (Fin n → ZMod 2) →ₗ[ZMod 2] ↥(A.mulVecLin).range :=
    (B.mulVecLin).codRestrict (A.mulVecLin).range (fun v => by
      rw [hrange]; exact LinearMap.mem_range.mpr ⟨v, rfl⟩)
  have hgU_bij : Function.Bijective gU := by
    refine ⟨?_, ?_⟩
    · intro v w hvw
      exact hg_inj (Subtype.ext_iff.mp hvw)
    · intro u
      have hu : (u : Fin m → ZMod 2) ∈ (B.mulVecLin).range := by
        rw [← hrange]; exact u.2
      obtain ⟨v, hv⟩ := LinearMap.mem_range.mp hu
      exact ⟨v, Subtype.ext hv⟩
  -- The linear equivalence `V ≃ A.range` induced by `A` (injective).
  have hRA_bij : Function.Bijective (A.mulVecLin).rangeRestrict :=
    ⟨(LinearMap.injective_rangeRestrict_iff A.mulVecLin).mpr hf_inj,
      LinearMap.surjective_rangeRestrict A.mulVecLin⟩
  let eA : (Fin n → ZMod 2) ≃ₗ[ZMod 2] ↥(A.mulVecLin).range :=
    LinearEquiv.ofBijective (A.mulVecLin).rangeRestrict hRA_bij
  let eB : (Fin n → ZMod 2) ≃ₗ[ZMod 2] ↥(A.mulVecLin).range :=
    LinearEquiv.ofBijective gU hgU_bij
  let φ : (Fin n → ZMod 2) ≃ₗ[ZMod 2] (Fin n → ZMod 2) := eB.trans eA.symm
  have hA_apply : ∀ x : Fin n → ZMod 2, (eA x : Fin m → ZMod 2) = A.mulVecLin x := by
    intro x
    simp [eA]
  have hB_apply : ∀ x : Fin n → ZMod 2, (eB x : Fin m → ZMod 2) = B.mulVecLin x := by
    intro x
    simp [eB, gU]
  have hφ_apply : ∀ x : Fin n → ZMod 2, φ x = eA.symm (eB x) := by
    intro x
    simp [φ, LinearEquiv.trans_apply]
  -- Key identity: `A ∘ φ = B`.
  have hkey : (A.mulVecLin).comp φ.toLinearMap = B.mulVecLin := by
    apply LinearMap.ext
    intro v
    change A.mulVecLin (φ v) = B.mulVecLin v
    rw [hφ_apply v, ← hA_apply (eA.symm (eB v)), ← hB_apply v]
    exact congrArg Subtype.val (LinearEquiv.apply_symm_apply eA (eB v))
  refine ⟨LinearMap.toMatrix' φ.toLinearMap, ?_, ?_⟩
  · rw [mulVecLin_eq_toLin', Matrix.toLin'_toMatrix']
    simpa using LinearEquiv.bijective φ
  · have hmat : Matrix.toLin' (A * LinearMap.toMatrix' φ.toLinearMap) = Matrix.toLin' B := by
      rw [Matrix.toLin'_mul, Matrix.toLin'_toMatrix', ← mulVecLin_eq_toLin' A, ← mulVecLin_eq_toLin' B]
      exact hkey
    exact (Matrix.toLin'.injective hmat).symm

end Commons.LinearAlgebra.Matrix