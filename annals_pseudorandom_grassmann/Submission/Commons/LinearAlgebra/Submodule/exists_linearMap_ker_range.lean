import Mathlib.Algebra.Algebra.ZMod
import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit

namespace Commons.LinearAlgebra.Submodule

/-- The linear map attached to `LinearMap.toMatrix' f` by `Matrix.mulVecLin` is `f` itself. -/
lemma mulVecLin_toMatrix' {R : Type*} [CommSemiring R] {n m : Type*} [DecidableEq n] [Fintype n]
    (f : (n → R) →ₗ[R] (m → R)) : (LinearMap.toMatrix' f).mulVecLin = f := by
  rw [← Matrix.toLin'_apply' (LinearMap.toMatrix' f), Matrix.toLin'_toMatrix']

theorem exists_linearMap_ker_range (n : ℕ) (V₁ : Submodule (ZMod 2) (Fin n → ZMod 2)) :
    (∃ (n' : ℕ) (Q : Matrix (Fin n') (Fin n) (ZMod 2)),
      LinearMap.ker Q.mulVecLin = V₁ ∧ LinearMap.range Q.mulVecLin = ⊤) ∧
    (∃ (m' : ℕ) (ι : Matrix (Fin n) (Fin m') (ZMod 2)),
      LinearMap.range ι.mulVecLin = V₁ ∧ LinearMap.ker ι.mulVecLin = ⊥) := by
  constructor
  · -- Part 1: the quotient projection `W / V₁ ≅ k^{n'}`, read as a matrix.
    let b : Module.Basis (Fin (Module.finrank (ZMod 2) ((Fin n → ZMod 2) ⧸ V₁))) (ZMod 2)
        ((Fin n → ZMod 2) ⧸ V₁) := Module.finBasis (ZMod 2) ((Fin n → ZMod 2) ⧸ V₁)
    let e : (Fin (Module.finrank (ZMod 2) ((Fin n → ZMod 2) ⧸ V₁)) → ZMod 2) ≃ₗ[ZMod 2]
        ((Fin n → ZMod 2) ⧸ V₁) := b.equivFun.symm
    let f : (Fin n → ZMod 2) →ₗ[ZMod 2]
        (Fin (Module.finrank (ZMod 2) ((Fin n → ZMod 2) ⧸ V₁)) → ZMod 2) :=
      e.symm.toLinearMap.comp (Submodule.mkQ V₁)
    refine ⟨Module.finrank (ZMod 2) ((Fin n → ZMod 2) ⧸ V₁), LinearMap.toMatrix' f, ?_, ?_⟩
    · rw [mulVecLin_toMatrix']
      rw [LinearMap.ker_comp_of_ker_eq_bot (Submodule.mkQ V₁) (by
        rw [LinearMap.ker_eq_bot]; exact e.symm.injective)]
      exact Submodule.ker_mkQ V₁
    · rw [mulVecLin_toMatrix']
      rw [LinearMap.range_comp_of_range_eq_top (e.symm.toLinearMap) (Submodule.range_mkQ V₁)]
      exact LinearMap.range_eq_top.mpr e.symm.surjective
  · -- Part 2: the inclusion of a basis of `V₁`, read as a matrix.
    let b : Module.Basis (Fin (Module.finrank (ZMod 2) V₁)) (ZMod 2) V₁ :=
      Module.finBasis (ZMod 2) V₁
    let e : (Fin (Module.finrank (ZMod 2) V₁) → ZMod 2) ≃ₗ[ZMod 2] V₁ := b.equivFun.symm
    let g : (Fin (Module.finrank (ZMod 2) V₁) → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2) :=
      V₁.subtype.comp e.toLinearMap
    refine ⟨Module.finrank (ZMod 2) V₁, LinearMap.toMatrix' g, ?_, ?_⟩
    · rw [mulVecLin_toMatrix']
      rw [LinearMap.range_comp_of_range_eq_top (V₁.subtype) (LinearMap.range_eq_top.mpr e.surjective)]
      exact Submodule.range_subtype V₁
    · rw [mulVecLin_toMatrix']
      rw [LinearMap.ker_comp_of_ker_eq_bot (e.toLinearMap) (Submodule.ker_subtype V₁)]
      exact LinearMap.ker_eq_bot.mpr e.injective

end Commons.LinearAlgebra.Submodule