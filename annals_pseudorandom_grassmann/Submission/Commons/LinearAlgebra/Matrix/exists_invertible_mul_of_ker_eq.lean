import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.RingTheory.TotallySplit

namespace Commons.LinearAlgebra.Matrix

theorem exists_invertible_mul_of_ker_eq {m n : ℕ} (A B : Matrix (Fin m) (Fin n) (ZMod 2))
    (hker : LinearMap.ker A.mulVecLin = LinearMap.ker B.mulVecLin)
    (hA : LinearMap.range A.mulVecLin = ⊤) (hB : LinearMap.range B.mulVecLin = ⊤) :
    ∃ T : Matrix (Fin m) (Fin m) (ZMod 2), Function.Bijective T.mulVecLin ∧ B = T * A := by
  classical
  obtain ⟨g, hg⟩ := A.mulVecLin.exists_rightInverse_of_surjective hA
  have hAg : ∀ w, A.mulVecLin (g w) = w := fun w => by
    have := DFunLike.congr_fun hg w
    simpa [LinearMap.comp_apply] using this
  let Tlin : (Fin m → ZMod 2) →ₗ[ZMod 2] (Fin m → ZMod 2) := B.mulVecLin.comp g
  have hTlin_apply : ∀ w, Tlin w = B.mulVecLin (g w) := fun w => rfl
  have hTA : Tlin.comp A.mulVecLin = B.mulVecLin := by
    apply LinearMap.ext
    intro v
    rw [LinearMap.comp_apply, hTlin_apply]
    have hmem : g (A.mulVecLin v) - v ∈ LinearMap.ker A.mulVecLin := by
      rw [LinearMap.mem_ker, map_sub, hAg, sub_self]
    rw [hker] at hmem
    rw [LinearMap.mem_ker, map_sub] at hmem
    exact sub_eq_zero.mp hmem
  have hTsurj : Function.Surjective Tlin := by
    intro w
    obtain ⟨v, hv⟩ := (show w ∈ LinearMap.range B.mulVecLin by rw [hB]; trivial)
    refine ⟨A.mulVecLin v, ?_⟩
    rw [← hv]
    simpa [LinearMap.comp_apply] using DFunLike.congr_fun hTA v
  have hkerT : LinearMap.ker Tlin = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro w hw
    rw [LinearMap.mem_ker] at hw
    obtain ⟨v, hv⟩ := (show w ∈ LinearMap.range A.mulVecLin by rw [hA]; trivial)
    have hBv : B.mulVecLin v = 0 := by
      have h1 : Tlin (A.mulVecLin v) = B.mulVecLin v := by
        simpa [LinearMap.comp_apply] using DFunLike.congr_fun hTA v
      have h2 : Tlin (A.mulVecLin v) = 0 := by rw [hv]; exact hw
      rw [h2] at h1; exact h1.symm
    have hmemA : v ∈ LinearMap.ker A.mulVecLin := by
      rw [hker, LinearMap.mem_ker]; exact hBv
    rw [LinearMap.mem_ker] at hmemA
    rw [← hv]; exact hmemA
  have hinj : Function.Injective Tlin := LinearMap.ker_eq_bot.mp hkerT
  have hTmul : (LinearMap.toMatrix' Tlin).mulVecLin = Tlin :=
    (Matrix.toLin'_apply' (LinearMap.toMatrix' Tlin)).symm.trans (Matrix.toLin'_toMatrix' Tlin)
  refine ⟨LinearMap.toMatrix' Tlin, ?_, ?_⟩
  · rw [hTmul]; exact ⟨hinj, hTsurj⟩
  · have hmul : (LinearMap.toMatrix' Tlin * A).mulVecLin = B.mulVecLin := by
      rw [Matrix.mulVecLin_mul, hTmul]; exact hTA
    apply Matrix.toLin'.injective
    rw [Matrix.toLin'_apply', Matrix.toLin'_apply', hmul]

end Commons.LinearAlgebra.Matrix