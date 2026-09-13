import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Matrix.ToLin

namespace Commons.LinearAlgebra.Matrix

open LinearMap

section General

variable {K : Type*} [Field K]
variable {V W V' U' : Type*}
  [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
  [AddCommGroup V'] [Module K V'] [AddCommGroup U'] [Module K U']

/-- If `range f ≤ range g`, then `f` factors through `g` on the right. -/
theorem exists_comp_eq_of_range_le {f : V →ₗ[K] W} {g : U' →ₗ[K] W}
    (h : LinearMap.range f ≤ LinearMap.range g) :
    ∃ e : V →ₗ[K] U', g.comp e = f := by
  obtain ⟨s, hs⟩ := g.rangeRestrict.exists_rightInverse_of_surjective
    (LinearMap.range_rangeRestrict g)
  refine ⟨s.comp (f.codRestrict (LinearMap.range g) fun x => h ⟨x, rfl⟩), ?_⟩
  ext x
  have h1 := LinearMap.congr_fun hs ((f.codRestrict (LinearMap.range g) fun x => h ⟨x, rfl⟩) x)
  have h2 := congrArg Subtype.val h1
  simpa using h2

/-- If `ker g ≤ ker f`, then `f` factors through `g` on the left. -/
theorem exists_comp_eq_of_ker_le {f : V →ₗ[K] W} {g : V →ₗ[K] V'}
    (h : LinearMap.ker g ≤ LinearMap.ker f) :
    ∃ c : V' →ₗ[K] W, c.comp g = f := by
  let fbar : (V ⧸ LinearMap.ker g) →ₗ[K] W := (LinearMap.ker g).liftQ f h
  have hfbar : fbar.comp (LinearMap.ker g).mkQ = f := (LinearMap.ker g).liftQ_mkQ f h
  let c₀ : (LinearMap.range g) →ₗ[K] W :=
    fbar.comp (g.quotKerEquivRange.symm : (LinearMap.range g) →ₗ[K] (V ⧸ LinearMap.ker g))
  obtain ⟨c, hc⟩ := LinearMap.exists_extend c₀
  refine ⟨c, ?_⟩
  ext x
  change c (g x) = f x
  have hco : ((g.quotKerEquivRange ((LinearMap.ker g).mkQ x)) : V') = g x :=
    LinearMap.quotKerEquivRange_apply_mk g x
  have step1 : c (g x) = c₀ (g.quotKerEquivRange ((LinearMap.ker g).mkQ x)) := by
    rw [← hco]
    exact LinearMap.congr_fun hc (g.quotKerEquivRange ((LinearMap.ker g).mkQ x))
  rw [step1]
  have step2 : c₀ (g.quotKerEquivRange ((LinearMap.ker g).mkQ x)) = f x := by
    show fbar (g.quotKerEquivRange.symm (g.quotKerEquivRange ((LinearMap.ker g).mkQ x))) = f x
    rw [LinearEquiv.symm_apply_apply]
    simpa only [LinearMap.comp_apply] using LinearMap.congr_fun hfbar x
  rw [step2]

end General

theorem mem_range_mul_mul_iff {m n m' n' : ℕ} (Q : Matrix (Fin n') (Fin n) (ZMod 2))
    (ι : Matrix (Fin m) (Fin m') (ZMod 2)) (M : Matrix (Fin m) (Fin n) (ZMod 2)) :
    (∃ A : Matrix (Fin m') (Fin n') (ZMod 2), ι * A * Q = M) ↔
      (LinearMap.ker Q.mulVecLin ≤ LinearMap.ker M.mulVecLin ∧
        LinearMap.range M.mulVecLin ≤ LinearMap.range ι.mulVecLin) := by
  constructor
  · rintro ⟨A, hA⟩
    have hlin : M.mulVecLin = ι.mulVecLin.comp (A.mulVecLin.comp Q.mulVecLin) := by
      rw [← hA]
      simp only [Matrix.mulVecLin_mul, LinearMap.comp_assoc]
    constructor
    · intro v hv
      simp only [LinearMap.mem_ker] at hv ⊢
      rw [hlin, LinearMap.comp_apply, LinearMap.comp_apply, hv, map_zero, map_zero]
    · rintro w ⟨v, rfl⟩
      simp only [hlin, LinearMap.comp_apply]
      exact ⟨A.mulVecLin (Q.mulVecLin v), rfl⟩
  · rintro ⟨hker, hrange⟩
    have hrf : LinearMap.range ((LinearMap.ker Q.mulVecLin).liftQ M.mulVecLin hker)
        ≤ LinearMap.range ι.mulVecLin := by
      rw [Submodule.range_liftQ]
      exact hrange
    obtain ⟨e, he⟩ := exists_comp_eq_of_range_le
      (f := (LinearMap.ker Q.mulVecLin).liftQ M.mulVecLin hker) (g := ι.mulVecLin) hrf
    have hker_d : LinearMap.ker Q.mulVecLin
        ≤ LinearMap.ker (e.comp (LinearMap.ker Q.mulVecLin).mkQ) := by
      intro v hv
      simp only [LinearMap.mem_ker] at hv ⊢
      show e ((LinearMap.ker Q.mulVecLin).mkQ v) = 0
      rw [show (LinearMap.ker Q.mulVecLin).mkQ v = 0 from by
        rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
        exact hv]
      exact map_zero e
    obtain ⟨a, ha⟩ := exists_comp_eq_of_ker_le
      (f := e.comp (LinearMap.ker Q.mulVecLin).mkQ) hker_d
    have hAmv : (LinearMap.toMatrix' a).mulVecLin = a := by
      rw [← Matrix.toLin'_apply']
      exact Matrix.toLin'_toMatrix' a
    have hlin2 : (ι * LinearMap.toMatrix' a * Q).mulVecLin = M.mulVecLin := by
      rw [Matrix.mulVecLin_mul, Matrix.mulVecLin_mul, hAmv]
      rw [LinearMap.comp_assoc, ha]
      rw [← LinearMap.comp_assoc, he]
      rw [Submodule.liftQ_mkQ]
    refine ⟨LinearMap.toMatrix' a, ?_⟩
    apply Matrix.toLin'.injective
    rw [Matrix.toLin'_apply', Matrix.toLin'_apply']
    exact hlin2

end Commons.LinearAlgebra.Matrix