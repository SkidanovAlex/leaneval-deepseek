import Mathlib
import Submission.Work.KT.Defs
import Submission.Work.KT.mvLin

namespace Work.KT

open Matrix

/-- If `Y * X = p` and `X * Y = 1` then `v ↦ Y *ᵥ v` is a linear isomorphism onto the image of
`p`. -/
theorem mvN_range_iso {R : Type} [Ring R] (hcomm : ∀ x y : R, x * y = y * x)
    {a b : ℕ} {p : Matrix (Fin a) (Fin a) R} {X : Matrix (Fin b) (Fin a) R}
    {Y : Matrix (Fin a) (Fin b) R} (hYX : Y * X = p) (hXY : X * Y = 1) :
    Nonempty ((Fin b → R) ≃ₗ[R] (mvLin hcomm p).range) := by
  -- `Y *ᵥ v` is a fixed point of `p`, hence lies in the image of `p`.
  have key1 : ∀ v : Fin b → R, mvLin hcomm p (mvLin hcomm Y v) = mvLin hcomm Y v := by
    intro v
    simp only [mvLin_apply]
    rw [← hYX, ← Matrix.mulVec_mulVec (Y.mulVec v) Y X, Matrix.mulVec_mulVec v X Y, hXY,
      Matrix.one_mulVec]
  let f : (Fin b → R) →ₗ[R] (mvLin hcomm p).range :=
    (mvLin hcomm Y).codRestrict (mvLin hcomm p).range (fun v => by
      rw [LinearMap.mem_range]
      exact ⟨mvLin hcomm Y v, key1 v⟩)
  have hfval : ∀ v, ((f v : (mvLin hcomm p).range) : Fin a → R) = (mvLin hcomm Y) v :=
    fun v => rfl
  -- `X` is a left inverse of `Y`, so `f` is injective.
  have hleft : ∀ u : Fin b → R, (mvLin hcomm X) ((mvLin hcomm Y) u) = u := by
    intro u
    rw [← LinearMap.comp_apply, ← mvLin_mul hcomm X Y, hXY, mvLin_one, LinearMap.id_apply]
  have hinj : Function.Injective f := by
    intro v w hvw
    have h2 : (mvLin hcomm X) ((mvLin hcomm Y) v) = (mvLin hcomm X) ((mvLin hcomm Y) w) := by
      rw [← hfval v, ← hfval w]
      exact congrArg (mvLin hcomm X) (congrArg Subtype.val hvw)
    rwa [hleft v, hleft w] at h2
  -- every element of the image of `p` is `Y *ᵥ (X *ᵥ u)`, so `f` is surjective.
  have hsurj : Function.Surjective f := by
    intro w
    obtain ⟨u, hu⟩ := LinearMap.mem_range.mp w.2
    refine ⟨X.mulVec u, ?_⟩
    apply Subtype.ext
    show Y.mulVec (X.mulVec u) = w.val
    rw [Matrix.mulVec_mulVec u Y X, hYX]
    simpa using hu
  exact ⟨LinearEquiv.ofBijective f ⟨hinj, hsurj⟩⟩

end Work.KT
