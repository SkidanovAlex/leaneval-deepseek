import Mathlib
import Submission.Work.ATOM.Defs
import Submission.Work.ATOM.homKSinglePrecomp

namespace Work.ATOM

open CategoryTheory Limits LightCondensed MonoidalCategory MonoidalClosed

/-- (F7, heart level) For a solid target `X`, precomposition with `(1-S) ⊗ id_Y` is bijective on
`Hom(P ⊗ Y, X)`.

This is the tensor-hom adjunction `tensorLeft P ⊣ ihom P`: under `curry` the map
`f ↦ preShift Y ≫ f` corresponds to `g ↦ g ≫ (pre oneMinusShift).app X`; the latter is bijective
because `(pre oneMinusShift).app X` is an isomorphism whenever `X` is solid. -/
theorem preShift_bijective_of_solid (X Y : LightCondAb) (hX : isSolid X) :
    Function.Bijective (fun f : tmul P Y ⟶ X => preShift Y ≫ f) := by
  have hθ : IsIso ((MonoidalClosed.pre oneMinusShift).app X) := hX
  let θ := (MonoidalClosed.pre oneMinusShift).app X
  let e : (P ⊗ Y ⟶ X) ≃ (Y ⟶ (ihom P).obj X) := (ihom.adjunction P).homEquiv Y X
  have key : ∀ f : P ⊗ Y ⟶ X, e (preShift Y ≫ f) = e f ≫ θ := by
    intro f
    show curry (preShift Y ≫ f) = curry f ≫ θ
    rw [MonoidalClosed.curry_pre_app oneMinusShift f]
  let Ψ : (P ⊗ Y ⟶ X) → (P ⊗ Y ⟶ X) := fun f => e.symm (e f ≫ inv θ)
  have hinv : Function.LeftInverse Ψ (fun f : P ⊗ Y ⟶ X => preShift Y ≫ f) := by
    intro f
    show e.symm (e (preShift Y ≫ f) ≫ inv θ) = f
    apply e.injective
    rw [Equiv.apply_symm_apply, key f, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  have hpre : Function.RightInverse Ψ (fun f : P ⊗ Y ⟶ X => preShift Y ≫ f) := by
    intro g
    show preShift Y ≫ e.symm (e g ≫ inv θ) = g
    apply e.injective
    rw [key, Equiv.apply_symm_apply, Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  exact ⟨hinv.injective, hpre.surjective⟩

/-- (F7 in the homotopy category) For a complex `N` of solid objects, precomposition with
`singleC n ((1-S) ⊗ id_Y)` is bijective on morphisms from `singleC n (P ⊗ Y)` into `ιC N`
in the homotopy category `K(LightCondAb)`. -/
theorem homK_pre_oneMinusShift_bijective (N : CochainComplex LightCondensed.Solid ℤ) (n : ℤ)
    (Y : LightCondAb) :
    Function.Bijective (fun φ : Work.ATOM.hq.obj
        ((Work.ATOM.singleC n).obj (Work.ATOM.tmul LightCondensed.P Y)) ⟶
        Work.ATOM.hq.obj (Submission.Blueprint.ιC.obj N) =>
      Work.ATOM.hq.map ((Work.ATOM.singleC n).map (Work.ATOM.preShift Y)) ≫ φ) := by
  refine homKSinglePrecomp (tmul P Y) (preShift Y)
    (Submission.Blueprint.ιC.obj N) n ?_
  intro q
  exact preShift_bijective_of_solid ((Submission.Blueprint.ιC.obj N).X q) Y (N.X q).property

end Work.ATOM
