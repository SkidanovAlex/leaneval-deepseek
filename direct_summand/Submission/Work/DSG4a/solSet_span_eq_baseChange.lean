import Mathlib
import Submission.Work.DSG4a.Present
import Submission.Work.DSG4a.piScalarRight_baseChange_transMap
import Submission.Work.DSG4a.ker_baseChange
import Submission.Work.DSG4a.map_ker_eq_ker

namespace Work.DSG4a

open TensorProduct

/-- Under the canonical identification `A' ⊗[A] (Fin m → A) ≃ₗ[A'] (Fin m → A')`, the
`A'`-span of the image of a submodule `N ≤ A^m` is the image of the base change
`N.baseChange A'`.  This is the "coordinate" form of `Submodule.baseChange_span`. -/
lemma span_image_eq_map_baseChange {A A' : Type*} [CommRing A] [CommRing A'] [Algebra A A']
    {m : ℕ} (N : Submodule A (Fin m → A)) :
    Submodule.span A' ((fun w : Fin m → A => fun i => algebraMap A A' (w i)) ''
        (N : Set (Fin m → A))) =
      Submodule.map (TensorProduct.piScalarRight A A' A' (Fin m)).toLinearMap
        (N.baseChange A') := by
  have hspan : N.baseChange A' = Submodule.span A'
      (((TensorProduct.mk A A' (Fin m → A)) 1) '' (N : Set (Fin m → A))) := by
    rw [← Submodule.baseChange_span A' (N : Set (Fin m → A)), Submodule.span_eq]
  rw [hspan, Submodule.map_span]
  congr 1
  ext y
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact ⟨(TensorProduct.mk A A' (Fin m → A)) 1 w, ⟨w, hw, rfl⟩, by
      ext i
      simp [TensorProduct.piScalarRightHom_tmul, Algebra.smul_def]⟩
  · rintro ⟨z, ⟨w, hw, rfl⟩, rfl⟩
    exact ⟨w, hw, by
      ext i
      simp [TensorProduct.piScalarRightHom_tmul, Algebra.smul_def]⟩

/-- The solution set of the transposed linear system commutes with flat base change:
the `A'`-span of the image of `solSet D` is the solution set of the entrywise-extended
matrix. -/
theorem solSet_span_eq_baseChange {A A' : Type*} [CommRing A] [CommRing A'] [Algebra A A']
    {m n : ℕ} (D : Fin m → Fin n → A) (hflat : Module.Flat A A') :
    Submodule.span A' ((fun w : Fin m → A => fun i => algebraMap A A' (w i)) ''
        (Work.DSG4a.solSet D : Set (Fin m → A))) =
      Work.DSG4a.solSet (fun i j => algebraMap A A' (D i j)) := by
  have hB := span_image_eq_map_baseChange (A := A) (A' := A') (N := solSet D)
  have hC := ker_baseChange (A := A) (A' := A') hflat (transMap D)
  have hD := map_ker_eq_ker (R := A) (S := A')
      (X := Fin m → A) (Y := Fin n → A) (P := Fin m → A') (Q := Fin n → A')
      (LinearMap.baseChange A' (transMap D))
      (transMap (fun i j => algebraMap A A' (D i j)))
      (TensorProduct.piScalarRight A A' A' (Fin m))
      (TensorProduct.piScalarRight A A' A' (Fin n))
      (piScalarRight_baseChange_transMap D)
  rw [hB]
  simp only [solSet]
  rw [hC, hD]

end Work.DSG4a
