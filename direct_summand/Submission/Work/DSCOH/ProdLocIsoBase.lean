import Mathlib
import Submission.Work.DSCOH.Basic
import Submission.Work.DSCOH.Shift

open MvPolynomial CategoryTheory

namespace Work.DSCOH

variable {A : Type*} [CommRing A] {n : ℕ}

/-! ## Localizing a finite product of copies of the polynomial ring

The chart Čech complex of the graded free module `∏_{j : Fin r} S(-d j)` is the `r`-fold product
of the chart Čech complexes of the shifts `S(-d j)`.  The first ingredient is the fact that the
localization of a finite product is the product of the localizations; `prodLocIso` is that
identification, obtained from `LocalizedModule.equivTensorProduct` and `TensorProduct.piRight`.

The vocabulary below (the linear equivalence `prodLocIso` and its computation rules) is needed by
`Work.DSCOH.prodLocIso_resAt` and by the files that build on it.  It is collected here, in a
module that only depends on `Submission.Work.DSCOH.Basic`, so that it sits *below* the lemmas
about it and can be shared by all of them. -/

/-- The chart localization of the product `∏_{j : Fin r} S` is the product of the chart
localizations of `S`. -/
noncomputable def prodLocIso (S : Finset (Fin n)) (r : ℕ) :
    LocalizedModule (subS (A := A) S) (Fin r → Poly A n) ≃ₗ[Poly A n]
      (Fin r → LocalizedModule (subS (A := A) S) (Poly A n)) :=
  (LocalizedModule.equivTensorProduct (subS (A := A) S) (Fin r → Poly A n)).restrictScalars
      (Poly A n) ≪≫ₗ
    (TensorProduct.piRight (Poly A n) (Localization (subS (A := A) S))
      (Localization (subS (A := A) S)) (fun _ : Fin r => Poly A n)).restrictScalars
      (Poly A n) ≪≫ₗ
    LinearEquiv.piCongrRight (fun _ : Fin r =>
      ((LocalizedModule.equivTensorProduct (subS (A := A) S) (Poly A n)).restrictScalars
        (Poly A n)).symm)

/-- The computation rule for `prodLocIso`: the class of `g` with denominator `s` is sent to the
family of the classes of the coordinates of `g` with the same denominator. -/
lemma prodLocIso_mk (S : Finset (Fin n)) (r : ℕ) (g : Fin r → Poly A n)
    (s : subS (A := A) S) :
    prodLocIso (A := A) (n := n) S r (LocalizedModule.mk g s) =
      fun j => LocalizedModule.mk (g j) s := by
  simp only [prodLocIso, LinearEquiv.trans_apply, LinearEquiv.restrictScalars_apply]
  rw [LocalizedModule.equivTensorProduct_apply_mk]
  simp only [TensorProduct.piRight_apply, TensorProduct.piRightHom_tmul]
  funext j
  simp only [LinearEquiv.piCongrRight_apply]
  rw [LinearEquiv.restrictScalars_symm_apply, LocalizedModule.equivTensorProduct_symm_apply_tmul]
  simp

/-- The image under `prodLocIso` of `g/1`. -/
lemma prodLocIso_mk_one (S : Finset (Fin n)) (r : ℕ) (g : Fin r → Poly A n) :
    prodLocIso (A := A) (n := n) S r (LocalizedModule.mk g 1) =
      fun j => LocalizedModule.mk (g j) 1 := by
  rw [prodLocIso_mk]

/-! ## The product of the degree-zero parts

This is the target of the identification `prodLocIso` at the level of degree-zero parts: the
`degZero`-part of the localization of `∏_{j : Fin r} S(-d j)` is the product, over `j`, of the
`degZero`-parts of the localizations of the shifts `S(-d j)`.  It is stated here (below
`Work.DSCOH.map_prodLocIso_degZero`, which uses it) so that both can be shared. -/

/-- The product over `j : Fin r` of the degree-zero parts of the chart localizations of the
shifts `S(-d j)`, viewed as a submodule of `∏_{j} S[1/X_S]`. -/
noncomputable def degZeroProd {A : Type*} [CommRing A] {n : ℕ} {r : ℕ}
    (d : Fin r → ℕ) (S : Finset (Fin n)) :
    Submodule A (Fin r → LocalizedModule (subS (A := A) S) (Poly A n)) :=
  ⨅ j, Submodule.comap
    ((LinearMap.proj (R := Poly A n)
      (φ := fun _ : Fin r => LocalizedModule (subS (A := A) S) (Poly A n)) j).restrictScalars A)
    (degZero (A := A) (n := n) (M := Poly A n) (shift (A := A) (n := n) (d j)) S)

lemma mem_degZeroProd {r : ℕ} {d : Fin r → ℕ} {S : Finset (Fin n)}
    {f : Fin r → LocalizedModule (subS (A := A) S) (Poly A n)} :
    f ∈ degZeroProd (A := A) (n := n) d S ↔
      ∀ j, f j ∈ degZero (A := A) (n := n) (M := Poly A n)
        (shift (A := A) (n := n) (d j)) S := by
  simp [degZeroProd]

end Work.DSCOH
