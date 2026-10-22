import Mathlib
import Submission.Work.ATOM.Defs
import Submission.Work.RESOL.Basic

namespace Work.ATOM

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed

/-- **A small atomic sum tensored with a free object is a small atomic sum.**
`Work.RESOL.IsAtomicSum M` means that `M` is a small coproduct of free objects `ℤ[S j]`
(`Work.RESOL.Basic`); tensoring with `ℤ[T]` gives
`ℤ[T] ⊗ ∐_j ℤ[S j] ≅ ∐_j (ℤ[T] ⊗ ℤ[S j]) ≅ ∐_j ℤ[T × S j]` using that
`LightCondensed.tensorLeft ℤ[T]` preserves small coproducts (it is a left adjoint) and
`Work.ATOM.zfreeTensorIso`. -/
theorem isAtomicSum_tmul_zfree (T : LightProfinite.{0}) {M : LightCondAb}
    (h : Work.RESOL.IsAtomicSum M) :
    Work.RESOL.IsAtomicSum
      (Work.ATOM.tmul ((LightCondensed.free (R := ℤ)).obj T.toCondensed) M) := by
  classical
  -- `M ≅ ∐_j ℤ[S j]`, presented by an explicit colimit cofan `c`.
  obtain ⟨J, S, c, ⟨hc⟩, ⟨eM⟩⟩ := h
  -- the two diagram functors: the atoms `ℤ[S j]`, and the atoms `ℤ[T × S j]` of the answer
  let F₁ : Discrete J ⥤ LightCondAb := Discrete.functor (fun j => Work.ATOM.zfree (S j))
  let F₂ : Discrete J ⥤ LightCondAb := Discrete.functor (fun j => Work.ATOM.zfree (T ⊗ S j))
  -- `ℤ[T] ⊗ -` is a left adjoint (`tensorLeft ℤ[T] ⊣ ihom ℤ[T]`, from `MonoidalClosed`), so it
  -- preserves the colimit cocone `c`, hence the small coproduct `∐_j ℤ[S j]`: the image cocone
  -- `hcF` is a colimit cocone for `∐_j (ℤ[T] ⊗ ℤ[S j])`.
  have hcF : IsColimit ((tensorLeft (Work.ATOM.zfree T)).mapCocone c) :=
    isColimitOfPreserves _ hc
  -- `ℤ[T ⊗ S j] ≅ ℤ[T] ⊗ ℤ[S j]`, so the same cocone is a colimit cocone for `∐_j ℤ[T ⊗ S j]`
  let β : F₂ ≅ F₁ ⋙ tensorLeft (Work.ATOM.zfree T) :=
    Discrete.natIso (fun j => (Work.ATOM.zfreeTensorIso T (S j.as)).symm)
  have hc' :
      IsColimit ((Cocone.precompose β.hom).obj ((tensorLeft (Work.ATOM.zfree T)).mapCocone c)) :=
    (IsColimit.equivOfNatIsoOfIso β.symm ((tensorLeft (Work.ATOM.zfree T)).mapCocone c)
      ((Cocone.precompose β.hom).obj
        ((tensorLeft (Work.ATOM.zfree T)).mapCocone c)) (Iso.refl _)).1 hcF
  refine ⟨J, fun j => T ⊗ S j,
    (Cocone.precompose β.hom).obj ((tensorLeft (Work.ATOM.zfree T)).mapCocone c), ⟨hc'⟩, ⟨?_⟩⟩
  -- and the point of that cocone is `ℤ[T] ⊗ c.pt ≅ ℤ[T] ⊗ M`
  exact (tensorLeft (Work.ATOM.zfree T)).mapIso eM

end Work.ATOM
