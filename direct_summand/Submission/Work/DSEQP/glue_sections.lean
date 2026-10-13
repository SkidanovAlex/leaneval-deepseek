import Mathlib

namespace Work.DSEQP

universe u

/-- **Gluing of compatible sections of the structure sheaf.**

If `U : ι → X.Opens` is a family of opens whose union is all of `X` and `s i` are sections of
the structure sheaf over `U i` agreeing on every pairwise intersection `U i ⊓ U j`, then the
`s i` glue to a global section `t` of `X` (i.e. `t` restricts to `s i` on each `U i`).

This is the `∃`-half of the sheaf condition for `X.presheaf` in its "unique gluing" form: the
structure sheaf of a scheme is a sheaf of rings on the site of open subsets
(`AlgebraicGeometry.SheafedSpace.IsSheaf`), and a sheaf of rings is a sheaf of types with
compatible (unique) gluings (`TopCat.Sheaf.existsUnique_gluing'`). -/
theorem glue_sections {X : AlgebraicGeometry.Scheme} {ι : Type u} (U : ι → X.Opens)
    (hcov : iSup U = ⊤) (s : ∀ i, ↥(X.presheaf.obj (Opposite.op (U i))))
    (h : ∀ i j, (X.presheaf.map (CategoryTheory.homOfLE (inf_le_left : U i ⊓ U j ≤ U i)).op).hom (s i)
      = (X.presheaf.map (CategoryTheory.homOfLE (inf_le_right : U i ⊓ U j ≤ U j)).op).hom (s j)) :
    ∃ t : ↥(X.presheaf.obj (Opposite.op ⊤)),
      ∀ i, (X.presheaf.map (CategoryTheory.homOfLE (le_top : U i ≤ ⊤)).op).hom t = s i := by
  -- The structure sheaf of `X`, bundled as a sheaf of rings on the underlying space.
  let F : TopCat.Sheaf CommRingCat X.toPresheafedSpace := ⟨X.presheaf, X.IsSheaf⟩
  -- The given data is exactly a compatible family for the sheaf condition.
  have hc : TopCat.Presheaf.IsCompatible X.presheaf U s := fun i j => h i j
  -- `⊤` is covered by the family `U`.
  have hcover : (⊤ : X.Opens) ≤ iSup U := le_of_eq hcov.symm
  obtain ⟨x, hx, -⟩ :=
    TopCat.Sheaf.existsUnique_gluing' (C := CommRingCat) F (X := X.toPresheafedSpace)
      U ⊤ (fun i => CategoryTheory.homOfLE (le_top : U i ≤ ⊤)) hcover s hc
  exact ⟨x, hx⟩

end Work.DSEQP
