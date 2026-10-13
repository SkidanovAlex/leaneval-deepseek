import Mathlib

namespace Work.DSEQP

open CategoryTheory

universe u

/-- If a section of the structure sheaf of a scheme restricts to zero on every member of a family
of open sets covering the whole scheme, then the section is zero.

This is the "separatedness" part of the sheaf condition: a section over `⊤` is determined by its
restrictions to the members of any open cover. -/
theorem sections_eq_zero_of_restrict_eq_zero {X : AlgebraicGeometry.Scheme} {ι : Type u}
    (U : ι → X.Opens) (hcov : iSup U = ⊤) (x : ↥(X.presheaf.obj (Opposite.op ⊤)))
    (h : ∀ i, (X.presheaf.map (CategoryTheory.homOfLE (le_top : U i ≤ ⊤)).op).hom x = 0) :
    x = 0 := by
  -- Regard the structure sheaf as a sheaf of types.
  let G : CategoryTheory.Sheaf (Opens.grothendieckTopology X) (Type _) :=
    ⟨X.presheaf ⋙ CategoryTheory.forget CommRingCat,
      (TopCat.Presheaf.isSheaf_iff_isSheaf_comp (CategoryTheory.forget CommRingCat)
        X.presheaf).mp X.IsSheaf⟩
  have hY : (Opens.grothendieckTopology X).CoversTop U :=
    (Opens.coversTop_iff X U).mpr (TopologicalSpace.IsOpenCover.mk hcov)
  -- Every element of `G` over `⊤` determines a section of `G`, by restriction to each open set.
  have hsec : ∀ y₀ : G.obj.obj (Opposite.op ⊤), ∀ (j j' : (X.Opens)ᵒᵖ) (f : j ⟶ j'),
      G.obj.map f (G.obj.map (CategoryTheory.homOfLE (le_top : j.unop ≤ ⊤)).op y₀) =
        G.obj.map (CategoryTheory.homOfLE (le_top : j'.unop ≤ ⊤)).op y₀ := by
    intro y₀ j j' f
    rw [← Functor.map_comp_apply]
    exact congrArg (fun φ => G.obj.map φ y₀) (Subsingleton.elim _ _)
  let sec : G.obj.obj (Opposite.op ⊤) → ↑G.obj.sections := fun y₀ =>
    ⟨fun j => G.obj.map (CategoryTheory.homOfLE (le_top : j.unop ≤ ⊤)).op y₀, by
      intro j j' f
      exact hsec y₀ j j' f⟩
  -- The sections determined by `x` and by `0` agree on the cover, so they are equal.
  have hxs : sec x = sec 0 := by
    apply GrothendieckTopology.CoversTop.sections_ext hY G
    intro i
    show (X.presheaf.map (CategoryTheory.homOfLE (le_top : U i ≤ ⊤)).op).hom x =
      (X.presheaf.map (CategoryTheory.homOfLE (le_top : U i ≤ ⊤)).op).hom
        (0 : ↥(X.presheaf.obj (Opposite.op ⊤)))
    rw [h i, map_zero]
  have key := (Functor.sections_ext_iff.mp hxs) (Opposite.op ⊤)
  -- Evaluate the equality of sections at `⊤`, where restriction from `⊤` to `⊤` is the identity.
  have htop1 : (sec x : ↑G.obj.sections).val (Opposite.op ⊤) = x := by
    show G.obj.map (CategoryTheory.homOfLE (le_top : (⊤ : X.Opens) ≤ ⊤)).op x = x
    rw [show CategoryTheory.homOfLE (le_top : (⊤ : X.Opens) ≤ ⊤) = 𝟙 ⊤ from
        Subsingleton.elim _ _,
      CategoryTheory.op_id]
    simp
  have htop0 : (sec 0 : ↑G.obj.sections).val (Opposite.op ⊤) = 0 := by
    show G.obj.map (CategoryTheory.homOfLE (le_top : (⊤ : X.Opens) ≤ ⊤)).op
      (0 : G.obj.obj (Opposite.op ⊤)) = 0
    rw [show CategoryTheory.homOfLE (le_top : (⊤ : X.Opens) ≤ ⊤) = 𝟙 ⊤ from
        Subsingleton.elim _ _,
      CategoryTheory.op_id]
    simp
  calc x = (sec x : ↑G.obj.sections).val (Opposite.op ⊤) := htop1.symm
    _ = (sec 0 : ↑G.obj.sections).val (Opposite.op ⊤) := key
    _ = 0 := htop0

end Work.DSEQP
