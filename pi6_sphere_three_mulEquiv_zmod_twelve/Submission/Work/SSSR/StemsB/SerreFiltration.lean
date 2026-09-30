import Mathlib
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

variable {R : Type} [CommRing R] [Nontrivial R]

namespace Work.SSSR.StemsB

noncomputable section

open CategoryTheory Simplicial
/-- **The Serre filtration** of a simplicial set `X` along a morphism `f : X ⟶ Y`: the preimage
under `f` of the `P`-skeleton of `Y`. -/
def serreSubcomplex {X Y : SSet} (f : X ⟶ Y) (P : ℕ) : X.Subcomplex :=
  (SSet.skeleton (X := Y) P).preimage f

theorem serreSubcomplex_mono {X Y : SSet} (f : X ⟶ Y) :
    Monotone (serreSubcomplex f) :=
  fun _ _ h => fun _ _ hx => (SSet.skeleton (X := Y)).monotone h _ hx

/-- Characterisation of the members of the Serre filtration. -/
theorem mem_serreSubcomplex {X Y : SSet} {f : X ⟶ Y} {P : ℕ}
    {n : SimplexCategoryᵒᵖ} {x : X.obj n} :
    x ∈ (serreSubcomplex f P).obj n ↔ f.app n x ∈ (SSet.skeleton (X := Y) P).obj n :=
  Iff.rfl

/-! ## The induced filtration of the singular chain complex -/

/-- The Serre filtration, as a functor `ℕ ⥤ SSet` (the index `ℕ` being the ordered set, viewed as
a category). -/
noncomputable def serreFiltration {X Y : SSet} (f : X ⟶ Y) : ℕ ⥤ SSet where
  obj P := (serreSubcomplex f P : SSet)
  map {P Q} h := Subfunctor.homOfLe (serreSubcomplex_mono f (leOfHom h))
  map_id P := SSet.Subcomplex.homOfLE_refl (serreSubcomplex f P)
  map_comp h₁ h₂ := by rw [SSet.Subcomplex.homOfLE_comp]

/-- The **Serre filtration of the singular chain complex** of `X` (coefficients in `R`) along
`f : X ⟶ Y`: the `P`-th term is the chain complex of the subcomplex `serreSubcomplex f P`, and the
maps are induced by the inclusions. -/
noncomputable def serreChainFiltration {X Y : SSet} (f : X ⟶ Y) (R : Type) [CommRing R] :
    ℕ ⥤ ChainComplex (ModuleCat R) ℕ :=
  serreFiltration f ⋙ ((SSet.chainComplexFunctor (ModuleCat R)).obj (ModuleCat.of R R))

end

end Work.SSSR.StemsB
