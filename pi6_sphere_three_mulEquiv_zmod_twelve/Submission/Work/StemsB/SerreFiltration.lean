import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The Serre filtration of the singular complex of a map

Let `f : X ⟶ Y` be a morphism of simplicial sets (for us `f = Sing p`, the singular simplicial
set of a continuous map `p : E → B`).  The **Serre filtration** of `X` induced by `f` is the
filtration by the subcomplexes

  `serreSubcomplex f P = f ⁻¹' (skeleton P Y) ⊆ X`  (`P : ℕ`),

i.e. the simplices of `X` whose image in `Y` lies in the `P`-skeleton of `Y`.  This is the
filtration underlying the Serre spectral sequence of a fibration.  Using the *simplicial* skeleton
filtration of `Y = Sing B` (rather than a CW structure on `B`) is what makes the construction
work for an arbitrary base `B`: it avoids any need for CW approximation
(see `CONTRACTS.md` §D2.2).

The subquotients `serreSubcomplex f P ⧸ serreSubcomplex f (P-1)` are wedges of `P`-spheres, one
for each nondegenerate `P`-simplex of `Y`, which is the input of the computation of the first page
of the spectral sequence.
-/

namespace Work.StemsB

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

/-- If the `P`-skeleton of `Y` is everything, then so is the `P`-th term of the Serre
filtration. -/
theorem serreSubcomplex_eq_top {X Y : SSet} (f : X ⟶ Y) {P : ℕ}
    (h : SSet.skeleton (X := Y) P = ⊤) : serreSubcomplex f P = ⊤ :=
  (Subfunctor.preimage_eq_top_iff (SSet.skeleton (X := Y) P) f).mpr (h ▸ le_top)

/-- The Serre filtration is **exhaustive**: every simplex of `X` lies in some `serreSubcomplex f P`. -/
theorem iSup_serreSubcomplex {X Y : SSet} (f : X ⟶ Y) :
    (⨆ P : ℕ, serreSubcomplex f P) = ⊤ := by
  refine le_antisymm le_top ?_
  intro n x _
  rw [Subfunctor.iSup_obj, Set.mem_iUnion]
  have h : f.app n x ∈ (⊤ : Y.Subcomplex).obj n := Set.mem_univ _
  rw [← Y.iSup_skeleton, Subfunctor.iSup_obj, Set.mem_iUnion] at h
  obtain ⟨P, hP⟩ := h
  exact ⟨P, hP⟩

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

end Work.StemsB
