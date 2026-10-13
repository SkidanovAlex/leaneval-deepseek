import Mathlib
import Submission.Work.DSMap.Mix2Fix
import Submission.Work.DSCHART.Main

/-!
# DSM8m2 — setup: the `A`-algebra structure on `K(X)` and the choice of chart

* `Work.DSM8m2.phiL` — the structure map `A → K(X)` of `f : X ⟶ Spec A`, i.e. the composite
  `A → Γ(X,⊤) → K(X)`.
* `Work.DSM8m2.phiL_phiU` — its compatibility with the structure map on an open `U`
  (`germ_U ∘ phiU = germ_⊤ ∘ phi`): this is exactly the statement that the germ map
  `Γ(X,U) → K(X)` is a map of `A`-algebras, and it is what lets us build
  `φ : Γ(X,U) →ₐ[A] K(X)` in `Main.lean`.
* `Work.DSM8m2.exists_nonempty_chart` — the chart cover of `ℙᴺ_A` (area DSCHART) has a nonempty
  member; we need the nonemptiness to have the germ map into the function field.
-/

open CategoryTheory AlgebraicGeometry

namespace Work.DSM8m2

universe u

/-- The structure map `A → K(X)` of `f : X ⟶ Spec A`. -/
noncomputable def phiL (A : Type u) [CommRing A] (X : Scheme.{u}) (f : X ⟶ Spec (.of A))
    [IrreducibleSpace ↥X] [Nonempty (⊤ : X.Opens)] : A →+* X.functionField :=
  (Scheme.germToFunctionField X ⊤).hom.comp (DSMap.phi A X f)

/-- The structure maps `A → Γ(X,U)` and `A → K(X)` are compatible with the germ. -/
theorem phiL_phiU (A : Type u) [CommRing A] {X : Scheme.{u}} (f : X ⟶ Spec (.of A))
    [IrreducibleSpace ↥X] [Nonempty (⊤ : X.Opens)] (U : X.Opens) [Nonempty U] (a : A) :
    (Scheme.germToFunctionField X U).hom (DSMap.phiU A X f U a) = phiL A X f a := by
  have hx : genericPoint X ∈ U :=
    ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr (by
      simpa using (show Nonempty U from inferInstance))
  exact X.presheaf.germ_res_apply (homOfLE le_top) (genericPoint X) hx (DSMap.phi A X f a)

/-- If the charts `X ∩ D₊(x_k)` cover `X` and `X` is nonempty, then some chart is nonempty. -/
theorem exists_nonempty_chart {A : Type u} [CommRing A] {X : Scheme.{u}} {N : ℕ}
    (i : X ⟶ DSMap.PSpace A N) (hcov : ⨆ k, DSMap.Mix2.chartCover i k = ⊤) (hX : Nonempty X) :
    ∃ j : Fin (N + 1), Nonempty ↥(DSMap.Mix2.chartCover i ⟨j⟩) := by
  obtain ⟨x⟩ := hX
  have hx : x ∈ ⨆ k, DSMap.Mix2.chartCover i k := by rw [hcov]; trivial
  obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
  exact ⟨k.down, ⟨⟨x, hk⟩⟩⟩

end Work.DSM8m2
