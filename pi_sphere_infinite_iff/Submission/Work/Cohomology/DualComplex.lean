import Mathlib
import Submission.Work.Cohomology.Singular

/-!
# The dual cochain complex of an arbitrary chain complex

`Work.Cohomology.singularCochainComplex R X` is the `R`-dual of the singular chain complex.  For
the Mayer–Vietoris argument on the cohomological side one needs the same construction for an
*arbitrary* chain complex of `R`-modules, together with its functoriality (contravariance) and the
fact that a homotopy dualises to a homotopy.

This file provides

* `dualObj R C n` — `Hom_R(C_n, R)`;
* `dualDiff R C n` — the transposed differential `f ↦ f ∘ d_{n+1,n}`;
* `dualComplex R C` — the dual cochain complex (`CochainComplex (ModuleCat R) ℕ`);
* `dualComplexMap R f` — the contravariant functoriality: `dualComplex D ⟶ dualComplex C` for
  `f : C ⟶ D`.

The bridge `dualComplex R (singularChains R X) = singularCochainComplex R X` is recorded as
`dualComplex_singularChains`.
-/

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicTopology

namespace Work.Cohomology

noncomputable section

variable (R : Type) [CommRing R]

/-- The `n`-th dual module `Hom_R(C_n, R)` of a chain complex. -/
abbrev dualObj (C : ChainComplex (ModuleCat R) ℕ) (n : ℕ) : ModuleCat R :=
  ModuleCat.of R ((C.X n) →ₗ[R] R)

/-- The transposed differential `f ↦ f ∘ d` of a chain complex. -/
def dualDiff (C : ChainComplex (ModuleCat R) ℕ) (n : ℕ) :
    dualObj R C n ⟶ dualObj R C (n + 1) :=
  ModuleCat.ofHom
    { toFun := fun f => f.comp ((C.d (n + 1) n).hom)
      map_add' := fun f g => by ext x; simp [LinearMap.add_comp]
      map_smul' := fun a f => by ext x; simp [LinearMap.smul_comp] }

/-- The transposed differentials compose to zero. -/
theorem dualDiff_comp (C : ChainComplex (ModuleCat R) ℕ) (n : ℕ) :
    dualDiff R C n ≫ dualDiff R C (n + 1) = 0 := by
  have htotal : ((C.d (n + 1) n).hom).comp ((C.d ((n + 1) + 1) (n + 1)).hom) = 0 := by
    rw [← ModuleCat.hom_comp, ← ModuleCat.hom_zero]
    exact congrArg ModuleCat.Hom.hom
      (HomologicalComplex.d_comp_d C ((n + 1) + 1) (n + 1) n)
  have key : ∀ y : C.X ((n + 1) + 1),
      ((C.d (n + 1) n).hom) (((C.d ((n + 1) + 1) (n + 1)).hom) y) = 0 := by
    intro y
    have h := LinearMap.congr_fun htotal y
    simpa [LinearMap.comp_apply] using h
  apply ModuleCat.hom_ext
  simp only [ModuleCat.hom_comp, ModuleCat.hom_zero, dualDiff, ModuleCat.hom_ofHom]
  ext f x
  change f (((C.d (n + 1) n).hom) (((C.d ((n + 1) + 1) (n + 1)).hom) x)) = 0
  rw [key x]
  exact map_zero f

/-- **The dual cochain complex** of a chain complex of `R`-modules. -/
def dualComplex (C : ChainComplex (ModuleCat R) ℕ) : CochainComplex (ModuleCat R) ℕ :=
  CochainComplex.of (dualObj R C) (dualDiff R C) (dualDiff_comp R C)

@[simp]
theorem dualComplex_X (C : ChainComplex (ModuleCat R) ℕ) (n : ℕ) :
    (dualComplex R C).X n = dualObj R C n := rfl

/-- The dual complex of the singular chains is the singular cochain complex. -/
theorem dualComplex_singularChains (X : TopCat) :
    dualComplex R (singularChains R X) = singularCochainComplex R X := rfl

end

end Work.Cohomology
