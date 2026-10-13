import Mathlib
import Submission.Work.DSG2.Defs

/-!
# Auxiliary definitions for `Work.DSG2.exists_immersion_pspace`

The proof of `Work.DSG2.exists_immersion_pspace` uses the standard affine chart
`Spec A[x_0,…,x_{n-1}] ⟶ ℙ^n_A` of projective space, described through the degree-zero part
`Away 𝒜 (X i)` of the localization of `A[x_0,…,x_n]` at `X i`.

* `Work.DSG2.chartAto` : the structure map `A →+* Away 𝒜 (X i)` of the chart (constants).
* `Work.DSG2.chartι` : the open immersion `Spec (Away 𝒜 (X i)) ⟶ ℙ^n_A` given by `Proj.awayι`,
  whose structure morphism is `chartAto` (`chartι_toSpec`).
-/

open CategoryTheory AlgebraicGeometry

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

namespace Work.DSG2

/-- The structure map `A →+* Away 𝒜 (X i)` of the `i`-th standard affine chart of `ℙ^n_A`,
where `𝒜 = MvPolynomial.homogeneousSubmodule (Fin (n+1)) A`.  It agrees with the map obtained
from `Proj.toSpecZero` (see `Proj.awayι_toSpecZero`). -/
noncomputable def chartAto (A : Type u) [CommRing A] (n : ℕ) (i : Fin (n + 1)) :
    A →+* chartRing A n i :=
  (HomogeneousLocalization.fromZeroRingHom (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A)
      (Submonoid.powers (MvPolynomial.X i))).comp
    (algebraMap A (↥(MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A 0)))

/-- The `i`-th standard affine chart of `ℙ^n_A`, as a morphism to `ℙ^n_A` over `Spec A`. -/
noncomputable def chartι (A : Type u) [CommRing A] (n : ℕ) (i : Fin (n + 1)) :
    Spec (CommRingCat.of (chartRing A n i)) ⟶ DSMap.PSpace A n :=
  Proj.awayι (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A) (MvPolynomial.X i)
    ((MvPolynomial.mem_homogeneousSubmodule 1 (MvPolynomial.X i)).mpr
      (MvPolynomial.isHomogeneous_X A i)) (by norm_num)

instance chartι_isOpenImmersion (A : Type u) [CommRing A] (n : ℕ) (i : Fin (n + 1)) :
    IsOpenImmersion (chartι A n i) := by
  change IsOpenImmersion (Proj.awayι (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A)
    (MvPolynomial.X i) ((MvPolynomial.mem_homogeneousSubmodule 1 (MvPolynomial.X i)).mpr
      (MvPolynomial.isHomogeneous_X A i)) (by norm_num))
  unfold Proj.awayι
  infer_instance

theorem chartι_toSpec (A : Type u) [CommRing A] (n : ℕ) (i : Fin (n + 1)) :
    chartι A n i ≫ DSMap.PSpace.toSpec A n =
      Spec.map (CommRingCat.ofHom (chartAto A n i)) := by
  change Proj.awayι (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A)
    (MvPolynomial.X i) ((MvPolynomial.mem_homogeneousSubmodule 1 (MvPolynomial.X i)).mpr
      (MvPolynomial.isHomogeneous_X A i)) (by norm_num) ≫ DSMap.PSpace.toSpec A n =
      Spec.map (CommRingCat.ofHom (chartAto A n i))
  rw [DSMap.PSpace.toSpec, ← Category.assoc, Proj.awayι_toSpecZero, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp]
  rfl

end Work.DSG2
