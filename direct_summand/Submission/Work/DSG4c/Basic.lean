import Submission.Work.DSMap.Map

/-!
# Base change of the projective space `ℙᴺ` (area DSG4c, part 1: vocabulary)

This file sets up the coefficient-extension morphism of graded rings and the induced
morphism `ℙᴺ_{A'} ⟶ ℙᴺ_A` of projective spaces, together with the standard affine charts
and their ring-theoretic structure maps.

Main definitions (namespace `Work.DSG4c`):

* `coeffExt A A' ψ N : DSMap.PGr A N →+*ᵍ DSMap.PGr A' N` — coefficient extension
  `A[x₀..x_N] → A'[x₀..x_N]` as a graded ring homomorphism;
* `awayChart A N i` and `chartMap A N i` — the `i`-th standard chart of `ℙᴺ_A`;
* `awayChartT A A' ψ N i` and `chartMapT A A' ψ N i` — the corresponding chart of `ℙᴺ_{A'}`,
  indexed by `coeffExt ψ (X i) = map ψ (X i)`;
* `awayMapChart A A' ψ N i` — the induced map of chart rings;
* `chartι`, `chartιT` — the chart inclusions into `ℙᴺ_A` resp. `ℙᴺ_{A'}`;
* `baseChangeMap A A' ψ N : DSMap.PSpace A' N ⟶ DSMap.PSpace A N` — the base change morphism.

All rings live in a fixed universe `u`.
-/

open CategoryTheory AlgebraicGeometry Limits MvPolynomial

namespace Work.DSG4c

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

variable (A A' : Type u) [CommRing A] [CommRing A'] (ψ : A →+* A') (N : ℕ)

/-! ## Coefficient extension of graded polynomial rings -/

/-- Coefficient extension `A[x] → A'[x]` as a morphism of graded rings, where
`DSMap.PGr A N` denotes the degree grading of `MvPolynomial (Fin (N+1)) A`. -/
noncomputable def coeffExt : DSMap.PGr A N →+*ᵍ DSMap.PGr A' N :=
  GradedRingHom.mk (MvPolynomial.map ψ) (fun {i} {x} hx => by
    rw [MvPolynomial.mem_homogeneousSubmodule] at hx ⊢
    exact hx.map ψ)

lemma coeffExt_apply (p : MvPolynomial (Fin (N+1)) A) :
    coeffExt A A' ψ N p = MvPolynomial.map ψ p := rfl

lemma coeffExt_X (i : Fin (N+1)) : coeffExt A A' ψ N (MvPolynomial.X i) = MvPolynomial.X i := by
  rw [coeffExt_apply, MvPolynomial.map_X]

/-- The coordinate `X i` is homogeneous of degree one. -/
lemma X_mem (i : Fin (N+1)) : MvPolynomial.X i ∈ DSMap.PGr A N 1 := by
  rw [MvPolynomial.mem_homogeneousSubmodule]
  exact MvPolynomial.isHomogeneous_X A i

/-! ## The irrelevant ideal is preserved -/

/-- The monomial `X^v` is homogeneous of degree `Finsupp.degree v`. -/
lemma monomial_one_mem (v : Fin (N+1) →₀ ℕ) :
    MvPolynomial.monomial v 1 ∈ DSMap.PGr A N (Finsupp.degree v) := by
  change MvPolynomial.monomial v 1 ∈
    MvPolynomial.homogeneousSubmodule (Fin (N+1)) A (Finsupp.degree v)
  rw [← MvPolynomial.homogeneousSubmodule_one_pow (σ := Fin (N+1)) (R := A) (Finsupp.degree v)]
  exact MvPolynomial.monomial_mem_homogeneousSubmodule_pow_degree (1 : A) v

lemma monomial_one_map (v : Fin (N+1) →₀ ℕ) :
    coeffExt A A' ψ N (MvPolynomial.monomial v 1) = MvPolynomial.monomial v 1 := by
  rw [coeffExt_apply, MvPolynomial.map_monomial]
  simp

lemma C_mul_monomial_one (v : Fin (N+1) →₀ ℕ) (a : A) :
    MvPolynomial.C a * MvPolynomial.monomial v 1 = MvPolynomial.monomial v a := by
  rw [MvPolynomial.C_mul_monomial, mul_one]

lemma coeffExt_irrelevant_le :
    HomogeneousIdeal.irrelevant (DSMap.PGr A' N) ≤
      HomogeneousIdeal.map (coeffExt A A' ψ N) (HomogeneousIdeal.irrelevant (DSMap.PGr A N)) := by
  refine (HomogeneousIdeal.irrelevant_le (𝒜 := DSMap.PGr A' N)).mpr fun i hi x hx => ?_
  change x ∈ (HomogeneousIdeal.map (coeffExt A A' ψ N)
    (HomogeneousIdeal.irrelevant (DSMap.PGr A N))).toIdeal
  rw [HomogeneousIdeal.toIdeal_map, HomogeneousIdeal.toIdeal_irrelevant]
  have hx' : x.IsHomogeneous i := hx
  rw [MvPolynomial.as_sum x]
  refine Ideal.sum_mem _ fun v hv => ?_
  have hdeg : Finsupp.degree v = i := by
    by_contra h
    exact (MvPolynomial.mem_support_iff.mp hv) (hx'.coeff_eq_zero h)
  have hmem : MvPolynomial.monomial v 1 ∈ (HomogeneousIdeal.irrelevant (DSMap.PGr A N)).toIdeal := by
    rw [HomogeneousIdeal.toIdeal_irrelevant]
    have h0 : 0 < Finsupp.degree v := by rw [hdeg]; exact hi
    exact HomogeneousIdeal.mem_irrelevant_of_mem (DSMap.PGr A N) h0
      (monomial_one_mem A N v)
  rw [← C_mul_monomial_one]
  refine Ideal.mul_mem_left _ _ ?_
  rw [← monomial_one_map A A' ψ N v]
  exact Ideal.mem_map_of_mem _ hmem

/-! ## The affine charts of `ℙᴺ_A` and of `ℙᴺ_{A'}` -/

/-- The standard chart `D₊(X i)` of `Proj (DSMap.PGr A N)`, i.e. the ring
`Away (DSMap.PGr A N) (X i) ≅ A[x_j/x_i : j ≠ i]`. -/
abbrev awayChart (i : Fin (N+1)) : Type u :=
  HomogeneousLocalization.Away (DSMap.PGr A N) (MvPolynomial.X i)

/-- The chart of `ℙᴺ_{A'}` corresponding to the `i`-th chart of `ℙᴺ_A`, indexed by the image
`coeffExt ψ (X i) = map ψ (X i)`.  Since `map ψ (X i) = X i` this is the usual `i`-th standard
chart of `ℙᴺ_{A'}`; the present indexing makes the `Away.map`-morphism typecheck without casts. -/
abbrev awayChartT (i : Fin (N+1)) : Type u :=
  HomogeneousLocalization.Away (DSMap.PGr A' N) ((coeffExt A A' ψ N) (MvPolynomial.X i))

/-- The structure map `A → Away (DSMap.PGr A N) (X i)` of the `i`-th chart. -/
noncomputable def chartMap (i : Fin (N+1)) : A →+* awayChart A N i :=
  (HomogeneousLocalization.fromZeroRingHom (DSMap.PGr A N)
      (Submonoid.powers (MvPolynomial.X i))).comp (algebraMap A (DSMap.PGr A N 0))

/-- The structure map `A' → Away (DSMap.PGr A' N) (coeffExt ψ (X i))` of the corresponding
chart of `ℙᴺ_{A'}`. -/
noncomputable def chartMapT (i : Fin (N+1)) : A' →+* awayChartT A A' ψ N i :=
  (HomogeneousLocalization.fromZeroRingHom (DSMap.PGr A' N)
      (Submonoid.powers ((coeffExt A A' ψ N) (MvPolynomial.X i)))).comp
    (algebraMap A' (DSMap.PGr A' N 0))

/-- The morphism of chart rings `Away (PGr A N) (X i) ⟶ Away (PGr A' N) (coeffExt ψ (X i))`
induced by coefficient extension; it is `Away.map` of `coeffExt`. -/
noncomputable def awayMapChart (i : Fin (N+1)) :
    awayChart A N i →+* awayChartT A A' ψ N i :=
  HomogeneousLocalization.Away.map (coeffExt A A' ψ N) (MvPolynomial.X i)

/-- The `i`-th standard chart of `ℙᴺ_A`, as a morphism
`Spec (Away (DSMap.PGr A N) (X i)) ⟶ ℙᴺ_A`. -/
noncomputable abbrev chartι (i : Fin (N+1)) :
    Spec ↧(awayChart A N i) ⟶ DSMap.PSpace A N :=
  Proj.awayι (DSMap.PGr A N) (MvPolynomial.X i) (X_mem A N i) one_pos

/-- The corresponding chart of `ℙᴺ_{A'}`. -/
noncomputable abbrev chartιT (i : Fin (N+1)) :
    Spec ↧(awayChartT A A' ψ N i) ⟶ DSMap.PSpace A' N :=
  Proj.awayι (DSMap.PGr A' N) ((coeffExt A A' ψ N) (MvPolynomial.X i))
    ((coeffExt A A' ψ N).2 (X_mem A N i)) one_pos

/-! ## The base change morphism and the structure maps of the charts -/

/-- The base change morphism `ℙᴺ_{A'} ⟶ ℙᴺ_A` induced by `Spec A' ⟶ Spec A`. -/
noncomputable def baseChangeMap : DSMap.PSpace A' N ⟶ DSMap.PSpace A N :=
  Proj.map (coeffExt A A' ψ N) (coeffExt_irrelevant_le A A' ψ N)

/-- **The base change morphism restricts to coefficient extension on the `i`-th chart.** -/
theorem chartιT_comp_baseChangeMap (i : Fin (N+1)) :
    chartιT A A' ψ N i ≫ baseChangeMap A A' ψ N =
      Spec.map (CommRingCat.ofHom (awayMapChart A A' ψ N i)) ≫ chartι A N i :=
  Proj.awayι_comp_map (coeffExt A A' ψ N) (coeffExt_irrelevant_le A A' ψ N) one_pos
    (MvPolynomial.X i) (X_mem A N i)

/-- The `i`-th chart of `ℙᴺ_A` composed with the structure morphism factors through
`Spec (chartMap A N i)`. -/
theorem chartι_comp_toSpec (i : Fin (N+1)) :
    chartι A N i ≫ DSMap.PSpace.toSpec A N =
      Spec.map (CommRingCat.ofHom (chartMap A N i)) := by
  rw [DSMap.PSpace.toSpec, ← Category.assoc, Proj.awayι_toSpecZero,
    ← Spec.map_comp (CommRingCat.ofHom (algebraMap A (DSMap.PGr A N 0)))
      (CommRingCat.ofHom (HomogeneousLocalization.fromZeroRingHom (DSMap.PGr A N)
        (Submonoid.powers (MvPolynomial.X i)))),
    ← CommRingCat.ofHom_comp]
  rfl

/-- The corresponding chart of `ℙᴺ_{A'}` composed with the structure morphism factors through
`Spec (chartMapT A A' ψ N i)`. -/
theorem chartιT_comp_toSpec (i : Fin (N+1)) :
    chartιT A A' ψ N i ≫ DSMap.PSpace.toSpec A' N =
      Spec.map (CommRingCat.ofHom (chartMapT A A' ψ N i)) := by
  rw [DSMap.PSpace.toSpec, ← Category.assoc, Proj.awayι_toSpecZero,
    ← Spec.map_comp (CommRingCat.ofHom (algebraMap A' (DSMap.PGr A' N 0)))
      (CommRingCat.ofHom (HomogeneousLocalization.fromZeroRingHom (DSMap.PGr A' N)
        (Submonoid.powers ((coeffExt A A' ψ N) (MvPolynomial.X i))))),
    ← CommRingCat.ofHom_comp]
  rfl

end Work.DSG4c
