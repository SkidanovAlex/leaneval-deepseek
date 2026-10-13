import Submission.Work.DSG4c.ChartPushout.Defs

/-!
# Chart pushout (area DSG4c): dehomogenization, coefficient extension

Functoriality in the coefficient ring of the identifications of `Defs.lean`.
-/

open CategoryTheory AlgebraicGeometry Limits MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra

namespace Work.DSG4c.ChartPushout

universe u

variable (A A' : Type u) [CommRing A] [CommRing A'] (ψ : A →+* A') (N : ℕ) (i : Fin (N+1))

/-- The element `X k / X i` of the target chart ring `Away (PGr A' N) (coeffExt ψ (X i))`. -/
noncomputable def chartElemAllT (k : Fin (N+1)) : Work.DSG4c.awayChartT A A' ψ N i :=
  HomogeneousLocalization.Away.mk (DSMap.PGr A' N)
    ((Work.DSG4c.coeffExt A A' ψ N).2 (X_mem A N i)) 1 (MvPolynomial.X k)
    (X_mem A' N k)

/-- The element `X j / X i` of the target chart ring, for `j ≠ i`. -/
noncomputable def chartElemT (j : chartIdx N i) : Work.DSG4c.awayChartT A A' ψ N i :=
  chartElemAllT A A' ψ N i j.1

lemma chartElemT_eq_chartElemAllT (j : chartIdx N i) :
    chartElemT A A' ψ N i j = chartElemAllT A A' ψ N i j.1 := rfl

lemma coeffExt_X_of (k : Fin (N+1)) :
    (Work.DSG4c.coeffExt A A' ψ N) (MvPolynomial.X k) = MvPolynomial.X k := by
  rw [Work.DSG4c.coeffExt_apply, MvPolynomial.map_X]

lemma dehomHom_coeffExt_X :
    dehomHom A' N i ((Work.DSG4c.coeffExt A A' ψ N) (MvPolynomial.X i)) = 1 := by
  rw [coeffExt_X_of A A' ψ N i, dehomHom_X_self]

lemma awayMapChart_chartElemAll (k : Fin (N+1)) :
    (Work.DSG4c.awayMapChart A A' ψ N i) (chartElemAll A N i k) =
      chartElemAllT A A' ψ N i k := by
  rw [chartElemAll, chartElemAllT, Work.DSG4c.awayMapChart, HomogeneousLocalization.Away.map_mk]
  simp only [coeffExt_X_of A A' ψ N k]

lemma awayMapChart_chartElem (j : chartIdx N i) :
    (Work.DSG4c.awayMapChart A A' ψ N i) (chartElem A N i j) =
      chartElemT A A' ψ N i j := by
  rw [chartElem, chartElemT, awayMapChart_chartElemAll]

lemma dehomHom_eq_one_of_mem_powersT {x : MvPolynomial (Fin (N+1)) A'}
    (hx : x ∈ Submonoid.powers ((Work.DSG4c.coeffExt A A' ψ N) (MvPolynomial.X i))) :
    dehomHom A' N i x = 1 := by
  obtain ⟨k, hk⟩ := hx
  rw [← hk, map_pow, dehomHom_coeffExt_X A A' ψ N i, one_pow]

lemma dehomHom_isUnitT
    (s : Submonoid.powers ((Work.DSG4c.coeffExt A A' ψ N) (MvPolynomial.X i))) :
    IsUnit (dehomHom A' N i (s : MvPolynomial (Fin (N+1)) A')) := by
  rw [dehomHom_eq_one_of_mem_powersT A A' ψ N i s.2]
  exact isUnit_one

/-- Dehomogenization out of the localization at `coeffExt ψ (X i)`. -/
noncomputable def dehomLiftT :
    Localization (Submonoid.powers ((Work.DSG4c.coeffExt A A' ψ N) (MvPolynomial.X i))) →+*
      MvPolynomial (chartIdx N i) A' :=
  IsLocalization.lift (R := MvPolynomial (Fin (N+1)) A')
    (M := Submonoid.powers ((Work.DSG4c.coeffExt A A' ψ N) (MvPolynomial.X i)))
    (S := Localization (Submonoid.powers
      ((Work.DSG4c.coeffExt A A' ψ N) (MvPolynomial.X i))))
    (P := MvPolynomial (chartIdx N i) A') (dehomHom_isUnitT A A' ψ N i)

lemma dehomLiftT_algebraMap (x : MvPolynomial (Fin (N+1)) A') :
    dehomLiftT A A' ψ N i ((algebraMap (MvPolynomial (Fin (N+1)) A')
        (Localization (Submonoid.powers
          ((Work.DSG4c.coeffExt A A' ψ N) (MvPolynomial.X i))))) x) =
      dehomHom A' N i x :=
  IsLocalization.lift_eq (dehomHom_isUnitT A A' ψ N i) x

lemma dehomLiftT_mk' (x : MvPolynomial (Fin (N+1)) A')
    (s : Submonoid.powers ((Work.DSG4c.coeffExt A A' ψ N) (MvPolynomial.X i))) :
    dehomLiftT A A' ψ N i (IsLocalization.mk' (Localization
        (Submonoid.powers ((Work.DSG4c.coeffExt A A' ψ N) (MvPolynomial.X i)))) x s) =
      dehomHom A' N i x := by
  have key := congrArg (dehomLiftT A A' ψ N i) (IsLocalization.mk'_spec
    (M := Submonoid.powers ((Work.DSG4c.coeffExt A A' ψ N) (MvPolynomial.X i)))
    (S := Localization (Submonoid.powers
      ((Work.DSG4c.coeffExt A A' ψ N) (MvPolynomial.X i)))) x s)
  rw [map_mul, dehomLiftT_algebraMap, dehomLiftT_algebraMap,
    dehomHom_eq_one_of_mem_powersT A A' ψ N i s.2, mul_one] at key
  exact key

/-- The inverse map `A'[x_j : j ≠ i] → Away (PGr A' N) (coeffExt ψ (X i))`. -/
noncomputable def chartToPolyT :
    MvPolynomial (chartIdx N i) A' →+* Work.DSG4c.awayChartT A A' ψ N i :=
  MvPolynomial.eval₂Hom (Work.DSG4c.chartMapT A A' ψ N i) (chartElemT A A' ψ N i)

/-- Dehomogenization `Away (PGr A' N) (coeffExt ψ (X i)) → A'[x_j : j ≠ i]`. -/
noncomputable def polyToChartT :
    Work.DSG4c.awayChartT A A' ψ N i →+* MvPolynomial (chartIdx N i) A' :=
  (dehomLiftT A A' ψ N i).comp
    (algebraMap (Work.DSG4c.awayChartT A A' ψ N i)
      (Localization (Submonoid.powers
        ((Work.DSG4c.coeffExt A A' ψ N) (MvPolynomial.X i)))))

lemma polyToChartT_mk (c : HomogeneousLocalization.NumDenSameDeg (DSMap.PGr A' N)
    (Submonoid.powers ((Work.DSG4c.coeffExt A A' ψ N) (MvPolynomial.X i)))) :
    polyToChartT A A' ψ N i (HomogeneousLocalization.mk c) =
      dehomHom A' N i (c.num : MvPolynomial (Fin (N+1)) A') := by
  rw [polyToChartT, RingHom.comp_apply, HomogeneousLocalization.algebraMap_apply,
    HomogeneousLocalization.val_mk, Localization.mk_eq_mk'_apply]
  exact dehomLiftT_mk' A A' ψ N i _ _

lemma polyToChartT_chartMapT (a : A') :
    polyToChartT A A' ψ N i (Work.DSG4c.chartMapT A A' ψ N i a) = MvPolynomial.C a := by
  have h : Work.DSG4c.chartMapT A A' ψ N i a = HomogeneousLocalization.mk
      (⟨0, algebraMap A' (DSMap.PGr A' N 0) a, 1, one_mem _⟩ :
        HomogeneousLocalization.NumDenSameDeg (DSMap.PGr A' N)
          (Submonoid.powers ((Work.DSG4c.coeffExt A A' ψ N) (MvPolynomial.X i)))) := rfl
  rw [h, polyToChartT_mk]
  simpa using dehomHom_C A' N i a

lemma polyToChartT_chartElem (j : chartIdx N i) :
    polyToChartT A A' ψ N i (chartElemT A A' ψ N i j) = MvPolynomial.X j := by
  have h : chartElemT A A' ψ N i j = HomogeneousLocalization.mk
      (⟨1, ⟨MvPolynomial.X j.1, X_mem A' N j.1⟩,
        ⟨((Work.DSG4c.coeffExt A A' ψ N) (MvPolynomial.X i)) ^ 1,
          SetLike.pow_mem_graded 1 ((Work.DSG4c.coeffExt A A' ψ N).2 (X_mem A N i))⟩,
        ⟨1, rfl⟩⟩ :
        HomogeneousLocalization.NumDenSameDeg (DSMap.PGr A' N)
          (Submonoid.powers ((Work.DSG4c.coeffExt A A' ψ N) (MvPolynomial.X i)))) := rfl
  rw [h, polyToChartT_mk]
  simpa using dehomHom_X_of_ne A' N i j.2

lemma chartToPolyT_C (a : A') :
    chartToPolyT A A' ψ N i (MvPolynomial.C a) = Work.DSG4c.chartMapT A A' ψ N i a :=
  MvPolynomial.eval₂Hom_C _ _ a

lemma chartToPolyT_X (j : chartIdx N i) :
    chartToPolyT A A' ψ N i (MvPolynomial.X j) = chartElemT A A' ψ N i j :=
  MvPolynomial.eval₂Hom_X' _ _ j

lemma polyToChartT_chartToPoly (x : MvPolynomial (chartIdx N i) A') :
    polyToChartT A A' ψ N i (chartToPolyT A A' ψ N i x) = x := by
  induction x using MvPolynomial.induction_on with
  | C a => rw [chartToPolyT_C, polyToChartT_chartMapT]
  | add p q hp hq => rw [map_add, map_add, hp, hq]
  | mul_X p j hp => rw [map_mul, chartToPolyT_X, map_mul, hp, polyToChartT_chartElem]

end Work.DSG4c.ChartPushout
