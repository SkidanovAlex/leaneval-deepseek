import Submission.Work.DSG4c.Basic

/-!
# Chart pushout (area DSG4c): dehomogenization of the standard charts of `ℙᴺ`

Auxiliary definitions and lemmas identifying the standard chart
`Away (PGr A N) (X i)` of `ℙᴺ_A` with the polynomial ring `A[x_j : j ≠ i]`
(`x_j ↦ X_j / X i`), together with functoriality in the coefficient ring.
-/

open CategoryTheory AlgebraicGeometry Limits MvPolynomial
-- We install the canonical grading of `MvPolynomial` as a *global* instance: everything in this
-- file (and in files importing it) lives in that graded setting, and making it global lets the
-- statements about `Away (PGr A N) (X i)` and its coefficient extension elaborate on their own.
attribute [instance] MvPolynomial.gradedAlgebra

namespace Work.DSG4c.ChartPushout

universe u

variable (A : Type u) [CommRing A] (N : ℕ) (i : Fin (N+1))

/-- The index set of the variables different from `i`. -/
abbrev chartIdx (N : ℕ) (i : Fin (N+1)) := {j : Fin (N+1) // j ≠ i}

/-- The element `X k / X i` of the `i`-th standard chart ring, for any `k`. -/
noncomputable def chartElemAll (k : Fin (N+1)) : Work.DSG4c.awayChart A N i :=
  HomogeneousLocalization.Away.mk (DSMap.PGr A N) (X_mem A N i) 1 (MvPolynomial.X k)
    (X_mem A N k)

/-- The element `X j / X i` of the `i`-th standard chart ring, for `j ≠ i`. -/
noncomputable def chartElem (j : chartIdx N i) : Work.DSG4c.awayChart A N i :=
  chartElemAll A N i j.1

lemma chartElem_eq_chartElemAll (j : chartIdx N i) :
    chartElem A N i j = chartElemAll A N i j.1 := rfl

/-- Dehomogenization `A[x₀,…,x_N] → A[x_j : j ≠ i]`, `X_i ↦ 1`, `X_j ↦ X_j`. -/
noncomputable def dehomHom : MvPolynomial (Fin (N+1)) A →+* MvPolynomial (chartIdx N i) A :=
  MvPolynomial.eval₂Hom (MvPolynomial.C : A →+* MvPolynomial (chartIdx N i) A)
    (fun j => if h : j = i then 1 else MvPolynomial.X ⟨j, h⟩)

lemma dehomHom_X_self : dehomHom A N i (MvPolynomial.X i) = 1 := by
  rw [dehomHom, MvPolynomial.eval₂Hom_X']
  exact dif_pos rfl

lemma dehomHom_X_of_ne {j : Fin (N+1)} (hj : ¬ j = i) :
    dehomHom A N i (MvPolynomial.X j) = MvPolynomial.X ⟨j, hj⟩ := by
  rw [dehomHom, MvPolynomial.eval₂Hom_X']
  exact dif_neg hj

lemma dehomHom_pow_self (k : ℕ) : dehomHom A N i (MvPolynomial.X i ^ k) = 1 := by
  rw [map_pow, dehomHom_X_self, one_pow]

lemma dehomHom_C (a : A) : dehomHom A N i (MvPolynomial.C a) = MvPolynomial.C a :=
  MvPolynomial.eval₂Hom_C _ _ a

lemma dehomHom_eq_one_of_mem_powers {x : MvPolynomial (Fin (N+1)) A}
    (hx : x ∈ Submonoid.powers (MvPolynomial.X (R := A) i)) : dehomHom A N i x = 1 := by
  obtain ⟨k, hk⟩ := hx
  rw [← hk]
  exact dehomHom_pow_self A N i k

lemma dehomHom_isUnit (s : Submonoid.powers (MvPolynomial.X (R := A) i)) :
    IsUnit (dehomHom A N i (s : MvPolynomial (Fin (N+1)) A)) := by
  rw [dehomHom_eq_one_of_mem_powers A N i s.2]
  exact isUnit_one

/-- Dehomogenization as a ring homomorphism out of the (exponential) localization. -/
noncomputable def dehomLift :
    Localization (Submonoid.powers (MvPolynomial.X (R := A) i)) →+*
      MvPolynomial (chartIdx N i) A :=
  IsLocalization.lift (R := MvPolynomial (Fin (N+1)) A)
    (M := Submonoid.powers (MvPolynomial.X (R := A) i))
    (S := Localization (Submonoid.powers (MvPolynomial.X (R := A) i)))
    (P := MvPolynomial (chartIdx N i) A) (dehomHom_isUnit A N i)

lemma dehomLift_algebraMap (x : MvPolynomial (Fin (N+1)) A) :
    dehomLift A N i ((algebraMap (MvPolynomial (Fin (N+1)) A)
        (Localization (Submonoid.powers (MvPolynomial.X (R := A) i)))) x) =
      dehomHom A N i x :=
  IsLocalization.lift_eq (dehomHom_isUnit A N i) x

lemma dehomLift_mk' (x : MvPolynomial (Fin (N+1)) A)
    (s : Submonoid.powers (MvPolynomial.X (R := A) i)) :
    dehomLift A N i (IsLocalization.mk' (Localization
        (Submonoid.powers (MvPolynomial.X (R := A) i))) x s) = dehomHom A N i x := by
  have key := congrArg (dehomLift A N i) (IsLocalization.mk'_spec (M := Submonoid.powers
    (MvPolynomial.X (R := A) i)) (S := Localization (Submonoid.powers
      (MvPolynomial.X (R := A) i))) x s)
  rw [map_mul, dehomLift_algebraMap, dehomLift_algebraMap,
    dehomHom_eq_one_of_mem_powers A N i s.2, mul_one] at key
  exact key

/-- The inverse map `A[x_j : j ≠ i] → Away (PGr A N) (X i)`, `X_j ↦ X_j / X_i`. -/
noncomputable def chartToPoly :
    MvPolynomial (chartIdx N i) A →+* Work.DSG4c.awayChart A N i :=
  MvPolynomial.eval₂Hom (Work.DSG4c.chartMap A N i) (chartElem A N i)

/-- Dehomogenization `Away (PGr A N) (X i) → A[x_j : j ≠ i]`. -/
noncomputable def polyToChart :
    Work.DSG4c.awayChart A N i →+* MvPolynomial (chartIdx N i) A :=
  (dehomLift A N i).comp
    (algebraMap (Work.DSG4c.awayChart A N i)
      (Localization (Submonoid.powers (MvPolynomial.X (R := A) i))))

lemma polyToChart_mk (c : HomogeneousLocalization.NumDenSameDeg (DSMap.PGr A N)
    (Submonoid.powers (MvPolynomial.X (R := A) i))) :
    polyToChart A N i (HomogeneousLocalization.mk c) =
      dehomHom A N i (c.num : MvPolynomial (Fin (N+1)) A) := by
  rw [polyToChart, RingHom.comp_apply, HomogeneousLocalization.algebraMap_apply,
    HomogeneousLocalization.val_mk, Localization.mk_eq_mk'_apply]
  exact dehomLift_mk' A N i _ _

lemma polyToChart_chartMap (a : A) :
    polyToChart A N i (Work.DSG4c.chartMap A N i a) = MvPolynomial.C a := by
  have h : Work.DSG4c.chartMap A N i a = HomogeneousLocalization.mk
      (⟨0, algebraMap A (DSMap.PGr A N 0) a, 1, one_mem _⟩ :
        HomogeneousLocalization.NumDenSameDeg (DSMap.PGr A N)
          (Submonoid.powers (MvPolynomial.X (R := A) i))) := rfl
  rw [h, polyToChart_mk]
  simpa using dehomHom_C A N i a

lemma polyToChart_chartElem (j : chartIdx N i) :
    polyToChart A N i (chartElem A N i j) = MvPolynomial.X j := by
  have h : chartElem A N i j = HomogeneousLocalization.mk
      (⟨1, ⟨MvPolynomial.X j.1, X_mem A N j.1⟩,
        ⟨MvPolynomial.X i ^ 1, SetLike.pow_mem_graded 1 (X_mem A N i)⟩, ⟨1, rfl⟩⟩ :
        HomogeneousLocalization.NumDenSameDeg (DSMap.PGr A N)
          (Submonoid.powers (MvPolynomial.X (R := A) i))) := rfl
  rw [h, polyToChart_mk]
  simpa using dehomHom_X_of_ne A N i j.2

lemma chartToPoly_C (a : A) :
    chartToPoly A N i (MvPolynomial.C a) = Work.DSG4c.chartMap A N i a :=
  MvPolynomial.eval₂Hom_C _ _ a

lemma chartToPoly_X (j : chartIdx N i) :
    chartToPoly A N i (MvPolynomial.X j) = chartElem A N i j :=
  MvPolynomial.eval₂Hom_X' _ _ j

lemma polyToChart_chartToPoly (x : MvPolynomial (chartIdx N i) A) :
    polyToChart A N i (chartToPoly A N i x) = x := by
  induction x using MvPolynomial.induction_on with
  | C a => rw [chartToPoly_C, polyToChart_chartMap]
  | add p q hp hq => rw [map_add, map_add, hp, hq]
  | mul_X p j hp => rw [map_mul, chartToPoly_X, map_mul, hp, polyToChart_chartElem]

lemma polyToChart_comp_chartToPoly :
    (polyToChart A N i).comp (chartToPoly A N i) = RingHom.id _ :=
  RingHom.ext (polyToChart_chartToPoly A N i)

end Work.DSG4c.ChartPushout
