import Mathlib
import Submission.Work.DSG4c.ChartPushout.Defs
import Submission.Work.DSG4c.ChartPushout.prod_chartElemAll
import Submission.Work.DSG4c.ChartPushout.algebra_adjoin_range_X

namespace Work.DSG4c.ChartPushout

universe u

open MvPolynomial HomogeneousLocalization

variable (A : Type u) [CommRing A] (N : ℕ) (i : Fin (N+1))

/-- The "coordinate" `X i / X i` of the `i`-th chart is `1`. -/
lemma chartElemAll_self : chartElemAll A N i i = 1 := by
  rw [chartElemAll]
  apply HomogeneousLocalization.val_injective (Submonoid.powers (MvPolynomial.X (R := A) i))
  rw [Away.val_mk, HomogeneousLocalization.val_one, Localization.mk_eq_mk'_apply,
    IsLocalization.mk'_eq_iff_eq_mul]
  simp

/-- Every element of the degree-zero part `A = PGr A N 0` of the polynomial ring, viewed in the
`i`-th chart via the structure map, lies in the range of `chartToPoly`.

Indeed `y` is a constant polynomial `C a` (degree-zero homogeneity), and `a` maps to
`chartToPoly (C a)`. -/
lemma algebraMap_zero_mem_range (y : DSMap.PGr A N 0) :
    algebraMap (DSMap.PGr A N 0) (Work.DSG4c.awayChart A N i) y
      ∈ (chartToPoly A N i).range := by
  have hdeg : (y : MvPolynomial (Fin (N+1)) A).totalDegree = 0 :=
    (MvPolynomial.totalDegree_zero_iff_isHomogeneous (Fin (N+1))).mpr y.2
  refine ⟨MvPolynomial.C (y.1.coeff 0), ?_⟩
  rw [chartToPoly_C]
  rw [Work.DSG4c.chartMap, HomogeneousLocalization.algebraMap_eq, RingHom.comp_apply]
  congr 1
  apply Subtype.ext
  rw [SetLike.GradeZero.coe_algebraMap, MvPolynomial.algebraMap_eq]
  exact (MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp hdeg).symm

/-- Each `X k / X i` is in the range of `chartToPoly` (for `k = i` it is `1`). -/
lemma chartElemAll_mem_range (k : Fin (N+1)) :
    chartElemAll A N i k ∈ (chartToPoly A N i).range := by
  by_cases hk : k = i
  · subst hk
    rw [chartElemAll_self]
    exact ⟨1, map_one _⟩
  · exact ⟨MvPolynomial.X ⟨k, hk⟩, by rw [chartToPoly_X]; rfl⟩

/-- The `A`-algebra `Away (PGr A N) (X i)` is generated over `PGr A N 0` by the elements
`X k / X i`.

This is `Away.adjoin_mk_prod_pow_eq_top` for the polynomial ring with the generators `X k`
of degree `1` (`algebra_adjoin_range_X`), combined with the monomial identity `prod_chartElemAll`
identifying the products `∏ X k ^ (a k) / X i ^ a` with products of the `X k / X i`. -/
lemma adjoin_range_chartElemAll :
    Algebra.adjoin (DSMap.PGr A N 0) (Set.range (chartElemAll A N i)) = ⊤ := by
  have h := Away.adjoin_mk_prod_pow_eq_top (Work.DSG4c.X_mem A N i) (Fin (N+1))
      (fun k => MvPolynomial.X k) (algebra_adjoin_range_X A N)
      (fun _ => 1) (fun k => Work.DSG4c.X_mem A N k)
  rw [eq_top_iff, ← h]
  apply Algebra.adjoin_le_iff.mpr
  rintro x ⟨a, ai, hai, hle, rfl⟩
  have hae : a = ∑ k, ai k := by simpa using hai.symm
  subst hae
  rw [← prod_chartElemAll A N i ai (hai ▸ SetLike.prod_pow_mem_graded _ _ _ _
    fun i _ => Work.DSG4c.X_mem A N i)]
  exact Subalgebra.prod_mem _
    (fun k _ => pow_mem (Algebra.subset_adjoin (Set.mem_range_self k)) _)

/-- **The dehomogenization `A[x_j : j ≠ i] → Away (PGr A N) (X i)`, `x_j ↦ X_j / X_i`, is
surjective**: every element of the `i`-th standard chart of `ℙᴺ_A` is a polynomial in the
coordinates `X_j / X_i` (`j ≠ i`). -/
theorem chartToPoly_surjective (A : Type u) [CommRing A] (N : ℕ) (i : Fin (N+1)) :
    Function.Surjective (Work.DSG4c.ChartPushout.chartToPoly A N i) := by
  rw [← RingHom.range_eq_top]
  rw [eq_top_iff]
  intro y _
  have hle : Subsemiring.closure
      (Set.range (algebraMap (DSMap.PGr A N 0) (Work.DSG4c.awayChart A N i))
        ∪ Set.range (chartElemAll A N i)) ≤ (chartToPoly A N i).range.toSubsemiring := by
    rw [Subsemiring.closure_le]
    rintro x (hx | hx)
    · obtain ⟨z, rfl⟩ := hx
      exact algebraMap_zero_mem_range A N i z
    · obtain ⟨k, rfl⟩ := hx
      exact chartElemAll_mem_range A N i k
  have hy' : y ∈ Subsemiring.closure
      (Set.range (algebraMap (DSMap.PGr A N 0) (Work.DSG4c.awayChart A N i))
        ∪ Set.range (chartElemAll A N i)) := by
    have hy : y ∈ Algebra.adjoin (DSMap.PGr A N 0) (Set.range (chartElemAll A N i)) := by
      rw [adjoin_range_chartElemAll]; trivial
    exact hy
  exact hle hy'

end Work.DSG4c.ChartPushout
