import Mathlib
import Submission.Work.Holonomy3.aux_defs

/-!
# `Work.Holonomy3.polyIndepPolyCoeff`

**Polynomial-coefficient independence.**  Let `R` be a commutative `ℚ`-algebra, `g : Fin m → ℚ⟦x⟧`
a `ℚ(x)`-linearly independent family (`Submission.CDTPlan.PolyIndependent g`), and
`B a ∈ R[x]` polynomials with `Σ_a (g a).map (algebraMap ℚ R) · B_a = 0` in `R⟦x⟧`.  Then every
`B a = 0`.

The proof extracts the coefficient of `x^n` of the relation, expands every `B_a.coeff j ∈ R` in a
`ℚ`-basis `b` of `R` (`Module.Free.of_divisionRing` + `Module.Free.chooseBasis`), and — for each
basis vector — reads off a relation `Σ_a g_a · (Σ_j (b.repr (B_a.coeff j)) ι · x^j) = 0` in
`ℚ⟦x⟧`, to which `PolyIndependent g` applies.
-/

noncomputable section

open PowerSeries Polynomial
open scoped BigOperators

namespace Work.Holonomy3

namespace PolyIndepPC

/-- The expansion of `p ∈ R[x]` in the `ℚ`-basis `b` of `R`: the coefficient of the basis vector
`b i` is the polynomial `Σ_j (b.repr (p.coeff j)) i · x^j ∈ ℚ[x]`. -/
def expandCoeff {R : Type*} {ι : Type*} [CommRing R] [Algebra ℚ R]
    (b : Module.Basis ι ℚ R) (p : Polynomial R) (i : ι) : Polynomial ℚ :=
  ∑ j ∈ p.support, Polynomial.monomial j (b.repr (p.coeff j) i)

/-- The defining property of `expandCoeff`: its `j`-th coefficient is the `i`-th coordinate of
`p.coeff j` in the basis `b`. -/
lemma expandCoeff_coeff {R : Type*} {ι : Type*} [CommRing R] [Algebra ℚ R]
    (b : Module.Basis ι ℚ R) (p : Polynomial R) (i : ι) (j : ℕ) :
    (expandCoeff b p i).coeff j = b.repr (p.coeff j) i := by
  rw [expandCoeff]
  rw [← Polynomial.lcoeff_apply, map_sum]
  simp only [Polynomial.lcoeff_apply, Polynomial.coeff_monomial]
  rw [Finset.sum_ite_eq']
  by_cases hj : j ∈ p.support
  · simp [hj]
  · have hz : p.coeff j = 0 := by
      by_contra hc
      exact hj ((Polynomial.mem_support_iff).mpr hc)
    rw [if_neg hj, hz, map_zero]
    simp

/-- Coefficient of `x^n` of `f · (expandCoeff b p i)`, with `f ∈ ℚ⟦x⟧` and `p ∈ R[x]`. -/
lemma coeff_mul_expand {R : Type*} {ι : Type*} [CommRing R] [Algebra ℚ R]
    (b : Module.Basis ι ℚ R) (f : PowerSeries ℚ) (p : Polynomial R) (i : ι) (n : ℕ) :
    PowerSeries.coeff n (f * (↑(expandCoeff b p i) : PowerSeries ℚ))
      = ∑ k ∈ Finset.range (n + 1), f.coeff k * b.repr (p.coeff (n - k)) i := by
  rw [PowerSeries.coeff_mul]
  simp only [Polynomial.coeff_coe]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ
        (fun k j => PowerSeries.coeff k f * (expandCoeff b p i).coeff j) n]
  refine Finset.sum_congr rfl ?_
  intro k _
  rw [expandCoeff_coeff]

/-- The `b.repr`-coordinates of the `n`-th coefficient of `(f.map) · p` in `R⟦x⟧`. -/
lemma repr_coeff_mul {R : Type*} {ι : Type*} [CommRing R] [Algebra ℚ R]
    (b : Module.Basis ι ℚ R) (f : PowerSeries ℚ) (p : Polynomial R) (n : ℕ) :
    b.repr (PowerSeries.coeff n (PowerSeries.map (algebraMap ℚ R) f * (↑p : PowerSeries R)))
      = ∑ k ∈ Finset.range (n + 1), f.coeff k • b.repr (p.coeff (n - k)) := by
  rw [PowerSeries.coeff_mul]
  simp only [PowerSeries.coeff_map, Polynomial.coeff_coe]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ
        (fun k j => algebraMap ℚ R (PowerSeries.coeff k f) * p.coeff j) n]
  rw [map_sum]
  refine Finset.sum_congr rfl ?_
  intro k _
  rw [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, map_smul]

end PolyIndepPC

open PolyIndepPC

/-- **Polynomial-coefficient independence.**  Let `R` be a commutative `ℚ`-algebra and let
`g : Fin m → ℚ⟦x⟧` be `ℚ(x)`-linearly independent (i.e. `PolyIndependent g`: `Σ_a P_a · g_a = 0`
with `P_a ∈ ℚ[x]` forces all `P_a = 0`).  If `B a ∈ R[x]` satisfy
`Σ_a (g a).map (algebraMap ℚ R) · B_a = 0` in `R⟦x⟧`, then every `B a = 0`.

(The hypothesis must be `PolyIndependent` and NOT mere `ℚ`-linear independence: `g_0 = 1`,
`g_1 = x`, `B_0 = x`, `B_1 = -1`, `R = ℚ` is a counterexample with `ℚ`-linear independence only.
Proof route: extract the coefficient of `x^n`; expand each `B_a.coeff j ∈ R` in a `ℚ`-basis `e` of
`R` (`Module.Free.of_divisionRing` + `Module.Free.chooseBasis`, `R` being a module over the field
`ℚ`); for each basis vector apply `PolyIndependent` to the resulting relation
`Σ_a g_a · (Σ_j (e.repr (B_a.coeff j)) ι · x^j) = 0` in `ℚ⟦x⟧`.) -/
lemma polyIndepPolyCoeff {m : ℕ} {R : Type*} [CommRing R] [Algebra ℚ R]
    (g : Fin m → PowerSeries ℚ) (hg : Submission.CDTPlan.PolyIndependent g)
    (B : Fin m → Polynomial R)
    (h : ∑ a, PowerSeries.map (algebraMap ℚ R) (g a) * (↑(B a) : PowerSeries R) = 0) :
    ∀ a, B a = 0 := by
  classical
  -- a `ℚ`-basis of `R`
  let b : Module.Basis (Module.Free.ChooseBasisIndex ℚ R) ℚ R := Module.Free.chooseBasis ℚ R
  -- For each basis vector `i`, `Σ_a g_a · (expandCoeff b (B a) i) = 0` in `ℚ⟦x⟧`.
  have hkey : ∀ i : Module.Free.ChooseBasisIndex ℚ R,
      (∑ a, g a * (↑(PolyIndepPC.expandCoeff b (B a) i) : PowerSeries ℚ)) = 0 := by
    intro i
    apply PowerSeries.ext
    intro n
    simp only [map_zero]
    -- coefficients of `Σ_a g_a · (expandCoeff b (B a) i)`
    have hL : PowerSeries.coeff n (∑ a, g a * (↑(PolyIndepPC.expandCoeff b (B a) i) : PowerSeries ℚ))
        = ∑ a, ∑ k ∈ Finset.range (n + 1), (g a).coeff k * b.repr ((B a).coeff (n - k)) i := by
      rw [map_sum]
      refine Finset.sum_congr rfl ?_
      intro a _
      rw [PolyIndepPC.coeff_mul_expand]
    -- the same sum, obtained from the hypothesis `h`
    have hzero : b.repr (PowerSeries.coeff n
        (∑ a, PowerSeries.map (algebraMap ℚ R) (g a) * (↑(B a) : PowerSeries R))) i = 0 := by
      rw [h]; simp
    have hR : (∑ a, ∑ k ∈ Finset.range (n + 1),
        (g a).coeff k * b.repr ((B a).coeff (n - k)) i) = 0 := by
      rw [← hzero]
      simp only [map_sum, Finsupp.coe_finsetSum, Finset.sum_apply]
      refine Finset.sum_congr rfl ?_
      intro a _
      rw [PolyIndepPC.repr_coeff_mul]
      simp only [Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.smul_apply]
      refine Finset.sum_congr rfl ?_
      intro k _
      rw [smul_eq_mul]
    rw [hL, hR]
  -- Apply `PolyIndependent` to each basis vector.
  have hQzero : ∀ (i : Module.Free.ChooseBasisIndex ℚ R) (a : Fin m),
      PolyIndepPC.expandCoeff b (B a) i = 0 := by
    intro i
    have hT' : ∑ a, (↑(PolyIndepPC.expandCoeff b (B a) i) : PowerSeries ℚ) * g a = 0 := by
      rw [← hkey i]
      exact Finset.sum_congr rfl (fun a _ => mul_comm _ _)
    exact hg (fun a => PolyIndepPC.expandCoeff b (B a) i) hT'
  -- Read off `B a = 0`.
  intro a
  apply Polynomial.ext
  intro j
  have h1 : (B a).coeff j = 0 := by
    have h2 : b.repr ((B a).coeff j) = 0 := by
      ext i
      rw [← PolyIndepPC.expandCoeff_coeff b (B a) i j, hQzero i a]
      simp
    exact b.repr.injective (by rw [h2, map_zero])
  rw [h1]
  simp

end Work.Holonomy3
