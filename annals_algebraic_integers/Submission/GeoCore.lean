import Mathlib
import Mathlib.Algebra.Module.ZLattice.Covolume
import Mathlib.MeasureTheory.Group.GeometryOfNumbers
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.LinearAlgebra.BilinearForm.DualLattice
import Submission.LatticeDefs
import Submission.GeoFinal

noncomputable section

open scoped BigOperators

/-!
# Geometric core of the covering lemma (`covering_of_dual`)

Given an invertible real matrix `B : Matrix (Fin n) (Fin n) ℝ` whose integer image
satisfies the **dual condition**

    ∀ nonzero integer vector d : ∃ i, 1 ≤ |∑ j, B i j * d j|           (∗)

(equivalently: no nonzero point of the lattice `B·ℤⁿ` lies in the open cube `(−1,1)ⁿ`,
i.e. the ℓ∞-norm first minimum of `M* := B·ℤⁿ` is ≥ 1), prove the following lattice
covering statement for the lattice

    M := {x : Fin n → ℝ | Bᵀ·x ∈ ℤⁿ}   (i.e. ∀ i, ∑ j, B j i * x j ∈ ℤ)

(the β-coordinates of integer polynomials in the real basis whose coefficient matrix is B):
for every real vector `p` there is a vector `β` with `p − Bᵀ·β` integer-valued and
`∑ i |β i| ≤ n^C` for an absolute constant `C` (independent of `n`).  We fix `C0 := 100`.
-/

namespace Submission.GeoCore

open scoped BigOperators RealInnerProductSpace
open Module Submodule MeasureTheory MeasureTheory.Measure Metric Filter

/-! ## Dual lattices in finite-dimensional real inner product spaces -/



section Volume

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

-- the fundamental domain of a real basis is well-behaved for volume
lemma measureReal_fundamentalDomain_of_isAddHaar {μ : Measure E} [μ.IsAddHaarMeasure]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b b₀ : Basis ι ℝ E) :
    μ.real (ZSpan.fundamentalDomain b) = |b₀.det b| * μ.real (ZSpan.fundamentalDomain b₀) := by
  simpa using ZSpan.measureReal_fundamentalDomain b μ b₀

end Volume

section Covol

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [ProperSpace E] [MeasurableSpace E] [BorelSpace E]

/-- covolume of a lattice = volume of the fundamental domain of the real extension of a Z-basis -/
lemma covol_eq_fund {ι : Type*} [Fintype ι] [DecidableEq ι] (Λ : Submodule ℤ E) [DiscreteTopology Λ]
    [IsZLattice ℝ Λ] (bz : Basis ι ℤ Λ) :
    ZLattice.covolume Λ = (volume.real (ZSpan.fundamentalDomain (bz.ofZLatticeBasis ℝ))) := by
  exact ZLattice.covolume_eq_measure_fundamentalDomain (μ := volume) Λ
    (ZLattice.isAddFundamentalDomain (μ := volume) bz)

end Covol
/-- Geometric core: under the dual condition, every `p` differs from `Bᵀ·β` by an integer
vector with `‖β‖₁ ≤ n^100`. -/
theorem geo_core (n : ℕ) (hn : 1 ≤ n) (B : Matrix (Fin n) (Fin n) ℝ)
    (hB : B.det ≠ 0)
    (hdual : ∀ d : Fin n → ℤ, d ≠ 0 → ∃ i : Fin n, (1 : ℝ) ≤ |∑ j : Fin n, B i j * (d j : ℝ)|) :
    ∃ C0 : ℝ, 0 < C0 ∧ C0 ≤ 100 ∧
      ∀ p : Fin n → ℝ,
        ∃ β : Fin n → ℝ,
          (∀ i : Fin n, ∃ z : ℤ, (p i - ∑ j : Fin n, B j i * β j) = (z : ℝ)) ∧
          (∑ i : Fin n, |β i|) ≤ (n : ℝ) ^ C0 := by
  exact Submission.GeoFinal.geo_core_main n hn B hB hdual



/-! ## Basic norm estimates for functions -/

section FuncNorm

lemma sum_abs_sq_le_card_mul {ι : Type*} [Fintype ι] (f : ι → ℝ) :
    (∑ i, |f i|) ^ 2 ≤ (Fintype.card ι : ℝ) * ∑ i, (f i) ^ 2 := by
  have h := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun i : ι => |f i|)
  simpa [abs_pow, sq, Finset.card_univ] using h

lemma sum_abs_le_sqrt_card_mul {ι : Type*} [Fintype ι] (f : ι → ℝ) :
    ∑ i, |f i| ≤ Real.sqrt (Fintype.card ι) * Real.sqrt (∑ i, (f i) ^ 2) := by
  have hsq : (∑ i, |f i|) ^ 2 ≤ (Fintype.card ι : ℝ) * ∑ i, (f i) ^ 2 := sum_abs_sq_le_card_mul f
  have hsqrt := Real.sqrt_le_sqrt hsq
  have hleft : Real.sqrt ((∑ i, |f i|) ^ 2) = ∑ i, |f i| := by
    rw [Real.sqrt_sq]
    positivity
  have hright : Real.sqrt ((Fintype.card ι : ℝ) * ∑ i, (f i) ^ 2) =
      Real.sqrt (Fintype.card ι) * Real.sqrt (∑ i, (f i) ^ 2) := by
    rw [Real.sqrt_mul]
    positivity
  rwa [hleft, hright] at hsqrt

lemma sum_abs_le_nat_mul_sqrt {ι : Type*} [Fintype ι] (f : ι → ℝ) (hcard : 1 ≤ Fintype.card ι) :
    ∑ i, |f i| ≤ (Fintype.card ι : ℝ) * Real.sqrt (∑ i, (f i) ^ 2) := by
  have h0 := sum_abs_le_sqrt_card_mul f
  have hc : (1 : ℝ) ≤ (Fintype.card ι : ℝ) := by exact_mod_cast hcard
  have hsqrt : Real.sqrt (Fintype.card ι : ℝ) ≤ (Fintype.card ι : ℝ) := by
    rw [Real.sqrt_le_iff]
    constructor
    · positivity
    · nlinarith [sq_nonneg ((Fintype.card ι : ℝ) - 1), hc]
  have hs : 0 ≤ Real.sqrt (∑ i, (f i) ^ 2) := Real.sqrt_nonneg _
  nlinarith

end FuncNorm

end Submission.GeoCore
