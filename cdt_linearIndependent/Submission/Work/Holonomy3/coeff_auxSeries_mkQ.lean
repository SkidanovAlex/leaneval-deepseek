import Mathlib
import Submission.Work.Holonomy3.siegelDefs
import Submission.Work.Holonomy3.coeff_auxSeries
import Submission.Work.Holonomy3.sum_support_mkQ

namespace Work.Holonomy3

open Submission.CDTPlan Submission.CDT.Discrepancy
open scoped BigOperators

/-!
# Coefficients of the auxiliary template `Q = mkQ y`

The general coefficient formula `Work.Holonomy3.coeff_auxSeries` expands the coefficient at `n` of
`auxSeries f Q` as a sum over the species vectors `i : Fin d → Fin m` and the monomials
`k ∈ (Q i).support` with the guard `k ≤ n`.  For the concrete template `Q = mkQ y` of the box
principle (`siegelDefs.mkQ`, whose monomials are indexed by the low-discrepancy exponents
`k ∈ P_ε^d ∩ [0,D]^d` with coefficient `y (i,k)`), the support reindexes bijectively onto
`P_ε^d ∩ [0,D]^d`, and the double sum collapses to a single sum over the column index type
`ColIdx d D ε m` of the linear system.
-/

/-- The `if k ≤ n` guard of `coeff_auxSeries` splits into the coordinatewise guards: since
`k ≤ n` for Finsupps is pointwise, either all coordinates satisfy `k s ≤ n s` or one factor of the
product vanishes. -/
private lemma if_le_mul_prod {d : ℕ} (k n : Fin d →₀ ℕ) (A : Fin d → ℚ) (c : ℚ) :
    (if k ≤ n then c * ∏ s, A s else 0) = c * ∏ s, (if k s ≤ n s then A s else 0) := by
  by_cases h : k ≤ n
  · rw [if_pos h]
    congr 1
    exact Finset.prod_congr rfl (fun s _ => by rw [if_pos (Finsupp.le_def.mp h s)])
  · rw [if_neg h]
    have hex : ∃ s, ¬ k s ≤ n s := by
      by_contra hc
      simp only [not_exists, not_not] at hc
      exact h (Finsupp.le_def.mpr hc)
    obtain ⟨s, hs⟩ := hex
    rw [Finset.prod_eq_zero (Finset.mem_univ s) (if_neg hs), mul_zero]

/-- Sums over the column index type `ColIdx d D ε m` (a subtype of a product, with the `Fintype`
instance coming from `Set.Finite.fintype`) as sums over the product finset
`balSet d m ×ˢ lowSet d D ε`. -/
private lemma sum_colIdx {m d : ℕ} {D : ℕ} {ε : ℝ} {M : Type*} [AddCommMonoid M]
    (F : ColIdx d D ε m → M) :
    (∑ p : ColIdx d D ε m, F p) =
      ∑ q ∈ (balSet d m).product (lowSet d D ε),
        (if hq : q.1 ∈ balSet d m ∧ q.2 ∈ lowSet d D ε then F ⟨q, hq⟩ else 0) := by
  rw [Finset.sum_subtype (p := fun q : (Fin d → Fin m) × (Fin d → ℕ) =>
          q.1 ∈ balSet d m ∧ q.2 ∈ lowSet d D ε)
        (s := (balSet d m).product (lowSet d D ε)) (h := fun q => Finset.mem_product)
        (f := fun q => if hq : q.1 ∈ balSet d m ∧ q.2 ∈ lowSet d D ε then F ⟨q, hq⟩ else 0)
        (F := colIdxFintype d D ε m)]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [dif_pos a.2]

/-- The integer vector `y`, regarded as a rational number on the product
`(Fin d → Fin m) × (Fin d → ℕ)`, made total by sending the pairs outside `balSet ×ˢ lowSet` to `0`. -/
private noncomputable def yCast {m d : ℕ} {D : ℕ} {ε : ℝ} (y : ColIdx d D ε m → ℤ)
    (q : (Fin d → Fin m) × (Fin d → ℕ)) : ℚ :=
  if hq : q.1 ∈ balSet d m ∧ q.2 ∈ lowSet d D ε then (y ⟨q, hq⟩ : ℚ) else 0

private lemma yCast_eq {m d : ℕ} {D : ℕ} {ε : ℝ} (y : ColIdx d D ε m → ℤ)
    (q : (Fin d → Fin m) × (Fin d → ℕ)) (hq : q.1 ∈ balSet d m ∧ q.2 ∈ lowSet d D ε) :
    yCast y q = (y ⟨q, hq⟩ : ℚ) := by
  rw [yCast, dif_pos hq]

/-- The scalar coefficient `∏_s [x_s^{n_s - k_s}] f_{i_s}` attached to the pair `(i,k)`, with the
convention `[x_s^{m}] f = 0` for `m < 0`. -/
private noncomputable def Bcoeff {m d : ℕ} (f : Fin m → PowerSeries ℚ) (n : Fin d →₀ ℕ)
    (i : Fin d → Fin m) (k : Fin d → ℕ) : ℚ :=
  ∏ s : Fin d, (if k s ≤ n s then PowerSeries.coeff (n s - k s) (f (i s)) else 0)

/-- The inner sum of `coeff_auxSeries` at the species vector `i`. -/
private noncomputable def InnerSum {m d : ℕ} (f : Fin m → PowerSeries ℚ) (D : ℕ) (ε : ℝ)
    (y : ColIdx d D ε m → ℤ) (n : Fin d →₀ ℕ) (i : Fin d → Fin m) : ℚ :=
  ∑ k ∈ (mkQ y i).support,
    (if k ≤ n then ((mkQ y i).coeff k : ℚ) *
      ∏ s : Fin d, PowerSeries.coeff (n s - k s) (f (i s)) else 0)

private lemma InnerSum_apply {m d : ℕ} (f : Fin m → PowerSeries ℚ) (D : ℕ) (ε : ℝ)
    (y : ColIdx d D ε m → ℤ) (n : Fin d →₀ ℕ) (i : Fin d → Fin m) :
    InnerSum f D ε y n i =
      ∑ k ∈ (mkQ y i).support,
        (if k ≤ n then ((mkQ y i).coeff k : ℚ) *
          ∏ s : Fin d, PowerSeries.coeff (n s - k s) (f (i s)) else 0) := rfl

/-- The system coefficient `sysCoeffFun f (fun s => n s) (i,k)` is the product of the coefficients
of the `f (i s)`. -/
private lemma sysCoeffFun_eq_Bcoeff {m d : ℕ} (f : Fin m → PowerSeries ℚ) (n : Fin d →₀ ℕ)
    (i : Fin d → Fin m) (k : Fin d → ℕ) :
    sysCoeffFun f (fun s => n s) (i, k) = Bcoeff f n i k := rfl

/-- The inner sum at a balanced species vector `i` is the sum over the low-discrepancy exponents
`k ∈ P_ε^d ∩ [0,D]^d` of `y (i,k) · ∏_s [x_s^{n_s - k_s}] f_{i_s}`. -/
private lemma inner_eq {m d : ℕ} (f : Fin m → PowerSeries ℚ) (D : ℕ) (ε : ℝ)
    (y : ColIdx d D ε m → ℤ) (n : Fin d →₀ ℕ) (i : Fin d → Fin m) (hi : i ∈ balSet d m) :
    InnerSum f D ε y n i =
      ∑ k ∈ lowSet d D ε, yCast y (i, k) * Bcoeff f n i k := by
  have h1 : InnerSum f D ε y n i =
      ∑ k ∈ (mkQ y i).support,
        ((mkQ y i).coeff k : ℚ) * Bcoeff f n i (Finsupp.equivFunOnFinite k) := by
    rw [InnerSum_apply]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [if_le_mul_prod k n (fun s => PowerSeries.coeff (n s - k s) (f (i s)))
      ((mkQ y i).coeff k : ℚ)]
    congr 1
  rw [h1, sum_support_mkQ y i hi (Bcoeff f n i)]
  rw [← Finset.sum_attach (lowSet d D ε) (fun k => yCast y (i, k) * Bcoeff f n i k)]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [yCast_eq y (i, x.1) ⟨hi, x.2⟩]

/-- Off the balanced multi-indices the template `mkQ y i` vanishes, so the inner sum is empty. -/
private lemma inner_zero {m d : ℕ} (f : Fin m → PowerSeries ℚ) (D : ℕ) (ε : ℝ)
    (y : ColIdx d D ε m → ℤ) (n : Fin d →₀ ℕ) {i : Fin d → Fin m} (hi : i ∉ balSet d m) :
    InnerSum f D ε y n i = 0 := by
  have h0 : mkQ y i = 0 := by
    by_contra h
    exact hi (mem_balSet.mpr (balanced_mkQ y h))
  rw [InnerSum_apply, h0]
  simp

/-- The left-hand side of `coeff_auxSeries` for `Q = mkQ y`, as a sum over the product
`balSet d m ×ˢ lowSet d D ε`. -/
private theorem key {m d : ℕ} (f : Fin m → PowerSeries ℚ) (D : ℕ) (ε : ℝ)
    (y : ColIdx d D ε m → ℤ) (n : Fin d →₀ ℕ) :
    (∑ i : Fin d → Fin m, InnerSum f D ε y n i) =
      ∑ q ∈ (balSet d m).product (lowSet d D ε), yCast y q * Bcoeff f n q.1 q.2 := by
  have hA : (∑ i : Fin d → Fin m, InnerSum f D ε y n i)
      = ∑ i ∈ balSet d m, InnerSum f D ε y n i := by
    refine (Finset.sum_subset (Finset.subset_univ _) ?_).symm
    intro i _ hi
    exact inner_zero f D ε y n hi
  have hB : (∑ i ∈ balSet d m, InnerSum f D ε y n i)
      = ∑ i ∈ balSet d m, ∑ k ∈ lowSet d D ε, yCast y (i, k) * Bcoeff f n i k := by
    refine Finset.sum_congr rfl (fun i hi => ?_)
    exact inner_eq f D ε y n i hi
  have hC : (∑ i ∈ balSet d m, ∑ k ∈ lowSet d D ε, yCast y (i, k) * Bcoeff f n i k)
      = ∑ q ∈ (balSet d m).product (lowSet d D ε), yCast y q * Bcoeff f n q.1 q.2 :=
    (Finset.sum_product (balSet d m) (lowSet d D ε)
      (fun q : (Fin d → Fin m) × (Fin d → ℕ) => yCast y q * Bcoeff f n q.1 q.2)).symm
  rw [hA, hB, hC]

/-- The right-hand side of the theorem, reindexed to the product `balSet d m ×ˢ lowSet d D ε`. -/
private lemma rhs_reindex {m d : ℕ} (f : Fin m → PowerSeries ℚ) (D : ℕ) (ε : ℝ)
    (y : ColIdx d D ε m → ℤ) (n : Fin d →₀ ℕ) :
    (∑ p : ColIdx d D ε m, (y p : ℚ) * sysCoeff f n p.1)
      = ∑ q ∈ (balSet d m).product (lowSet d D ε), yCast y q * Bcoeff f n q.1 q.2 := by
  rw [show (∑ p : ColIdx d D ε m, (y p : ℚ) * sysCoeff f n p.1)
      = ∑ p : ColIdx d D ε m, yCast y p.1 * sysCoeffFun f (fun s => n s) p.1 from by
    refine Finset.sum_congr rfl (fun p _ => ?_)
    rw [yCast_eq y p.1 p.2]
    rfl]
  rw [sum_colIdx (F := fun p => yCast y p.1 * sysCoeffFun f (fun s => n s) p.1)]
  refine Finset.sum_congr rfl (fun q hq => ?_)
  rw [dif_pos (Finset.mem_product.mp hq)]
  rfl

/-- **Coefficients of the auxiliary template.** For the template `Q = Work.Holonomy3.mkQ y` built
from an integer vector `y` on the columns `(i,k)` with `i ∈ V_m^d` balanced and `k ∈ P_ε^d ∩ [0,D]^d`,
the coefficient of `x^n` in the auxiliary series `Submission.CDTPlan.auxSeries f Q` is the column
sum `∑_p y p · ∏_s [x_s^{n_s-k_s}] f_{i_s}`, where the scalar factor is
`Work.Holonomy3.sysCoeff f n p.1` (with the convention that `[x_s^{m}] f = 0` for `m < 0`).

There is an existing general lemma `coeff_auxSeries` (in `Submission.Work.QuadraticTy/coeff_auxSeries.lean`
or wherever it lives) that expands `coeff n (auxSeries f Q)` as a sum over `i` and `k ∈ (Q i).support`
with the guard `k ≤ n`; this statement is the specialisation to `Q = mkQ y`, using
`Work.Holonomy3.coeff_mkQ` and the injective reindexing `(i,k) ↦ ⟨(i,k), ·⟩` of `ColIdx`. -/
theorem coeff_auxSeries_mkQ {m d : ℕ} (f : Fin m → PowerSeries ℚ) (D : ℕ) (ε : ℝ)
    (y : Work.Holonomy3.ColIdx d D ε m → ℤ) (n : Fin d →₀ ℕ) :
    MvPowerSeries.coeff n (Submission.CDTPlan.auxSeries f (Work.Holonomy3.mkQ y)) =
      ∑ p : Work.Holonomy3.ColIdx d D ε m, (y p : ℚ) * Work.Holonomy3.sysCoeff f n p.1 := by
  have h := (key f D ε y n).trans (rhs_reindex f D ε y n).symm
  rw [coeff_auxSeries]
  exact (Finset.sum_congr rfl (fun i _ => (InnerSum_apply f D ε y n i).symm)).trans h

end Work.Holonomy3
