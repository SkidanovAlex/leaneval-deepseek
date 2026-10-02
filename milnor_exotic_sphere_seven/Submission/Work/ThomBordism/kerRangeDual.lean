import Mathlib
import Submission.Work.Cohomology.uctDual_evaluation

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The cycles of a dual complex with vanishing cohomology are the boundaries

If the `k`-th homology of the `ℤ`-dual `dualComplex ℤ E` of a chain complex `E` of `ℤ`-modules
vanishes, the complex is exact at `k`: the `k`-cocycles are exactly the `k`-coboundaries, i.e.

`ker (dᵏ : (dualComplex ℤ E)ᵏ ⟶ (dualComplex ℤ E)ᵏ⁺¹) = range (dᵏ⁻¹)`.

This is `HomologicalComplex.ExactAt` rewritten through `ShortComplex.moduleCat_exact_iff_range_eq_ker`;
the only bookkeeping is the identification of the short complex `(dualComplex ℤ E).sc' (k-1) k (k+1)`
with the two differentials appearing in the statement (via `up_prev` and `up_next`).
-/

open CategoryTheory CategoryTheory.Limits

namespace Work.ThomBordism

/-- Vanishing of the `k`-th cohomology of the dual complex makes it exact at `k`: the `k`-cocycles
are the `k`-coboundaries. -/
theorem kerRangeDual (E : ChainComplex (ModuleCat ℤ) ℕ) (k : ℕ)
    (h : CategoryTheory.Limits.IsZero ((Work.Cohomology.dualComplex ℤ E).homology k)) :
    LinearMap.ker (ModuleCat.Hom.hom ((Work.Cohomology.dualComplex ℤ E).d k (k + 1))) =
      LinearMap.range (ModuleCat.Hom.hom ((Work.Cohomology.dualComplex ℤ E).d (k - 1) k)) := by
  -- the vanishing of the homology is exactness at `k`
  have hEA : (Work.Cohomology.dualComplex ℤ E).ExactAt k :=
    (HomologicalComplex.exactAt_iff_isZero_homology _ k).mpr h
  -- rewritten as exactness of the short complex `dᵏ⁻¹, dᵏ`
  have hsc : ((Work.Cohomology.dualComplex ℤ E).sc' (k - 1) k (k + 1)).Exact :=
    (HomologicalComplex.exactAt_iff' (Work.Cohomology.dualComplex ℤ E) (k - 1) k (k + 1)
      (Work.Cohomology.up_prev k) (Work.Cohomology.up_next k)).mp hEA
  -- exactness of the short complex is `range f = ker g` for the two module homs
  have hrange := (ShortComplex.moduleCat_exact_iff_range_eq_ker
    ((Work.Cohomology.dualComplex ℤ E).sc' (k - 1) k (k + 1))).mp hsc
  exact hrange.symm

end Work.ThomBordism
