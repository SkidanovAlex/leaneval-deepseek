import Mathlib
import Submission.Commons.RingTheory.Henselian.coeff_mem_of_irreducible_of_henselian_alt
import Submission.Commons.RingTheory.Polynomial.minpoly_inv_eq_reverse
import Submission.Commons.RingTheory.Valuation.exists_pow_eq_algebraMap_of_isAlgebraic

/-!
# The integral closure of a henselian valuation subring

Let `V` be a henselian valuation subring of a field `K`, let `L/K` be algebraic and let
`W` be a valuation subring of `L` with `W ∩ K = V` (i.e. `W` is an extension of `V` to `L`).
Then every element of `W` is integral over `V`.

The mathematical content is the classical theorem that a henselian valuation extends uniquely
to every algebraic extension: the integral closure of `V` in `L` is then a valuation ring, so
it must coincide with `W`.

## Proof outline

* `isIntegral_of_monic_of_coeff_mem` is a formal bookkeeping step: a monic polynomial over `K`
  whose coefficients all lie in `V` and which has a root `z ∈ L` exhibits `z` as integral
  over `V`.

* `integral_or_inv_integral_of_henselian`: for every `y ∈ L`, either `y` or `y⁻¹` is integral
  over `V`.  Indeed, if `f = minpoly K y`, then either `f.coeff 0 ∈ V`, in which case the
  Newton polygon lemma `coeff_mem_of_irreducible_of_henselian` shows that all coefficients of
  `f` lie in `V`, or `f.coeff 0 ∉ V`, in which case `minpoly K y⁻¹` is the reversed polynomial
  `C (f.coeff 0)⁻¹ * f.reverse` (this is `minpoly_inv_eq_reverse`), whose constant term
  `(f.coeff 0)⁻¹` lies in `V` and to which the same lemma applies.
  Thus the integral closure `A` of `V` in `L` is a valuation ring.

* For the main theorem, write `A` for the integral closure of `V` in `L` viewed as a valuation
  subring of `L`.  Since `W` is integrally closed in `L` and contains `V`, we have `A ≤ W`.
  Suppose `x ∈ W` were not integral over `V`.  Then `A.valuation x > 1`, so that
  `A.valuation x ^ m > 1` for every positive `m`.  The value group of `A` is torsion over the
  values coming from `K` (`exists_pow_eq_algebraMap_of_isAlgebraic`), so for some `m > 0` and
  some `c ∈ K^*` we have `A.valuation x ^ m = A.valuation (algebraMap K L c)`.  Hence
  `A.valuation (algebraMap K L c) > 1`, so `algebraMap K L c ∉ A`, i.e. `c ∉ V`, which by
  `W ∩ K = V` means `algebraMap K L c ∉ W`.  On the other hand `A.valuation (algebraMap K L c)
  ≤ A.valuation (x ^ m)` and the corresponding element of `A` witnesses
  `algebraMap K L c = a * x ^ m` with `a ∈ A ≤ W` and `x ^ m ∈ W`, so `algebraMap K L c ∈ W`,
  a contradiction.
-/

namespace Commons.RingTheory.Valuation

open _root_.Polynomial

set_option linter.style.haveILetI false

/-- A monic polynomial over `K` with coefficients in `V` and a root in `L` gives integrality
of that root over `V`. -/
lemma isIntegral_of_monic_of_coeff_mem {K L : Type*} [Field K] [Field L] [Algebra K L]
    (V : ValuationSubring K) {q : Polynomial K} (hq : q.Monic)
    (hcoeff : ∀ i, q.coeff i ∈ V) {z : L} (hz : Polynomial.aeval z q = 0) :
    IsIntegral V z := by
  classical
  have hinj : Function.Injective (algebraMap V K) := fun a b h => Subtype.ext h
  set p : Polynomial V :=
    ∑ i ∈ q.support, Polynomial.C (⟨q.coeff i, hcoeff i⟩ : V) * Polynomial.X ^ i with hp
  have hmap : p.map (algebraMap V K) = q := by
    rw [hp, Polynomial.map_sum]
    conv_rhs => rw [← Polynomial.sum_C_mul_X_pow_eq q]
    refine Finset.sum_congr rfl fun i hi => ?_
    simp [Polynomial.map_mul, Polynomial.map_pow]
  refine ⟨p, ?_, ?_⟩
  · rw [Function.Injective.monic_map_iff hinj, hmap]
    exact hq
  · have h1 : Polynomial.eval₂ (algebraMap V L) z p
        = Polynomial.eval₂ (algebraMap K L) z (p.map (algebraMap V K)) := by
      rw [Polynomial.eval₂_map, IsScalarTower.algebraMap_eq V K L]
    rw [h1, hmap]
    simpa [Polynomial.aeval_def] using hz

/-- **The integral closure of a henselian valuation subring is a valuation ring.**
If `V` is a henselian valuation subring of `K` and `L/K` is algebraic, then every element of
`L` or its inverse is integral over `V`. -/
lemma integral_or_inv_integral_of_henselian {K L : Type*} [Field K] [Field L] [Algebra K L]
    [Algebra.IsAlgebraic K L] (V : ValuationSubring K) [HenselianLocalRing V] (y : L) :
    IsIntegral V y ∨ IsIntegral V y⁻¹ := by
  by_cases hy : y = 0
  · left
    subst hy
    exact isIntegral_zero
  have hyint : IsIntegral K y := (Algebra.IsAlgebraic.isAlgebraic y).isIntegral
  have hfmonic : (minpoly K y).Monic := minpoly.monic hyint
  have hfirr : Irreducible (minpoly K y) := minpoly.irreducible hyint
  by_cases h0 : (minpoly K y).coeff 0 ∈ V
  · left
    exact isIntegral_of_monic_of_coeff_mem V hfmonic
      (Commons.RingTheory.Henselian.coeff_mem_of_irreducible_of_henselian_alt V hfmonic hfirr h0) (minpoly.aeval K y)
  · right
    have hinv : minpoly K y⁻¹
        = Polynomial.C ((minpoly K y).coeff 0)⁻¹ * (minpoly K y).reverse :=
      Commons.RingTheory.Polynomial.minpoly_inv_eq_reverse hy hyint
    have hyinvint : IsIntegral K y⁻¹ := (Algebra.IsAlgebraic.isAlgebraic y⁻¹).isIntegral
    have hmonic_inv : (minpoly K y⁻¹).Monic := minpoly.monic hyinvint
    have hirr_inv : Irreducible (minpoly K y⁻¹) := minpoly.irreducible hyinvint
    have h0_inv : (minpoly K y⁻¹).coeff 0 ∈ V := by
      rw [hinv, Polynomial.coeff_C_mul, Polynomial.coeff_zero_reverse, hfmonic.leadingCoeff,
        mul_one]
      exact (V.mem_or_inv_mem ((minpoly K y).coeff 0)).resolve_left h0
    exact isIntegral_of_monic_of_coeff_mem V hmonic_inv
      (Commons.RingTheory.Henselian.coeff_mem_of_irreducible_of_henselian_alt V hmonic_inv hirr_inv h0_inv)
      (minpoly.aeval K y⁻¹)

/-- Every element of a valuation subring `W` extending a henselian valuation subring `V` to an
algebraic extension is integral over `V`. -/
theorem isIntegral_of_mem_of_henselian {K L : Type*} [Field K] [Field L] [Algebra K L]
    [Algebra.IsAlgebraic K L] (V : ValuationSubring K) [HenselianLocalRing V]
    (W : ValuationSubring L) (hW : W.comap (algebraMap K L) = V) {x : L} (hx : x ∈ W) :
    IsIntegral V x := by
  by_contra hnot
  -- the integral closure of `V` in `L`, as a valuation subring
  let A : ValuationSubring L :=
    { toSubring := (integralClosure V L).toSubring
      mem_or_inv_mem' := fun y => integral_or_inv_integral_of_henselian V y }
  have hxA : x ∉ A := fun h => hnot h
  have hx0 : x ≠ 0 := fun h => hxA (h ▸ A.zero_mem)
  -- the value group of `A` is torsion over the values coming from `K`
  obtain ⟨m, hm, c, hc0, hval⟩ :=
    Commons.RingTheory.Valuation.exists_pow_eq_algebraMap_of_isAlgebraic (k := K) (K := L)
      A.valuation (Algebra.IsAlgebraic.isAlgebraic x) hx0
  have hxgt : 1 < A.valuation x := by
    rw [← not_le]
    intro hle
    exact hxA ((ValuationSubring.valuation_le_one_iff A x).mp hle)
  have hcgt : 1 < A.valuation (algebraMap K L c) := by
    rw [← hval]
    exact one_lt_pow₀ hxgt hm.ne'
  have hcA : algebraMap K L c ∉ A := fun hmem =>
    absurd hcgt (not_lt.mpr ((ValuationSubring.valuation_le_one_iff A _).mpr hmem))
  have hcV : c ∉ V := by
    intro hc
    apply hcA
    have h2 : IsIntegral V (algebraMap K L (algebraMap V K (⟨c, hc⟩ : V))) :=
      IsIntegral.algebraMap isIntegral_algebraMap
    rw [ValuationSubring.algebraMap_apply] at h2
    exact h2
  have hcW : algebraMap K L c ∉ W := by
    intro hmem
    have h := SetLike.ext_iff.mp hW c
    simp only [ValuationSubring.mem_comap] at h
    exact hcV (h.mp hmem)
  -- the integral closure is contained in `W`, since `W` is integrally closed in `L`
  have hAW : (integralClosure V L).toSubring ≤ W.toSubring := by
    haveI : IsIntegrallyClosedIn ↥W.toSubring L :=
      Subring.isIntegrallyClosedIn_iff.mpr fun z hz =>
        LocalSubring.mem_of_isMax_of_isIntegral W.isMax_toLocalSubring hz
    exact Subring.integralClosure_le_iff.mpr fun r => by
      rw [IsScalarTower.algebraMap_apply V K L, ValuationSubring.algebraMap_apply]
      exact (ValuationSubring.mem_toSubring W _).mpr
        ((ValuationSubring.mem_comap).mp ((SetLike.ext_iff.mp hW (r : K)).mpr r.2))
  -- but `x ∈ W` and `A.valuation x ^ m = A.valuation c` force `algebraMap K L c ∈ W`
  have hmemW : algebraMap K L c ∈ W.toSubring := by
    obtain ⟨a, ha⟩ := (ValuationSubring.valuation_le_iff A (algebraMap K L c) (x ^ m)).mp (by
      rw [map_pow]
      exact le_of_eq hval.symm)
    rw [← ha]
    refine Subring.mul_mem W.toSubring ?_ (Subring.pow_mem W.toSubring hx m)
    exact hAW a.2
  exact hcW ((ValuationSubring.mem_toSubring W _).mp hmemW)

end Commons.RingTheory.Valuation
