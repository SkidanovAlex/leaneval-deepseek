import Mathlib
import Submission.Work.ORLyndon.CLDirect.cldDefs

set_option autoImplicit false

namespace Work.ORLyndon.CLDirect

open MonoidAlgebra

section NormElemCoeff

variable {G : Type*} [Group G] [DecidableEq G] {K : Type*} [Field K]

/-- The coefficients of the norm element `1 + w + ⋯ + w ^ (l-1)` of `w` are the indicators of the
powers `w ^ k`, `k < l`. -/
private lemma normElem_coeff_eq (l : ℕ) (w y : G) :
    (normElem K l w).coeff y =
      ∑ k ∈ Finset.range l, (if w ^ k = y then (1 : K) else 0) := by
  classical
  rw [normElem, MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
  exact Finset.sum_congr rfl fun k _ => by
    rw [← map_pow, MonoidAlgebra.of_apply, MonoidAlgebra.coeff_single, Finsupp.single_apply]

/-- The coefficient of the identity in the norm element is `1`, provided `w` has order exactly `l`
with `l ≥ 1` (so that `0 < l` is in range and the other powers are `≠ 1`). -/
private lemma normElem_coeff_one {l : ℕ} (hl : 1 ≤ l) {w : G} (hord : orderOf w = l) :
    (normElem K l w).coeff (1 : G) = 1 := by
  classical
  rw [normElem_coeff_eq, Finset.sum_eq_single 0]
  · simp
  · intro k hk hk0
    have hklt : k < orderOf w := by rw [hord]; exact Finset.mem_range.mp hk
    rw [if_neg (fun hwk => pow_ne_one_of_lt_orderOf hk0 hklt hwk)]
  · intro h0
    exact absurd (Finset.mem_range.mpr (by omega)) h0

end NormElemCoeff

/-- A coefficient count on the disjoint cosets `g_i ⟨w⟩` (\(w =\) `presentRho r u` of order `l`). Sketch: take the coefficient of `g j` in `hsum`; `Finset.sum_mul`, `normElem`, `Finset.mul_sum`, `← map_pow`, `← map_mul`, coefficient of `single` give `∑ i, ∑ k ∈ range l, c i * (if g i * w^k = g j then 1 else 0) = 0`; only `(i,k) = (j,0)` survives: for `i ≠ j` use `hdist j i (Ne.symm _) k` (cast `k : ℤ`, `zpow_natCast`); for `i = j` and `0 < k < l` use `pow_ne_one_of_lt_orderOf` with `hord`. Do NOT use `coeff_mul_normElem` (it lives in the forbidden `powDefs`); its proof can be copied. -/
theorem coeffs_zero_of_sum_mul_normElem {X : Type*} [DecidableEq X] {K : Type*} [Field K]
    (r u : FreeGroup X) (l : ℕ) (hl : 1 ≤ l)
    (hord : orderOf (Work.ORLyndon.presentRho r u) = l)
    (ι : Type) [Fintype ι] (g : ι → Work.ORLyndon.OneRelatorGroup r) (c : ι → K)
    (hdist : ∀ i j, i ≠ j → ∀ k : ℤ, g i ≠ g j * (Work.ORLyndon.presentRho r u) ^ k)
    (hsum : (∑ i, c i • MonoidAlgebra.of K _ (g i)) *
      Work.ORLyndon.normElem K l (Work.ORLyndon.presentRho r u) = 0) :
    ∀ i, c i = 0 := by
  classical
  intro j
  -- the coefficient of `g j` in the `i`-th summand of the product
  have hterm : ∀ i, (((c i • MonoidAlgebra.of K (Work.ORLyndon.OneRelatorGroup r) (g i)) *
      Work.ORLyndon.normElem K l (Work.ORLyndon.presentRho r u)).coeff (g j))
      = if i = j then c i else 0 := by
    intro i
    rw [smul_mul_assoc, MonoidAlgebra.coeff_smul_apply, smul_eq_mul]
    have hcoeff : ((MonoidAlgebra.of K (Work.ORLyndon.OneRelatorGroup r) (g i)) *
        Work.ORLyndon.normElem K l (Work.ORLyndon.presentRho r u)).coeff (g j)
        = (Work.ORLyndon.normElem K l (Work.ORLyndon.presentRho r u)).coeff ((g i)⁻¹ * g j) := by
      rw [MonoidAlgebra.of_apply, MonoidAlgebra.coeff_single_mul_apply, one_mul]
    rw [hcoeff]
    by_cases hij : i = j
    · subst hij
      rw [if_pos rfl, inv_mul_cancel, normElem_coeff_one hl hord, mul_one]
    · -- the coset hypothesis: no power of `w` carries `g i` to `g j`
      have hN0 : (Work.ORLyndon.normElem K l (Work.ORLyndon.presentRho r u)).coeff
          ((g i)⁻¹ * g j) = 0 := by
        rw [normElem_coeff_eq]
        refine Finset.sum_eq_zero fun k _ => ?_
        have hne : (Work.ORLyndon.presentRho r u) ^ k ≠ (g i)⁻¹ * g j := by
          intro hwk
          exact hdist j i (Ne.symm hij) (k : ℤ)
            (by rw [zpow_natCast, hwk, mul_inv_cancel_left])
        rw [if_neg hne]
      rw [if_neg hij, hN0, mul_zero]
  -- hence the coefficient of `g j` in the whole product is `c j`
  have hcoeff_j : ((∑ i, c i • MonoidAlgebra.of K (Work.ORLyndon.OneRelatorGroup r) (g i)) *
      Work.ORLyndon.normElem K l (Work.ORLyndon.presentRho r u)).coeff (g j) = c j := by
    rw [Finset.sum_mul, MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
    rw [Finset.sum_congr rfl fun i _ => hterm i, Finset.sum_eq_single j]
    · simp
    · intro b _ hb
      rw [if_neg hb]
    · intro h
      exact absurd (Finset.mem_univ j) h
  rw [← hcoeff_j, hsum, MonoidAlgebra.coeff_zero]
  exact Finsupp.zero_apply

end Work.ORLyndon.CLDirect
