import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.BridgeDefs

/-!
# The height of `formOf d n a` is the Euclidean norm of `a`

The challenge fixes the height of a rational polynomial `f` as the Euclidean norm of the
primitive integer coefficient vector obtained from `f` by clearing denominators and dividing
by the gcd of the coefficients (`HassePrincipleRandomFano.height`).  For a coefficient vector
`a : Mon d n → ℤ` that is already primitive this is simply `eNorm a`, which is the statement
proved here.

The proof proceeds in three steps.

* `support_formOf`: the support of `formOf d n a` is the image under `Mon.toFinsupp` of the
  monomials at which `a` is non-zero;
* `lcm_den_formOf` / `gcd_num_formOf`: consequently the lcm of the denominators of the
  coefficients is `1` and, when `a` is primitive, the gcd of the numerators is `1`;
* `height_eq_of_forall`: a general computation of `HassePrincipleRandomFano.height` under
  those two hypotheses.
-/

set_option autoImplicit false

open MvPolynomial Finset

namespace Work.HP.BridgeAux

/-! ## A general computation of the height -/

/-- If the lcm of the denominators of the coefficients in the support is `1` and the gcd of
the numerators over the support is `1`, then the height is the Euclidean norm of the
(integer) coefficient vector restricted to the support. -/
lemma height_eq_of_forall {σ : Type*} (f : MvPolynomial σ ℚ)
    (hD : f.support.lcm (fun m => (f.coeff m).den) = 1)
    (hgcd : f.support.gcd (fun m => (f.coeff m).num) = 1) :
    HassePrincipleRandomFano.height f = √(f.support.sum fun m => ((f.coeff m).num : ℝ) ^ 2) := by
  rw [HassePrincipleRandomFano.height, hD]
  simp only [Nat.cast_one, one_mul]
  rw [hgcd]
  simp only [Int.ediv_one]

/-- The lcm of the constant function `1` over any finset is `1`. -/
lemma lcm_const_one {α : Type*} [CommMonoidWithZero α] [NormalizedGCDMonoid α]
    {β : Type*} (s : Finset β) : s.lcm (fun _ => (1 : α)) = 1 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s _ ih => rw [Finset.lcm_insert, ih, lcm_one_left, normalize_one]

/-! ## The support of `formOf` -/

/-- Coefficients of `formOf d n a` as a sum over the monomial index. -/
lemma coeff_formOf (d n : ℕ) (a : Mon d n → ℤ) (s : Fin (n + 1) →₀ ℕ) :
    (formOf d n a).coeff s = ∑ m, if Mon.toFinsupp m = s then (a m : ℚ) else 0 := by
  simp only [formOf, MvPolynomial.coeff_sum]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  rw [MvPolynomial.coeff_monomial]

/-- The support of `formOf d n a` is the image under `Mon.toFinsupp` of the monomials with
non-zero coefficient. -/
lemma support_formOf (d n : ℕ) (a : Mon d n → ℤ) :
    (formOf d n a).support = (Finset.univ.filter fun m => a m ≠ 0).image Mon.toFinsupp := by
  ext s
  rw [MvPolynomial.mem_support_iff, Finset.mem_image]
  constructor
  · intro h
    by_contra hc
    apply h
    rw [coeff_formOf]
    apply Finset.sum_eq_zero
    intro m _
    by_cases hms : Mon.toFinsupp m = s
    · have ham : a m = 0 := by
        by_contra h
        exact hc ⟨m, by simp [h], hms⟩
      simp [hms, ham]
    · simp [hms]
  · rintro ⟨m, hm, rfl⟩
    have hmem : a m ≠ 0 := by simpa using hm
    rw [Work.HP.formOf_coeff]
    simpa using hmem

/-! ## Denominators and numerators of the coefficients -/

/-- All coefficients of `formOf d n a` have denominator `1`. -/
lemma lcm_den_formOf (d n : ℕ) (a : Mon d n → ℤ) :
    (formOf d n a).support.lcm (fun m => ((formOf d n a).coeff m).den) = 1 := by
  rw [support_formOf, Finset.lcm_image]
  trans (Finset.univ.filter fun m : Mon d n => a m ≠ 0).lcm (fun _ => (1 : ℕ))
  · exact Finset.lcm_congr rfl
      (fun m _ => by rw [Function.comp_apply, formOf_coeff, Rat.den_intCast])
  · exact lcm_const_one _

/-- For primitive `a`, the gcd of the numerators of the coefficients over the support of
`formOf d n a` is `1`. -/
lemma gcd_num_formOf (d n : ℕ) (a : Mon d n → ℤ) (ha : IsPrim a) :
    (formOf d n a).support.gcd (fun m => ((formOf d n a).coeff m).num) = 1 := by
  rw [support_formOf, Finset.gcd_image]
  have hcomp : ((fun m => ((formOf d n a).coeff m).num) ∘ Mon.toFinsupp) = a := by
    funext m; rw [Function.comp_apply, formOf_coeff, Rat.num_intCast]
  rw [hcomp]
  rw [← Finset.gcd_eq_gcd_filter_ne_zero]
  exact ha

/-! ## The main statement -/

/-- The height of the rational form with primitive integer coefficient vector `a` is the
Euclidean norm of `a`. -/
theorem height_formOf (d n : ℕ) (a : Mon d n → ℤ) (ha : IsPrim a) :
    HassePrincipleRandomFano.height (formOf d n a) = eNorm a := by
  rw [height_eq_of_forall _ (lcm_den_formOf d n a) (gcd_num_formOf d n a ha), eNorm]
  apply congrArg Real.sqrt
  have hinj : Set.InjOn (Mon.toFinsupp (d := d) (n := n))
      ↑(Finset.univ.filter fun m : Mon d n => a m ≠ 0) :=
    fun _ _ _ _ h => Mon_toFinsupp_injective h
  rw [support_formOf, Finset.sum_image hinj]
  trans (∑ m ∈ (Finset.univ.filter fun m : Mon d n => a m ≠ 0), (a m : ℝ) ^ 2)
  · apply Finset.sum_congr rfl
    intro m _
    rw [formOf_coeff, Rat.num_intCast]
  · refine Finset.sum_subset (Finset.subset_univ _) ?_
    intro m _ hm
    have ham : a m = 0 := by
      by_contra h
      exact hm (Finset.mem_filter.2 ⟨Finset.mem_univ m, h⟩)
    simp [ham]

end Work.HP.BridgeAux
