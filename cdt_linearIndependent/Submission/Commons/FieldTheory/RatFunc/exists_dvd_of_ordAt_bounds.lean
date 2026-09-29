import Mathlib
import Submission.Commons.Algebra.Polynomial.dvd_of_forall_rootMultiplicity_le
import Submission.Commons.FieldTheory.RatFunc.ordAt_mul
import Submission.Commons.FieldTheory.RatFunc.ordAt_algebraMap

namespace Commons.FieldTheory.RatFunc

/-- If `x.denom` divides `x.num`, then the rational function `x` is a polynomial. -/
theorem exists_eq_algebraMap_of_denom_dvd_num {K : Type*} [Field K] {x : RatFunc K}
    (h : x.denom ∣ x.num) : ∃ Q : Polynomial K, x = algebraMap (Polynomial K) (RatFunc K) Q := by
  obtain ⟨Q, hQ⟩ := h
  refine ⟨Q, ?_⟩
  have hB : algebraMap (Polynomial K) (RatFunc K) x.denom ≠ 0 :=
    RatFunc.algebraMap_ne_zero (RatFunc.denom_ne_zero x)
  -- `algebraMap x.num = x * algebraMap x.denom`
  have key : algebraMap (Polynomial K) (RatFunc K) x.num
      = x * algebraMap (Polynomial K) (RatFunc K) x.denom := by
    have h2 : (algebraMap (Polynomial K) (RatFunc K) x.num
          / algebraMap (Polynomial K) (RatFunc K) x.denom)
        * algebraMap (Polynomial K) (RatFunc K) x.denom
        = x * algebraMap (Polynomial K) (RatFunc K) x.denom := by
      rw [RatFunc.num_div_denom x]
    rw [div_mul_cancel₀ (algebraMap (Polynomial K) (RatFunc K) x.num) hB] at h2
    exact h2
  rw [hQ, map_mul] at key
  have hkey : algebraMap (Polynomial K) (RatFunc K) x.denom * algebraMap (Polynomial K) (RatFunc K) Q
      = algebraMap (Polynomial K) (RatFunc K) x.denom * x := by
    rw [key, mul_comm x (algebraMap (Polynomial K) (RatFunc K) x.denom)]
  exact (mul_left_cancel₀ hB hkey).symm

/-- If a rational function has nonnegative order of vanishing at every point (over an
algebraically closed field), then it is a polynomial. -/
theorem exists_eq_algebraMap_of_forall_nonneg_ordAt {K : Type*} [Field K] [IsAlgClosed K]
    {x : RatFunc K} (h : ∀ α : K, (0 : ℤ) ≤ ordAt α x) :
    ∃ Q : Polynomial K, x = algebraMap (Polynomial K) (RatFunc K) Q := by
  apply exists_eq_algebraMap_of_denom_dvd_num
  apply Commons.Algebra.Polynomial.dvd_of_forall_rootMultiplicity_le (RatFunc.denom_ne_zero x)
  intro α
  have hα := h α
  rw [ordAt_def] at hα
  omega

/-- **The divisor bound (general form).**  Let `b ≠ 0` be a rational function over an algebraically closed field and let `P₀, D ≠ 0` be polynomials with no common root.  Suppose that

* at every root `α` of `P₀` the order of `b` is at least the root multiplicity of `P₀` at `α`;
* at every root `γ` of `D` the order of `b` is at least `−1` (at worst a simple pole);
* away from the roots of `P₀` and of `D`, `b` has no pole (`0 ≤ ord_α b`);

then `D·b` is a polynomial and it is divisible by `P₀`.  Equivalently, `b = P₀·Q/D` with `Q` a polynomial.

This is the common shape of the divisor bounds of the CDT systems (`arXiv:2408.15403`): the A-side bound `cub·b₃ = y²(y−4)²(y + 1/72)·Q` and the C-side bound `b₃ = ((y−4)²R₄/R₁₀)·Q` are both instances (with `P₀` the product of the required vanishing factors and `D` the "denominator" `R₁₀`).  The proof multiplies `b` by `D`, checks that the product has nonnegative order at every point (using `rootMultiplicity_pos` at the roots of `D` and the three hypotheses elsewhere), converts it into a polynomial `Q` through `Commons.Algebra.Polynomial.dvd_of_forall_rootMultiplicity_le` applied to `(D·b).denom ∣ (D·b).num`, and then divides by `P₀` using the same criterion. -/
theorem exists_dvd_of_ordAt_bounds {K : Type*} [Field K] [IsAlgClosed K] [CharZero K]
    {b : RatFunc K} (hb : b ≠ 0) {P0 D : Polynomial K} (hP0 : P0 ≠ 0) (hD : D ≠ 0)
    (hcop : ∀ α : K, P0.eval α = 0 → D.eval α ≠ 0)
    (hmult : ∀ α : K, P0.eval α = 0 → (Polynomial.rootMultiplicity α P0 : ℤ) ≤ ordAt α b)
    (hroot : ∀ γ : K, D.eval γ = 0 → (-1 : ℤ) ≤ ordAt γ b)
    (hgen : ∀ α : K, P0.eval α ≠ 0 → D.eval α ≠ 0 → (0 : ℤ) ≤ ordAt α b) :
    ∃ Q : Polynomial K, P0 ∣ Q ∧
      algebraMap (Polynomial K) (RatFunc K) D * b = algebraMap (Polynomial K) (RatFunc K) Q := by
  classical
  set c : RatFunc K := algebraMap (Polynomial K) (RatFunc K) D * b with hc
  have hc_map_ne : algebraMap (Polynomial K) (RatFunc K) D ≠ 0 := RatFunc.algebraMap_ne_zero hD
  have hc_ord : ∀ α : K, ordAt α c
      = (Polynomial.rootMultiplicity α D : ℤ) + ordAt α b := by
    intro α
    rw [hc, ordAt_mul α hc_map_ne hb, ordAt_algebraMap]
  have hc_nonneg : ∀ α : K, (0 : ℤ) ≤ ordAt α c := by
    intro α
    rw [hc_ord α]
    by_cases hDα : D.eval α = 0
    · have hpos : (0 : ℤ) < (Polynomial.rootMultiplicity α D : ℤ) := by
        exact_mod_cast (Polynomial.rootMultiplicity_pos hD).mpr hDα
      have := hroot α hDα
      linarith
    · have hzero : (Polynomial.rootMultiplicity α D : ℤ) = 0 := by
        rw [Polynomial.rootMultiplicity_eq_zero (fun h => hDα h)]
        norm_num
      rw [hzero, zero_add]
      by_cases hPα : P0.eval α = 0
      · have hpos : (0 : ℤ) < (Polynomial.rootMultiplicity α P0 : ℤ) := by
          exact_mod_cast (Polynomial.rootMultiplicity_pos hP0).mpr hPα
        have := hmult α hPα
        linarith
      · exact hgen α hPα hDα
  obtain ⟨Q, hQ⟩ := exists_eq_algebraMap_of_forall_nonneg_ordAt hc_nonneg
  refine ⟨Q, ?_, ?_⟩
  · apply Commons.Algebra.Polynomial.dvd_of_forall_rootMultiplicity_le hP0
    intro α
    by_cases hPα : P0.eval α = 0
    · have hDα : D.eval α ≠ 0 := hcop α hPα
      have hrmD : (Polynomial.rootMultiplicity α D : ℤ) = 0 := by
        rw [Polynomial.rootMultiplicity_eq_zero (fun h => hDα h)]
        norm_num
      have hQmult : (Polynomial.rootMultiplicity α Q : ℤ) = ordAt α b := by
        have h1 : (Polynomial.rootMultiplicity α Q : ℤ)
            = ordAt α (algebraMap (Polynomial K) (RatFunc K) Q) :=
          (ordAt_algebraMap α Q).symm
        rw [← hQ, hc_ord α, hrmD, zero_add] at h1
        exact h1
      have hZ : (Polynomial.rootMultiplicity α P0 : ℤ)
          ≤ (Polynomial.rootMultiplicity α Q : ℤ) := by
        rw [hQmult]
        exact hmult α hPα
      exact_mod_cast hZ
    · rw [Polynomial.rootMultiplicity_eq_zero (fun h => hPα h)]
      exact Nat.zero_le _
  · exact hQ

end Commons.FieldTheory.RatFunc
