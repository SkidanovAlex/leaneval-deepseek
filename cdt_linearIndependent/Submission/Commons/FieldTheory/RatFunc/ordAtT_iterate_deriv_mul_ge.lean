import Mathlib
import Submission.Commons.FieldTheory.RatFunc.ordAtT_mul
import Submission.Commons.FieldTheory.RatFunc.ordAtT_div
import Submission.Commons.FieldTheory.RatFunc.ordAtT_neg
import Submission.Commons.FieldTheory.RatFunc.ordAtT_add_ge
import Submission.Commons.FieldTheory.RatFunc.ordAtT_algebraMap
import Submission.Commons.FieldTheory.RatFunc.ordAt_algebraMap
import Submission.Commons.FieldTheory.RatFunc.ordAt_mul

namespace Commons.FieldTheory.RatFunc

open Classical

/-- The logarithmic derivative `p'/p` of a polynomial `p` has order of vanishing at least
`-1` at every point.  This is the polynomial case of "a derivative lowers the order by at most
one": `ord(p') ≥ ord(p) - 1` (`Polynomial.rootMultiplicity_sub_one_le_derivative_...`), and
dividing by `p` subtracts `ord(p)`.  If `p' = 0` (possible in positive characteristic) the
logarithmic derivative vanishes and the bound is trivial. -/
theorem neg_one_le_ordAtT_logDeriv {K : Type*} [Field K] (α : K) (p : Polynomial K) :
    ((-1 : ℤ) : WithTop ℤ) ≤
      ordAtT α (algebraMap (Polynomial K) (RatFunc K) p.derivative
        / algebraMap (Polynomial K) (RatFunc K) p) := by
  rcases eq_or_ne p.derivative 0 with h | h
  · rw [h]
    simp [ordAtT]
  · rcases eq_or_ne p 0 with hp | hp
    · rw [hp]
      simp [ordAtT]
    · have hp' : algebraMap (Polynomial K) (RatFunc K) p.derivative ≠ 0 :=
        RatFunc.algebraMap_ne_zero h
      have hp0 : algebraMap (Polynomial K) (RatFunc K) p ≠ 0 := RatFunc.algebraMap_ne_zero hp
      rw [ordAtT_div α hp' hp0, ordAtT_algebraMap h, ordAtT_algebraMap hp]
      rw [← WithTop.LinearOrderedAddCommGroup.coe_sub]
      apply WithTop.coe_le_coe.mpr
      have hnat :=
        Polynomial.rootMultiplicity_sub_one_le_derivative_rootMultiplicity_of_ne_zero p α h
      omega

/-- The derivative of a nonzero rational function `h` as `h` times the difference of the
logarithmic derivatives of its numerator and denominator: `D h = h·(p'/p − q'/q)` where
`h = p/q`. -/
theorem deriv_eq_mul_sub_logDeriv {K : Type*} [Field K]
    (D : Derivation K (RatFunc K) (RatFunc K))
    (hd : ∀ p : Polynomial K, D (algebraMap (Polynomial K) (RatFunc K) p)
      = algebraMap (Polynomial K) (RatFunc K) p.derivative)
    {h : RatFunc K} (hh : h ≠ 0) :
    D h = h * (algebraMap (Polynomial K) (RatFunc K) h.num.derivative
          / algebraMap (Polynomial K) (RatFunc K) h.num)
        - h * (algebraMap (Polynomial K) (RatFunc K) h.denom.derivative
          / algebraMap (Polynomial K) (RatFunc K) h.denom) := by
  have hnum : h.num ≠ 0 := RatFunc.num_ne_zero hh
  have hden : h.denom ≠ 0 := RatFunc.denom_ne_zero h
  have hn0 : algebraMap (Polynomial K) (RatFunc K) h.num ≠ 0 := RatFunc.algebraMap_ne_zero hnum
  have hd0 : algebraMap (Polynomial K) (RatFunc K) h.denom ≠ 0 := RatFunc.algebraMap_ne_zero hden
  suffices key : D (algebraMap (Polynomial K) (RatFunc K) h.num
        / algebraMap (Polynomial K) (RatFunc K) h.denom)
      = (algebraMap (Polynomial K) (RatFunc K) h.num
            / algebraMap (Polynomial K) (RatFunc K) h.denom)
          * (algebraMap (Polynomial K) (RatFunc K) h.num.derivative
              / algebraMap (Polynomial K) (RatFunc K) h.num)
        - (algebraMap (Polynomial K) (RatFunc K) h.num
            / algebraMap (Polynomial K) (RatFunc K) h.denom)
          * (algebraMap (Polynomial K) (RatFunc K) h.denom.derivative
              / algebraMap (Polynomial K) (RatFunc K) h.denom) by
    rwa [RatFunc.num_div_denom h] at key
  rw [div_eq_mul_inv, Derivation.leibniz, Derivation.leibniz_inv, hd h.num, hd h.denom]
  simp only [Algebra.smul_def, Algebra.algebraMap_self_apply]
  field_simp
  ring

/-- The difference of the logarithmic derivatives of the numerator and denominator of a
nonzero rational function has order of vanishing at least `-1` at every point.  Immediate
from `neg_one_le_ordAtT_logDeriv` and the `min` rule. -/
theorem neg_one_le_ordAtT_logDeriv_sub {K : Type*} [Field K] (α : K) (h : RatFunc K) :
    ((-1 : ℤ) : WithTop ℤ) ≤
      ordAtT α (algebraMap (Polynomial K) (RatFunc K) h.num.derivative
            / algebraMap (Polynomial K) (RatFunc K) h.num
          - algebraMap (Polynomial K) (RatFunc K) h.denom.derivative
            / algebraMap (Polynomial K) (RatFunc K) h.denom) := by
  have hA := neg_one_le_ordAtT_logDeriv α h.num
  have hB := neg_one_le_ordAtT_logDeriv α h.denom
  refine le_trans (le_min hA hB) ?_
  have h1 := ordAtT_add_ge α
    (algebraMap (Polynomial K) (RatFunc K) h.num.derivative
      / algebraMap (Polynomial K) (RatFunc K) h.num)
    (-(algebraMap (Polynomial K) (RatFunc K) h.denom.derivative
      / algebraMap (Polynomial K) (RatFunc K) h.denom))
  rwa [ordAtT_neg, ← sub_eq_add_neg] at h1

/-- **One step of the derivative estimate**: for a nonzero rational function `h`, the order of
vanishing of `D h` at `α` is at least `ord_α h − 1`.  Writing `h = p/q` with `p = h.num`,
`q = h.denom`, one has `D h = h·(p'/p − q'/q)`; the logarithmic derivatives `p'/p`, `q'/q` have
order at least `-1`, hence so does their difference, and `ord_α (D h) ≥ ord_α h − 1`. -/
theorem ordAtT_deriv_lower_bound {K : Type*} [Field K]
    (D : Derivation K (RatFunc K) (RatFunc K))
    (hd : ∀ p : Polynomial K, D (algebraMap (Polynomial K) (RatFunc K) p)
      = algebraMap (Polynomial K) (RatFunc K) p.derivative)
    (α : K) {h : RatFunc K} (hh : h ≠ 0) :
    ((ordAt α h - 1 : ℤ) : WithTop ℤ) ≤ ordAtT α (D h) := by
  rcases eq_or_ne (D h) 0 with h0 | h0
  · rw [h0]
    simp [ordAtT]
  · let LA : RatFunc K := algebraMap (Polynomial K) (RatFunc K) h.num.derivative
        / algebraMap (Polynomial K) (RatFunc K) h.num
    let LB : RatFunc K := algebraMap (Polynomial K) (RatFunc K) h.denom.derivative
        / algebraMap (Polynomial K) (RatFunc K) h.denom
    have hAB : D h = h * (LA - LB) := by
      rw [deriv_eq_mul_sub_logDeriv D hd hh]
      ring
    have hne : LA - LB ≠ 0 := by
      intro hz
      exact h0 (by rw [hAB, hz, mul_zero])
    have hsub : ((-1 : ℤ) : WithTop ℤ) ≤ ordAtT α (LA - LB) :=
      neg_one_le_ordAtT_logDeriv_sub α h
    rw [hAB, ordAtT_mul α hh hne, ordAtT_def α hh]
    calc ((ordAt α h - 1 : ℤ) : WithTop ℤ)
        = (ordAt α h : WithTop ℤ) + ((-1 : ℤ) : WithTop ℤ) := by
          rw [← WithTop.coe_add]; congr 1
      _ ≤ (ordAt α h : WithTop ℤ) + ordAtT α (LA - LB) := add_le_add le_rfl hsub

/-- **The iterated derivative estimate**: for a nonzero rational function `h`, the order of
vanishing of the `j`-th derivative satisfies `ord_α h − j ≤ ord_α (D^j h)` (with the right hand
side read as `⊤` when `D^j h = 0`).  Iterate `ordAtT_deriv_lower_bound`. -/
theorem ordAtT_iterate_deriv_lower_bound {K : Type*} [Field K]
    (D : Derivation K (RatFunc K) (RatFunc K))
    (hd : ∀ p : Polynomial K, D (algebraMap (Polynomial K) (RatFunc K) p)
      = algebraMap (Polynomial K) (RatFunc K) p.derivative)
    (α : K) {h : RatFunc K} (hh : h ≠ 0) (j : ℕ) :
    ((ordAt α h - (j : ℤ) : ℤ) : WithTop ℤ)
      ≤ ordAtT α (((fun x : RatFunc K => D x)^[j]) h) := by
  induction j with
  | zero =>
    rw [Function.iterate_zero, id_eq, ordAtT_def α hh]
    simp
  | succ j ih =>
    rcases eq_or_ne (((fun x : RatFunc K => D x)^[j]) h) 0 with hw | hw
    · rw [Function.iterate_succ_apply', hw]
      simp [ordAtT]
    · rw [ordAtT_def α hw] at ih
      have hj : ordAt α h - (j : ℤ) ≤ ordAt α (((fun x : RatFunc K => D x)^[j]) h) :=
        WithTop.coe_le_coe.mp ih
      have hstep := ordAtT_deriv_lower_bound D hd α hw
      calc ((ordAt α h - ((j + 1 : ℕ) : ℤ) : ℤ) : WithTop ℤ)
          = ((ordAt α h - (j : ℤ) - 1 : ℤ) : WithTop ℤ) := by congr 1; push_cast; ring
        _ ≤ ((ordAt α (((fun x : RatFunc K => D x)^[j]) h) - 1 : ℤ) : WithTop ℤ) :=
              WithTop.coe_le_coe.mpr (by omega)
        _ ≤ ordAtT α (D (((fun x : RatFunc K => D x)^[j]) h)) := hstep
        _ = ordAtT α (((fun x : RatFunc K => D x)^[j + 1]) h) := by
              rw [Function.iterate_succ_apply']

/-- The order-at-`α` estimate for an iterated derivative of a product:
`ord_α(Dᵏ(γ·f)) ≥ ord_α γ + ord_α f − k` (with `ord_α 0 = ⊤`).  This is the local
estimate used at each singularity `α` of a first-order system to bound the order of
the eliminated fourth-order expression `Σᵢ (−1)ⁱ (γᵢ b₃)^{(i)}`, and hence the pole
orders of the `bᵢ` (CDT arXiv:2408.15403, the systems `(onceagain)` and Lemma
`14functions`).  Proof: `Dᵏ(γ f) = Σ_{k'≤k} C(k,k') D^{k'}(γ)·D^{k−k'}(f)` and
`ord_α (Dᵐ h) ≥ ord_α h − m`. -/
theorem ordAtT_iterate_deriv_mul_ge {K : Type*} [Field K]
    (D : Derivation K (RatFunc K) (RatFunc K))
    (hd : ∀ p : Polynomial K, D (algebraMap (Polynomial K) (RatFunc K) p)
      = algebraMap (Polynomial K) (RatFunc K) p.derivative)
    (α : K) (γ f : RatFunc K) (hf : f ≠ 0) (j : ℕ) :
    ordAtT α γ + (ordAt α f : WithTop ℤ) - ((j : ℤ) : WithTop ℤ)
      ≤ ordAtT α ((fun x : RatFunc K => D x)^[j] (γ * f)) := by
  rcases eq_or_ne γ 0 with hγ | hγ
  · subst hγ
    rw [zero_mul, Function.iterate_fixed (map_zero D)]
    simp [ordAtT]
  · have hh : γ * f ≠ 0 := mul_ne_zero hγ hf
    have hiter := ordAtT_iterate_deriv_lower_bound D hd α hh j
    rw [ordAt_mul α hγ hf] at hiter
    rw [ordAtT_def α hγ]
    refine le_trans ?_ hiter
    rw [← WithTop.coe_add, ← WithTop.LinearOrderedAddCommGroup.coe_sub]

end Commons.FieldTheory.RatFunc
