import Mathlib
import Submission.Work.MotV.PlaceDefs
import Submission.Work.MotC2.Defs
import Submission.Work.MotV5.placeVal_valuation
import Submission.Work.MotV5.two_le_ordInf_deriv_of_pole
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The order of vanishing of a polynomial in an element with a pole

Let `E` be a Weierstrass curve over a field `N`, `S` a rational place of the function field `N(E)`
and `r ∈ N(E)` an element with a pole at `S` (`ordOfPlace E S hS r < 0`).  For a polynomial `f` of
degree `n ≥ 2` with `5 ∤ n` (characteristic `5`) the leading term of `f(r)` dominates all others:

`ord (f(r)) = n · ord r`,   `ord (f'(r)) = (n - 1) · ord r`.

The mechanism is the standard one for a non-archimedean absolute value: every term `c i · r ^ i`
with `c i ≠ 0` has order `i · ord r`, these are strictly increasing in `i` because `ord r < 0`, so
the top term `c n · r ^ n` has the strictly smallest order and the ultrametric (no-cancellation)
inequality gives the order of the sum.  The second identity follows because `f'` really has degree
`n - 1`, its leading coefficient being `n · c n ≠ 0` since `5 ∤ n`.

The order function is fed to the elementary `od`-interface through the valuation
`placeValuation E S hS` of `Submission/Work/MotV5/placeVal_valuation.lean`
(`placeValuation_apply`): `placeValuation E S hS f = exp (-(ordOfPlace E S hS f))` for `f ≠ 0`, so
the multiplicative and additive laws of the order are those of a valuation, read through `exp`.
-/

open Polynomial WeierstrassCurve

open scoped WithZero

namespace Work.MotV5

noncomputable section

set_option autoImplicit false
set_option linter.style.haveILetI false

variable {N : Type*} [Field N]

/-! ## §1 The elementary laws of the order at a rational place -/

/-- The order of the zero function at a rational place is `0` (the convention of `ordOfPlace`:
`addVal 0 = ⊤` and `.untopD 0` returns the default `0`). -/
theorem ordOfPlace_zero_local (E : WeierstrassCurve N) (S : Subalgebra N (MotC2.Func E))
    (hS : MotC2.IsRatPlace E S) :
    MotV.ordOfPlace E S hS (0 : MotC2.Func E) = 0 := by
  haveI : IsDiscreteValuationRing ↥S := hS.1.choose
  rw [MotV.ordOfPlace]
  simp only [Subalgebra.zero_mem, ↓reduceDIte]
  rw [show (⟨0, Subalgebra.zero_mem S⟩ : ↥S) = 0 from Subtype.ext rfl,
    IsDiscreteValuationRing.addVal_zero]
  show ((WithTop.untopD (0 : ℕ) (⊤ : WithTop ℕ) : ℕ) : ℤ) = 0
  rw [WithTop.untopD_top]
  norm_num

/-- **Multiplicativity of the order** at a rational place, read off the valuation
`placeValuation E S hS` (whose value on `f ≠ 0` is `exp (-(ord f))`). -/
theorem ordOfPlace_mul_local (E : WeierstrassCurve N) (S : Subalgebra N (MotC2.Func E))
    (hS : MotC2.IsRatPlace E S) {f g : MotC2.Func E} (hf : f ≠ 0) (hg : g ≠ 0) :
    MotV.ordOfPlace E S hS (f * g) =
      MotV.ordOfPlace E S hS f + MotV.ordOfPlace E S hS g := by
  have hv := placeValuation_apply E S hS
  have hfg : f * g ≠ 0 := mul_ne_zero hf hg
  have h1 : WithZero.exp (-(MotV.ordOfPlace E S hS (f * g))) =
      WithZero.exp (-(MotV.ordOfPlace E S hS f)) *
        WithZero.exp (-(MotV.ordOfPlace E S hS g)) := by
    rw [← hv (f * g) hfg, map_mul, hv f hf, hv g hg]
  rw [← WithZero.exp_add, WithZero.exp_inj] at h1
  linarith

/-- **No cancellation at a rational place**: if `ord f < ord g` and `f ≠ 0`, then
`ord (f + g) = ord f`. -/
theorem ordOfPlace_add_eq_of_lt_local (E : WeierstrassCurve N) (S : Subalgebra N (MotC2.Func E))
    (hS : MotC2.IsRatPlace E S) {f : MotC2.Func E} (hf : f ≠ 0) (g : MotC2.Func E)
    (h : MotV.ordOfPlace E S hS f < MotV.ordOfPlace E S hS g) :
    MotV.ordOfPlace E S hS (f + g) = MotV.ordOfPlace E S hS f := by
  rcases eq_or_ne g 0 with rfl | hg
  · rw [add_zero]
  have hv := placeValuation_apply E S hS
  have hlt : placeValuation E S hS g < placeValuation E S hS f := by
    rw [hv g hg, hv f hf, WithZero.exp_lt_exp]
    omega
  have hadd : placeValuation E S hS (f + g) = placeValuation E S hS f :=
    Valuation.map_add_eq_of_lt_left _ hlt
  have hvne : placeValuation E S hS f ≠ 0 := (Valuation.ne_zero_iff _).mpr hf
  have hfg : f + g ≠ 0 := by
    intro h0
    rw [h0, Valuation.map_zero] at hadd
    exact hvne hadd.symm
  have h1 : WithZero.exp (-(MotV.ordOfPlace E S hS (f + g))) =
      WithZero.exp (-(MotV.ordOfPlace E S hS f)) := by
    rw [← hv (f + g) hfg, ← hv f hf, hadd]
  rw [WithZero.exp_inj] at h1
  linarith

/-- **The order of a constant is zero** at a rational place (for `c = 0` this is the convention
`ordOfPlace 0 = 0`). -/
theorem ordOfPlace_algebraMap_local (E : WeierstrassCurve N) (S : Subalgebra N (MotC2.Func E))
    (hS : MotC2.IsRatPlace E S) (c : N) :
    MotV.ordOfPlace E S hS (algebraMap N (MotC2.Func E) c) = 0 := by
  rcases eq_or_ne c 0 with rfl | hc
  · rw [map_zero]
    exact ordOfPlace_zero_local E S hS
  obtain ⟨v, hvTriv, hv1, -, -⟩ := placeVal_valuation E S hS
  have hc0 : algebraMap N (MotC2.Func E) c ≠ 0 := fun h =>
    hc ((FaithfulSMul.algebraMap_injective N (MotC2.Func E)) (by simpa using h))
  have h1 : WithZero.exp (-(MotV.ordOfPlace E S hS (algebraMap N (MotC2.Func E) c))) = 1 := by
    rw [← hv1 _ hc0, hvTriv c hc]
  rw [← WithZero.exp_zero] at h1
  have h2 := WithZero.exp_inj.mp h1
  linarith

/-! ## §2 The dominating-term lemma for a general order function -/

/-- **The leading term dominates.**  Let `od : B → ℤ` be the order function of a place of a field
`B` over a field `A` — multiplicative, with no cancellation, additive on constants.  For an element
`r` with `od r < 0` (a pole) and any polynomial `g` over `A`,
`od (g(r)) = deg g · od r`: the highest degree term is the only one of minimal order. -/
theorem aeval_ord_eq_of_neg_aux {A B : Type*} [Field A] [Field B] [Algebra A B] (od : B → ℤ)
    (hzero : od 0 = 0) (hmul : ∀ x y : B, x ≠ 0 → y ≠ 0 → od (x * y) = od x + od y)
    (hadd : ∀ x : B, x ≠ 0 → ∀ y : B, od x < od y → od (x + y) = od x)
    (hconst : ∀ c : A, od (algebraMap A B c) = 0)
    {r : B} (hr : od r < 0) (g : Polynomial A) :
    od (Polynomial.aeval r g) = (g.natDegree : ℤ) * od r := by
  have hr0 : r ≠ 0 := by
    intro h
    rw [h, hzero] at hr
    exact lt_irrefl 0 hr
  -- the order of a power
  have hpow : ∀ n : ℕ, od (r ^ n) = (n : ℤ) * od r := by
    intro n
    induction n with
    | zero => simpa using hconst 1
    | succ n ih =>
      rw [pow_succ, hmul _ _ (pow_ne_zero n hr0) hr0, ih]
      push_cast
      first | refl_ring1 | ring
  -- strong induction on the degree
  have key : ∀ n : ℕ, ∀ g : Polynomial A, g.natDegree = n →
      od (Polynomial.aeval r g) = (n : ℤ) * od r := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro g hgn
      rcases Nat.eq_zero_or_pos n with hn | hn
      · -- a constant
        subst hn
        rw [Polynomial.eq_C_of_natDegree_eq_zero hgn, Polynomial.aeval_C, hconst]
        first | refl_ring1 | ring
      · have hgne : g ≠ 0 := by
          intro h
          rw [h, Polynomial.natDegree_zero] at hgn
          omega
        have hcoeff : g.coeff n ≠ 0 := by
          have h := Polynomial.leadingCoeff_ne_zero.mpr hgne
          rwa [Polynomial.leadingCoeff, hgn] at h
        have hxnz : algebraMap A B (g.coeff n) ≠ 0 := by
          simpa using (FaithfulSMul.algebraMap_injective A B).ne hcoeff
        have hpownz : r ^ n ≠ 0 := pow_ne_zero n hr0
        have hdecomp : g = g.eraseLead + Polynomial.C (g.coeff n) * Polynomial.X ^ n := by
          rw [← hgn]
          exact (Polynomial.eraseLead_add_C_mul_X_pow g).symm
        have haeval : Polynomial.aeval r g =
            Polynomial.aeval r g.eraseLead + algebraMap A B (g.coeff n) * r ^ n := by
          conv_lhs => rw [hdecomp]
          rw [map_add, map_mul, Polynomial.aeval_C, Polynomial.aeval_X_pow]
        have htop : od (algebraMap A B (g.coeff n) * r ^ n) = (n : ℤ) * od r := by
          rw [hmul _ _ hxnz hpownz, hconst, zero_add, hpow n]
        rw [haeval]
        rcases Polynomial.eraseLead_natDegree_lt_or_eraseLead_eq_zero g with hlt | heq
        · rw [hgn] at hlt
          have hrest : od (Polynomial.aeval r g.eraseLead) =
              (g.eraseLead.natDegree : ℤ) * od r := ih _ hlt _ rfl
          have hlt' : od (algebraMap A B (g.coeff n) * r ^ n) <
              od (Polynomial.aeval r g.eraseLead) := by
            rw [htop, hrest]
            have hcast : (g.eraseLead.natDegree : ℤ) < (n : ℤ) := by exact_mod_cast hlt
            nlinarith [hr]
          rw [add_comm, hadd _ (mul_ne_zero hxnz hpownz) _ hlt', htop]
        · rw [heq, map_zero, zero_add, htop]
  exact key g.natDegree g rfl

/-! ## §3 The target -/

/-- **The pole order of a polynomial in `r`.**  If `r ∈ N(E)` has a pole at the rational place `S`
and `f` has degree `n ≥ 2` with `5 ∤ n` (characteristic `5`), then `f(r)` has a pole of order
`n · ord r` and `f'(r)` a pole of order `(n - 1) · ord r` at `S`. -/
theorem aeval_order_pole {N : Type*} [Field N] [CharP N 5] (E : WeierstrassCurve N)
    (f : Polynomial N) (hf2 : 2 ≤ f.natDegree) (hf5 : ¬ 5 ∣ f.natDegree)
    (S : Subalgebra N (Work.MotC2.Func E)) (hS : Work.MotC2.IsRatPlace E S)
    (r : Work.MotC2.Func E) (h : Work.MotV.ordOfPlace E S hS r < 0) :
    Work.MotV.ordOfPlace E S hS (Polynomial.aeval r f) =
        f.natDegree * Work.MotV.ordOfPlace E S hS r ∧
      Work.MotV.ordOfPlace E S hS (Polynomial.aeval r f.derivative) =
        (f.natDegree - 1) * Work.MotV.ordOfPlace E S hS r := by
  have hmain := aeval_ord_eq_of_neg_aux (A := N) (B := MotC2.Func E)
    (od := fun x => MotV.ordOfPlace E S hS x)
    (ordOfPlace_zero_local E S hS)
    (fun x y hx hy => ordOfPlace_mul_local E S hS hx hy)
    (fun x hx y hy => ordOfPlace_add_eq_of_lt_local E S hS hx y hy)
    (fun c => ordOfPlace_algebraMap_local E S hS c) h f
  have hderiv := aeval_ord_eq_of_neg_aux (A := N) (B := MotC2.Func E)
    (od := fun x => MotV.ordOfPlace E S hS x)
    (ordOfPlace_zero_local E S hS)
    (fun x y hx hy => ordOfPlace_mul_local E S hS hx hy)
    (fun x hx y hy => ordOfPlace_add_eq_of_lt_local E S hS hx y hy)
    (fun c => ordOfPlace_algebraMap_local E S hS c) h f.derivative
  rw [natDegree_derivative_eq_of_not_dvd (M := N) hf5] at hderiv
  have hcast : ((f.natDegree - 1 : ℕ) : ℤ) = (f.natDegree : ℤ) - 1 := by
    rw [Int.natCast_sub (show 1 ≤ f.natDegree by omega)]
    norm_num
  rw [hcast] at hderiv
  exact ⟨hmain, hderiv⟩

end

end Work.MotV5
