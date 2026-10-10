/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Work.MotV

# The order at infinity of `p(x) + q(x)·y`

Let `E : WeierstrassCurve N` be an elliptic curve over a field `N`, and let `x = genX E`,
`y = genY E` be the coordinates in the function field `N(E)`.  At the point at infinity `O` the
coordinate `x` has a pole of order `2` and `y` a pole of order `3`.  Hence for polynomials
`p, q ∈ N[X]` the two summands of

  `f = p(x) + q(x)·y`

have pole orders `2·deg p` and `2·deg q + 3`, which have *opposite parity* and therefore can never
cancel; the order of the sum is minus the larger of the two.

The main theorem `Work.MotV.ordAevalSum` states exactly this:

`ord_O (p(x) + q(x)·y) = -max (2·deg p) (2·deg q + 3)`,

where the degree is taken in `WithBot ℕ` (`deg 0 = ⊥`, so that `-max(⊥, ⊥)` gives `0`, the order of
the zero function).

The key input is the "dominating term" lemma `ordOfPlace_aeval_of_neg`: if `r` has a pole at a
rational place `S`, then `g(r)` has order `g.natDegree · ord r` for every polynomial `g` — the
leading term of `g(r)` is the unique term of minimal order, and the ultrametric inequality turns
this into an exact computation.
-/

import Mathlib
import Submission.Work.MotV.ordBasic
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open WeierstrassCurve WeierstrassCurve.Affine
open scoped WithZero

namespace Work.MotV

noncomputable section

variable {N : Type*} [Field N]

/-! ## §1 Elementary laws of the order at a rational place -/

section Laws

variable (E : WeierstrassCurve N) [E.IsElliptic] (H : H1Data N E)
variable (S : Subalgebra N (MotC2.Func E)) (hS : MotC2.IsRatPlace E S)
include H

/-- The order of the zero function is `0` (the convention built into `ordOfPlace`). -/
private lemma ordZero : ordOfPlace E S hS (0 : MotC2.Func E) = 0 := by
  haveI : IsDiscreteValuationRing ↥S := hS.1.choose
  rw [ordOfPlace]
  simp only [Subalgebra.zero_mem, ↓reduceDIte]
  rw [show (⟨0, Subalgebra.zero_mem S⟩ : ↥S) = 0 from Subtype.ext rfl,
    IsDiscreteValuationRing.addVal_zero]
  show ((WithTop.untopD (0 : ℕ) (⊤ : WithTop ℕ) : ℕ) : ℤ) = 0
  rw [WithTop.untopD_top]
  norm_num

/-- The order of a constant is `0` (including the zero constant). -/
private lemma ordConst (c : N) :
    ordOfPlace E S hS (algebraMap N (MotC2.Func E) c) = 0 := by
  rcases eq_or_ne c 0 with rfl | hc
  · rw [map_zero]
    exact ordZero E H S hS
  · exact ordOfPlace_const E H S hS c hc

/-- **No cancellation.**  If `f ≠ 0` and `ord f < ord g` then `ord (f + g) = ord f`.  Unlike
`ordOfPlace_add_eq_of_lt` of the parent file, this version needs no hypothesis on `f + g`: it is
automatic there, because `f + g = 0` would force `g = -f`, hence `ord g = ord f`. -/
private lemma ordAddOfLt {f g : MotC2.Func E} (hf : f ≠ 0)
    (h : ordOfPlace E S hS f < ordOfPlace E S hS g) :
    ordOfPlace E S hS (f + g) = ordOfPlace E S hS f := by
  rcases eq_or_ne g 0 with rfl | hg
  · rw [add_zero]
  have hfg : f + g ≠ 0 := by
    intro h0
    have hgf : g = -f := ((neg_eq_iff_add_eq_zero).mpr h0).symm
    rw [hgf, ordOfPlace_neg E H S hS f hf] at h
    exact lt_irrefl _ h
  have hle : ordOfPlace E S hS f ≤ ordOfPlace E S hS (f + g) := by
    have hh := H.ord_add S hS f g hfg
    rwa [min_eq_left (le_of_lt h)] at hh
  by_contra hne
  have hlt : ordOfPlace E S hS f < ordOfPlace E S hS (f + g) :=
    lt_of_le_of_ne hle (Ne.symm hne)
  have hsum := H.ord_add S hS (f + g) (-g) (by rw [add_neg_cancel_right]; exact hf)
  rw [add_neg_cancel_right, ordOfPlace_neg E H S hS g hg] at hsum
  exact absurd hsum (not_le.mpr (lt_min hlt h))

/-- If `f, g ≠ 0` have different orders then `ord (f + g) = min (ord f) (ord g)`. -/
private lemma ordAddEqMin {f g : MotC2.Func E} (hf : f ≠ 0) (hg : g ≠ 0)
    (hne : ordOfPlace E S hS f ≠ ordOfPlace E S hS g) :
    ordOfPlace E S hS (f + g) =
      min (ordOfPlace E S hS f) (ordOfPlace E S hS g) := by
  rcases lt_or_gt_of_ne hne with h | h
  · rw [ordAddOfLt E H S hS hf h, min_eq_left (le_of_lt h)]
  · rw [add_comm, ordAddOfLt E H S hS hg h, min_eq_right (le_of_lt h)]

/-- **Dominating term.**  If `r` has a pole at the rational place `S` then, for every polynomial
`g`, the element `g(r)` has order `g.natDegree · ord r`: the leading term of `g(r)` is the unique
term of minimal order, so the ultrametric inequality is an equality.

(For `g = 0` both sides are `0`.) -/
theorem ordOfPlace_aeval_of_neg (r : MotC2.Func E)
    (hr : ordOfPlace E S hS r < 0) (g : Polynomial N) :
    ordOfPlace E S hS (Polynomial.aeval r g) =
      (g.natDegree : ℤ) * ordOfPlace E S hS r := by
  have hr0 : r ≠ 0 := by
    intro h0
    rw [h0, ordZero E H S hS] at hr
    exact lt_irrefl 0 hr
  have hpow : ∀ n : ℕ, ordOfPlace E S hS (r ^ n) = (n : ℤ) * ordOfPlace E S hS r :=
    fun n => ordOfPlace_pow E H S hS r hr0 n
  -- strong induction on the degree of `g`
  have key : ∀ n : ℕ, ∀ g : Polynomial N, g.natDegree = n →
      ordOfPlace E S hS (Polynomial.aeval r g) = (n : ℤ) * ordOfPlace E S hS r := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro g hgn
      rcases Nat.eq_zero_or_pos n with hn | hn
      · -- `g` is a constant
        subst hn
        rw [Polynomial.eq_C_of_natDegree_eq_zero hgn, Polynomial.aeval_C,
          ordConst E H S hS]
        first | refl_ring1 | ring
      · have hgne : g ≠ 0 := by
          intro hh
          rw [hh, Polynomial.natDegree_zero] at hgn
          omega
        have hcoeff : g.coeff n ≠ 0 := by
          have h := Polynomial.leadingCoeff_ne_zero.mpr hgne
          rwa [Polynomial.leadingCoeff, hgn] at h
        have hxnz : algebraMap N (MotC2.Func E) (g.coeff n) ≠ 0 := by
          simpa using (FaithfulSMul.algebraMap_injective N (MotC2.Func E)).ne hcoeff
        have hpownz : r ^ n ≠ 0 := pow_ne_zero n hr0
        have hdecomp : g = g.eraseLead + Polynomial.C (g.coeff n) * Polynomial.X ^ n := by
          rw [← hgn]
          exact (Polynomial.eraseLead_add_C_mul_X_pow g).symm
        have haeval : Polynomial.aeval r g =
            Polynomial.aeval r g.eraseLead +
              algebraMap N (MotC2.Func E) (g.coeff n) * r ^ n := by
          conv_lhs => rw [hdecomp]
          rw [Polynomial.aeval_add, Polynomial.aeval_mul, Polynomial.aeval_C,
            Polynomial.aeval_X_pow]
        have htop : ordOfPlace E S hS
            (algebraMap N (MotC2.Func E) (g.coeff n) * r ^ n) =
            (n : ℤ) * ordOfPlace E S hS r := by
          rw [H.ord_mul S hS (algebraMap N (MotC2.Func E) (g.coeff n)) (r ^ n) hxnz hpownz,
            ordConst E H S hS (g.coeff n), zero_add, hpow n]
        rw [haeval]
        rcases Polynomial.eraseLead_natDegree_lt_or_eraseLead_eq_zero g with hlt | heq
        · rw [hgn] at hlt
          have hrest := ih g.eraseLead.natDegree hlt g.eraseLead rfl
          have hlt' : ordOfPlace E S hS
              (algebraMap N (MotC2.Func E) (g.coeff n) * r ^ n) <
              ordOfPlace E S hS (Polynomial.aeval r g.eraseLead) := by
            rw [htop, hrest]
            have hcast : (g.eraseLead.natDegree : ℤ) < (n : ℤ) := by exact_mod_cast hlt
            exact mul_lt_mul_of_neg_right hcast hr
          rw [add_comm, ordAddOfLt E H S hS (mul_ne_zero hxnz hpownz) hlt', htop]
        · rw [heq, Polynomial.aeval_zero, zero_add, htop]
  exact key g.natDegree g rfl

end Laws

/-! ## §2 The degree arithmetic of the right-hand side

The right-hand side of `ordAevalSum` involves `max (2 • p.degree) (2 • q.degree + 3)` in
`WithBot ℕ` together with the `unbotD` projection; here it is evaluated in the three cases
`p = 0` / `q = 0` / both nonzero. -/

section DegreeArith

private lemma unbotD_some (m : ℕ) : (WithBot.some m).unbotD 0 = m := by
  rw [WithBot.unbotD_coe]

private lemma unbotD_max_some (m n : ℕ) :
    (max (WithBot.some m) (WithBot.some n)).unbotD 0 = max m n := by
  rw [← WithBot.coe_max, WithBot.unbotD_coe]

private lemma two_nsmul_degree_eq (p : Polynomial N) (hp : p ≠ 0) :
    (2 • p.degree : WithBot ℕ) = WithBot.some (2 * p.natDegree) := by
  rw [Polynomial.degree_eq_natDegree hp]
  change ((2 : ℕ) • (WithBot.some p.natDegree)) = WithBot.some (2 * p.natDegree)
  rw [two_nsmul]
  change WithBot.some (p.natDegree + p.natDegree) = WithBot.some (2 * p.natDegree)
  rw [two_mul]

private lemma two_nsmul_degree_add_three_eq (q : Polynomial N) (hq : q ≠ 0) :
    (2 • q.degree + 3 : WithBot ℕ) = WithBot.some (2 * q.natDegree + 3) := by
  rw [Polynomial.degree_eq_natDegree hq]
  change ((2 : ℕ) • (WithBot.some q.natDegree) + WithBot.some 3) =
    WithBot.some (2 * q.natDegree + 3)
  rw [two_nsmul]
  change WithBot.some (q.natDegree + q.natDegree + 3) = WithBot.some (2 * q.natDegree + 3)
  rw [two_mul]

private lemma two_nsmul_zero_degree_eq :
    (2 • (0 : Polynomial N).degree : WithBot ℕ) = ⊥ := by
  rw [Polynomial.degree_zero]; simp

private lemma two_nsmul_zero_degree_add_three_eq :
    (2 • (0 : Polynomial N).degree + 3 : WithBot ℕ) = ⊥ := by
  rw [Polynomial.degree_zero]; simp

end DegreeArith

/-! ## §3 The main theorem -/

theorem ordAevalSum {N : Type*} [Field N] (E : WeierstrassCurve N) [E.IsElliptic]
    (H : Work.MotV.H1Data N E) (p q : Polynomial N) (h : p ≠ 0 ∨ q ≠ 0) :
    Work.MotV.ordOfPlace E (Work.MotC2.infPlace E) H.infRat
      (Polynomial.aeval (Work.MotC2.genX E) p +
        Polynomial.aeval (Work.MotC2.genX E) q * Work.MotC2.genY E)
      = - (((max (2 • p.degree) (2 • q.degree + 3)).unbotD 0 : ℕ) : ℤ) := by
  have hGX : ordOfPlace E (MotC2.infPlace E) H.infRat (MotC2.genX E) = -2 := H.inf_local.1
  have hGY : ordOfPlace E (MotC2.infPlace E) H.infRat (MotC2.genY E) = -3 := H.inf_local.2.2.2
  have hY : MotC2.genY E ≠ 0 := genY_ne_zero E
  -- the pole order of a polynomial in `x`
  have hAeval : ∀ g : Polynomial N,
      ordOfPlace E (MotC2.infPlace E) H.infRat (Polynomial.aeval (MotC2.genX E) g)
        = -(2 * (g.natDegree : ℤ)) := by
    intro g
    have hlt : ordOfPlace E (MotC2.infPlace E) H.infRat (MotC2.genX E) < 0 := by
      rw [hGX]; norm_num
    have hmain := ordOfPlace_aeval_of_neg E H (MotC2.infPlace E) H.infRat (MotC2.genX E) hlt g
    rw [hGX] at hmain
    rw [hmain]; ring
  -- the pole order of `q(x)·y`
  have hBeval : ∀ g : Polynomial N, g ≠ 0 →
      ordOfPlace E (MotC2.infPlace E) H.infRat
        (Polynomial.aeval (MotC2.genX E) g * MotC2.genY E)
        = -(2 * (g.natDegree : ℤ) + 3) := by
    intro g hg
    rw [H.ord_mul (MotC2.infPlace E) H.infRat _ _
        (MotC2.aeval_genX_ne_zero E hg) hY, hAeval g, hGY]
    first | refl_ring1 | ring
  by_cases hp : p = 0
  · by_cases hq : q = 0
    · exact (h.elim (fun hp' => hp' hp) (fun hq' => hq' hq)).elim
    · -- `p = 0`, `q ≠ 0`
      have hpa : Polynomial.aeval (MotC2.genX E) p = 0 := by
        rw [hp, Polynomial.aeval_zero]
      have hR : (max (2 • p.degree) (2 • q.degree + 3)).unbotD 0 = 2 * q.natDegree + 3 := by
        rw [hp, two_nsmul_zero_degree_eq, two_nsmul_degree_add_three_eq q hq,
          max_eq_right bot_le, unbotD_some]
      rw [hpa, zero_add, hBeval q hq, hR]
      push_cast
      first | refl_ring1 | ring
  · by_cases hq : q = 0
    · -- `p ≠ 0`, `q = 0`
      have hqa : Polynomial.aeval (MotC2.genX E) q * MotC2.genY E = 0 := by
        rw [hq, Polynomial.aeval_zero, zero_mul]
      have hR : (max (2 • p.degree) (2 • q.degree + 3)).unbotD 0 = 2 * p.natDegree := by
        rw [hq, two_nsmul_zero_degree_add_three_eq, two_nsmul_degree_eq p hp,
          max_eq_left bot_le, unbotD_some]
      rw [hqa, add_zero, hAeval p, hR]
      push_cast
      first | refl_ring1 | ring
    · -- both nonzero: the two pole orders have opposite parity, so no cancellation
      have hAne : Polynomial.aeval (MotC2.genX E) p ≠ 0 := MotC2.aeval_genX_ne_zero E hp
      have hBne : Polynomial.aeval (MotC2.genX E) q * MotC2.genY E ≠ 0 :=
        mul_ne_zero (MotC2.aeval_genX_ne_zero E hq) hY
      have hne : ordOfPlace E (MotC2.infPlace E) H.infRat
            (Polynomial.aeval (MotC2.genX E) p) ≠
          ordOfPlace E (MotC2.infPlace E) H.infRat
            (Polynomial.aeval (MotC2.genX E) q * MotC2.genY E) := by
        rw [hAeval p, hBeval q hq]
        intro hcon
        omega
      have hR : (max (2 • p.degree) (2 • q.degree + 3)).unbotD 0
          = max (2 * p.natDegree) (2 * q.natDegree + 3) := by
        rw [two_nsmul_degree_eq p hp, two_nsmul_degree_add_three_eq q hq]
        exact unbotD_max_some _ _
      rw [ordAddEqMin E H (MotC2.infPlace E) H.infRat hAne hBne hne,
        hAeval p, hBeval q hq, min_neg_neg, hR]
      push_cast
      first | refl_ring1 | ring

end

end Work.MotV
