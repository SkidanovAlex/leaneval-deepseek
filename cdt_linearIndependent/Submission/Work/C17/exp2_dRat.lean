import Mathlib
import Submission.Work.C17.exp2_defs
import Submission.Commons.FieldTheory.RatFunc.ordAtT_iterate_deriv_mul_ge

namespace Work.C17

open Commons.FieldTheory.RatFunc

noncomputable section

set_option linter.style.haveILetI false

/-! ## `dRat` as a derivation, and the Euler identity

The formal derivative `Submission.CDT.dRat` of `ℚ(x)` is a derivation (`dRatDeriv` below);
`Derivation.leibniz_zpow` then computes `dRat (xQ ^ e)` for every integer `e`, since the
Euler operator `x·d/dx` satisfies `(x·d/dx)(x^e) = e·x^e`.  Together with the elementary
order bound `ord_0 (dRat H) ≥ ord_0 H − 1` (proved below from the logarithmic-derivative
decomposition of `dRat`), this yields `exp2_dRat`.
-/

/-- `dRat` kills the constants. -/
lemma dRat_C_rat (c : ℚ) : Submission.CDT.dRat (algebraMap ℚ (RatFunc ℚ) c) = 0 := by
  rw [IsScalarTower.algebraMap_apply ℚ (Polynomial ℚ) (RatFunc ℚ) c,
    show (algebraMap ℚ (Polynomial ℚ)) c = Polynomial.C c from
      (Polynomial.C_eq_algebraMap c).symm,
    Submission.CDT.dRat_algebraMap, Polynomial.derivative_C, map_zero]

/-- `dRat xQ = 1`. -/
lemma dRat_xQ : Submission.CDT.dRat xQ = 1 := by
  rw [xQ_eq_algebraMap, Submission.CDT.dRat_algebraMap, Polynomial.derivative_X, map_one]

/-- `dRat` as a `ℚ`-derivation of `ℚ(x)`. -/
def dRatDeriv : Derivation ℚ (RatFunc ℚ) (RatFunc ℚ) where
  toFun := Submission.CDT.dRat
  map_add' := Submission.CDT.dRat_add
  map_smul' := by
    intro c f
    simp only [Algebra.smul_def, RingHom.id_apply, Submission.CDT.dRat_mul, dRat_C_rat,
      zero_mul, zero_add]
  map_one_eq_zero' := Submission.CDT.dRat_one
  leibniz' := by
    intro a b
    change Submission.CDT.dRat (a * b) =
      a * Submission.CDT.dRat b + b * Submission.CDT.dRat a
    rw [Submission.CDT.dRat_mul]
    ring

/-- The integer cast of `ℚ(x)` is the `ℚ`-algebra map. -/
lemma intCast_ratFunc_eq (n : ℤ) : (n : RatFunc ℚ) = algebraMap ℚ (RatFunc ℚ) (n : ℚ) :=
  (map_intCast (algebraMap ℚ (RatFunc ℚ)) n).symm

/-- `dRat (xQ^e) = e·xQ^{e-1}` for every integer `e`. -/
lemma dRat_xQ_zpow (e : ℤ) :
    Submission.CDT.dRat (xQ ^ e) = (e : RatFunc ℚ) * xQ ^ (e - 1) := by
  have h := Derivation.leibniz_zpow (R := ℚ) dRatDeriv xQ e
  rw [show dRatDeriv xQ = (1 : RatFunc ℚ) from dRat_xQ,
    show dRatDeriv (xQ ^ e) = Submission.CDT.dRat (xQ ^ e) from rfl] at h
  simpa only [smul_eq_mul, mul_one, zsmul_eq_mul] using h

/-! ## The order bound for `dRat` -/

/-- `↑(a - 1) = ↑a + ↑(-1)` in `WithTop ℤ`. -/
lemma withTop_coe_sub_one (a : ℤ) :
    ((a - 1 : ℤ) : WithTop ℤ) = ((a : ℤ) : WithTop ℤ) + ((-1 : ℤ) : WithTop ℤ) := by
  rw [sub_eq_add_neg, WithTop.coe_add]

/-- `dRat` lowers the order of vanishing at `0` by at most one.  Written as
`dRat h = h · (A − B)` with `A`, `B` the logarithmic derivatives of numerator and
denominator of `h`; both have order `≥ -1`. -/
lemma ordAtT_dRat_lower_bound {H : RatFunc ℚ} (hH0 : H ≠ 0) :
    ((ordAt (0 : ℚ) H - 1 : ℤ) : WithTop ℤ) ≤ ordAtT (0 : ℚ) (Submission.CDT.dRat H) := by
  -- the two `ℚ`-algebra structures on `ℚ(x)` are propositionally equal; the lemmas from
  -- `Commons.FieldTheory.RatFunc` are stated for the `ℚ[X]`-flavoured one, so we install it
  -- locally (as `Submission/Work/ZeroEst/orbit_prefix.lean` does).
  letI : Algebra ℚ (RatFunc ℚ) := RatFunc.instAlgebraOfPolynomial ℚ ℚ
  have hC : ∀ c : ℚ, algebraMap ℚ (RatFunc ℚ) c
      = algebraMap (Polynomial ℚ) (RatFunc ℚ) (Polynomial.C c) := by
    intro c
    rw [IsScalarTower.algebraMap_apply ℚ (Polynomial ℚ) (RatFunc ℚ) c,
      show (algebraMap ℚ (Polynomial ℚ)) c = Polynomial.C c from
        (Polynomial.C_eq_algebraMap c).symm]
  let D : Derivation ℚ (RatFunc ℚ) (RatFunc ℚ) :=
    { toFun := Submission.CDT.dRat
      map_add' := Submission.CDT.dRat_add
      map_smul' := by
        intro c f
        rw [Algebra.smul_def, Algebra.smul_def, RingHom.id_apply, hC c]
        rw [Submission.CDT.dRat_mul, Submission.CDT.dRat_algebraMap, Polynomial.derivative_C,
          map_zero, zero_mul, zero_add]
      map_one_eq_zero' := Submission.CDT.dRat_one
      leibniz' := by
        intro a b
        change Submission.CDT.dRat (a * b) =
          a * Submission.CDT.dRat b + b * Submission.CDT.dRat a
        rw [Submission.CDT.dRat_mul]
        ring }
  have hd : ∀ p : Polynomial ℚ, D (algebraMap (Polynomial ℚ) (RatFunc ℚ) p)
      = algebraMap (Polynomial ℚ) (RatFunc ℚ) p.derivative :=
    fun p => Submission.CDT.dRat_algebraMap p
  have hdec : Submission.CDT.dRat H = H *
      (algebraMap (Polynomial ℚ) (RatFunc ℚ) H.num.derivative
            / algebraMap (Polynomial ℚ) (RatFunc ℚ) H.num
        - (algebraMap (Polynomial ℚ) (RatFunc ℚ) H.denom.derivative
            / algebraMap (Polynomial ℚ) (RatFunc ℚ) H.denom)) := by
    rw [show Submission.CDT.dRat H = D H from rfl, deriv_eq_mul_sub_logDeriv D hd hH0]
    ring
  have hAB : ((-1 : ℤ) : WithTop ℤ) ≤ ordAtT (0 : ℚ)
      (algebraMap (Polynomial ℚ) (RatFunc ℚ) H.num.derivative
            / algebraMap (Polynomial ℚ) (RatFunc ℚ) H.num
        - (algebraMap (Polynomial ℚ) (RatFunc ℚ) H.denom.derivative
            / algebraMap (Polynomial ℚ) (RatFunc ℚ) H.denom)) :=
    neg_one_le_ordAtT_logDeriv_sub (0 : ℚ) H
  set W : RatFunc ℚ :=
    algebraMap (Polynomial ℚ) (RatFunc ℚ) H.num.derivative
          / algebraMap (Polynomial ℚ) (RatFunc ℚ) H.num
      - (algebraMap (Polynomial ℚ) (RatFunc ℚ) H.denom.derivative
          / algebraMap (Polynomial ℚ) (RatFunc ℚ) H.denom) with hW
  rw [hdec]
  rcases eq_or_ne W 0 with h0 | h0
  · rw [h0, mul_zero, ordAtT_zero]; exact le_top
  · rw [ordAtT_mul (0 : ℚ) hH0 h0]
    calc ((ordAt (0 : ℚ) H - 1 : ℤ) : WithTop ℤ)
        = ((ordAt (0 : ℚ) H : ℤ) : WithTop ℤ) + ((-1 : ℤ) : WithTop ℤ) :=
          withTop_coe_sub_one (ordAt (0 : ℚ) H)
      _ ≤ ((ordAt (0 : ℚ) H : ℤ) : WithTop ℤ) + ordAtT (0 : ℚ) W := add_le_add le_rfl hAB
      _ = ordAtT (0 : ℚ) H + ordAtT (0 : ℚ) W := by rw [ordAtT_def (0 : ℚ) hH0]

/-- `xQ * dRat H` has order at least that of `H`. -/
lemma ordAtT_xQ_mul_dRat_ge {H : RatFunc ℚ} {k : ℤ}
    (hH : ((k : ℤ) : WithTop ℤ) ≤ ordAtT (0 : ℚ) H) :
    ((k : ℤ) : WithTop ℤ) ≤ ordAtT (0 : ℚ) (xQ * Submission.CDT.dRat H) := by
  rcases eq_or_ne H 0 with rfl | hH0
  · rw [Submission.CDT.dRat_zero, mul_zero, ordAtT_zero]; exact le_top
  rcases eq_or_ne (Submission.CDT.dRat H) 0 with h0 | h0
  · rw [h0, mul_zero, ordAtT_zero]; exact le_top
  · rw [ordAtT_mul (0 : ℚ) xQ_ne_zero h0, ordAtT_xQ]
    have hk : k ≤ ordAt (0 : ℚ) H := by
      have hh := hH
      rw [ordAtT_def (0 : ℚ) hH0] at hh
      exact WithTop.coe_le_coe.mp hh
    have hb := ordAtT_dRat_lower_bound hH0
    calc ((k : ℤ) : WithTop ℤ) ≤ ((ordAt (0 : ℚ) H : ℤ) : WithTop ℤ) :=
          withTop_coe_le_coe_int hk
      _ = ((1 : ℤ) : WithTop ℤ) + ((ordAt (0 : ℚ) H - 1 : ℤ) : WithTop ℤ) := by
            rw [← WithTop.coe_add]; congr 1; ring
      _ ≤ ((1 : ℤ) : WithTop ℤ) + ordAtT (0 : ℚ) (Submission.CDT.dRat H) :=
            add_le_add le_rfl hb

/-- Multiplying by a constant does not lower the order. -/
lemma ordAtT_const_mul_ge {c : ℚ} {H : RatFunc ℚ} {k : ℤ}
    (hH : ((k : ℤ) : WithTop ℤ) ≤ ordAtT (0 : ℚ) H) :
    ((k : ℤ) : WithTop ℤ) ≤ ordAtT (0 : ℚ) (algebraMap ℚ (RatFunc ℚ) c * H) := by
  rcases eq_or_ne c 0 with rfl | hc
  · rw [map_zero, zero_mul, ordAtT_zero]; exact le_top
  rcases eq_or_ne H 0 with rfl | hH0
  · rw [mul_zero, ordAtT_zero]; exact le_top
  · have hc0 : algebraMap ℚ (RatFunc ℚ) c ≠ 0 := fun h =>
      hc ((algebraMap ℚ (RatFunc ℚ)).injective (by rw [h, map_zero]))
    rw [ordAtT_mul (0 : ℚ) hc0 hH0, ordAtT_rat hc, zero_add]
    exact hH

theorem exp2_dRat {f : RatFunc ℚ} {e : ℤ} {l m : ℚ} (hf : Exp2 f e l m) :
    Exp2 (Submission.CDT.dRat f) (e - 1) (e * l) ((e + 1) * m) := by
  unfold Exp2 at hf ⊢
  set H : RatFunc ℚ :=
    f * xQ ^ (-e) - algebraMap ℚ (RatFunc ℚ) l - algebraMap ℚ (RatFunc ℚ) m * xQ with hH
  set G : RatFunc ℚ :=
    algebraMap ℚ (RatFunc ℚ) l + algebraMap ℚ (RatFunc ℚ) m * xQ + H with hG
  have hHord : ((2 : ℤ) : WithTop ℤ) ≤ ordAtT (0 : ℚ) H := hf
  -- `f = xQ^e · G`
  have hfG : f = xQ ^ e * G := by
    have h1 : f * xQ ^ (-e) = G := by rw [hG, hH]; ring
    calc f = f * 1 := (mul_one f).symm
      _ = f * (xQ ^ e * xQ ^ (-e)) := by
            rw [← zpow_add₀ xQ_ne_zero, show e + -e = 0 by ring, zpow_zero]
      _ = (f * xQ ^ (-e)) * xQ ^ e := by ring
      _ = G * xQ ^ e := by rw [h1]
      _ = xQ ^ e * G := by ring
  have hdG : Submission.CDT.dRat G =
      algebraMap ℚ (RatFunc ℚ) m + Submission.CDT.dRat H := by
    rw [hG, Submission.CDT.dRat_add, Submission.CDT.dRat_add, Submission.CDT.dRat_mul,
      dRat_C_rat l, dRat_C_rat m, dRat_xQ]
    ring
  have hdF : Submission.CDT.dRat f =
      (e : RatFunc ℚ) * xQ ^ (e - 1) * G + xQ ^ e * Submission.CDT.dRat G := by
    rw [hfG, Submission.CDT.dRat_mul, dRat_xQ_zpow]
  have hstep : Submission.CDT.dRat f * xQ ^ (-(e - 1)) =
      algebraMap ℚ (RatFunc ℚ) (e : ℚ) * G + xQ * Submission.CDT.dRat G := by
    have hz1 : xQ ^ (e - 1) * xQ ^ (-(e - 1)) = 1 := by
      rw [← zpow_add₀ xQ_ne_zero, show (e - 1) + (-(e - 1)) = 0 by ring, zpow_zero]
    have hz2 : xQ ^ e * xQ ^ (-(e - 1)) = xQ := by
      rw [← zpow_add₀ xQ_ne_zero, show e + (-(e - 1)) = 1 by ring, zpow_one]
    have h1 : (e : RatFunc ℚ) * xQ ^ (e - 1) * G * xQ ^ (-(e - 1)) =
        (e : RatFunc ℚ) * G := by
      calc (e : RatFunc ℚ) * xQ ^ (e - 1) * G * xQ ^ (-(e - 1))
          = (e : RatFunc ℚ) * G * (xQ ^ (e - 1) * xQ ^ (-(e - 1))) := by ring
        _ = (e : RatFunc ℚ) * G := by rw [hz1, mul_one]
    have h2 : xQ ^ e * Submission.CDT.dRat G * xQ ^ (-(e - 1)) =
        xQ * Submission.CDT.dRat G := by
      calc xQ ^ e * Submission.CDT.dRat G * xQ ^ (-(e - 1))
          = (xQ ^ e * xQ ^ (-(e - 1))) * Submission.CDT.dRat G := by ring
        _ = xQ * Submission.CDT.dRat G := by rw [hz2]
    rw [hdF, add_mul, h1, h2, intCast_ratFunc_eq e]
  have key : Submission.CDT.dRat f * xQ ^ (-(e - 1)) - algebraMap ℚ (RatFunc ℚ) (e * l)
      - algebraMap ℚ (RatFunc ℚ) ((e + 1) * m) * xQ
      = algebraMap ℚ (RatFunc ℚ) (e : ℚ) * H + xQ * Submission.CDT.dRat H := by
    have h1 : algebraMap ℚ (RatFunc ℚ) (e : ℚ) * algebraMap ℚ (RatFunc ℚ) l
        = algebraMap ℚ (RatFunc ℚ) (e * l) := by rw [← map_mul]
    have h2 : algebraMap ℚ (RatFunc ℚ) (e : ℚ) * algebraMap ℚ (RatFunc ℚ) m
        + algebraMap ℚ (RatFunc ℚ) m = algebraMap ℚ (RatFunc ℚ) ((e + 1) * m) := by
      rw [← map_mul, ← map_add]
      congr 1
      push_cast
      ring
    have hrearr : algebraMap ℚ (RatFunc ℚ) (e : ℚ)
          * (algebraMap ℚ (RatFunc ℚ) l + algebraMap ℚ (RatFunc ℚ) m * xQ + H)
          + xQ * (algebraMap ℚ (RatFunc ℚ) m + Submission.CDT.dRat H)
          - algebraMap ℚ (RatFunc ℚ) (e * l) - algebraMap ℚ (RatFunc ℚ) ((e + 1) * m) * xQ
        = (algebraMap ℚ (RatFunc ℚ) (e : ℚ) * algebraMap ℚ (RatFunc ℚ) l
              - algebraMap ℚ (RatFunc ℚ) (e * l))
          + (algebraMap ℚ (RatFunc ℚ) (e : ℚ) * algebraMap ℚ (RatFunc ℚ) m
              + algebraMap ℚ (RatFunc ℚ) m - algebraMap ℚ (RatFunc ℚ) ((e + 1) * m)) * xQ
          + algebraMap ℚ (RatFunc ℚ) (e : ℚ) * H + xQ * Submission.CDT.dRat H := by ring
    rw [hstep, hdG, hG, hrearr, h1, h2]
    ring
  rw [key]
  refine ordAtT_add_ge' ?_ (ordAtT_xQ_mul_dRat_ge hHord)
  exact ordAtT_const_mul_ge (c := (e : ℚ)) hHord

end

end Work.C17
