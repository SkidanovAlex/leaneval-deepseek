import Mathlib
import Submission.Work.A14D.Zadj_defs
import Submission.Work.C17adj.adjoint_divisor_boundC

/-!
# `Work.A14D.Zadj_singular`

The local (indicial) order of the Zagier operator `LZf` at a *regular singular* point `α` of its
leading coefficient `P2Z`.  This is the `Z`-side analogue of `Work.C17adj.order_eq_singular`.

If `β ≠ 0` has a pole of order `N = ordAt α β < 0` at `α`, and `P2Z = (X − α)·P2s` with
`P2s(α) ≠ 0` (so `α` is a *simple* root of the leading coefficient), then the indicial polynomial
value of `LZf` at `α` is `N·((N−1)·P2s(α) + P1Z(α))`; when this is nonzero the order of `LZf β` at
`α` is exactly `N − 1`.

The general second-order statement is proved first (`order_eq_singular_general`, for arbitrary
coefficient polynomials `P2, P1, P0`) and then specialised, exactly as on the C-side.
-/

namespace Work.A14D

open Polynomial

noncomputable section

open Commons.FieldTheory.RatFunc

set_option maxHeartbeats 3200000

/-- **Singular local order bound, general coefficients.**  Let `P2, P1, P0 ∈ ℂ[X]`, and let
`β ≠ 0` have a pole of order `N = ord_α β < 0` at `α`, where `P2 = (X − α)·P2s` with
`P2s(α) ≠ 0`.  If the indicial value `N·((N−1)·P2s(α) + P1(α))` is nonzero, then
`ord_α (P2·β'' + P1·β' + P0·β) = N − 1`. -/
theorem order_eq_singular_general {β : RatFunc ℂ} (hβ : β ≠ 0) {α : ℂ}
    (hN : ordAt α β < 0)
    {P2 P1 P0 : Polynomial ℂ} {P2s : Polynomial ℂ} (hfac : P2 = (X - C α) * P2s)
    (hP2s : P2s.eval α ≠ 0)
    (hcoef : (((ordAt α β : ℤ) : ℂ) * ((((ordAt α β : ℤ) : ℂ) - 1) * P2s.eval α
      + P1.eval α)) ≠ 0) :
    ordAtT α (algebraMap (Polynomial ℂ) (RatFunc ℂ) P2
        * Submission.CDT.dRat (Submission.CDT.dRat β)
      + algebraMap (Polynomial ℂ) (RatFunc ℂ) P1 * Submission.CDT.dRat β
      + algebraMap (Polynomial ℂ) (RatFunc ℂ) P0 * β)
      = ((((ordAt α β : ℤ)) - 1 : ℤ) : WithTop ℤ) := by
  obtain ⟨r, hr, hres⟩ := Work.C17adj.leading_resid (α := α) hβ
  have hN0 : (ordAt α β : ℤ) ≠ 0 := by omega
  have hN1 : (ordAt α β : ℤ) - 1 ≠ 0 := by omega
  set c1 : ℂ := ((ordAt α β : ℤ) : ℂ) * r with hc1
  set c2 : ℂ := ((((ordAt α β : ℤ)) * (((ordAt α β : ℤ)) - 1)) * r) with hc2
  have hc1ne : c1 ≠ 0 := by
    rw [hc1]; exact mul_ne_zero (fun h => hN0 (Int.cast_eq_zero.mp h)) hr
  have hc2ne : c2 ≠ 0 := by
    rw [hc2]
    refine mul_ne_zero (mul_ne_zero (fun h => hN0 (Int.cast_eq_zero.mp h)) ?_) hr
    intro h
    have h1 : ((ordAt α β : ℤ) : ℂ) = ((1 : ℤ) : ℂ) := by simpa using (sub_eq_zero.mp h)
    exact absurd (Int.cast_inj.mp h1) (by omega)
  -- residual data
  have hres1 : (((ordAt α β : ℤ)) : WithTop ℤ) ≤ ordAtT α
      (Submission.CDT.dRat β - algebraMap (Polynomial ℂ) (RatFunc ℂ)
        (Polynomial.C c1) * linFactor (K := ℂ) α ^ ((ordAt α β : ℤ) - 1)) := by
    have h := Work.C17adj.deriv1_resid (α := α) (β := β) (r := r) hres
    rwa [← hc1] at h
  have hres2 : ((((ordAt α β : ℤ)) - 1 : ℤ) : WithTop ℤ) ≤ ordAtT α
      (Submission.CDT.dRat (Submission.CDT.dRat β) - algebraMap (Polynomial ℂ) (RatFunc ℂ)
        (Polynomial.C c2) * linFactor (K := ℂ) α ^ ((ordAt α β : ℤ) - 2)) := by
    have h := Work.C17adj.deriv2_resid (α := α) (β := β) (r := r) hres
    rwa [← hc2] at h
  have hres2' : ((((ordAt α β : ℤ) - 2) + 1 : ℤ) : WithTop ℤ) ≤ ordAtT α
      (Submission.CDT.dRat (Submission.CDT.dRat β) - algebraMap (Polynomial ℂ) (RatFunc ℂ)
        (Polynomial.C c2) * linFactor (K := ℂ) α ^ (((ordAt α β : ℤ)) - 2)) := by
    rw [show (((ordAt α β : ℤ) - 2) + 1) = (((ordAt α β : ℤ)) - 1) from by ring]
    exact hres2
  have hordβ : ordAtT α β = (((ordAt α β : ℤ)) : WithTop ℤ) :=
    Work.C17adj.ord_eq_of_resid (f := β) (N := (ordAt α β : ℤ)) (c := r) hr hres
  have hord1 : ordAtT α (Submission.CDT.dRat β) = (((ordAt α β : ℤ)) - 1 : WithTop ℤ) := by
    have h : ((((ordAt α β : ℤ) - 1) + 1 : ℤ) : WithTop ℤ) ≤ ordAtT α
        (Submission.CDT.dRat β - algebraMap (Polynomial ℂ) (RatFunc ℂ)
          (Polynomial.C c1) * linFactor (K := ℂ) α ^ (((ordAt α β : ℤ)) - 1)) := by
      rw [show (((ordAt α β : ℤ) - 1) + 1) = (ordAt α β : ℤ) from by ring]
      exact hres1
    exact Work.C17adj.ord_eq_of_resid (f := Submission.CDT.dRat β) (N := ((ordAt α β : ℤ)) - 1)
      (c := c1) hc1ne h
  -- `q · β''` has leading term `c₂·q^{N−1}`
  have hq : (((ordAt α β : ℤ)) : WithTop ℤ) ≤ ordAtT α
      (linFactor (K := ℂ) α * Submission.CDT.dRat (Submission.CDT.dRat β)
        - algebraMap (Polynomial ℂ) (RatFunc ℂ) (Polynomial.C c2)
          * linFactor (K := ℂ) α ^ (((ordAt α β : ℤ)) - 1)) := by
    have hzt : linFactor (K := ℂ) α ^ (((ordAt α β : ℤ)) - 1)
        = linFactor (K := ℂ) α * linFactor (K := ℂ) α ^ (((ordAt α β : ℤ)) - 2) := by
      rw [show (((ordAt α β : ℤ)) - 1) = ((((ordAt α β : ℤ)) - 2) + 1) from by ring,
        zpow_add_one₀ (linFactor_ne_zero (K := ℂ) α), mul_comm]
    have he : linFactor (K := ℂ) α * Submission.CDT.dRat (Submission.CDT.dRat β)
        - algebraMap (Polynomial ℂ) (RatFunc ℂ) (Polynomial.C c2)
          * linFactor (K := ℂ) α ^ (((ordAt α β : ℤ)) - 1)
        = linFactor (K := ℂ) α * (Submission.CDT.dRat (Submission.CDT.dRat β)
          - algebraMap (Polynomial ℂ) (RatFunc ℂ) (Polynomial.C c2)
            * linFactor (K := ℂ) α ^ (((ordAt α β : ℤ)) - 2)) := by
      rw [hzt]; ring
    have h1q : ((1 : ℤ) : WithTop ℤ) ≤ ordAtT α (linFactor (K := ℂ) α) := by
      rw [← zpow_one (linFactor (K := ℂ) α), ordAtT_linFactor_zpow]
    rw [he]
    calc (((ordAt α β : ℤ)) : WithTop ℤ)
        = ((1 : ℤ) : WithTop ℤ) + ((((ordAt α β : ℤ)) - 1 : ℤ) : WithTop ℤ) := by
          rw [← WithTop.coe_add]; congr 1; ring
      _ ≤ ordAtT α (linFactor (K := ℂ) α) + ordAtT α (Submission.CDT.dRat (Submission.CDT.dRat β)
            - algebraMap (Polynomial ℂ) (RatFunc ℂ) (Polynomial.C c2)
              * linFactor (K := ℂ) α ^ (((ordAt α β : ℤ)) - 2)) :=
          add_le_add h1q hres2
      _ ≤ _ := ordAtT_mul_ge α _ _
  have hq_ord : ordAtT α (linFactor (K := ℂ) α * Submission.CDT.dRat (Submission.CDT.dRat β))
      = ((((ordAt α β : ℤ)) - 1 : ℤ) : WithTop ℤ) := by
    refine Work.C17adj.ord_eq_of_resid (f := linFactor (K := ℂ) α * Submission.CDT.dRat (Submission.CDT.dRat β))
      (N := ((ordAt α β : ℤ)) - 1) (c := c2) hc2ne ?_
    rw [sub_add_cancel]
    exact hq
  -- the `P₂·β''` term
  have hP2eq : algebraMap (Polynomial ℂ) (RatFunc ℂ) (P2)
        * Submission.CDT.dRat (Submission.CDT.dRat β)
      = algebraMap (Polynomial ℂ) (RatFunc ℂ) P2s
        * (linFactor (K := ℂ) α * Submission.CDT.dRat (Submission.CDT.dRat β)) := by
    rw [hfac, map_mul]
    simp only [linFactor]
    ring
  have hT1 : (((ordAt α β : ℤ)) : WithTop ℤ) ≤ ordAtT α
      (algebraMap (Polynomial ℂ) (RatFunc ℂ) (P2)
          * Submission.CDT.dRat (Submission.CDT.dRat β)
        - algebraMap (Polynomial ℂ) (RatFunc ℂ) (Polynomial.C (P2s.eval α * c2))
          * linFactor (K := ℂ) α ^ (((ordAt α β : ℤ)) - 1)) := by
    rw [hP2eq]
    have h := Work.C17adj.mul_poly_resid (f := linFactor (K := ℂ) α * Submission.CDT.dRat (Submission.CDT.dRat β))
      (N := ((ordAt α β : ℤ)) - 1) (c := c2) hc2ne (by rw [sub_add_cancel]; exact hq) hP2s
    rw [sub_add_cancel] at h
    exact h
  -- the `A·β'` term
  have hT2 : (((ordAt α β : ℤ)) : WithTop ℤ) ≤ ordAtT α
      (algebraMap (Polynomial ℂ) (RatFunc ℂ) (P1) * Submission.CDT.dRat β
        - algebraMap (Polynomial ℂ) (RatFunc ℂ) (Polynomial.C ((P1).eval α * c1))
          * linFactor (K := ℂ) α ^ (((ordAt α β : ℤ)) - 1)) := by
    have hdecomp : algebraMap (Polynomial ℂ) (RatFunc ℂ) (P1) * Submission.CDT.dRat β
        - algebraMap (Polynomial ℂ) (RatFunc ℂ) (Polynomial.C ((P1).eval α * c1))
          * linFactor (K := ℂ) α ^ (((ordAt α β : ℤ)) - 1)
        = algebraMap (Polynomial ℂ) (RatFunc ℂ) (Polynomial.C ((P1).eval α))
            * (Submission.CDT.dRat β - algebraMap (Polynomial ℂ) (RatFunc ℂ) (Polynomial.C c1)
              * linFactor (K := ℂ) α ^ (((ordAt α β : ℤ)) - 1))
          + algebraMap (Polynomial ℂ) (RatFunc ℂ)
              (P1 - Polynomial.C ((P1).eval α)) * Submission.CDT.dRat β := by
      simp only [map_sub, map_mul, Polynomial.C_mul]
      ring
    rw [hdecomp]
    refine le_trans (le_min ?_ ?_) (ordAtT_add_ge α _ _)
    · calc (((ordAt α β : ℤ)) : WithTop ℤ)
          = (0 : WithTop ℤ) + (((ordAt α β : ℤ)) : WithTop ℤ) := (zero_add _).symm
        _ ≤ ordAtT α (algebraMap (Polynomial ℂ) (RatFunc ℂ) (Polynomial.C ((P1).eval α)))
              + ordAtT α (Submission.CDT.dRat β - algebraMap (Polynomial ℂ) (RatFunc ℂ)
                  (Polynomial.C c1) * linFactor (K := ℂ) α ^ (((ordAt α β : ℤ)) - 1)) :=
            add_le_add (zero_le_ordAtT_algebraMap_C α _) hres1
        _ ≤ _ := ordAtT_mul_ge α _ _
    · calc (((ordAt α β : ℤ)) : WithTop ℤ)
          = ((1 : ℤ) : WithTop ℤ) + ((((ordAt α β : ℤ)) - 1 : ℤ) : WithTop ℤ) := by
            rw [← WithTop.coe_add]; congr 1; ring
        _ ≤ ordAtT α (algebraMap (Polynomial ℂ) (RatFunc ℂ)
              (P1 - Polynomial.C ((P1).eval α)))
              + ordAtT α (Submission.CDT.dRat β) :=
            add_le_add Work.C17adj.one_le_ordAtT_algebraMap_sub_C_eval (le_of_eq hord1.symm)
        _ ≤ _ := ordAtT_mul_ge α _ _
  -- the `C·β` term
  have hT3 : (((ordAt α β : ℤ)) : WithTop ℤ) ≤ ordAtT α
      (algebraMap (Polynomial ℂ) (RatFunc ℂ) (P0) * β) := by
    calc (((ordAt α β : ℤ)) : WithTop ℤ)
        = (0 : WithTop ℤ) + (((ordAt α β : ℤ)) : WithTop ℤ) := (zero_add _).symm
      _ ≤ ordAtT α (algebraMap (Polynomial ℂ) (RatFunc ℂ) (P0)) + ordAtT α β :=
          add_le_add (Work.C17adj.zero_le_ordAtT_algebraMap_poly (P0)) (le_of_eq hordβ.symm)
      _ ≤ _ := ordAtT_mul_ge α _ _
  -- the indicial coefficient
  have hcoefne : (P2s.eval α * c2 + (P1).eval α * c1) ≠ 0 := by
    have heq : P2s.eval α * c2 + (P1).eval α * c1
        = r * (((ordAt α β : ℤ) : ℂ) * ((((ordAt α β : ℤ) : ℂ) - 1) * P2s.eval α
            + (P1).eval α)) := by
      rw [hc1, hc2]; ring
    rw [heq]
    exact mul_ne_zero hr hcoef
  have hlt : ordAtT α (algebraMap (Polynomial ℂ) (RatFunc ℂ)
      (Polynomial.C (P2s.eval α * c2 + (P1).eval α * c1))
        * linFactor (K := ℂ) α ^ (((ordAt α β : ℤ)) - 1)) = ((((ordAt α β : ℤ)) - 1 : ℤ) : WithTop ℤ) :=
    Work.C17adj.ord_C_mul_linFactor _ hcoefne _
  -- the residual
  have hcomb : (((ordAt α β : ℤ)) : WithTop ℤ) ≤ ordAtT α
      (algebraMap (Polynomial ℂ) (RatFunc ℂ) (P2)
          * Submission.CDT.dRat (Submission.CDT.dRat β)
        + algebraMap (Polynomial ℂ) (RatFunc ℂ) (P1) * Submission.CDT.dRat β
        + algebraMap (Polynomial ℂ) (RatFunc ℂ) (P0) * β
        - algebraMap (Polynomial ℂ) (RatFunc ℂ)
            (Polynomial.C (P2s.eval α * c2 + (P1).eval α * c1))
          * linFactor (K := ℂ) α ^ (((ordAt α β : ℤ)) - 1)) := by
    have he : algebraMap (Polynomial ℂ) (RatFunc ℂ) (P2)
          * Submission.CDT.dRat (Submission.CDT.dRat β)
        + algebraMap (Polynomial ℂ) (RatFunc ℂ) (P1) * Submission.CDT.dRat β
        + algebraMap (Polynomial ℂ) (RatFunc ℂ) (P0) * β
        - algebraMap (Polynomial ℂ) (RatFunc ℂ)
            (Polynomial.C (P2s.eval α * c2 + (P1).eval α * c1))
          * linFactor (K := ℂ) α ^ (((ordAt α β : ℤ)) - 1)
        = (algebraMap (Polynomial ℂ) (RatFunc ℂ) (P2)
              * Submission.CDT.dRat (Submission.CDT.dRat β)
            - algebraMap (Polynomial ℂ) (RatFunc ℂ) (Polynomial.C (P2s.eval α * c2))
              * linFactor (K := ℂ) α ^ (((ordAt α β : ℤ)) - 1))
          + ((algebraMap (Polynomial ℂ) (RatFunc ℂ) (P1) * Submission.CDT.dRat β
              - algebraMap (Polynomial ℂ) (RatFunc ℂ) (Polynomial.C ((P1).eval α * c1))
                * linFactor (K := ℂ) α ^ (((ordAt α β : ℤ)) - 1))
            + algebraMap (Polynomial ℂ) (RatFunc ℂ) (P0) * β) := by
      simp only [Polynomial.C_add, Polynomial.C_mul, map_add, map_mul]
      ring
    rw [he]
    refine le_trans (le_min hT1 ?_) (ordAtT_add_ge α _ _)
    refine le_trans (le_min hT2 ?_) (ordAtT_add_ge α _ _)
    exact hT3
  -- conclude
  have he : algebraMap (Polynomial ℂ) (RatFunc ℂ) (P2)
        * Submission.CDT.dRat (Submission.CDT.dRat β)
      + algebraMap (Polynomial ℂ) (RatFunc ℂ) (P1) * Submission.CDT.dRat β
      + algebraMap (Polynomial ℂ) (RatFunc ℂ) (P0) * β
      = algebraMap (Polynomial ℂ) (RatFunc ℂ)
          (Polynomial.C (P2s.eval α * c2 + (P1).eval α * c1))
          * linFactor (K := ℂ) α ^ (((ordAt α β : ℤ)) - 1)
        + (algebraMap (Polynomial ℂ) (RatFunc ℂ) (P2)
              * Submission.CDT.dRat (Submission.CDT.dRat β)
          + algebraMap (Polynomial ℂ) (RatFunc ℂ) (P1) * Submission.CDT.dRat β
          + algebraMap (Polynomial ℂ) (RatFunc ℂ) (P0) * β
          - algebraMap (Polynomial ℂ) (RatFunc ℂ)
              (Polynomial.C (P2s.eval α * c2 + (P1).eval α * c1))
            * linFactor (K := ℂ) α ^ (((ordAt α β : ℤ)) - 1)) := by ring
  rw [he]
  refine ordAtT_add_eq_of_le_succ hlt ?_
  rw [sub_add_cancel]
  exact hcomb


/-- **`Work.A14D.Zadj_singular`.**  The singular local order of the Zagier operator `LZf`:
specialisation of `order_eq_singular_general` to `P2 = P2Z`, `P1 = P1Z`, `P0 = P0Z`. -/
theorem Zadj_singular {β : RatFunc ℂ} (hβ : β ≠ 0) {α : ℂ}
    (hN : Commons.FieldTheory.RatFunc.ordAt α β < 0)
    {P2s : Polynomial ℂ} (hfac : P2Z = (X - C α) * P2s) (hP2s : P2s.eval α ≠ 0)
    (hcoef : (((Commons.FieldTheory.RatFunc.ordAt α β : ℤ) : ℂ)
        * ((((Commons.FieldTheory.RatFunc.ordAt α β : ℤ) : ℂ) - 1) * P2s.eval α
          + (P1Z).eval α)) ≠ 0) :
    Commons.FieldTheory.RatFunc.ordAtT α (LZf β)
      = (((Commons.FieldTheory.RatFunc.ordAt α β : ℤ) - 1 : ℤ) : WithTop ℤ) := by
  have h := order_eq_singular_general (P2 := P2Z) (P1 := P1Z) (P0 := P0Z)
    (β := β) (α := α) hβ hN (P2s := P2s) hfac hP2s hcoef
  simpa [LZf] using h

end

end Work.A14D
