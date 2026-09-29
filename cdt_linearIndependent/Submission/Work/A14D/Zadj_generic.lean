import Mathlib
import Submission.Work.A14D.Zadj_defs
import Submission.Work.C17adj.adjoint_divisor_boundC

namespace Work.A14D

open Polynomial
open Commons.FieldTheory.RatFunc

set_option maxHeartbeats 3200000

/-- **Regular point, second-order self-adjoint operator.**

Let `P₂, P₁, P₀ ∈ ℂ[x]` and let `β ≠ 0` have a pole of order `N = ord_α β < 0` at `α`.  If
`P₂(α) ≠ 0` (that is, `α` is not a singular point of the operator `P₂∂² + P₁∂ + P₀`), then

`ord_α (P₂β'' + P₁β' + P₀β) = N − 2`.

Indeed `P₂β''` has order exactly `N − 2` — its leading coefficient is
`P₂(α)·N·(N−1)·r ≠ 0`, since `N < 0` forces `N ≠ 0` and `N − 1 ≠ 0` — while `P₁β'` has order at
least `N − 1` and `P₀β` has order at least `N`, so neither can cancel the leading term. -/
lemma ordAtT_secondOrder_regular {P2 P1 P0 : Polynomial ℂ} {β : RatFunc ℂ} (hβ : β ≠ 0)
    {α : ℂ} (hN : ordAt α β < 0) (hP2 : P2.eval α ≠ 0) :
    ordAtT α (algebraMap (Polynomial ℂ) (RatFunc ℂ) P2
        * Submission.CDT.dRat (Submission.CDT.dRat β)
      + algebraMap (Polynomial ℂ) (RatFunc ℂ) P1 * Submission.CDT.dRat β
      + algebraMap (Polynomial ℂ) (RatFunc ℂ) P0 * β)
      = (((ordAt α β : ℤ) - 2 : ℤ) : WithTop ℤ) := by
  obtain ⟨r, hr, hres⟩ := Work.C17adj.leading_resid (α := α) hβ
  -- the two leading coefficients
  have hN0 : (ordAt α β : ℤ) ≠ 0 := by omega
  have hN1 : (ordAt α β : ℤ) - 1 ≠ 0 := by omega
  have hc1ne : (((ordAt α β : ℤ) : ℂ) * r) ≠ 0 :=
    mul_ne_zero (fun h => hN0 (Int.cast_eq_zero.mp h)) hr
  have hc2ne : ((((ordAt α β : ℤ)) * ((ordAt α β : ℤ) - 1)) * r) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (fun h => hN0 (Int.cast_eq_zero.mp h)) (by
      intro h
      have h1 : ((ordAt α β : ℤ) : ℂ) = ((1 : ℤ) : ℂ) := by simpa using (sub_eq_zero.mp h)
      exact absurd (Int.cast_inj.mp h1) (by omega))) hr
  -- residual data and exact orders
  have hres1 : (((ordAt α β : ℤ)) : WithTop ℤ) ≤ ordAtT α
      (Submission.CDT.dRat β - algebraMap (Polynomial ℂ) (RatFunc ℂ)
        (Polynomial.C (((ordAt α β : ℤ)) * r)) * linFactor (K := ℂ) α ^ ((ordAt α β : ℤ) - 1)) :=
    Work.C17adj.deriv1_resid (α := α) (β := β) (r := r) hres
  have hres2 : ((((ordAt α β : ℤ)) - 1 : ℤ) : WithTop ℤ) ≤ ordAtT α
      (Submission.CDT.dRat (Submission.CDT.dRat β) - algebraMap (Polynomial ℂ) (RatFunc ℂ)
        (Polynomial.C ((((ordAt α β : ℤ)) * ((ordAt α β : ℤ) - 1)) * r))
        * linFactor (K := ℂ) α ^ ((ordAt α β : ℤ) - 2)) :=
    Work.C17adj.deriv2_resid (α := α) (β := β) (r := r) hres
  have hres1' : ((((ordAt α β : ℤ) - 1) + 1 : ℤ) : WithTop ℤ) ≤ ordAtT α
      (Submission.CDT.dRat β - algebraMap (Polynomial ℂ) (RatFunc ℂ)
        (Polynomial.C (((ordAt α β : ℤ) : ℂ) * r)) * linFactor (K := ℂ) α ^ (((ordAt α β : ℤ)) - 1)) := by
    rw [show (((ordAt α β : ℤ) - 1) + 1) = (ordAt α β : ℤ) from by ring]
    exact hres1
  have hres2' : ((((ordAt α β : ℤ) - 2) + 1 : ℤ) : WithTop ℤ) ≤ ordAtT α
      (Submission.CDT.dRat (Submission.CDT.dRat β) - algebraMap (Polynomial ℂ) (RatFunc ℂ)
        (Polynomial.C ((((ordAt α β : ℤ)) * ((ordAt α β : ℤ) - 1)) * r))
        * linFactor (K := ℂ) α ^ (((ordAt α β : ℤ)) - 2)) := by
    rw [show (((ordAt α β : ℤ) - 2) + 1) = (((ordAt α β : ℤ)) - 1) from by ring]
    exact hres2
  have hordβ : ordAtT α β = (((ordAt α β : ℤ)) : WithTop ℤ) :=
    Work.C17adj.ord_eq_of_resid (f := β) (N := (ordAt α β : ℤ)) (c := r) hr hres
  have hord1 : ordAtT α (Submission.CDT.dRat β) = (((ordAt α β : ℤ)) - 1 : WithTop ℤ) :=
    Work.C17adj.ord_eq_of_resid (f := Submission.CDT.dRat β) (N := ((ordAt α β : ℤ)) - 1)
      (c := ((ordAt α β : ℤ) : ℂ) * r) hc1ne hres1'
  have hord2 : ordAtT α (Submission.CDT.dRat (Submission.CDT.dRat β))
      = (((ordAt α β : ℤ)) - 2 : WithTop ℤ) :=
    Work.C17adj.ord_eq_of_resid (f := Submission.CDT.dRat (Submission.CDT.dRat β))
      (N := ((ordAt α β : ℤ)) - 2)
      (c := (((ordAt α β : ℤ)) * ((ordAt α β : ℤ) - 1)) * r) hc2ne hres2'
  -- term bounds
  have hT1 : ((((ordAt α β : ℤ)) - 1 : ℤ) : WithTop ℤ) ≤ ordAtT α
      (algebraMap (Polynomial ℂ) (RatFunc ℂ) P2
          * Submission.CDT.dRat (Submission.CDT.dRat β)
        - algebraMap (Polynomial ℂ) (RatFunc ℂ)
            (Polynomial.C (P2.eval α * ((((ordAt α β : ℤ)) * ((ordAt α β : ℤ) - 1)) * r)))
          * linFactor (K := ℂ) α ^ ((ordAt α β : ℤ) - 2)) := by
    have h := Work.C17adj.mul_poly_resid (f := Submission.CDT.dRat (Submission.CDT.dRat β))
      (N := ((ordAt α β : ℤ)) - 2)
      (c := (((ordAt α β : ℤ)) * ((ordAt α β : ℤ) - 1)) * r) hc2ne hres2' hP2
    have h2 : (((((ordAt α β : ℤ)) - 2) + 1 : ℤ)) = ((((ordAt α β : ℤ)) - 1 : ℤ)) := by ring
    rwa [h2] at h
  have hordT1 : ordAtT α (algebraMap (Polynomial ℂ) (RatFunc ℂ) P2
      * Submission.CDT.dRat (Submission.CDT.dRat β)) = (((ordAt α β : ℤ)) - 2 : WithTop ℤ) :=
    Work.C17adj.mul_poly_ord (f := Submission.CDT.dRat (Submission.CDT.dRat β))
      (N := ((ordAt α β : ℤ)) - 2)
      (c := (((ordAt α β : ℤ)) * ((ordAt α β : ℤ) - 1)) * r) hc2ne hres2' hP2
  have hT2 : ((((ordAt α β : ℤ)) - 1 : ℤ) : WithTop ℤ) ≤ ordAtT α
      (algebraMap (Polynomial ℂ) (RatFunc ℂ) P1 * Submission.CDT.dRat β) := by
    calc ((((ordAt α β : ℤ)) - 1 : ℤ) : WithTop ℤ)
        = (0 : WithTop ℤ) + ((((ordAt α β : ℤ)) - 1 : ℤ) : WithTop ℤ) := (zero_add _).symm
      _ ≤ ordAtT α (algebraMap (Polynomial ℂ) (RatFunc ℂ) P1)
            + ordAtT α (Submission.CDT.dRat β) :=
          add_le_add (Work.C17adj.zero_le_ordAtT_algebraMap_poly P1) (le_of_eq hord1.symm)
      _ ≤ _ := ordAtT_mul_ge α _ _
  have hT3 : (((ordAt α β : ℤ)) : WithTop ℤ) ≤ ordAtT α
      (algebraMap (Polynomial ℂ) (RatFunc ℂ) P0 * β) := by
    calc (((ordAt α β : ℤ)) : WithTop ℤ)
        = (0 : WithTop ℤ) + (((ordAt α β : ℤ)) : WithTop ℤ) := (zero_add _).symm
      _ ≤ ordAtT α (algebraMap (Polynomial ℂ) (RatFunc ℂ) P0) + ordAtT α β :=
          add_le_add (Work.C17adj.zero_le_ordAtT_algebraMap_poly P0) (le_of_eq hordβ.symm)
      _ ≤ _ := ordAtT_mul_ge α _ _
  -- the leading term
  have hlt : ordAtT α (algebraMap (Polynomial ℂ) (RatFunc ℂ)
      (Polynomial.C (P2.eval α * ((((ordAt α β : ℤ)) * ((ordAt α β : ℤ) - 1)) * r)))
        * linFactor (K := ℂ) α ^ ((ordAt α β : ℤ) - 2)) = (((ordAt α β : ℤ)) - 2 : WithTop ℤ) :=
    Work.C17adj.ord_C_mul_linFactor _ (mul_ne_zero hP2 hc2ne) _
  -- the residual
  have hcomb : ((((ordAt α β : ℤ)) - 1 : ℤ) : WithTop ℤ) ≤ ordAtT α
      (algebraMap (Polynomial ℂ) (RatFunc ℂ) P2
          * Submission.CDT.dRat (Submission.CDT.dRat β)
        + algebraMap (Polynomial ℂ) (RatFunc ℂ) P1 * Submission.CDT.dRat β
        + algebraMap (Polynomial ℂ) (RatFunc ℂ) P0 * β
        - algebraMap (Polynomial ℂ) (RatFunc ℂ)
            (Polynomial.C (P2.eval α * ((((ordAt α β : ℤ)) * ((ordAt α β : ℤ) - 1)) * r)))
          * linFactor (K := ℂ) α ^ ((ordAt α β : ℤ) - 2)) := by
    have he : algebraMap (Polynomial ℂ) (RatFunc ℂ) P2
          * Submission.CDT.dRat (Submission.CDT.dRat β)
        + algebraMap (Polynomial ℂ) (RatFunc ℂ) P1 * Submission.CDT.dRat β
        + algebraMap (Polynomial ℂ) (RatFunc ℂ) P0 * β
        - algebraMap (Polynomial ℂ) (RatFunc ℂ)
            (Polynomial.C (P2.eval α * ((((ordAt α β : ℤ)) * ((ordAt α β : ℤ) - 1)) * r)))
          * linFactor (K := ℂ) α ^ ((ordAt α β : ℤ) - 2)
        = (algebraMap (Polynomial ℂ) (RatFunc ℂ) P2
              * Submission.CDT.dRat (Submission.CDT.dRat β)
            - algebraMap (Polynomial ℂ) (RatFunc ℂ)
                (Polynomial.C (P2.eval α * ((((ordAt α β : ℤ)) * ((ordAt α β : ℤ) - 1)) * r)))
              * linFactor (K := ℂ) α ^ ((ordAt α β : ℤ) - 2))
          + (algebraMap (Polynomial ℂ) (RatFunc ℂ) P1 * Submission.CDT.dRat β
              + algebraMap (Polynomial ℂ) (RatFunc ℂ) P0 * β) := by ring
    rw [he]
    refine le_trans (le_min hT1 ?_) (ordAtT_add_ge α _ _)
    refine le_trans (le_min hT2 ?_) (ordAtT_add_ge α _ _)
    exact le_trans (by rw [WithTop.coe_le_coe]; omega) hT3
  -- conclude
  have he : algebraMap (Polynomial ℂ) (RatFunc ℂ) P2
        * Submission.CDT.dRat (Submission.CDT.dRat β)
      + algebraMap (Polynomial ℂ) (RatFunc ℂ) P1 * Submission.CDT.dRat β
      + algebraMap (Polynomial ℂ) (RatFunc ℂ) P0 * β
      = algebraMap (Polynomial ℂ) (RatFunc ℂ)
          (Polynomial.C (P2.eval α * ((((ordAt α β : ℤ)) * ((ordAt α β : ℤ) - 1)) * r)))
          * linFactor (K := ℂ) α ^ ((ordAt α β : ℤ) - 2)
        + (algebraMap (Polynomial ℂ) (RatFunc ℂ) P2
              * Submission.CDT.dRat (Submission.CDT.dRat β)
          + algebraMap (Polynomial ℂ) (RatFunc ℂ) P1 * Submission.CDT.dRat β
          + algebraMap (Polynomial ℂ) (RatFunc ℂ) P0 * β
          - algebraMap (Polynomial ℂ) (RatFunc ℂ)
              (Polynomial.C (P2.eval α * ((((ordAt α β : ℤ)) * ((ordAt α β : ℤ) - 1)) * r)))
            * linFactor (K := ℂ) α ^ ((ordAt α β : ℤ) - 2)) := by ring
  rw [he]
  refine ordAtT_add_eq_of_le_succ hlt ?_
  have h2 : ((((ordAt α β : ℤ)) - 2) + 1) = (((ordAt α β : ℤ)) - 1) := by ring
  rwa [h2]

theorem Zadj_generic {β : RatFunc ℂ} (hβ : β ≠ 0) {α : ℂ}
    (hP2 : (P2Z).eval α ≠ 0) (hN : Commons.FieldTheory.RatFunc.ordAt α β < 0) :
    Commons.FieldTheory.RatFunc.ordAtT α (LZf β)
      = (((Commons.FieldTheory.RatFunc.ordAt α β : ℤ) - 2 : ℤ) : WithTop ℤ) := by
  have h := ordAtT_secondOrder_regular (P2 := P2Z) (P1 := P1Z) (P0 := P0Z) hβ hN hP2
  simpa only [LZf] using h

end Work.A14D

namespace Work.A14D
namespace Work.A14D

set_option linter.dupNamespace false in
/-- The statement as originally placed in this file (doubled namespace). -/
theorem Zadj_generic {β : RatFunc ℂ} (hβ : β ≠ 0) {α : ℂ}
    (hP2 : (P2Z).eval α ≠ 0) (hN : Commons.FieldTheory.RatFunc.ordAt α β < 0) :
    Commons.FieldTheory.RatFunc.ordAtT α (LZf β)
      = (((Commons.FieldTheory.RatFunc.ordAt α β : ℤ) - 2 : ℤ) : WithTop ℤ) :=
  _root_.Work.A14D.Zadj_generic hβ hP2 hN

end Work.A14D
end Work.A14D
