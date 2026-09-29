import Mathlib
import Submission.Work.C17.adjoint_defs
import Submission.Work.C17adj.divisor_defs
import Submission.Work.C17adj.rhs_structure
import Submission.Work.C17adj.rhs_ord
import Submission.Work.C17adj.phi_degree
import Submission.Work.C17adj.phi_identity
import Submission.Work.C17.p2x_roots_simple
import Submission.CDT.RatFuncDifferential
import Submission.Commons.Algebra.Polynomial.dvd_sq_X_sub_C_iff
import Submission.Commons.Algebra.Polynomial.fallFact_cast_ne_zero
import Submission.Commons.FieldTheory.RatFunc.exists_dvd_of_ordAt_bounds

namespace Work.C17adj
open Polynomial
open Commons.FieldTheory.RatFunc
noncomputable section
set_option maxHeartbeats 3200000

/-! ## 0. `dRat` as a `ℂ`-derivation -/

def dRatDerivC : Derivation ℂ (RatFunc ℂ) (RatFunc ℂ) where
  toFun := Submission.CDT.dRat
  map_add' := Submission.CDT.dRat_add
  map_smul' := by
    intro c f
    simp only [Algebra.smul_def, RingHom.id_apply, Submission.CDT.dRat_mul,
      Submission.CDT.dRat_algebraMap_field, zero_mul, zero_add]
  map_one_eq_zero' := Submission.CDT.dRat_one
  leibniz' := by
    intro a b
    change Submission.CDT.dRat (a * b) =
      a * Submission.CDT.dRat b + b * Submission.CDT.dRat a
    rw [Submission.CDT.dRat_mul]
    ring

lemma dRatDerivC_algebraMap (p : Polynomial ℂ) :
    dRatDerivC (algebraMap (Polynomial ℂ) (RatFunc ℂ) p)
      = algebraMap (Polynomial ℂ) (RatFunc ℂ) p.derivative :=
  Submission.CDT.dRat_algebraMap p

/-! ## 1. The operator identity -/

lemma Pac_eq_P2Cm (a b : ℚ) : Work.C17.Pac a b
    = algebraMap (Polynomial ℂ) (RatFunc ℂ) (P2Cm a b) := rfl

lemma Pbc_eq_P1Cm (a b : ℚ) : Work.C17.Pbc a b
    = algebraMap (Polynomial ℂ) (RatFunc ℂ) (P1Cm a b) := rfl

lemma Pcc_eq_P0Cm (a b : ℚ) : Work.C17.Pcc a b
    = algebraMap (Polynomial ℂ) (RatFunc ℂ) (P0Cm a b) := rfl

lemma op_eq (a b : ℚ) (β : RatFunc ℂ) :
    Submission.CDT.dRat (Submission.CDT.dRat (Work.C17.Pac a b * β))
      - Submission.CDT.dRat (Work.C17.Pbc a b * β) + Work.C17.Pcc a b * β
    = algebraMap (Polynomial ℂ) (RatFunc ℂ) (P2Cm a b)
        * (Submission.CDT.dRat (Submission.CDT.dRat β))
      + algebraMap (Polynomial ℂ) (RatFunc ℂ) (AadjL a b) * Submission.CDT.dRat β
      + algebraMap (Polynomial ℂ) (RatFunc ℂ) (CadjL a b) * β := by
  rw [Pac_eq_P2Cm a b, Pbc_eq_P1Cm a b, Pcc_eq_P0Cm a b]
  simp only [AadjL, CadjL, Submission.CDT.dRat_mul, Submission.CDT.dRat_sub,
    Submission.CDT.dRat_add, Submission.CDT.dRat_algebraMap, map_add, map_sub, map_mul,
    map_ofNat]
  ring

/-! ## 2. Leading-term data at a point -/

variable {α : ℂ}

/-- The leading term of `β ≠ 0` at `α`. -/
lemma leading_resid {β : RatFunc ℂ} (hβ : β ≠ 0) :
    ∃ r : ℂ, r ≠ 0 ∧ ((ordAt α β + 1 : ℤ) : WithTop ℤ) ≤ ordAtT α
      (β - algebraMap (Polynomial ℂ) (RatFunc ℂ) (Polynomial.C r)
        * linFactor (K := ℂ) α ^ (ordAt α β)) :=
  exists_leading_term α hβ

/-- The residual of the `j`-th derivative, `fallFact` form. -/
lemma deriv_resid' {β : RatFunc ℂ} {r : ℂ}
    (hres : ((ordAt α β + 1 : ℤ) : WithTop ℤ) ≤ ordAtT α
      (β - algebraMap (Polynomial ℂ) (RatFunc ℂ) (Polynomial.C r)
        * linFactor (K := ℂ) α ^ (ordAt α β))) (j : ℕ) :
    (((ordAt α β - (j : ℤ) + 1 : ℤ)) : WithTop ℤ) ≤ ordAtT α
      (((dRatDerivC : RatFunc ℂ → RatFunc ℂ)^[j]) β
        - algebraMap (Polynomial ℂ) (RatFunc ℂ)
            (Polynomial.C (r * ((Commons.Algebra.Polynomial.fallFact (ordAt α β) j : ℤ) : ℂ)))
          * linFactor (K := ℂ) α ^ (ordAt α β - (j : ℤ))) :=
  ordAtT_iterate_deriv_leading (D := dRatDerivC) dRatDerivC_algebraMap hres j

lemma fallFact_one (N : ℤ) : Commons.Algebra.Polynomial.fallFact N 1 = N := by
  simp [Commons.Algebra.Polynomial.fallFact]

lemma fallFact_two (N : ℤ) : Commons.Algebra.Polynomial.fallFact N 2 = N * (N - 1) := by
  simp [Commons.Algebra.Polynomial.fallFact, Finset.prod_range_succ]

/-- Residual of `dRat β`, explicit constant. -/
lemma deriv1_resid {β : RatFunc ℂ} {r : ℂ}
    (hres : ((ordAt α β + 1 : ℤ) : WithTop ℤ) ≤ ordAtT α
      (β - algebraMap (Polynomial ℂ) (RatFunc ℂ) (Polynomial.C r)
        * linFactor (K := ℂ) α ^ (ordAt α β))) :
    (((ordAt α β : ℤ)) : WithTop ℤ) ≤ ordAtT α
      (Submission.CDT.dRat β - algebraMap (Polynomial ℂ) (RatFunc ℂ)
          (Polynomial.C (((ordAt α β : ℤ)) * r)) * linFactor (K := ℂ) α ^ ((ordAt α β : ℤ) - 1)) := by
  have h : (((ordAt α β - (1 : ℤ) + 1 : ℤ)) : WithTop ℤ) ≤ ordAtT α
      (Submission.CDT.dRat β - algebraMap (Polynomial ℂ) (RatFunc ℂ)
          (Polynomial.C (r * ((Commons.Algebra.Polynomial.fallFact (ordAt α β) 1 : ℤ) : ℂ)))
          * linFactor (K := ℂ) α ^ (ordAt α β - (1 : ℤ))) :=
    deriv_resid' (α := α) (r := r) hres 1
  have h2 : (((ordAt α β - (1 : ℤ) + 1 : ℤ)) : WithTop ℤ) = (((ordAt α β : ℤ)) : WithTop ℤ) := by
    congr 1; ring
  have hc : (r * ((Commons.Algebra.Polynomial.fallFact (ordAt α β) 1 : ℤ) : ℂ))
      = (((ordAt α β : ℤ) : ℂ) * r) := by rw [fallFact_one]; push_cast; ring
  rw [h2, hc] at h
  exact h

/-- Residual of `dRat (dRat β)`, explicit constant. -/
lemma deriv2_resid {β : RatFunc ℂ} {r : ℂ}
    (hres : ((ordAt α β + 1 : ℤ) : WithTop ℤ) ≤ ordAtT α
      (β - algebraMap (Polynomial ℂ) (RatFunc ℂ) (Polynomial.C r)
        * linFactor (K := ℂ) α ^ (ordAt α β))) :
    ((((ordAt α β : ℤ) - 1 : ℤ)) : WithTop ℤ) ≤ ordAtT α
      (Submission.CDT.dRat (Submission.CDT.dRat β) - algebraMap (Polynomial ℂ) (RatFunc ℂ)
          (Polynomial.C ((((ordAt α β : ℤ)) * (((ordAt α β : ℤ)) - 1)) * r))
          * linFactor (K := ℂ) α ^ (((ordAt α β : ℤ)) - 2)) := by
  have h : (((ordAt α β - (2 : ℤ) + 1 : ℤ)) : WithTop ℤ) ≤ ordAtT α
      (Submission.CDT.dRat (Submission.CDT.dRat β) - algebraMap (Polynomial ℂ) (RatFunc ℂ)
          (Polynomial.C (r * ((Commons.Algebra.Polynomial.fallFact (ordAt α β) 2 : ℤ) : ℂ)))
          * linFactor (K := ℂ) α ^ (ordAt α β - (2 : ℤ))) :=
    deriv_resid' (α := α) (r := r) hres 2
  have h2 : (((ordAt α β - (2 : ℤ) + 1 : ℤ)) : WithTop ℤ)
      = ((((ordAt α β : ℤ) - 1 : ℤ)) : WithTop ℤ) := by
    congr 1; ring
  have hc : (r * ((Commons.Algebra.Polynomial.fallFact (ordAt α β) 2 : ℤ) : ℂ))
      = ((((ordAt α β : ℤ)) * (((ordAt α β : ℤ)) - 1)) * r) := by
    rw [fallFact_two]; push_cast; ring
  rw [h2, hc] at h
  exact h

lemma ord_C_mul_linFactor (c : ℂ) (hc : c ≠ 0) (k : ℤ) :
    ordAtT α (algebraMap (Polynomial ℂ) (RatFunc ℂ) (Polynomial.C c) * linFactor (K := ℂ) α ^ k)
      = (k : WithTop ℤ) := by
  rw [ordAtT_mul α (RatFunc.algebraMap_ne_zero (Polynomial.C_ne_zero.mpr hc))
      (zpow_ne_zero _ (linFactor_ne_zero α)),
    ordAtT_algebraMap (Polynomial.C_ne_zero.mpr hc), Polynomial.rootMultiplicity_C,
    ordAtT_linFactor_zpow]
  simp

lemma ord_eq_of_resid {f : RatFunc ℂ} {N : ℤ} {c : ℂ} (hc : c ≠ 0)
    (hres : ((N + 1 : ℤ) : WithTop ℤ) ≤ ordAtT α
      (f - algebraMap (Polynomial ℂ) (RatFunc ℂ) (Polynomial.C c) * linFactor (K := ℂ) α ^ N)) :
    ordAtT α f = (N : WithTop ℤ) := by
  have h1 : ordAtT α (algebraMap (Polynomial ℂ) (RatFunc ℂ) (Polynomial.C c)
      * linFactor (K := ℂ) α ^ N) = (N : WithTop ℤ) := ord_C_mul_linFactor c hc N
  have he : f = algebraMap (Polynomial ℂ) (RatFunc ℂ) (Polynomial.C c) * linFactor (K := ℂ) α ^ N
      + (f - algebraMap (Polynomial ℂ) (RatFunc ℂ) (Polynomial.C c) * linFactor (K := ℂ) α ^ N) := by
    ring
  rw [he]
  exact ordAtT_add_eq_of_le_succ h1 hres

/-- Multiplication by a polynomial that does not vanish at `α`, applied to a function with
leading term `c·(X−α)^N`: the residual. -/
lemma mul_poly_resid {f : RatFunc ℂ} {N : ℤ} {c : ℂ} (hc : c ≠ 0)
    (hres : ((N + 1 : ℤ) : WithTop ℤ) ≤ ordAtT α
      (f - algebraMap (Polynomial ℂ) (RatFunc ℂ) (Polynomial.C c) * linFactor (K := ℂ) α ^ N))
    {P : Polynomial ℂ} (hP : P.eval α ≠ 0) :
    ((N + 1 : ℤ) : WithTop ℤ) ≤ ordAtT α
      (algebraMap (Polynomial ℂ) (RatFunc ℂ) P * f
        - algebraMap (Polynomial ℂ) (RatFunc ℂ) (Polynomial.C (P.eval α * c))
          * linFactor (K := ℂ) α ^ N) := by
  have hf : ordAtT α f = (N : WithTop ℤ) := ord_eq_of_resid hc hres
  have hdecomp : algebraMap (Polynomial ℂ) (RatFunc ℂ) P * f
      - algebraMap (Polynomial ℂ) (RatFunc ℂ) (Polynomial.C (P.eval α * c))
        * linFactor (K := ℂ) α ^ N
      = algebraMap (Polynomial ℂ) (RatFunc ℂ) (Polynomial.C (P.eval α))
          * (f - algebraMap (Polynomial ℂ) (RatFunc ℂ) (Polynomial.C c) * linFactor (K := ℂ) α ^ N)
        + algebraMap (Polynomial ℂ) (RatFunc ℂ) (P - Polynomial.C (P.eval α)) * f := by
    simp only [map_sub, map_mul, Polynomial.C_mul]
    ring
  rw [hdecomp]
  refine le_trans (le_min ?_ ?_) (ordAtT_add_ge α _ _)
  · calc ((N + 1 : ℤ) : WithTop ℤ)
        = (0 : WithTop ℤ) + ((N + 1 : ℤ) : WithTop ℤ) := (zero_add _).symm
      _ ≤ ordAtT α (algebraMap (Polynomial ℂ) (RatFunc ℂ) (Polynomial.C (P.eval α)))
            + ordAtT α (f - algebraMap (Polynomial ℂ) (RatFunc ℂ) (Polynomial.C c)
                * linFactor (K := ℂ) α ^ N) :=
          add_le_add (zero_le_ordAtT_algebraMap_C α (P.eval α)) hres
      _ ≤ _ := ordAtT_mul_ge α _ _
  · by_cases hP0 : P - Polynomial.C (P.eval α) = 0
    · rw [hP0, map_zero, zero_mul]
      simp [ordAtT]
    · have hev : (P - Polynomial.C (P.eval α)).eval α = 0 := by simp
      have hroot : ((1 : ℤ) : WithTop ℤ) ≤ ordAtT α
          (algebraMap (Polynomial ℂ) (RatFunc ℂ) (P - Polynomial.C (P.eval α))) := by
        rw [ordAtT_algebraMap hP0]
        have h1 : 1 ≤ Polynomial.rootMultiplicity α (P - Polynomial.C (P.eval α)) := by
          rw [Polynomial.le_rootMultiplicity_iff hP0, pow_one, Polynomial.dvd_iff_isRoot,
            Polynomial.IsRoot.def]
          exact hev
        exact_mod_cast h1
      calc ((N + 1 : ℤ) : WithTop ℤ)
          = ((1 : ℤ) : WithTop ℤ) + ((N : ℤ) : WithTop ℤ) := by
            rw [← WithTop.coe_add]; congr 1; ring
        _ ≤ ordAtT α (algebraMap (Polynomial ℂ) (RatFunc ℂ) (P - Polynomial.C (P.eval α)))
              + ordAtT α f := add_le_add hroot (le_of_eq hf.symm)
        _ ≤ _ := ordAtT_mul_ge α _ _

/-- Multiplication by a polynomial that does not vanish at `α`: the product has order `N`. -/
lemma mul_poly_ord {f : RatFunc ℂ} {N : ℤ} {c : ℂ} (hc : c ≠ 0)
    (hres : ((N + 1 : ℤ) : WithTop ℤ) ≤ ordAtT α
      (f - algebraMap (Polynomial ℂ) (RatFunc ℂ) (Polynomial.C c) * linFactor (K := ℂ) α ^ N))
    {P : Polynomial ℂ} (hP : P.eval α ≠ 0) :
    ordAtT α (algebraMap (Polynomial ℂ) (RatFunc ℂ) P * f) = (N : WithTop ℤ) := by
  have hres' := mul_poly_resid hc hres hP
  have hc' : P.eval α * c ≠ 0 := mul_ne_zero hP hc
  have := ord_eq_of_resid (f := algebraMap (Polynomial ℂ) (RatFunc ℂ) P * f)
    (N := N) (c := P.eval α * c) hc' hres'
  -- the leading term is `C (P.eval α * c) * linFactor^N`
  simpa using this


/-! ## 3. The two local order lemmas -/

/-- The order of a polynomial is nonnegative. -/
lemma zero_le_ordAtT_algebraMap_poly {α : ℂ} (P : Polynomial ℂ) :
    (0 : WithTop ℤ) ≤ ordAtT α (algebraMap (Polynomial ℂ) (RatFunc ℂ) P) := by
  rcases eq_or_ne P 0 with rfl | hP
  · rw [map_zero]; simp [ordAtT]
  · rw [ordAtT_algebraMap hP]
    exact WithTop.coe_le_coe.mpr (by exact_mod_cast Nat.zero_le (Polynomial.rootMultiplicity α P))

/-- **Generic local bound.**  If `P₂` does not vanish at `α`, a solution `β ≠ 0` with a pole at
`α` has order exactly `ord_α β - 2` there. -/
lemma order_eq_generic {a b : ℚ} {β : RatFunc ℂ} (hβ : β ≠ 0) (hN : ordAt α β < 0)
    (hP2 : (P2Cm a b).eval α ≠ 0) :
    ordAtT α (algebraMap (Polynomial ℂ) (RatFunc ℂ) (P2Cm a b)
        * Submission.CDT.dRat (Submission.CDT.dRat β)
      + algebraMap (Polynomial ℂ) (RatFunc ℂ) (AadjL a b) * Submission.CDT.dRat β
      + algebraMap (Polynomial ℂ) (RatFunc ℂ) (CadjL a b) * β)
      = ((((ordAt α β : ℤ)) - 2 : ℤ) : WithTop ℤ) := by
  obtain ⟨r, hr, hres⟩ := leading_resid (α := α) hβ
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
    deriv1_resid (α := α) (β := β) (r := r) hres
  have hres2 : ((((ordAt α β : ℤ)) - 1 : ℤ) : WithTop ℤ) ≤ ordAtT α
      (Submission.CDT.dRat (Submission.CDT.dRat β) - algebraMap (Polynomial ℂ) (RatFunc ℂ)
        (Polynomial.C ((((ordAt α β : ℤ)) * ((ordAt α β : ℤ) - 1)) * r))
        * linFactor (K := ℂ) α ^ ((ordAt α β : ℤ) - 2)) :=
    deriv2_resid (α := α) (β := β) (r := r) hres
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
    ord_eq_of_resid (f := β) (N := (ordAt α β : ℤ)) (c := r) hr hres
  have hord1 : ordAtT α (Submission.CDT.dRat β) = (((ordAt α β : ℤ)) - 1 : WithTop ℤ) :=
    ord_eq_of_resid (f := Submission.CDT.dRat β) (N := ((ordAt α β : ℤ)) - 1)
      (c := ((ordAt α β : ℤ) : ℂ) * r) hc1ne hres1'
  have hord2 : ordAtT α (Submission.CDT.dRat (Submission.CDT.dRat β))
      = (((ordAt α β : ℤ)) - 2 : WithTop ℤ) :=
    ord_eq_of_resid (f := Submission.CDT.dRat (Submission.CDT.dRat β))
      (N := ((ordAt α β : ℤ)) - 2)
      (c := (((ordAt α β : ℤ)) * ((ordAt α β : ℤ) - 1)) * r) hc2ne hres2'
  -- term bounds
  have hT1 : ((((ordAt α β : ℤ)) - 1 : ℤ) : WithTop ℤ) ≤ ordAtT α
      (algebraMap (Polynomial ℂ) (RatFunc ℂ) (P2Cm a b)
          * Submission.CDT.dRat (Submission.CDT.dRat β)
        - algebraMap (Polynomial ℂ) (RatFunc ℂ)
            (Polynomial.C ((P2Cm a b).eval α * ((((ordAt α β : ℤ)) * ((ordAt α β : ℤ) - 1)) * r)))
          * linFactor (K := ℂ) α ^ ((ordAt α β : ℤ) - 2)) := by
    have h := mul_poly_resid (f := Submission.CDT.dRat (Submission.CDT.dRat β))
      (N := ((ordAt α β : ℤ)) - 2)
      (c := (((ordAt α β : ℤ)) * ((ordAt α β : ℤ) - 1)) * r) hc2ne hres2' hP2
    have h2 : (((((ordAt α β : ℤ)) - 2) + 1 : ℤ)) = ((((ordAt α β : ℤ)) - 1 : ℤ)) := by ring
    rwa [h2] at h
  have hordT1 : ordAtT α (algebraMap (Polynomial ℂ) (RatFunc ℂ) (P2Cm a b)
      * Submission.CDT.dRat (Submission.CDT.dRat β)) = (((ordAt α β : ℤ)) - 2 : WithTop ℤ) :=
    mul_poly_ord (f := Submission.CDT.dRat (Submission.CDT.dRat β))
      (N := ((ordAt α β : ℤ)) - 2)
      (c := (((ordAt α β : ℤ)) * ((ordAt α β : ℤ) - 1)) * r) hc2ne hres2' hP2
  have hT2 : ((((ordAt α β : ℤ)) - 1 : ℤ) : WithTop ℤ) ≤ ordAtT α
      (algebraMap (Polynomial ℂ) (RatFunc ℂ) (AadjL a b) * Submission.CDT.dRat β) := by
    calc ((((ordAt α β : ℤ)) - 1 : ℤ) : WithTop ℤ)
        = (0 : WithTop ℤ) + ((((ordAt α β : ℤ)) - 1 : ℤ) : WithTop ℤ) := (zero_add _).symm
      _ ≤ ordAtT α (algebraMap (Polynomial ℂ) (RatFunc ℂ) (AadjL a b))
            + ordAtT α (Submission.CDT.dRat β) :=
          add_le_add (zero_le_ordAtT_algebraMap_poly (AadjL a b)) (le_of_eq hord1.symm)
      _ ≤ _ := ordAtT_mul_ge α _ _
  have hT3 : (((ordAt α β : ℤ)) : WithTop ℤ) ≤ ordAtT α
      (algebraMap (Polynomial ℂ) (RatFunc ℂ) (CadjL a b) * β) := by
    calc (((ordAt α β : ℤ)) : WithTop ℤ)
        = (0 : WithTop ℤ) + (((ordAt α β : ℤ)) : WithTop ℤ) := (zero_add _).symm
      _ ≤ ordAtT α (algebraMap (Polynomial ℂ) (RatFunc ℂ) (CadjL a b)) + ordAtT α β :=
          add_le_add (zero_le_ordAtT_algebraMap_poly (CadjL a b)) (le_of_eq hordβ.symm)
      _ ≤ _ := ordAtT_mul_ge α _ _
  -- the leading term
  have hlt : ordAtT α (algebraMap (Polynomial ℂ) (RatFunc ℂ)
      (Polynomial.C ((P2Cm a b).eval α * ((((ordAt α β : ℤ)) * ((ordAt α β : ℤ) - 1)) * r)))
        * linFactor (K := ℂ) α ^ ((ordAt α β : ℤ) - 2)) = (((ordAt α β : ℤ)) - 2 : WithTop ℤ) :=
    ord_C_mul_linFactor _ (mul_ne_zero hP2 hc2ne) _
  -- the residual
  have hcomb : ((((ordAt α β : ℤ)) - 1 : ℤ) : WithTop ℤ) ≤ ordAtT α
      (algebraMap (Polynomial ℂ) (RatFunc ℂ) (P2Cm a b)
          * Submission.CDT.dRat (Submission.CDT.dRat β)
        + algebraMap (Polynomial ℂ) (RatFunc ℂ) (AadjL a b) * Submission.CDT.dRat β
        + algebraMap (Polynomial ℂ) (RatFunc ℂ) (CadjL a b) * β
        - algebraMap (Polynomial ℂ) (RatFunc ℂ)
            (Polynomial.C ((P2Cm a b).eval α * ((((ordAt α β : ℤ)) * ((ordAt α β : ℤ) - 1)) * r)))
          * linFactor (K := ℂ) α ^ ((ordAt α β : ℤ) - 2)) := by
    have he : algebraMap (Polynomial ℂ) (RatFunc ℂ) (P2Cm a b)
          * Submission.CDT.dRat (Submission.CDT.dRat β)
        + algebraMap (Polynomial ℂ) (RatFunc ℂ) (AadjL a b) * Submission.CDT.dRat β
        + algebraMap (Polynomial ℂ) (RatFunc ℂ) (CadjL a b) * β
        - algebraMap (Polynomial ℂ) (RatFunc ℂ)
            (Polynomial.C ((P2Cm a b).eval α * ((((ordAt α β : ℤ)) * ((ordAt α β : ℤ) - 1)) * r)))
          * linFactor (K := ℂ) α ^ ((ordAt α β : ℤ) - 2)
        = (algebraMap (Polynomial ℂ) (RatFunc ℂ) (P2Cm a b)
              * Submission.CDT.dRat (Submission.CDT.dRat β)
            - algebraMap (Polynomial ℂ) (RatFunc ℂ)
                (Polynomial.C ((P2Cm a b).eval α * ((((ordAt α β : ℤ)) * ((ordAt α β : ℤ) - 1)) * r)))
              * linFactor (K := ℂ) α ^ ((ordAt α β : ℤ) - 2))
          + (algebraMap (Polynomial ℂ) (RatFunc ℂ) (AadjL a b) * Submission.CDT.dRat β
              + algebraMap (Polynomial ℂ) (RatFunc ℂ) (CadjL a b) * β) := by ring
    rw [he]
    refine le_trans (le_min hT1 ?_) (ordAtT_add_ge α _ _)
    refine le_trans (le_min hT2 ?_) (ordAtT_add_ge α _ _)
    exact le_trans (by rw [WithTop.coe_le_coe]; omega) hT3
  -- conclude
  have he : algebraMap (Polynomial ℂ) (RatFunc ℂ) (P2Cm a b)
        * Submission.CDT.dRat (Submission.CDT.dRat β)
      + algebraMap (Polynomial ℂ) (RatFunc ℂ) (AadjL a b) * Submission.CDT.dRat β
      + algebraMap (Polynomial ℂ) (RatFunc ℂ) (CadjL a b) * β
      = algebraMap (Polynomial ℂ) (RatFunc ℂ)
          (Polynomial.C ((P2Cm a b).eval α * ((((ordAt α β : ℤ)) * ((ordAt α β : ℤ) - 1)) * r)))
          * linFactor (K := ℂ) α ^ ((ordAt α β : ℤ) - 2)
        + (algebraMap (Polynomial ℂ) (RatFunc ℂ) (P2Cm a b)
              * Submission.CDT.dRat (Submission.CDT.dRat β)
          + algebraMap (Polynomial ℂ) (RatFunc ℂ) (AadjL a b) * Submission.CDT.dRat β
          + algebraMap (Polynomial ℂ) (RatFunc ℂ) (CadjL a b) * β
          - algebraMap (Polynomial ℂ) (RatFunc ℂ)
              (Polynomial.C ((P2Cm a b).eval α * ((((ordAt α β : ℤ)) * ((ordAt α β : ℤ) - 1)) * r)))
            * linFactor (K := ℂ) α ^ ((ordAt α β : ℤ) - 2)) := by ring
  rw [he]
  refine ordAtT_add_eq_of_le_succ hlt ?_
  have h2 : ((((ordAt α β : ℤ)) - 2) + 1) = (((ordAt α β : ℤ)) - 1) := by ring
  rwa [h2]


/-- The order of `P − P(α)` (a polynomial vanishing at `α`) is at least one. -/
lemma one_le_ordAtT_algebraMap_sub_C_eval {α : ℂ} {P : Polynomial ℂ} :
    ((1 : ℤ) : WithTop ℤ) ≤ ordAtT α
      (algebraMap (Polynomial ℂ) (RatFunc ℂ) (P - Polynomial.C (P.eval α))) := by
  by_cases hP0 : P - Polynomial.C (P.eval α) = 0
  · rw [hP0, map_zero]; simp [ordAtT]
  · have hev : (P - Polynomial.C (P.eval α)).eval α = 0 := by simp
    rw [ordAtT_algebraMap hP0]
    have h1 : 1 ≤ Polynomial.rootMultiplicity α (P - Polynomial.C (P.eval α)) := by
      rw [Polynomial.le_rootMultiplicity_iff hP0, pow_one, Polynomial.dvd_iff_isRoot,
        Polynomial.IsRoot.def]
      exact hev
    exact_mod_cast h1

/-- **Singular local bound.**  If `P₂ = (X−α)·P₂ˢ` with `P₂ˢ(α) ≠ 0`, a solution `β ≠ 0` with a
pole at `α` has order exactly `ord_α β - 1` there, the indicial value being
`(ord_α β)·((ord_α β − 1)·P₂ˢ(α) + A(α))`. -/
lemma order_eq_singular {a b : ℚ} {β : RatFunc ℂ} (hβ : β ≠ 0) (hN : ordAt α β < 0)
    {P2s : Polynomial ℂ} (hfac : P2Cm a b = (Polynomial.X - Polynomial.C α) * P2s)
    (hP2s : P2s.eval α ≠ 0)
    (hcoef : (((ordAt α β : ℤ) : ℂ) * ((((ordAt α β : ℤ) : ℂ) - 1) * P2s.eval α
      + (AadjL a b).eval α)) ≠ 0) :
    ordAtT α (algebraMap (Polynomial ℂ) (RatFunc ℂ) (P2Cm a b)
        * Submission.CDT.dRat (Submission.CDT.dRat β)
      + algebraMap (Polynomial ℂ) (RatFunc ℂ) (AadjL a b) * Submission.CDT.dRat β
      + algebraMap (Polynomial ℂ) (RatFunc ℂ) (CadjL a b) * β)
      = ((((ordAt α β : ℤ)) - 1 : ℤ) : WithTop ℤ) := by
  obtain ⟨r, hr, hres⟩ := leading_resid (α := α) hβ
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
    have h := deriv1_resid (α := α) (β := β) (r := r) hres
    rwa [← hc1] at h
  have hres2 : ((((ordAt α β : ℤ)) - 1 : ℤ) : WithTop ℤ) ≤ ordAtT α
      (Submission.CDT.dRat (Submission.CDT.dRat β) - algebraMap (Polynomial ℂ) (RatFunc ℂ)
        (Polynomial.C c2) * linFactor (K := ℂ) α ^ ((ordAt α β : ℤ) - 2)) := by
    have h := deriv2_resid (α := α) (β := β) (r := r) hres
    rwa [← hc2] at h
  have hres2' : ((((ordAt α β : ℤ) - 2) + 1 : ℤ) : WithTop ℤ) ≤ ordAtT α
      (Submission.CDT.dRat (Submission.CDT.dRat β) - algebraMap (Polynomial ℂ) (RatFunc ℂ)
        (Polynomial.C c2) * linFactor (K := ℂ) α ^ (((ordAt α β : ℤ)) - 2)) := by
    rw [show (((ordAt α β : ℤ) - 2) + 1) = (((ordAt α β : ℤ)) - 1) from by ring]
    exact hres2
  have hordβ : ordAtT α β = (((ordAt α β : ℤ)) : WithTop ℤ) :=
    ord_eq_of_resid (f := β) (N := (ordAt α β : ℤ)) (c := r) hr hres
  have hord1 : ordAtT α (Submission.CDT.dRat β) = (((ordAt α β : ℤ)) - 1 : WithTop ℤ) := by
    have h : ((((ordAt α β : ℤ) - 1) + 1 : ℤ) : WithTop ℤ) ≤ ordAtT α
        (Submission.CDT.dRat β - algebraMap (Polynomial ℂ) (RatFunc ℂ)
          (Polynomial.C c1) * linFactor (K := ℂ) α ^ (((ordAt α β : ℤ)) - 1)) := by
      rw [show (((ordAt α β : ℤ) - 1) + 1) = (ordAt α β : ℤ) from by ring]
      exact hres1
    exact ord_eq_of_resid (f := Submission.CDT.dRat β) (N := ((ordAt α β : ℤ)) - 1)
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
    refine ord_eq_of_resid (f := linFactor (K := ℂ) α * Submission.CDT.dRat (Submission.CDT.dRat β))
      (N := ((ordAt α β : ℤ)) - 1) (c := c2) hc2ne ?_
    rw [sub_add_cancel]
    exact hq
  -- the `P₂·β''` term
  have hP2eq : algebraMap (Polynomial ℂ) (RatFunc ℂ) (P2Cm a b)
        * Submission.CDT.dRat (Submission.CDT.dRat β)
      = algebraMap (Polynomial ℂ) (RatFunc ℂ) P2s
        * (linFactor (K := ℂ) α * Submission.CDT.dRat (Submission.CDT.dRat β)) := by
    rw [hfac, map_mul]
    simp only [linFactor]
    ring
  have hT1 : (((ordAt α β : ℤ)) : WithTop ℤ) ≤ ordAtT α
      (algebraMap (Polynomial ℂ) (RatFunc ℂ) (P2Cm a b)
          * Submission.CDT.dRat (Submission.CDT.dRat β)
        - algebraMap (Polynomial ℂ) (RatFunc ℂ) (Polynomial.C (P2s.eval α * c2))
          * linFactor (K := ℂ) α ^ (((ordAt α β : ℤ)) - 1)) := by
    rw [hP2eq]
    have h := mul_poly_resid (f := linFactor (K := ℂ) α * Submission.CDT.dRat (Submission.CDT.dRat β))
      (N := ((ordAt α β : ℤ)) - 1) (c := c2) hc2ne (by rw [sub_add_cancel]; exact hq) hP2s
    rw [sub_add_cancel] at h
    exact h
  -- the `A·β'` term
  have hT2 : (((ordAt α β : ℤ)) : WithTop ℤ) ≤ ordAtT α
      (algebraMap (Polynomial ℂ) (RatFunc ℂ) (AadjL a b) * Submission.CDT.dRat β
        - algebraMap (Polynomial ℂ) (RatFunc ℂ) (Polynomial.C ((AadjL a b).eval α * c1))
          * linFactor (K := ℂ) α ^ (((ordAt α β : ℤ)) - 1)) := by
    have hdecomp : algebraMap (Polynomial ℂ) (RatFunc ℂ) (AadjL a b) * Submission.CDT.dRat β
        - algebraMap (Polynomial ℂ) (RatFunc ℂ) (Polynomial.C ((AadjL a b).eval α * c1))
          * linFactor (K := ℂ) α ^ (((ordAt α β : ℤ)) - 1)
        = algebraMap (Polynomial ℂ) (RatFunc ℂ) (Polynomial.C ((AadjL a b).eval α))
            * (Submission.CDT.dRat β - algebraMap (Polynomial ℂ) (RatFunc ℂ) (Polynomial.C c1)
              * linFactor (K := ℂ) α ^ (((ordAt α β : ℤ)) - 1))
          + algebraMap (Polynomial ℂ) (RatFunc ℂ)
              (AadjL a b - Polynomial.C ((AadjL a b).eval α)) * Submission.CDT.dRat β := by
      simp only [map_sub, map_mul, Polynomial.C_mul]
      ring
    rw [hdecomp]
    refine le_trans (le_min ?_ ?_) (ordAtT_add_ge α _ _)
    · calc (((ordAt α β : ℤ)) : WithTop ℤ)
          = (0 : WithTop ℤ) + (((ordAt α β : ℤ)) : WithTop ℤ) := (zero_add _).symm
        _ ≤ ordAtT α (algebraMap (Polynomial ℂ) (RatFunc ℂ) (Polynomial.C ((AadjL a b).eval α)))
              + ordAtT α (Submission.CDT.dRat β - algebraMap (Polynomial ℂ) (RatFunc ℂ)
                  (Polynomial.C c1) * linFactor (K := ℂ) α ^ (((ordAt α β : ℤ)) - 1)) :=
            add_le_add (zero_le_ordAtT_algebraMap_C α _) hres1
        _ ≤ _ := ordAtT_mul_ge α _ _
    · calc (((ordAt α β : ℤ)) : WithTop ℤ)
          = ((1 : ℤ) : WithTop ℤ) + ((((ordAt α β : ℤ)) - 1 : ℤ) : WithTop ℤ) := by
            rw [← WithTop.coe_add]; congr 1; ring
        _ ≤ ordAtT α (algebraMap (Polynomial ℂ) (RatFunc ℂ)
              (AadjL a b - Polynomial.C ((AadjL a b).eval α)))
              + ordAtT α (Submission.CDT.dRat β) :=
            add_le_add one_le_ordAtT_algebraMap_sub_C_eval (le_of_eq hord1.symm)
        _ ≤ _ := ordAtT_mul_ge α _ _
  -- the `C·β` term
  have hT3 : (((ordAt α β : ℤ)) : WithTop ℤ) ≤ ordAtT α
      (algebraMap (Polynomial ℂ) (RatFunc ℂ) (CadjL a b) * β) := by
    calc (((ordAt α β : ℤ)) : WithTop ℤ)
        = (0 : WithTop ℤ) + (((ordAt α β : ℤ)) : WithTop ℤ) := (zero_add _).symm
      _ ≤ ordAtT α (algebraMap (Polynomial ℂ) (RatFunc ℂ) (CadjL a b)) + ordAtT α β :=
          add_le_add (zero_le_ordAtT_algebraMap_poly (CadjL a b)) (le_of_eq hordβ.symm)
      _ ≤ _ := ordAtT_mul_ge α _ _
  -- the indicial coefficient
  have hcoefne : (P2s.eval α * c2 + (AadjL a b).eval α * c1) ≠ 0 := by
    have heq : P2s.eval α * c2 + (AadjL a b).eval α * c1
        = r * (((ordAt α β : ℤ) : ℂ) * ((((ordAt α β : ℤ) : ℂ) - 1) * P2s.eval α
            + (AadjL a b).eval α)) := by
      rw [hc1, hc2]; ring
    rw [heq]
    exact mul_ne_zero hr hcoef
  have hlt : ordAtT α (algebraMap (Polynomial ℂ) (RatFunc ℂ)
      (Polynomial.C (P2s.eval α * c2 + (AadjL a b).eval α * c1))
        * linFactor (K := ℂ) α ^ (((ordAt α β : ℤ)) - 1)) = ((((ordAt α β : ℤ)) - 1 : ℤ) : WithTop ℤ) :=
    ord_C_mul_linFactor _ hcoefne _
  -- the residual
  have hcomb : (((ordAt α β : ℤ)) : WithTop ℤ) ≤ ordAtT α
      (algebraMap (Polynomial ℂ) (RatFunc ℂ) (P2Cm a b)
          * Submission.CDT.dRat (Submission.CDT.dRat β)
        + algebraMap (Polynomial ℂ) (RatFunc ℂ) (AadjL a b) * Submission.CDT.dRat β
        + algebraMap (Polynomial ℂ) (RatFunc ℂ) (CadjL a b) * β
        - algebraMap (Polynomial ℂ) (RatFunc ℂ)
            (Polynomial.C (P2s.eval α * c2 + (AadjL a b).eval α * c1))
          * linFactor (K := ℂ) α ^ (((ordAt α β : ℤ)) - 1)) := by
    have he : algebraMap (Polynomial ℂ) (RatFunc ℂ) (P2Cm a b)
          * Submission.CDT.dRat (Submission.CDT.dRat β)
        + algebraMap (Polynomial ℂ) (RatFunc ℂ) (AadjL a b) * Submission.CDT.dRat β
        + algebraMap (Polynomial ℂ) (RatFunc ℂ) (CadjL a b) * β
        - algebraMap (Polynomial ℂ) (RatFunc ℂ)
            (Polynomial.C (P2s.eval α * c2 + (AadjL a b).eval α * c1))
          * linFactor (K := ℂ) α ^ (((ordAt α β : ℤ)) - 1)
        = (algebraMap (Polynomial ℂ) (RatFunc ℂ) (P2Cm a b)
              * Submission.CDT.dRat (Submission.CDT.dRat β)
            - algebraMap (Polynomial ℂ) (RatFunc ℂ) (Polynomial.C (P2s.eval α * c2))
              * linFactor (K := ℂ) α ^ (((ordAt α β : ℤ)) - 1))
          + ((algebraMap (Polynomial ℂ) (RatFunc ℂ) (AadjL a b) * Submission.CDT.dRat β
              - algebraMap (Polynomial ℂ) (RatFunc ℂ) (Polynomial.C ((AadjL a b).eval α * c1))
                * linFactor (K := ℂ) α ^ (((ordAt α β : ℤ)) - 1))
            + algebraMap (Polynomial ℂ) (RatFunc ℂ) (CadjL a b) * β) := by
      simp only [Polynomial.C_add, Polynomial.C_mul, map_add, map_mul]
      ring
    rw [he]
    refine le_trans (le_min hT1 ?_) (ordAtT_add_ge α _ _)
    refine le_trans (le_min hT2 ?_) (ordAtT_add_ge α _ _)
    exact hT3
  -- conclude
  have he : algebraMap (Polynomial ℂ) (RatFunc ℂ) (P2Cm a b)
        * Submission.CDT.dRat (Submission.CDT.dRat β)
      + algebraMap (Polynomial ℂ) (RatFunc ℂ) (AadjL a b) * Submission.CDT.dRat β
      + algebraMap (Polynomial ℂ) (RatFunc ℂ) (CadjL a b) * β
      = algebraMap (Polynomial ℂ) (RatFunc ℂ)
          (Polynomial.C (P2s.eval α * c2 + (AadjL a b).eval α * c1))
          * linFactor (K := ℂ) α ^ (((ordAt α β : ℤ)) - 1)
        + (algebraMap (Polynomial ℂ) (RatFunc ℂ) (P2Cm a b)
              * Submission.CDT.dRat (Submission.CDT.dRat β)
          + algebraMap (Polynomial ℂ) (RatFunc ℂ) (AadjL a b) * Submission.CDT.dRat β
          + algebraMap (Polynomial ℂ) (RatFunc ℂ) (CadjL a b) * β
          - algebraMap (Polynomial ℂ) (RatFunc ℂ)
              (Polynomial.C (P2s.eval α * c2 + (AadjL a b).eval α * c1))
            * linFactor (K := ℂ) α ^ (((ordAt α β : ℤ)) - 1)) := by ring
  rw [he]
  refine ordAtT_add_eq_of_le_succ hlt ?_
  rw [sub_add_cancel]
  exact hcomb


/-! ## 4. Evaluations of the coefficient polynomials -/

lemma eval_map_rat (p : Polynomial ℚ) (x : ℚ) :
    ((p.map (algebraMap ℚ ℂ)).eval (algebraMap ℚ ℂ x)) = algebraMap ℚ ℂ (p.eval x) := by
  rw [Polynomial.eval_map, Polynomial.eval₂_at_apply]

lemma eval_map_rat_deriv (p : Polynomial ℚ) (x : ℚ) :
    (((p.map (algebraMap ℚ ℂ)).derivative).eval (algebraMap ℚ ℂ x))
      = algebraMap ℚ ℂ (p.derivative.eval x) := by
  rw [Polynomial.derivative_map, eval_map_rat]

lemma Q4x_eval_zero (a b : ℚ) : (Work.C17.Q4x a b).eval (0 : ℚ) = 1 := by
  simp [Work.C17.Q4x]

lemma Q4x_eval_one (a b : ℚ) : (Work.C17.Q4x a b).eval (1 : ℚ) = 4 * (a - b) ^ 2 := by
  simp only [Work.C17.Q4x, Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C, Polynomial.eval_one,
    Polynomial.eval_ofNat]
  ring

lemma Q4x_eval_neg_one (a b : ℚ) : (Work.C17.Q4x a b).eval (-1 : ℚ) = 4 * (a + b) ^ 2 := by
  simp only [Work.C17.Q4x, Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C, Polynomial.eval_one,
    Polynomial.eval_neg, Polynomial.eval_ofNat]
  ring

lemma Q4Cm_eval_zero (a b : ℚ) : (Q4Cm a b).eval (0 : ℂ) = 1 := by
  rw [show (0 : ℂ) = algebraMap ℚ ℂ (0 : ℚ) from by simp, Q4Cm, eval_map_rat, Q4x_eval_zero]
  push_cast
  norm_num

lemma Q4Cm_eval_one (a b : ℚ) : (Q4Cm a b).eval (1 : ℂ) = 4 * ((a : ℂ) - (b : ℂ)) ^ 2 := by
  rw [show (1 : ℂ) = algebraMap ℚ ℂ (1 : ℚ) from by simp, Q4Cm, eval_map_rat, Q4x_eval_one]
  push_cast
  norm_num

lemma Q4Cm_eval_neg_one (a b : ℚ) :
    (Q4Cm a b).eval (-1 : ℂ) = 4 * ((a : ℂ) + (b : ℂ)) ^ 2 := by
  rw [show (-1 : ℂ) = algebraMap ℚ ℂ (-1 : ℚ) from by simp, Q4Cm, eval_map_rat,
    Q4x_eval_neg_one]
  push_cast
  norm_num

lemma P2x_deriv_eval_zero (a b : ℚ) : (Work.C17.P2x a b).derivative.eval (0 : ℚ) = -1 := by
  simp only [Work.C17.P2x, Work.C17.Q4x, Polynomial.derivative_mul, Polynomial.derivative_sub,
    Polynomial.derivative_add, Polynomial.derivative_pow, Polynomial.derivative_X,
    Polynomial.derivative_C, Polynomial.derivative_one, Polynomial.eval_add, Polynomial.eval_sub,
    Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C,
    Polynomial.eval_one, Polynomial.eval_neg, Polynomial.eval_zero, Polynomial.eval_ofNat]
  ring

lemma P2x_deriv_eval_one (a b : ℚ) : (Work.C17.P2x a b).derivative.eval (1 : ℚ)
    = 8 * (a - b) ^ 2 := by
  simp only [Work.C17.P2x, Work.C17.Q4x, Polynomial.derivative_mul, Polynomial.derivative_sub,
    Polynomial.derivative_add, Polynomial.derivative_pow, Polynomial.derivative_X,
    Polynomial.derivative_C, Polynomial.derivative_one, Polynomial.eval_add, Polynomial.eval_sub,
    Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C,
    Polynomial.eval_one, Polynomial.eval_neg, Polynomial.eval_zero, Polynomial.eval_ofNat]
  ring

lemma P2x_deriv_eval_neg_one (a b : ℚ) : (Work.C17.P2x a b).derivative.eval (-1 : ℚ)
    = 8 * (a + b) ^ 2 := by
  simp only [Work.C17.P2x, Work.C17.Q4x, Polynomial.derivative_mul, Polynomial.derivative_sub,
    Polynomial.derivative_add, Polynomial.derivative_pow, Polynomial.derivative_X,
    Polynomial.derivative_C, Polynomial.derivative_one, Polynomial.eval_add, Polynomial.eval_sub,
    Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C,
    Polynomial.eval_one, Polynomial.eval_neg, Polynomial.eval_zero, Polynomial.eval_ofNat]
  ring

lemma P1x_eval_zero (a b : ℚ) : (Work.C17.P1x a b).eval (0 : ℚ) = -1 := by
  simp only [Work.C17.P1x, Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C, Polynomial.eval_one,
    Polynomial.eval_neg, Polynomial.eval_zero, Polynomial.eval_ofNat]
  ring

lemma P1x_eval_one (a b : ℚ) : (Work.C17.P1x a b).eval (1 : ℚ) = -8 * (a - b) ^ 2 := by
  simp only [Work.C17.P1x, Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C, Polynomial.eval_one,
    Polynomial.eval_neg, Polynomial.eval_zero, Polynomial.eval_ofNat]
  ring

lemma P1x_eval_neg_one (a b : ℚ) : (Work.C17.P1x a b).eval (-1 : ℚ) = -8 * (a + b) ^ 2 := by
  simp only [Work.C17.P1x, Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C, Polynomial.eval_one,
    Polynomial.eval_neg, Polynomial.eval_zero, Polynomial.eval_ofNat]
  ring

lemma P2Cm_eval_eq (a b : ℚ) : P2Cm a b = (X - 1) * X * (X + 1) * Q4Cm a b := by
  simp only [P2Cm, Q4Cm, Work.C17.P2x, Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_X,
    Polynomial.map_one, Polynomial.map_add]

lemma P2Cm_deriv_eval_zero (a b : ℚ) : (P2Cm a b).derivative.eval (0 : ℂ) = -1 := by
  rw [show (0 : ℂ) = algebraMap ℚ ℂ (0 : ℚ) from by simp, P2Cm, eval_map_rat_deriv,
    P2x_deriv_eval_zero]
  push_cast
  norm_num

lemma P2Cm_deriv_eval_one (a b : ℚ) : (P2Cm a b).derivative.eval (1 : ℂ)
    = 8 * ((a : ℂ) - (b : ℂ)) ^ 2 := by
  rw [show (1 : ℂ) = algebraMap ℚ ℂ (1 : ℚ) from by simp, P2Cm, eval_map_rat_deriv,
    P2x_deriv_eval_one]
  push_cast
  norm_num

lemma P2Cm_deriv_eval_neg_one (a b : ℚ) : (P2Cm a b).derivative.eval (-1 : ℂ)
    = 8 * ((a : ℂ) + (b : ℂ)) ^ 2 := by
  rw [show (-1 : ℂ) = algebraMap ℚ ℂ (-1 : ℚ) from by simp, P2Cm, eval_map_rat_deriv,
    P2x_deriv_eval_neg_one]
  push_cast
  norm_num

lemma P1Cm_eval_zero (a b : ℚ) : (P1Cm a b).eval (0 : ℂ) = -1 := by
  rw [show (0 : ℂ) = algebraMap ℚ ℂ (0 : ℚ) from by simp, P1Cm, eval_map_rat, P1x_eval_zero]
  push_cast
  norm_num

lemma P1Cm_eval_one (a b : ℚ) : (P1Cm a b).eval (1 : ℂ) = -8 * ((a : ℂ) - (b : ℂ)) ^ 2 := by
  rw [show (1 : ℂ) = algebraMap ℚ ℂ (1 : ℚ) from by simp, P1Cm, eval_map_rat, P1x_eval_one]
  push_cast
  norm_num

lemma P1Cm_eval_neg_one (a b : ℚ) : (P1Cm a b).eval (-1 : ℂ)
    = -8 * ((a : ℂ) + (b : ℂ)) ^ 2 := by
  rw [show (-1 : ℂ) = algebraMap ℚ ℂ (-1 : ℚ) from by simp, P1Cm, eval_map_rat,
    P1x_eval_neg_one]
  push_cast
  norm_num

lemma P1x_eq_deriv (a b : ℚ) :
    Work.C17.P1x a b
      = (X - 1) * X * (X + 1) * (Work.C17.Q4x a b).derivative
        - (X ^ 2 + 1) * Work.C17.Q4x a b := by
  apply Polynomial.funext
  intro x
  simp only [Work.C17.P1x, Work.C17.Q4x, Polynomial.eval_sub, Polynomial.eval_add,
    Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C,
    Polynomial.eval_one, Polynomial.eval_neg, Polynomial.eval_zero, Polynomial.derivative_mul,
    Polynomial.derivative_X, Polynomial.derivative_sub, Polynomial.derivative_C,
    Polynomial.derivative_one, Polynomial.derivative_add, Polynomial.derivative_pow]
  ring

lemma P1Cm_eq (a b : ℚ) :
    P1Cm a b = (X - 1) * X * (X + 1) * (Q4Cm a b).derivative - (X ^ 2 + 1) * Q4Cm a b := by
  have h := congrArg (Polynomial.map (algebraMap ℚ ℂ)) (P1x_eq_deriv a b)
  simpa only [P1Cm, Q4Cm, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_add,
    Polynomial.map_pow, Polynomial.map_X, Polynomial.map_one, Polynomial.map_C,
    Polynomial.map_ofNat, ← Polynomial.derivative_map] using h

lemma Q4Cm_root_ne_zero (a b : ℚ) {r : ℂ} (h : (Q4Cm a b).eval r = 0) : r ≠ 0 := by
  intro h0
  rw [h0, Q4Cm_eval_zero] at h
  exact one_ne_zero h

lemma Q4Cm_root_ne_one (a b : ℚ) (hab : a ≠ b) {r : ℂ} (h : (Q4Cm a b).eval r = 0) : r ≠ 1 := by
  intro h0
  rw [h0, Q4Cm_eval_one] at h
  have h' : ((a : ℂ) - (b : ℂ)) = 0 := by
    rcases mul_eq_zero.mp h with h1 | h1
    · exact absurd h1 (by norm_num)
    · exact sq_eq_zero_iff.mp h1
  exact hab (by exact_mod_cast (sub_eq_zero.mp h'))

lemma Q4Cm_root_ne_neg_one (a b : ℚ) (ha : 3 ≤ a) (hb : 3 ≤ b) {r : ℂ}
    (h : (Q4Cm a b).eval r = 0) : r ≠ -1 := by
  intro h0
  rw [h0, Q4Cm_eval_neg_one] at h
  have h' : ((a : ℂ) + (b : ℂ)) = 0 := by
    rcases mul_eq_zero.mp h with h1 | h1
    · exact absurd h1 (by norm_num)
    · exact sq_eq_zero_iff.mp h1
  have h2 : a + b = 0 := by exact_mod_cast h'
  linarith

lemma P2Cm_deriv_eval_ne_zero_of_Q4_root (a b : ℚ) (ha : 3 ≤ a) (hb : 3 ≤ b) (hab : a ≠ b)
    {r : ℂ} (h : (Q4Cm a b).eval r = 0) : (P2Cm a b).derivative.eval r ≠ 0 := by
  intro h0
  have hQ4ne : Q4Cm a b ≠ 0 := by
    intro hz
    have h1 : (Q4Cm a b).eval (0 : ℂ) = 0 := by rw [hz, Polynomial.eval_zero]
    rw [Q4Cm_eval_zero] at h1
    exact one_ne_zero h1
  have hX1 : (X + 1 : Polynomial ℂ) ≠ 0 := by
    intro hz
    have h1 : (X + 1 : Polynomial ℂ).eval (0 : ℂ) = 0 := by rw [hz, Polynomial.eval_zero]
    rw [show (X + 1 : Polynomial ℂ).eval (0 : ℂ) = 1 from by simp] at h1
    exact one_ne_zero h1
  have hP2ne : P2Cm a b ≠ 0 := by
    rw [P2Cm_eval_eq]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (Polynomial.X_sub_C_ne_zero 1)
      Polynomial.X_ne_zero) hX1) hQ4ne
  have hsq : (X - Polynomial.C r) ^ 2 ∣ P2Cm a b := by
    rw [Commons.Algebra.Polynomial.dvd_sq_X_sub_C_iff]
    constructor
    · rw [P2Cm_eval_eq]
      simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_X,
        Polynomial.eval_one, h, mul_zero]
    · exact h0
  have hroot : Polynomial.rootMultiplicity r (P2Cm a b) ≤ 1 := by
    simpa only [P2Cm] using Work.C17.p2x_roots_simple a b ha hb hab r
  have h2 : 2 ≤ Polynomial.rootMultiplicity r (P2Cm a b) := by
    rw [Polynomial.le_rootMultiplicity_iff hP2ne]
    exact hsq
  omega


/-! ## 5. Applications: the local pole bounds -/

lemma P1Cm_eval_eq_P2Cm_deriv_eval (a b : ℚ) {r : ℂ} (hr : (Q4Cm a b).eval r = 0) :
    (P1Cm a b).eval r = (P2Cm a b).derivative.eval r := by
  have hder : (P2Cm a b).derivative.eval r
      = (r - 1) * r * (r + 1) * (Q4Cm a b).derivative.eval r := by
    have h0 := congrArg Polynomial.derivative (P2Cm_eval_eq a b)
    rw [Polynomial.derivative_mul] at h0
    rw [h0]
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_pow,
      Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_C, Polynomial.derivative_mul,
      Polynomial.derivative_sub, Polynomial.derivative_add, Polynomial.derivative_pow,
      Polynomial.derivative_X, Polynomial.derivative_C, Polynomial.derivative_one, hr, mul_zero,
      add_zero, sub_zero, zero_mul]
    try ring
  have h1 : (P1Cm a b).eval r = (r - 1) * r * (r + 1) * (Q4Cm a b).derivative.eval r := by
    rw [P1Cm_eq a b]
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_pow,
      Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_C, hr, mul_zero, add_zero, sub_zero,
      zero_mul]
    try ring
  rw [h1, hder]

lemma AadjL_eval_zero (a b : ℚ) : (AadjL a b).eval (0 : ℂ) = -1 := by
  rw [AadjL, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_ofNat,
    P2Cm_deriv_eval_zero, P1Cm_eval_zero]
  norm_num

lemma AadjL_eval_one (a b : ℚ) : (AadjL a b).eval (1 : ℂ) = 24 * ((a : ℂ) - (b : ℂ)) ^ 2 := by
  rw [AadjL, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_ofNat,
    P2Cm_deriv_eval_one, P1Cm_eval_one]
  ring

lemma AadjL_eval_neg_one (a b : ℚ) :
    (AadjL a b).eval (-1 : ℂ) = 24 * ((a : ℂ) + (b : ℂ)) ^ 2 := by
  rw [AadjL, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_ofNat,
    P2Cm_deriv_eval_neg_one, P1Cm_eval_neg_one]
  ring

lemma P2s0_eval (a b : ℚ) : ((X - 1) * (X + 1) * Q4Cm a b).eval (0 : ℂ) = -1 := by
  rw [Polynomial.eval_mul, Polynomial.eval_mul, Q4Cm_eval_zero]
  simp only [Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one,
    Polynomial.eval_zero]
  norm_num

lemma P2s1_eval (a b : ℚ) : (X * (X + 1) * Q4Cm a b).eval (1 : ℂ)
    = 8 * ((a : ℂ) - (b : ℂ)) ^ 2 := by
  rw [Polynomial.eval_mul, Polynomial.eval_mul, Q4Cm_eval_one]
  simp only [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one]
  ring

lemma P2sm1_eval (a b : ℚ) : ((X - 1) * X * Q4Cm a b).eval (-1 : ℂ)
    = 8 * ((a : ℂ) + (b : ℂ)) ^ 2 := by
  rw [Polynomial.eval_mul, Polynomial.eval_mul, Q4Cm_eval_neg_one]
  simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_neg]
  ring

lemma DadjL_eq : DadjL = X ^ 6 * (X - Polynomial.C (1 : ℂ)) ^ 2
    * (X - Polynomial.C (-1)) ^ 2 := by
  apply Polynomial.funext
  intro x
  simp only [DadjL, Work.C17.Dadj, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_sub,
    Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C, Polynomial.eval_one,
    Polynomial.eval_neg, Polynomial.eval_map, Polynomial.eval₂_add, Polynomial.eval₂_mul,
    Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_C,
    Polynomial.eval₂_one, Polynomial.eval₂_ofNat]
  push_cast
  norm_num
  ring

lemma DadjL_rootMultiplicity_zero : Polynomial.rootMultiplicity (0 : ℂ) DadjL = 6 := by
  have hne1 : ((X - Polynomial.C 1) ^ 2 * (X - Polynomial.C (-1)) ^ 2 : Polynomial ℂ) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (Polynomial.X_sub_C_ne_zero 1))
      (pow_ne_zero _ (Polynomial.X_sub_C_ne_zero (-1)))
  have hroot : Polynomial.rootMultiplicity (0 : ℂ)
      ((X - Polynomial.C 1) ^ 2 * (X - Polynomial.C (-1)) ^ 2) = 0 := by
    rw [Polynomial.rootMultiplicity_eq_zero]
    intro hh
    have hval : ((X - Polynomial.C 1) ^ 2 * (X - Polynomial.C (-1)) ^ 2
        : Polynomial ℂ).eval (0 : ℂ) ≠ 0 := by
      simp only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_X,
        Polynomial.eval_C, Polynomial.eval_zero]
      norm_num
    exact hval hh
  have hfac : DadjL = (X - Polynomial.C (0 : ℂ)) ^ 6
      * ((X - Polynomial.C 1) ^ 2 * (X - Polynomial.C (-1)) ^ 2) := by
    rw [DadjL_eq, Polynomial.C_0, sub_zero]
    ring
  have hne' : (X - Polynomial.C (0 : ℂ)) ^ 6
      * ((X - Polynomial.C 1) ^ 2 * (X - Polynomial.C (-1)) ^ 2) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (Polynomial.X_sub_C_ne_zero 0)) hne1
  rw [hfac, Polynomial.rootMultiplicity_mul hne', Polynomial.rootMultiplicity_X_sub_C_pow,
    hroot, add_zero]

lemma DadjL_rootMultiplicity_one : Polynomial.rootMultiplicity (1 : ℂ) DadjL = 2 := by
  have hne1 : ((X - Polynomial.C 0) ^ 6 * (X - Polynomial.C (-1)) ^ 2 : Polynomial ℂ) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (Polynomial.X_sub_C_ne_zero 0))
      (pow_ne_zero _ (Polynomial.X_sub_C_ne_zero (-1)))
  have hroot : Polynomial.rootMultiplicity (1 : ℂ)
      ((X - Polynomial.C 0) ^ 6 * (X - Polynomial.C (-1)) ^ 2) = 0 := by
    rw [Polynomial.rootMultiplicity_eq_zero]
    intro hh
    have hval : ((X - Polynomial.C 0) ^ 6 * (X - Polynomial.C (-1)) ^ 2
        : Polynomial ℂ).eval (1 : ℂ) ≠ 0 := by
      simp only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_X,
        Polynomial.eval_C, Polynomial.eval_one, Polynomial.eval_zero, Polynomial.eval_neg]
      norm_num
    exact hval hh
  have hfac : DadjL = (X - Polynomial.C (1 : ℂ)) ^ 2
      * ((X - Polynomial.C 0) ^ 6 * (X - Polynomial.C (-1)) ^ 2) := by
    rw [DadjL_eq]
    simp only [Polynomial.C_0, Polynomial.C_neg, Polynomial.C_eq_natCast]
    ring
  have hne' : (X - Polynomial.C (1 : ℂ)) ^ 2
      * ((X - Polynomial.C 0) ^ 6 * (X - Polynomial.C (-1)) ^ 2) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (Polynomial.X_sub_C_ne_zero 1)) hne1
  rw [hfac, Polynomial.rootMultiplicity_mul hne', Polynomial.rootMultiplicity_X_sub_C_pow, hroot,
    add_zero]

lemma DadjL_rootMultiplicity_neg_one : Polynomial.rootMultiplicity (-1 : ℂ) DadjL = 2 := by
  have hne1 : ((X - Polynomial.C 0) ^ 6 * (X - Polynomial.C 1) ^ 2 : Polynomial ℂ) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (Polynomial.X_sub_C_ne_zero 0))
      (pow_ne_zero _ (Polynomial.X_sub_C_ne_zero 1))
  have hroot : Polynomial.rootMultiplicity (-1 : ℂ)
      ((X - Polynomial.C 0) ^ 6 * (X - Polynomial.C 1) ^ 2) = 0 := by
    rw [Polynomial.rootMultiplicity_eq_zero]
    intro hh
    have hval : ((X - Polynomial.C 0) ^ 6 * (X - Polynomial.C 1) ^ 2
        : Polynomial ℂ).eval (-1 : ℂ) ≠ 0 := by
      simp only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_X,
        Polynomial.eval_C, Polynomial.eval_one, Polynomial.eval_zero, Polynomial.eval_neg]
      norm_num
    exact hval hh
  have hfac : DadjL = (X - Polynomial.C (-1 : ℂ)) ^ 2
      * ((X - Polynomial.C 0) ^ 6 * (X - Polynomial.C 1) ^ 2) := by
    rw [DadjL_eq]
    simp only [Polynomial.C_0, Polynomial.C_1, Polynomial.C_eq_natCast]
    ring
  have hne' : (X - Polynomial.C (-1 : ℂ)) ^ 2
      * ((X - Polynomial.C 0) ^ 6 * (X - Polynomial.C 1) ^ 2) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (Polynomial.X_sub_C_ne_zero (-1))) hne1
  rw [hfac, Polynomial.rootMultiplicity_mul hne', Polynomial.rootMultiplicity_X_sub_C_pow, hroot,
    add_zero]

lemma DadjL_rootMultiplicity_eq_zero {α : ℂ} (h0 : α ≠ 0) (h1 : α ≠ 1) (hm1 : α ≠ -1) :
    Polynomial.rootMultiplicity α DadjL = 0 := by
  have hA : ((X ^ 6 : Polynomial ℂ)).eval α = α ^ 6 := by
    simp only [Polynomial.eval_pow, Polynomial.eval_X]
  have hB : (((X - Polynomial.C (1 : ℂ)) ^ 2)).eval α = (α - 1) ^ 2 := by
    simp only [Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
  have hC : (((X - Polynomial.C (-1 : ℂ)) ^ 2)).eval α = (α + 1) ^ 2 := by
    simp only [Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
    ring
  rw [Polynomial.rootMultiplicity_eq_zero]
  intro hh
  have hval : (X ^ 6 * (X - Polynomial.C (1 : ℂ)) ^ 2 * (X - Polynomial.C (-1)) ^ 2
      : Polynomial ℂ).eval α ≠ 0 := by
    rw [Polynomial.eval_mul, Polynomial.eval_mul, hA, hB, hC]
    refine mul_ne_zero (mul_ne_zero (pow_ne_zero _ h0) ?_) ?_
    · intro hh'
      exact h1 (sub_eq_zero.mp (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hh'))
    · intro hh'
      have h2 : α = -1 := by
        have h := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hh'
        linear_combination h
      exact hm1 h2
  rw [DadjL_eq] at hh
  exact hval hh


/-! ## 6. The local pole bounds -/

lemma eight_sq_ne_zero {a b : ℚ} (hab : a ≠ b) : 8 * ((a : ℂ) - (b : ℂ)) ^ 2 ≠ 0 := by
  intro hh
  rcases mul_eq_zero.mp hh with h | h
  · exact absurd h (by norm_num)
  · have h2 : (a : ℂ) - (b : ℂ) = 0 := sq_eq_zero_iff.mp h
    exact hab (by exact_mod_cast (sub_eq_zero.mp h2))

lemma add_ne_zero {a b : ℚ} (ha : 3 ≤ a) (hb : 3 ≤ b) : (a : ℂ) + (b : ℂ) ≠ 0 := by
  intro hh
  have h2 : a + b = 0 := by exact_mod_cast hh
  linarith

lemma ordAt_bounds {a b : ℚ} (ha : 3 ≤ a) (hb : 3 ≤ b) (hab : a ≠ b)
    {β : RatFunc ℂ} (hβ : β ≠ 0) {c : Fin 6 → ℂ}
    (h : Submission.CDT.dRat (Submission.CDT.dRat (Work.C17.Pac a b * β))
        - Submission.CDT.dRat (Work.C17.Pbc a b * β) + Work.C17.Pcc a b * β = RhsC c) :
    (-6 : ℤ) ≤ ordAt 0 β ∧ (-2 : ℤ) ≤ ordAt 1 β ∧ (-2 : ℤ) ≤ ordAt (-1) β ∧
    (∀ α : ℂ, α ≠ 0 → α ≠ 1 → α ≠ -1 → (0 : ℤ) ≤ ordAt α β) := by
  have hMR : algebraMap (Polynomial ℂ) (RatFunc ℂ) (P2Cm a b)
        * Submission.CDT.dRat (Submission.CDT.dRat β)
      + algebraMap (Polynomial ℂ) (RatFunc ℂ) (AadjL a b) * Submission.CDT.dRat β
      + algebraMap (Polynomial ℂ) (RatFunc ℂ) (CadjL a b) * β = RhsC c := by
    rw [← op_eq a b β]; exact h
  have hrhs0 : ∀ α : ℂ, α ≠ 0 → α ≠ 1 → ((0 : ℤ) : WithTop ℤ) ≤ ordAtT α (RhsC c) := by
    intro α h0 h1
    have h' := rhs_ord c α
    rw [if_neg h1, if_neg h0] at h'
    exact h'
  refine ⟨?_, ?_, ?_, ?_⟩
  · by_cases hlt : ordAt (0 : ℂ) β < 0
    · have hP2s : ((X - 1) * (X + 1) * Q4Cm a b).eval (0 : ℂ) ≠ 0 := by
        rw [P2s0_eval]; norm_num
      have hfac : P2Cm a b = (X - Polynomial.C (0 : ℂ)) * ((X - 1) * (X + 1) * Q4Cm a b) := by
        rw [P2Cm_eval_eq, Polynomial.C_0, sub_zero]
        ring_nf
      have hN0 : (ordAt (0 : ℂ) β : ℤ) ≠ 0 := by omega
      have hcoef : (((ordAt (0 : ℂ) β : ℤ) : ℂ) * ((((ordAt (0 : ℂ) β : ℤ) : ℂ) - 1)
          * ((X - 1) * (X + 1) * Q4Cm a b).eval (0 : ℂ) + (AadjL a b).eval (0 : ℂ))) ≠ 0 := by
        rw [P2s0_eval, AadjL_eval_zero]
        have heq : (((ordAt (0 : ℂ) β : ℤ) : ℂ) * ((((ordAt (0 : ℂ) β : ℤ) : ℂ) - 1) * (-1) + -1))
            = -(((ordAt (0 : ℂ) β : ℤ) : ℂ) ^ 2) := by ring
        rw [heq]
        exact neg_ne_zero.mpr (pow_ne_zero 2 (fun hh => hN0 (Int.cast_eq_zero.mp hh)))
      have hord := order_eq_singular (a := a) (b := b) (α := (0 : ℂ)) hβ hlt hfac hP2s hcoef
      have hhr : ((-7 : ℤ) : WithTop ℤ) ≤ ordAtT (0 : ℂ) (RhsC c) := by
        simpa using rhs_ord c 0
      have hge : ((-7 : ℤ) : WithTop ℤ) ≤ (((ordAt (0 : ℂ) β : ℤ) - 1 : ℤ) : WithTop ℤ) := by
        rw [← hord, hMR]; exact hhr
      have h7 : (-7 : ℤ) ≤ (ordAt (0 : ℂ) β : ℤ) - 1 := WithTop.coe_le_coe.mp hge
      omega
    · omega
  · by_cases hlt : ordAt (1 : ℂ) β < -2
    · have hN0 : (ordAt (1 : ℂ) β : ℤ) ≠ 0 := by omega
      have hN2 : (ordAt (1 : ℂ) β : ℤ) ≠ -2 := by omega
      have hP2s : (X * (X + 1) * Q4Cm a b).eval (1 : ℂ) ≠ 0 := by
        rw [P2s1_eval]; exact eight_sq_ne_zero hab
      have hfac : P2Cm a b = (X - Polynomial.C (1 : ℂ)) * (X * (X + 1) * Q4Cm a b) := by
        rw [P2Cm_eval_eq]
        apply Polynomial.funext
        intro x
        simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_X,
          Polynomial.eval_C, Polynomial.eval_one]
        ring
      have hcoef : (((ordAt (1 : ℂ) β : ℤ) : ℂ) * ((((ordAt (1 : ℂ) β : ℤ) : ℂ) - 1)
          * (X * (X + 1) * Q4Cm a b).eval (1 : ℂ) + (AadjL a b).eval (1 : ℂ))) ≠ 0 := by
        rw [P2s1_eval, AadjL_eval_one]
        have heq : (((ordAt (1 : ℂ) β : ℤ) : ℂ) * ((((ordAt (1 : ℂ) β : ℤ) : ℂ) - 1)
              * (8 * ((a : ℂ) - (b : ℂ)) ^ 2) + 24 * ((a : ℂ) - (b : ℂ)) ^ 2))
            = ((ordAt (1 : ℂ) β : ℤ) : ℂ) * (8 * ((a : ℂ) - (b : ℂ)) ^ 2)
              * (((ordAt (1 : ℂ) β : ℤ) : ℂ) + 2) := by ring
        rw [heq]
        refine mul_ne_zero (mul_ne_zero (fun hh => hN0 (Int.cast_eq_zero.mp hh))
          (eight_sq_ne_zero hab)) ?_
        intro hh
        have h2 : ((ordAt (1 : ℂ) β : ℤ) : ℂ) = ((-2 : ℤ) : ℂ) := by linear_combination hh
        exact hN2 (Int.cast_inj.mp h2)
      have hord := order_eq_singular (a := a) (b := b) (α := (1 : ℂ)) hβ (by omega) hfac hP2s hcoef
      have hhr : ((-3 : ℤ) : WithTop ℤ) ≤ ordAtT (1 : ℂ) (RhsC c) := by
        simpa using rhs_ord c 1
      have hge : ((-3 : ℤ) : WithTop ℤ) ≤ (((ordAt (1 : ℂ) β : ℤ) - 1 : ℤ) : WithTop ℤ) := by
        rw [← hord, hMR]; exact hhr
      have h3 : (-3 : ℤ) ≤ (ordAt (1 : ℂ) β : ℤ) - 1 := WithTop.coe_le_coe.mp hge
      omega
    · omega
  · by_cases hlt : ordAt (-1 : ℂ) β < -2
    · have hN0 : (ordAt (-1 : ℂ) β : ℤ) ≠ 0 := by omega
      have hN2 : (ordAt (-1 : ℂ) β : ℤ) ≠ -2 := by omega
      have hP2s : ((X - 1) * X * Q4Cm a b).eval (-1 : ℂ) ≠ 0 := by
        rw [P2sm1_eval]
        intro hh
        rcases mul_eq_zero.mp hh with h' | h'
        · exact absurd h' (by norm_num)
        · exact add_ne_zero ha hb (sq_eq_zero_iff.mp h')
      have hfac : P2Cm a b = (X - Polynomial.C (-1 : ℂ)) * ((X - 1) * X * Q4Cm a b) := by
        rw [P2Cm_eval_eq]
        apply Polynomial.funext
        intro x
        simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_X,
          Polynomial.eval_C, Polynomial.eval_one]
        ring
      have hcoef : (((ordAt (-1 : ℂ) β : ℤ) : ℂ) * ((((ordAt (-1 : ℂ) β : ℤ) : ℂ) - 1)
          * ((X - 1) * X * Q4Cm a b).eval (-1 : ℂ) + (AadjL a b).eval (-1 : ℂ))) ≠ 0 := by
        rw [P2sm1_eval, AadjL_eval_neg_one]
        have heq : (((ordAt (-1 : ℂ) β : ℤ) : ℂ) * ((((ordAt (-1 : ℂ) β : ℤ) : ℂ) - 1)
              * (8 * ((a : ℂ) + (b : ℂ)) ^ 2) + 24 * ((a : ℂ) + (b : ℂ)) ^ 2))
            = ((ordAt (-1 : ℂ) β : ℤ) : ℂ) * (8 * ((a : ℂ) + (b : ℂ)) ^ 2)
              * (((ordAt (-1 : ℂ) β : ℤ) : ℂ) + 2) := by ring
        rw [heq]
        refine mul_ne_zero (mul_ne_zero (fun hh => hN0 (Int.cast_eq_zero.mp hh)) ?_) ?_
        · intro hh
          rcases mul_eq_zero.mp hh with h' | h'
          · exact absurd h' (by norm_num)
          · exact add_ne_zero ha hb (sq_eq_zero_iff.mp h')
        · intro hh
          have h2 : ((ordAt (-1 : ℂ) β : ℤ) : ℂ) = ((-2 : ℤ) : ℂ) := by linear_combination hh
          exact hN2 (Int.cast_inj.mp h2)
      have hord := order_eq_singular (a := a) (b := b) (α := (-1 : ℂ)) hβ (by omega) hfac hP2s hcoef
      have hhr : ((0 : ℤ) : WithTop ℤ) ≤ ordAtT (-1 : ℂ) (RhsC c) := by
        have h' := rhs_ord c (-1 : ℂ)
        rw [if_neg (by norm_num : ¬((-1 : ℂ) = 1)),
          if_neg (by norm_num : ¬((-1 : ℂ) = 0))] at h'
        exact h'
      have hge : ((0 : ℤ) : WithTop ℤ) ≤ (((ordAt (-1 : ℂ) β : ℤ) - 1 : ℤ) : WithTop ℤ) := by
        rw [← hord, hMR]; exact hhr
      have h3 : (0 : ℤ) ≤ (ordAt (-1 : ℂ) β : ℤ) - 1 := WithTop.coe_le_coe.mp hge
      omega
    · omega
  · intro α h0 h1 hm1
    by_cases hlt : ordAt α β < 0
    swap
    · omega
    have hrhsα : ((0 : ℤ) : WithTop ℤ) ≤ ordAtT α (RhsC c) := hrhs0 α h0 h1
    by_cases hQ4 : (Q4Cm a b).eval α = 0
    · have hP2deriv : (P2Cm a b).derivative.eval α ≠ 0 :=
        P2Cm_deriv_eval_ne_zero_of_Q4_root a b ha hb hab hQ4
      have hP1eq : (P1Cm a b).eval α = (P2Cm a b).derivative.eval α :=
        P1Cm_eval_eq_P2Cm_deriv_eval a b hQ4
      have hQ4ne : Q4Cm a b ≠ 0 := by
        intro hz
        have h1' : (Q4Cm a b).eval (0 : ℂ) = 0 := by rw [hz, Polynomial.eval_zero]
        rw [Q4Cm_eval_zero] at h1'
        exact one_ne_zero h1'
      have hX1 : (X + 1 : Polynomial ℂ) ≠ 0 := by
        intro hz
        have h1' : (X + 1 : Polynomial ℂ).eval (0 : ℂ) = 0 := by rw [hz, Polynomial.eval_zero]
        rw [show (X + 1 : Polynomial ℂ).eval (0 : ℂ) = 1 from by simp] at h1'
        exact one_ne_zero h1'
      have hP2ne : P2Cm a b ≠ 0 := by
        rw [P2Cm_eval_eq]
        exact mul_ne_zero (mul_ne_zero (mul_ne_zero (Polynomial.X_sub_C_ne_zero 1)
          Polynomial.X_ne_zero) hX1) hQ4ne
      have hdvd : (X - Polynomial.C α) ∣ P2Cm a b := by
        rw [Polynomial.dvd_iff_isRoot, Polynomial.IsRoot.def, P2Cm_eval_eq]
        simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_X,
          Polynomial.eval_one, hQ4, mul_zero]
      have hrm : Polynomial.rootMultiplicity α (P2Cm a b) = 1 := by
        have h1' : 1 ≤ Polynomial.rootMultiplicity α (P2Cm a b) := by
          rw [Polynomial.le_rootMultiplicity_iff hP2ne, pow_one]
          exact hdvd
        have h2' : Polynomial.rootMultiplicity α (P2Cm a b) ≤ 1 := by
          simpa only [P2Cm] using Work.C17.p2x_roots_simple a b ha hb hab α
        omega
      have hfac : P2Cm a b = (X - Polynomial.C α) * (P2Cm a b /ₘ (X - Polynomial.C α)) := by
        have hh := Polynomial.pow_mul_divByMonic_rootMultiplicity_eq (P2Cm a b) α
        rw [hrm, pow_one] at hh
        exact hh.symm
      have hP2sval : (P2Cm a b /ₘ (X - Polynomial.C α)).eval α
          = (P2Cm a b).derivative.eval α := by
        have hh := congrArg (fun q : Polynomial ℂ => q.eval α) (congrArg Polynomial.derivative hfac)
        rw [Polynomial.derivative_mul, Polynomial.eval_add] at hh
        simp only [Polynomial.derivative_X_sub_C, Polynomial.eval_mul, Polynomial.eval_sub,
          Polynomial.eval_X, Polynomial.eval_C, Polynomial.eval_one, sub_self, mul_zero, zero_add,
          one_mul] at hh
        rw [zero_mul, add_zero] at hh
        exact hh.symm
      have hN0 : (ordAt α β : ℤ) ≠ 0 := by omega
      have hcoef : (((ordAt α β : ℤ) : ℂ) * ((((ordAt α β : ℤ) : ℂ) - 1)
          * (P2Cm a b /ₘ (X - Polynomial.C α)).eval α + (AadjL a b).eval α)) ≠ 0 := by
        rw [hP2sval, AadjL, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_ofNat, hP1eq]
        have heq : (((ordAt α β : ℤ) : ℂ) * ((((ordAt α β : ℤ) : ℂ) - 1)
              * (P2Cm a b).derivative.eval α + (2 * (P2Cm a b).derivative.eval α
                - (P2Cm a b).derivative.eval α)))
            = ((ordAt α β : ℤ) : ℂ) ^ 2 * (P2Cm a b).derivative.eval α := by ring
        rw [heq]
        exact mul_ne_zero (pow_ne_zero 2 (fun hh => hN0 (Int.cast_eq_zero.mp hh))) hP2deriv
      have hord := order_eq_singular (a := a) (b := b) (α := α) hβ hlt hfac
        (by rw [hP2sval]; exact hP2deriv) hcoef
      have hge : ((0 : ℤ) : WithTop ℤ) ≤ (((ordAt α β : ℤ) - 1 : ℤ) : WithTop ℤ) := by
        rw [← hord, hMR]; exact hrhsα
      have h0' : (0 : ℤ) ≤ (ordAt α β : ℤ) - 1 := WithTop.coe_le_coe.mp hge
      omega
    · have hX1' : (X + 1 : Polynomial ℂ).eval α ≠ 0 := by
        intro hX
        simp only [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one] at hX
        have h3 : α = -1 := by linear_combination hX
        exact hm1 h3
      have hP2 : (P2Cm a b).eval α ≠ 0 := by
        rw [P2Cm_eval_eq]
        simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_one]
        exact mul_ne_zero (mul_ne_zero (mul_ne_zero (sub_ne_zero.mpr h1) h0) hX1') hQ4
      have hord := order_eq_generic (a := a) (b := b) (α := α) hβ hlt hP2
      have hge : ((0 : ℤ) : WithTop ℤ) ≤ (((ordAt α β : ℤ) - 2 : ℤ) : WithTop ℤ) := by
        rw [← hord, hMR]; exact hrhsα
      have h0' : (0 : ℤ) ≤ (ordAt α β : ℤ) - 2 := WithTop.coe_le_coe.mp hge
      omega

/-! ## 7. The divisor bound and the degree chase -/

lemma beta_Dadj_is_poly {a b : ℚ} (ha : 3 ≤ a) (hb : 3 ≤ b) (hab : a ≠ b)
    {β : RatFunc ℂ} (hβ : β ≠ 0) {c : Fin 6 → ℂ}
    (h : Submission.CDT.dRat (Submission.CDT.dRat (Work.C17.Pac a b * β))
        - Submission.CDT.dRat (Work.C17.Pbc a b * β) + Work.C17.Pcc a b * β = RhsC c) :
    ∃ W : Polynomial ℂ, β * Work.C17.DadjC = algebraMap (Polynomial ℂ) (RatFunc ℂ) W := by
  have hbnds := ordAt_bounds ha hb hab hβ h
  have hDadj : Work.C17.DadjC = algebraMap (Polynomial ℂ) (RatFunc ℂ) DadjL := rfl
  rw [hDadj]
  refine Commons.FieldTheory.RatFunc.exists_eq_algebraMap_of_forall_nonneg_ordAt ?_
  intro α
  rw [ordAt_mul α hβ (RatFunc.algebraMap_ne_zero DadjL_ne_zero), ordAt_algebraMap]
  by_cases h0 : α = 0
  · subst h0
    rw [DadjL_rootMultiplicity_zero]
    have := hbnds.1
    omega
  by_cases h1 : α = 1
  · subst h1
    rw [DadjL_rootMultiplicity_one]
    have := hbnds.2.1
    omega
  by_cases hm1 : α = -1
  · subst hm1
    rw [DadjL_rootMultiplicity_neg_one]
    have := hbnds.2.2.1
    omega
  · rw [DadjL_rootMultiplicity_eq_zero h0 h1 hm1]
    have := hbnds.2.2.2 α h0 h1 hm1
    omega

lemma DadjL_natDegree : DadjL.natDegree = 10 := by
  rw [DadjL_eq]
  rw [Polynomial.natDegree_mul (mul_ne_zero (pow_ne_zero _ Polynomial.X_ne_zero)
      (pow_ne_zero _ (Polynomial.X_sub_C_ne_zero 1)))
    (pow_ne_zero _ (Polynomial.X_sub_C_ne_zero (-1)))]
  rw [Polynomial.natDegree_mul (pow_ne_zero _ Polynomial.X_ne_zero)
    (pow_ne_zero _ (Polynomial.X_sub_C_ne_zero 1))]
  rw [Polynomial.natDegree_pow, Polynomial.natDegree_pow, Polynomial.natDegree_pow,
    Polynomial.natDegree_X, Polynomial.natDegree_X_sub_C, Polynomial.natDegree_X_sub_C]

lemma eq_sum_fin_seven (W : Polynomial ℂ) (h : W.natDegree ≤ 6) :
    W = ∑ k : Fin 7, Polynomial.C (W.coeff (k : ℕ)) * Polynomial.X ^ (k : ℕ) := by
  conv_lhs => rw [Polynomial.as_sum_range (p := W)]
  have h7 : W.natDegree + 1 ≤ 7 := by omega
  rw [Finset.sum_subset (Finset.range_subset_range.mpr h7)]
  · rw [Fin.sum_univ_eq_sum_range (fun k => Polynomial.C (W.coeff k) * Polynomial.X ^ k) 7]
    refine Finset.sum_congr rfl (fun k hk => ?_)
    exact (Polynomial.C_mul_X_pow_eq_monomial).symm
  · intro x hx7 hx
    have hx' : W.natDegree < x := by
      simp only [Finset.mem_range] at hx7 hx
      omega
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt hx', Polynomial.monomial_zero_right]

lemma degree_bound {a b : ℚ} {β : RatFunc ℂ} {c : Fin 6 → ℂ} {W : Polynomial ℂ} (hW : W ≠ 0)
    (hβW : β * Work.C17.DadjC = algebraMap (Polynomial ℂ) (RatFunc ℂ) W)
    (h : Submission.CDT.dRat (Submission.CDT.dRat (Work.C17.Pac a b * β))
        - Submission.CDT.dRat (Work.C17.Pbc a b * β) + Work.C17.Pcc a b * β = RhsC c) :
    W.natDegree ≤ 6 := by
  have hMR : algebraMap (Polynomial ℂ) (RatFunc ℂ) (P2Cm a b)
        * Submission.CDT.dRat (Submission.CDT.dRat β)
      + algebraMap (Polynomial ℂ) (RatFunc ℂ) (AadjL a b) * Submission.CDT.dRat β
      + algebraMap (Polynomial ℂ) (RatFunc ℂ) (CadjL a b) * β = RhsC c := by
    rw [← op_eq a b β]; exact h
  have hDadj : Work.C17.DadjC = algebraMap (Polynomial ℂ) (RatFunc ℂ) DadjL := rfl
  have hDne : (algebraMap (Polynomial ℂ) (RatFunc ℂ) DadjL : RatFunc ℂ) ≠ 0 :=
    RatFunc.algebraMap_ne_zero DadjL_ne_zero
  have hβeq : β = algebraMap (Polynomial ℂ) (RatFunc ℂ) W
      / algebraMap (Polynomial ℂ) (RatFunc ℂ) DadjL := by
    rw [eq_div_iff hDne, ← hβW, hDadj]
  have h2 : algebraMap (Polynomial ℂ) (RatFunc ℂ) (PhiNum a b W)
      = (algebraMap (Polynomial ℂ) (RatFunc ℂ) DadjL) ^ 3 * RhsC c := by
    rw [phi_identity (a := a) (b := b) W]
    congr 1
    rw [← hβeq]
    exact hMR
  obtain ⟨hpsideg, hpsi⟩ := rhs_structure c
  have hden : (algebraMap (Polynomial ℂ) (RatFunc ℂ)
      (Polynomial.X ^ 7 * (Polynomial.X - 1) ^ 3) : RatFunc ℂ) ≠ 0 :=
    RatFunc.algebraMap_ne_zero (mul_ne_zero (pow_ne_zero _ Polynomial.X_ne_zero)
      (pow_ne_zero _ (Polynomial.X_sub_C_ne_zero 1)))
  have h3 : algebraMap (Polynomial ℂ) (RatFunc ℂ) (PhiNum a b W * (X ^ 7 * (X - 1) ^ 3))
      = algebraMap (Polynomial ℂ) (RatFunc ℂ) (DadjL ^ 3 * PsiNum c) := by
    have e1 : algebraMap (Polynomial ℂ) (RatFunc ℂ) (PhiNum a b W * (X ^ 7 * (X - 1) ^ 3))
        = algebraMap (Polynomial ℂ) (RatFunc ℂ) (PhiNum a b W)
          * algebraMap (Polynomial ℂ) (RatFunc ℂ) (X ^ 7 * (X - 1) ^ 3) := by rw [map_mul]
    have e2 : algebraMap (Polynomial ℂ) (RatFunc ℂ) (DadjL ^ 3 * PsiNum c)
        = (algebraMap (Polynomial ℂ) (RatFunc ℂ) DadjL) ^ 3
          * algebraMap (Polynomial ℂ) (RatFunc ℂ) (PsiNum c) := by rw [map_mul, map_pow]
    rw [e1, e2, h2, hpsi, mul_assoc, div_mul_cancel₀ _ hden]
  have h4 : PhiNum a b W * (X ^ 7 * (X - 1) ^ 3) = DadjL ^ 3 * PsiNum c :=
    RatFunc.algebraMap_injective ℂ h3
  by_cases hd5 : W.natDegree = 5
  · omega
  have hnat : (PhiNum a b W).natDegree = W.natDegree + 25 := by
    refine Polynomial.natDegree_eq_of_le_of_coeff_ne_zero (phi_degree a b W hW).1 ?_
    rw [(phi_degree a b W hW).2]
    refine mul_ne_zero (Polynomial.leadingCoeff_ne_zero.mpr hW) (pow_ne_zero 2 ?_)
    intro hh
    exact hd5 (by exact_mod_cast (sub_eq_zero.mp hh))
  have hPhi_ne : PhiNum a b W ≠ 0 := by
    intro hz
    have h := hnat
    rw [hz] at h
    simp at h

  have hPsi_ne : PsiNum c ≠ 0 := by
    intro hz
    rw [hz, mul_zero] at h4
    rcases mul_eq_zero.mp h4 with h' | h'
    · exact hPhi_ne h'
    · exact absurd h' (mul_ne_zero (pow_ne_zero _ Polynomial.X_ne_zero)
        (pow_ne_zero _ (Polynomial.X_sub_C_ne_zero 1)))
  have hX1ne : (X - 1 : Polynomial ℂ) ≠ 0 := by
    intro hh
    have h1 : (X - 1 : Polynomial ℂ).eval (0 : ℂ) = 0 := by rw [hh, Polynomial.eval_zero]
    rw [show (X - 1 : Polynomial ℂ).eval (0 : ℂ) = -1 from by simp] at h1
    norm_num at h1
  have hxne : (X ^ 7 * (X - 1) ^ 3 : Polynomial ℂ) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ Polynomial.X_ne_zero) (pow_ne_zero _ hX1ne)
  have hxd : (X ^ 7 * (X - 1) ^ 3 : Polynomial ℂ).natDegree = 10 := by
    rw [Polynomial.natDegree_mul (pow_ne_zero _ Polynomial.X_ne_zero) (pow_ne_zero _ hX1ne)]
    rw [Polynomial.natDegree_pow, Polynomial.natDegree_pow, Polynomial.natDegree_X,
      show ((X - 1 : Polynomial ℂ)).natDegree = 1 from Polynomial.natDegree_X_sub_C 1]
  have hLHS : (PhiNum a b W * (X ^ 7 * (X - 1) ^ 3)).natDegree = W.natDegree + 35 := by
    rw [Polynomial.natDegree_mul hPhi_ne hxne, hnat, hxd]
  have hRHS : (DadjL ^ 3 * PsiNum c).natDegree ≤ 41 := by
    rw [Polynomial.natDegree_mul (pow_ne_zero _ DadjL_ne_zero) hPsi_ne]
    have h3' : (DadjL ^ 3).natDegree ≤ 30 := by
      rw [Polynomial.natDegree_pow, DadjL_natDegree]
    calc (DadjL ^ 3).natDegree + (PsiNum c).natDegree ≤ 30 + 11 := add_le_add h3' hpsideg
      _ ≤ 41 := by norm_num
  have h5 : W.natDegree + 35 ≤ 41 := by rw [← hLHS, h4]; exact hRHS
  omega


/-- **The adjoint divisor bound.**  Any solution `β ∈ ℂ(x)` of the adjoint equation whose right hand
side lies in the span of `y^{i−4}·y'` (`i < 6`, `y = x²/(x−1)`) has `β·x⁶(x−1)²(x+1)²` a polynomial
of degree at most six. -/
theorem adjoint_divisor_boundC (a b : ℚ) (hA : Work.C17.AdmQ a b) (β : RatFunc ℂ) (c : Fin 6 → ℂ)
    (h : Submission.CDT.dRat (Submission.CDT.dRat (Work.C17.Pac a b * β))
        - Submission.CDT.dRat (Work.C17.Pbc a b * β) + Work.C17.Pcc a b * β
      = ∑ i : Fin 6, algebraMap ℂ (RatFunc ℂ) (c i) * Work.C17.yQc ^ ((i : ℤ) - 4) * Work.C17.dyQc) :
    ∃ n : Fin 7 → ℂ, β * Work.C17.DadjC
      = ∑ k : Fin 7, algebraMap (Polynomial ℂ) (RatFunc ℂ) (Polynomial.C (n k) * Polynomial.X ^ (k : ℕ)) := by
  obtain ⟨ha, hab, -, hm, hn⟩ := hA
  have hb : 3 ≤ b := by linarith
  have hab' : a ≠ b := hab.ne
  rcases eq_or_ne β 0 with hβ0 | hβ
  · subst hβ0
    exact ⟨fun _ => 0, by simp⟩
  have h' : Submission.CDT.dRat (Submission.CDT.dRat (Work.C17.Pac a b * β))
        - Submission.CDT.dRat (Work.C17.Pbc a b * β) + Work.C17.Pcc a b * β = RhsC c := by
    unfold RhsC
    exact h
  obtain ⟨W, hW⟩ := beta_Dadj_is_poly ha hb hab' hβ h'
  have hWne : W ≠ 0 := by
    intro hz
    rw [hz] at hW
    have h0 : β * Work.C17.DadjC = 0 := by rw [hW]; simp
    rcases mul_eq_zero.mp h0 with h1 | h1
    · exact hβ h1
    · exact (RatFunc.algebraMap_ne_zero DadjL_ne_zero) h1
  have hd : W.natDegree ≤ 6 := degree_bound hWne hW h'
  refine ⟨fun k => W.coeff (k : ℕ), ?_⟩
  conv_lhs => rw [hW, eq_sum_fin_seven W hd, map_sum]

end
end Work.C17adj
