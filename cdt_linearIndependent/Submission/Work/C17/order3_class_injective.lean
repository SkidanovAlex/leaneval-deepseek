import Mathlib
import Submission.Work.C17.seventeen_defs
import Submission.Work.C17.lead_defs
import Submission.Work.C17.lead_api
import Submission.Work.C17.reg_sigma
import Submission.Work.C17.local_base
import Submission.Work.C17.sigma_lead
import Submission.Work.C17.sigma_lead1
import Submission.Work.C17.local_dw

namespace Work.C17

open Commons.FieldTheory.RatFunc
open Polynomial
open scoped BigOperators
open Submission.CDTPlan

noncomputable section

/-! ## The deck involution `sigmaQ` fixes `yQ` and the `yQ`-evaluations -/

theorem sigmaQ_yQ : sigmaQ yQ = yQ := by
  have h1 : yQ = xQ ^ 2 / (xQ - 1) := rfl
  rw [h1, map_div₀, map_pow, map_sub, map_one, sigmaQ_X]
  have hx1 : xQ - 1 ≠ (0 : RatFunc ℚ) := unit0_ne_zero unit0_X_sub_one
  field_simp
  ring

theorem sigmaQ_eval₂ (P : Polynomial ℚ) :
    sigmaQ (P.eval₂ (algebraMap ℚ (RatFunc ℚ)) yQ)
      = P.eval₂ (algebraMap ℚ (RatFunc ℚ)) yQ := by
  conv_lhs => rw [Polynomial.eval₂_eq_sum_range]
  rw [Polynomial.eval₂_eq_sum_range, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_mul, map_pow, sigmaQ_yQ,
    show sigmaQ ((algebraMap ℚ (RatFunc ℚ)) (P.coeff k))
        = (algebraMap ℚ (RatFunc ℚ)) (P.coeff k) from map_ratCast sigmaQ (P.coeff k)]

/-! ## The components of `cls a b k` for `k ≤ 3` -/

theorem cls_zero_fst (a b : ℚ) : (cls a b 0).1 = 1 := by
  show (((dW a b)^[((0 : Fin 4) : ℕ)] ((1, 0), 0)).1).1 = 1
  rw [show (((0 : Fin 4) : ℕ)) = 0 from rfl, Function.iterate_zero_apply]

theorem cls_zero_snd (a b : ℚ) : (cls a b 0).2 = 0 := by
  show (((dW a b)^[((0 : Fin 4) : ℕ)] ((1, 0), 0)).1).2 = 0
  rw [show (((0 : Fin 4) : ℕ)) = 0 from rfl, Function.iterate_zero_apply]

theorem cls_one_fst (a b : ℚ) : (cls a b 1).1 = 0 := by
  show (((dW a b)^[((1 : Fin 4) : ℕ)] ((1, 0), 0)).1).1 = 0
  rw [show (((1 : Fin 4) : ℕ)) = 1 from rfl, Function.iterate_one]
  simp [dW]

theorem cls_one_snd (a b : ℚ) : (cls a b 1).2 = rhoQ := by
  show (((dW a b)^[((1 : Fin 4) : ℕ)] ((1, 0), 0)).1).2 = rhoQ
  rw [show (((1 : Fin 4) : ℕ)) = 1 from rfl, Function.iterate_one]
  simp [dW]

theorem cls_two_fst (a b : ℚ) : (cls a b 2).1 = u2 a b := by
  show (((dW a b)^[((2 : Fin 4) : ℕ)] ((1, 0), 0)).1).1 = u2 a b
  rw [show (((2 : Fin 4) : ℕ)) = 2 from rfl, Function.iterate_succ_apply', Function.iterate_one]
  simp only [dW, u2]
  simp

theorem cls_two_snd (a b : ℚ) : (cls a b 2).2 = v2 a b := by
  show (((dW a b)^[((2 : Fin 4) : ℕ)] ((1, 0), 0)).1).2 = v2 a b
  rw [show (((2 : Fin 4) : ℕ)) = 2 from rfl, Function.iterate_succ_apply', Function.iterate_one]
  simp only [dW, v2]
  simp

theorem cls_three_fst (a b : ℚ) : (cls a b 3).1 = u3 a b := by
  show (((dW a b)^[((3 : Fin 4) : ℕ)] ((1, 0), 0)).1).1 = u3 a b
  rw [show (((3 : Fin 4) : ℕ)) = 3 from rfl, Function.iterate_succ_apply',
    Function.iterate_succ_apply', Function.iterate_one]
  simp only [dW, u3, u2, v2]
  simp

theorem cls_three_snd (a b : ℚ) : (cls a b 3).2 = v3 a b := by
  show (((dW a b)^[((3 : Fin 4) : ℕ)] ((1, 0), 0)).1).2 = v3 a b
  rw [show (((3 : Fin 4) : ℕ)) = 3 from rfl, Function.iterate_succ_apply',
    Function.iterate_succ_apply', Function.iterate_one]
  simp only [dW, v3, u2, v2]
  simp


/-! ## The injectivity of `P ↦ P(yQ)` -/

theorem ordAtT_eq_top_zero (α : ℚ) : ordAtT α (0 : RatFunc ℚ) = ⊤ := by
  rw [ordAtT]; simp

theorem ordAtT_one_xQ : ordAtT (1 : ℚ) xQ = 0 := by
  rw [xQ_eq_algebraMap, ordAtT_algebraMap Polynomial.X_ne_zero]
  have h : (Polynomial.X : Polynomial ℚ).rootMultiplicity (1 : ℚ) = 0 := by
    rw [Polynomial.rootMultiplicity_eq_zero_iff]
    intro hroot
    exact absurd hroot (by simpa [Polynomial.IsRoot] using (one_ne_zero : (1 : ℚ) ≠ 0))
  rw [h]; norm_num

theorem ordAtT_one_xQ_sub_one : ordAtT (1 : ℚ) (xQ - 1) = 1 := by
  rw [show (xQ - 1 : RatFunc ℚ)
      = algebraMap (Polynomial ℚ) (RatFunc ℚ) (Polynomial.X - 1) from by
    rw [xQ_eq_algebraMap, map_sub, map_one]]
  rw [show (Polynomial.X - 1 : Polynomial ℚ) = Polynomial.X - Polynomial.C 1 by simp]
  rw [ordAtT_algebraMap (Polynomial.X_sub_C_ne_zero 1),
    Polynomial.rootMultiplicity_X_sub_C_self]
  norm_num

theorem yQ_ne_zero : yQ ≠ (0 : RatFunc ℚ) := by
  rw [show yQ = xQ ^ 2 / (xQ - 1) from rfl]
  exact div_ne_zero (pow_ne_zero 2 xQ_ne_zero) (unit0_ne_zero unit0_X_sub_one)

theorem ordAtT_one_yQ : ordAtT (1 : ℚ) yQ = (-1 : WithTop ℤ) := by
  have hx1 : (xQ - 1 : RatFunc ℚ) ≠ 0 := unit0_ne_zero unit0_X_sub_one
  have hx2 : (xQ ^ 2 : RatFunc ℚ) ≠ 0 := pow_ne_zero 2 xQ_ne_zero
  rw [show yQ = xQ ^ 2 / (xQ - 1) from rfl, ordAtT_div (1 : ℚ) hx2 hx1,
    show ordAtT (1 : ℚ) (xQ ^ 2) = 0 from by
      rw [ordAtT_pow (1 : ℚ) xQ_ne_zero 2, ordAtT_one_xQ]
      norm_num, ordAtT_one_xQ_sub_one]
  norm_num

theorem ordAtT_one_rat {c : ℚ} (hc : c ≠ 0) : ordAtT (1 : ℚ) (algebraMap ℚ (RatFunc ℚ) c) = 0 := by
  rw [IsScalarTower.algebraMap_apply ℚ (Polynomial ℚ) (RatFunc ℚ) c,
    show (algebraMap ℚ (Polynomial ℚ)) c = Polynomial.C c from (Polynomial.C_eq_algebraMap c).symm,
    ordAtT_algebraMap (Polynomial.C_ne_zero.mpr hc)]
  rw [show (Polynomial.C c).rootMultiplicity (1 : ℚ) = 0 from by
    rw [Polynomial.rootMultiplicity_eq_zero_iff]
    intro h
    rw [Polynomial.IsRoot, Polynomial.eval_C] at h
    exact absurd h hc]
  norm_num

theorem yQ_pow_ne_zero (n : ℕ) : yQ ^ n ≠ (0 : RatFunc ℚ) := pow_ne_zero n yQ_ne_zero

/-- `yQ` is transcendental over `ℚ`: `P(yQ) = 0` forces `P = 0`. -/
theorem eval₂_yQ_eq_zero {P : Polynomial ℚ}
    (hP : P.eval₂ (algebraMap ℚ (RatFunc ℚ)) yQ = 0) : P = 0 := by
  by_contra hne
  have hcd : P.coeff P.natDegree ≠ 0 := by
    rw [Polynomial.coeff_natDegree]
    exact Polynomial.leadingCoeff_ne_zero.mpr hne
  rw [Polynomial.eval₂_eq_sum_range] at hP
  have hmem : P.natDegree ∈ Finset.range (P.natDegree + 1) :=
    Finset.mem_range.mpr (Nat.lt_succ_iff.mpr le_rfl)
  rw [← Finset.sum_erase_add _ _ hmem, add_comm] at hP
  have htop : ordAtT (1 : ℚ) (algebraMap ℚ (RatFunc ℚ) (P.coeff P.natDegree) * yQ ^ P.natDegree)
      = ((-(P.natDegree : ℤ)) : WithTop ℤ) := by
    rw [ordAtT_mul (1 : ℚ) (fun h => hcd (by simpa using h)) (yQ_pow_ne_zero _),
      ordAtT_one_rat hcd, ordAtT_pow (1 : ℚ) yQ_ne_zero P.natDegree, ordAtT_one_yQ]
    rw [show (-1 : WithTop ℤ) = ((-1 : ℤ) : WithTop ℤ) from rfl, ← WithTop.coe_mul, zero_add]
    congr 1
    ring
  have hrest : (((-(P.natDegree : ℤ) + 1 : ℤ)) : WithTop ℤ)
      ≤ ordAtT (1 : ℚ) (∑ k ∈ (Finset.range (P.natDegree + 1)).erase P.natDegree,
          algebraMap ℚ (RatFunc ℚ) (P.coeff k) * yQ ^ k) := by
    refine le_ordAtT_finset_sum fun k hk => ?_
    rw [Finset.mem_erase, Finset.mem_range] at hk
    obtain ⟨hkne, hklt⟩ := hk
    have hk' : k < P.natDegree := by
      have := Nat.lt_succ_iff.mp hklt
      omega
    rcases eq_or_ne (P.coeff k) 0 with h0 | h0
    · rw [h0, map_zero, zero_mul, ordAtT_eq_top_zero]; exact le_top
    · rw [ordAtT_mul (1 : ℚ) (fun h => h0 (by simpa using h)) (yQ_pow_ne_zero k),
        ordAtT_one_rat h0, ordAtT_pow (1 : ℚ) yQ_ne_zero k, ordAtT_one_yQ]
      rw [show (-1 : WithTop ℤ) = ((-1 : ℤ) : WithTop ℤ) from rfl, ← WithTop.coe_mul, zero_add,
        WithTop.coe_le_coe]
      have := hk'
      omega
  have hord := ordAtT_add_eq_of_le_succ (α := (1 : ℚ)) htop hrest
  rw [hP, ordAtT_eq_top_zero] at hord
  exact WithTop.coe_ne_top hord.symm

/-! ## The main theorem -/

theorem order3_class_injective (a b : ℚ) (hA : AdmQ a b)
    (p : Fin 4 → Polynomial ℚ)
    (h : ((∑ k : Fin 4, ((p k).eval₂ (algebraMap ℚ (RatFunc ℚ)) (yQ)) * (cls a b k).1),
          (∑ k : Fin 4, ((p k).eval₂ (algebraMap ℚ (RatFunc ℚ)) (yQ)) * (cls a b k).2)) = (0, 0)) :
    p = 0 := by
  have ha3 : 3 ≤ a := hA.1
  have hab : a < b := hA.2.1
  have hab0 : a * b ≠ 0 := by
    have ha0 : a ≠ 0 := by linarith
    have hb0 : b ≠ 0 := by linarith
    exact mul_ne_zero ha0 hb0
  obtain ⟨hbρ, hbρ', hbP0, hbP1, hbP2, hbP1dP2⟩ := local_base a b hA
  have hσ1 : ∀ (f : RatFunc ℚ) (e : ℤ) (l : ℚ), LeadAt f e l →
      LeadAt (sigmaQ f) e ((-1 : ℚ) ^ e * l) := by
    intro f e l h1
    exact sigma_lead1 f e l h1
  have hσ2 : ∀ (f : RatFunc ℚ) (e : ℤ) (l m : ℚ), Lead2At f e l m →
      Lead2At (sigmaQ f) e ((-1 : ℚ) ^ e * l) ((-1 : ℚ) ^ e * ((e : ℚ) * l - m)) := by
    intro f e l m h2
    exact (sigma_lead f e l m h2.to_LeadAt h2).2
  obtain ⟨hZ2, hZ3, hY2, hY3⟩ :=
    local_dw a b hA hbρ hbρ' hbP0 hbP1 hbP2 hbP1dP2 hσ1 hσ2
  have hdet : Dd a b ≠ 0 := by
    have hcoef : ((a * b / 2) * (5 / 4 - 19 * a * b / 2)) - ((5 * a * b / 4) * (1 / 2 - 4 * a * b))
        ≠ 0 := by
      have hval : ((a * b / 2) * (5 / 4 - 19 * a * b / 2)) - ((5 * a * b / 4) * (1 / 2 - 4 * a * b))
          = (a * b) ^ 2 / 4 := by ring
      rw [hval]
      exact div_ne_zero (pow_ne_zero 2 hab0) (by norm_num)
    have hmul1 : LeadAt (Z2 a b * Y3 a b) (-3 + -3) ((a * b / 2) * (5 / 4 - 19 * a * b / 2)) :=
      LeadAt.mul hZ2 hY3
    have hmul2 : LeadAt (Z3 a b * Y2 a b) (-5 + -1) ((5 * a * b / 4) * (1 / 2 - 4 * a * b)) :=
      LeadAt.mul hZ3 hY2
    have hsub : LeadAt (Z2 a b * Y3 a b - Z3 a b * Y2 a b) (-3 + -3)
        (((a * b / 2) * (5 / 4 - 19 * a * b / 2)) - ((5 * a * b / 4) * (1 / 2 - 4 * a * b))) :=
      LeadAt.sub_of_eq hmul1 hmul2 hcoef
    have hne' : Z2 a b * Y3 a b - Z3 a b * Y2 a b ≠ 0 := hsub.ne_zero
    rwa [show Dd a b = Z2 a b * Y3 a b - Z3 a b * Y2 a b from rfl]
  have hsum1 : (∑ k : Fin 4, ((p k).eval₂ (algebraMap ℚ (RatFunc ℚ)) (yQ)) * (cls a b k).1) = 0 :=
    congrArg Prod.fst h
  have hsum2 : (∑ k : Fin 4, ((p k).eval₂ (algebraMap ℚ (RatFunc ℚ)) (yQ)) * (cls a b k).2) = 0 :=
    congrArg Prod.snd h
  rw [Fin.sum_univ_four] at hsum1 hsum2
  rw [cls_zero_fst a b, cls_one_fst a b, cls_two_fst a b, cls_three_fst a b] at hsum1
  rw [cls_zero_snd a b, cls_one_snd a b, cls_two_snd a b, cls_three_snd a b] at hsum2
  set Q : Fin 4 → RatFunc ℚ := fun k => (p k).eval₂ (algebraMap ℚ (RatFunc ℚ)) yQ with hQdef
  have hQeq : ∀ k, (p k).eval₂ (algebraMap ℚ (RatFunc ℚ)) yQ = Q k := fun k => rfl
  have hQ0 : Q 0 = -(Q 2 * u2 a b + Q 3 * u3 a b) := by
    simp only [hQeq] at hsum1
    linear_combination hsum1
  have hQ1 : Q 1 = -(Q 2 * w2 a b + Q 3 * w3 a b) := by
    simp only [hQeq] at hsum2
    have hrne : rhoQ ≠ 0 := hbρ.ne_zero
    have h2 : Q 1 * rhoQ = -(Q 2 * v2 a b + Q 3 * v3 a b) := by
      linear_combination hsum2
    have h3 := congrArg (fun x => x * rhoQ⁻¹) h2
    have hv2 : v2 a b * rhoQ⁻¹ = w2 a b := by rw [v2, w2]; field_simp
    have hv3 : v3 a b * rhoQ⁻¹ = w3 a b := by rw [v3, w3]; field_simp
    rw [mul_assoc, mul_inv_cancel₀ hrne, mul_one, neg_mul, add_mul, mul_assoc, mul_assoc,
      hv2, hv3] at h3
    exact h3
  have hfix : ∀ k, sigmaQ (Q k) = Q k := fun k => by
    rw [← hQeq k]; exact sigmaQ_eval₂ (p k)
  have heq1 : Q 2 * Z2 a b + Q 3 * Z3 a b = 0 := by
    have hs : sigmaQ (Q 0) = sigmaQ (-(Q 2 * u2 a b + Q 3 * u3 a b)) := by rw [hQ0]
    rw [hfix 0, map_neg, map_add, map_mul, map_mul, hfix 2, hfix 3] at hs
    rw [hQ0] at hs
    have hA' : Q 2 * u2 a b + Q 3 * u3 a b = Q 2 * sigmaQ (u2 a b) + Q 3 * sigmaQ (u3 a b) :=
      neg_inj.mp hs
    rw [Z2, Z3, mul_sub, mul_sub]
    linear_combination hA'
  have heq2 : Q 2 * Y2 a b + Q 3 * Y3 a b = 0 := by
    have hs : sigmaQ (Q 1) = sigmaQ (-(Q 2 * w2 a b + Q 3 * w3 a b)) := by rw [hQ1]
    rw [hfix 1, map_neg, map_add, map_mul, map_mul, hfix 2, hfix 3] at hs
    rw [hQ1] at hs
    have hA' : Q 2 * w2 a b + Q 3 * w3 a b = Q 2 * sigmaQ (w2 a b) + Q 3 * sigmaQ (w3 a b) :=
      neg_inj.mp hs
    rw [Y2, Y3, mul_sub, mul_sub]
    linear_combination hA'
  have hQ2 : Q 2 = 0 := by
    have hcomb : Q 2 * Dd a b = 0 := by
      have h1' := congrArg (fun x => Y3 a b * x) heq1
      have h2' := congrArg (fun x => Z3 a b * x) heq2
      rw [mul_zero] at h1' h2'
      rw [show Dd a b = Z2 a b * Y3 a b - Z3 a b * Y2 a b from rfl]
      linear_combination h1' - h2'
    exact (mul_eq_zero.mp hcomb).resolve_right hdet
  have hQ3 : Q 3 = 0 := by
    rw [hQ2, zero_mul, zero_add] at heq1
    exact (mul_eq_zero.mp heq1).resolve_right hZ3.ne_zero
  have hQ0z : Q 0 = 0 := by
    rw [hQ0, hQ2, hQ3, zero_mul, zero_mul, add_zero, neg_zero]
  have hQ1z : Q 1 = 0 := by
    rw [hQ1, hQ2, hQ3, zero_mul, zero_mul, add_zero, neg_zero]
  funext k
  have hk : Q k = 0 := by fin_cases k <;> assumption
  exact eval₂_yQ_eq_zero (P := p k) (by rw [hQeq k]; exact hk)

end

end Work.C17
