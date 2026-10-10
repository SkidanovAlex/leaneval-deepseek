import Mathlib
import Submission.Work.MotV5.WtDefs
import Submission.Work.MotV5.Wt_kleinQPoly_le
import Submission.Work.MotV5.topPart_asPolyF_mul_gen
import Submission.Work.MotV5.coeff_kleinQPoly_top
import Submission.Work.MotV5.Wt_polyOf
import Submission.Work.MotV5.TpLeaves.kleinQPoly_monomial_structure
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option maxHeartbeats 1000000

namespace Work.MotV5

open Work.MotV5.TpLeaves

open Polynomial

/-! ## Coefficients of `polyOf y` -/

lemma polyOf_coeff {F : Type*} [CommRing F] (y : Fin 5 → F) (l : ℕ) :
    (polyOf y).coeff l = if h : l < 5 then y ⟨l, h⟩ else 0 := by
  have hsum : (polyOf y).coeff l
      = ∑ j : Fin 5, y j * (if l = (j : ℕ) then (1 : F) else 0) := by
    have h1 : (polyOf y) = ∑ j : Fin 5, C (y j) * X ^ (j : ℕ) := rfl
    rw [h1]
    rw [show (∑ j : Fin 5, C (y j) * X ^ (j : ℕ))
        = ∑ j ∈ (Finset.univ : Finset (Fin 5)), C (y j) * X ^ (j : ℕ) from rfl]
    rw [Polynomial.finsetSum_coeff]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
  rw [hsum]
  by_cases h : l < 5
  · rw [dif_pos h]
    have hterm : ∀ j : Fin 5, y j * (if l = (j : ℕ) then (1 : F) else 0)
        = if j = (⟨l, h⟩ : Fin 5) then y j else 0 := by
      intro j
      by_cases hj : j = ⟨l, h⟩
      · subst hj; simp
      · have hjl : ¬ (l = (j : ℕ)) := fun hh => hj (Fin.ext hh.symm)
        rw [if_neg hj, if_neg hjl, mul_zero]
    simp only [hterm]
    rw [Finset.sum_ite_eq', if_pos (Finset.mem_univ _)]
  · rw [dif_neg h]
    refine Finset.sum_eq_zero (fun j _ => ?_)
    have hjl : ¬ (l = (j : ℕ)) := by have := j.isLt; omega
    rw [if_neg hjl, mul_zero]

lemma polyOf_coeff_fin {F : Type*} [CommRing F] (y : Fin 5 → F) (j : Fin 5) :
    (polyOf y).coeff (j : ℕ) = y j := by
  rw [polyOf_coeff, dif_pos j.isLt]

/-! ## The maximum weight of `y` and the leading monomial -/

/-- The index `l₀` of the (unique) maximal weight has `y l₀ ≠ 0`. -/
lemma y_l₀_ne_zero {F Γ₀ : Type*} [Field F] [CharP F 5] [LinearOrderedCommGroupWithZero Γ₀]
    (v : Valuation F Γ₀) {g : F} {y : Fin 5 → F} {l₀ : Fin 5}
    (hmax : ∀ l : Fin 5, wt v g (y l) l ≤ wt v g (y l₀) l₀)
    (huniq : ∀ l : Fin 5, wt v g (y l) l = wt v g (y l₀) l₀ → l = l₀) : y l₀ ≠ 0 := by
  intro h0
  have hW0 : wt v g (y l₀) l₀ = 0 := by rw [h0]; simp [wt]
  have hall : ∀ l : Fin 5, wt v g (y l) l = 0 := fun l =>
    le_antisymm (by rw [← hW0]; exact hmax l) zero_le
  have hcon : ∀ l : Fin 5, l = l₀ := fun l => huniq l (by rw [hall l, hall l₀])
  have h01 : (0 : Fin 5) = (1 : Fin 5) := (hcon 0).trans (hcon 1).symm
  exact absurd h01 (by decide)

lemma wt_y_l₀_pos {F Γ₀ : Type*} [Field F] [CharP F 5] [LinearOrderedCommGroupWithZero Γ₀]
    (v : Valuation F Γ₀) {g : F} {y : Fin 5 → F} {l₀ : Fin 5} (hg1 : 1 < v g)
    (hyne : y l₀ ≠ 0) : 0 < wt v g (y l₀) l₀ := by
  rw [wt]
  exact mul_pos (pow_pos (lt_trans zero_lt_one hg1) _)
    (pow_pos (zero_lt_iff.mpr ((Valuation.ne_zero_iff v).mpr hyne)) _)

/-- The weight of `polyOf y - C (y l₀) * X^l₀` is strictly smaller than the maximal weight. -/
lemma Wt_polyOf_sub_leading {F Γ₀ : Type*} [Field F] [CharP F 5]
    [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation F Γ₀) {g : F} (hg1 : 1 < v g)
    {y : Fin 5 → F} {l₀ : Fin 5}
    (hmax : ∀ l : Fin 5, wt v g (y l) l ≤ wt v g (y l₀) l₀)
    (huniq : ∀ l : Fin 5, wt v g (y l) l = wt v g (y l₀) l₀ → l = l₀) :
    Wt v g (polyOf y - C (y l₀) * X ^ (l₀ : ℕ)) < wt v g (y l₀) l₀ := by
  have hyne := y_l₀_ne_zero v hmax huniq
  have hWpos : 0 < wt v g (y l₀) l₀ := wt_y_l₀_pos v hg1 hyne
  have hlt : ∀ l : Fin 5, l ≠ l₀ → wt v g (y l) l < wt v g (y l₀) l₀ :=
    fun l hl => lt_of_le_of_ne (hmax l) (fun heq => hl (huniq l heq))
  have hpt : ∀ m, wt v g ((polyOf y - C (y l₀) * X ^ (l₀ : ℕ)).coeff m) m
      < wt v g (y l₀) l₀ := by
    intro m
    rw [Polynomial.coeff_sub]
    by_cases hm : m < 5
    · rw [polyOf_coeff, dif_pos hm, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
      rcases eq_or_ne m (l₀ : ℕ) with h | h
      · have hfin : (⟨m, hm⟩ : Fin 5) = l₀ := Fin.ext h
        rw [hfin, if_pos h, mul_one, sub_self, wt_zero v g 0 m rfl]
        exact hWpos
      · rw [if_neg h, mul_zero, sub_zero]
        have hfin : (⟨m, hm⟩ : Fin 5) ≠ l₀ := fun hh => h (congrArg Fin.val hh)
        exact hlt ⟨m, hm⟩ hfin
    · rw [polyOf_coeff, dif_neg hm, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
        if_neg (by omega : m ≠ (l₀ : ℕ)), mul_zero, sub_zero, wt_zero v g 0 m rfl]
      exact hWpos
  rw [Wt, Finset.sup_lt_iff (show (⊥ : Γ₀) < wt v g (y l₀) l₀ from by
    rw [bot_eq_zero]; exact hWpos)]
  intro m _
  exact hpt m

/-! ## The top part of a polynomial with a unique maximal-weight coefficient -/

lemma topPart_eq_C_mul_X {F Γ₀ : Type*} [Field F] [CharP F 5]
    [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation F Γ₀) (g : F) (Q : Polynomial F)
    {i₀ : ℕ} (hmem : i₀ ∈ Q.support)
    (hmax : ∀ l ∈ Q.support, wt v g (Q.coeff l) l ≤ wt v g (Q.coeff i₀) i₀)
    (huniq : ∀ l ∈ Q.support, l ≠ i₀ → wt v g (Q.coeff l) l < wt v g (Q.coeff i₀) i₀) :
    topPart v g Q = C (Q.coeff i₀) * X ^ i₀ := by
  have hWt : Wt v g Q = wt v g (Q.coeff i₀) i₀ :=
    le_antisymm (by rw [Wt]; exact Finset.sup_le hmax)
      (by rw [Wt]; exact Finset.le_sup (f := fun l => wt v g (Q.coeff l) l) hmem)
  rw [topPart, hWt]
  rw [Finset.sum_eq_single_of_mem i₀ hmem (fun l hl hne => by
    rw [if_neg]; exact ne_of_lt (huniq l hl hne))]
  rw [if_pos rfl]

/-! ## The Klein polynomial of a scalar multiple -/

lemma kleinQPoly_C_mul {R : Type*} [CommRing R] (a b c : R) (P : Polynomial R) :
    kleinQPoly a b (C c * P) = C (c ^ 2) * kleinQPoly a b P := by
  simp only [kleinQPoly, Polynomial.mul_comp, Polynomial.C_comp, map_pow]
  first | refl_ring1 | ring

/-- Bilinear expansion of `kleinQPoly` at a sum. -/
lemma kleinQPoly_add_cross {R : Type*} [CommRing R] (a b : R) (L R' : Polynomial R) :
    kleinQPoly a b (L + R')
      = kleinQPoly a b L + kleinQPoly a b R'
        + (-C (a*b) * (2 * (L * R'))
            + C (a^2) * ((L.comp (X + C 2)) * (R'.comp (X + C 3))
                          + (R'.comp (X + C 2)) * (L.comp (X + C 3)))
            - C (b^2) * ((L.comp (X + C 1)) * (R'.comp (X + C 4))
                          + (R'.comp (X + C 1)) * (L.comp (X + C 4)))) := by
  simp only [kleinQPoly, Polynomial.add_comp]
  first | refl_ring1 | ring

/-! ## Weight of a monomial and of a scalar multiple -/

lemma Wt_C_mul_X_pow {F Γ₀ : Type*} [Field F] [CharP F 5]
    [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation F Γ₀) (g : F) (u : F) (n : ℕ) :
    Wt v g (C u * X ^ n) = wt v g u n := by
  refine le_antisymm ?_ ?_
  · rw [WtKL_Wt_le_iff]
    intro m
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
    by_cases h : m = n
    · rw [if_pos h, mul_one, h]
    · rw [if_neg h, mul_zero, wt_zero v g 0 m rfl]
      exact zero_le
  · have hcoeff : (C u * X ^ n).coeff n = u := by
      rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_pos rfl, mul_one]
    calc wt v g u n = wt v g ((C u * X ^ n).coeff n) n := by rw [hcoeff]
      _ ≤ Wt v g (C u * X ^ n) := WtKL_wt_coeff_le_Wt v g (C u * X ^ n) n

/-- A scalar factor of 5th-power value `≤ 1` does not increase `Wt`. -/
lemma Wt_C_mul_le_of_val {F Γ₀ : Type*} [Field F] [CharP F 5]
    [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation F Γ₀) (g : F) {lam : F}
    (hlam : (v lam) ^ 5 ≤ 1) {f : Polynomial F} {B : Γ₀} (h : Wt v g f ≤ B) :
    Wt v g (C lam * f) ≤ B :=
  le_trans (WtKL_Wt_C_mul_le v g lam f) (by
    have := mul_le_mul hlam h (zero_le : (0 : Γ₀) ≤ Wt v g f) (zero_le : (0 : Γ₀) ≤ 1)
    simpa using this)

theorem topPart_kleinQPoly {F Γ₀ : Type*} [Field F] [CharP F 5]
    [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation F Γ₀) {g a b : F} (hg1 : 1 < v g)
    (ha : v a = 1) (hb : v b = 1) (hab : v (a ^ 2 - a * b - b ^ 2) = 1)
    {y : Fin 5 → F} {l₀ : Fin 5} (hmax : ∀ l : Fin 5, wt v g (y l) l ≤ wt v g (y l₀) l₀)
    (huniq : ∀ l : Fin 5, wt v g (y l) l = wt v g (y l₀) l₀ → l = l₀) :
    topPart v g (kleinQPoly a b (polyOf y))
        = Polynomial.C ((kleinQPoly a b (polyOf y)).coeff (2 * (l₀ : ℕ))) * Polynomial.X ^ (2 * (l₀ : ℕ))
      ∧ wt v g ((kleinQPoly a b (polyOf y)).coeff (2 * (l₀ : ℕ))) (2 * (l₀ : ℕ))
          = wt v g (y l₀) l₀ * wt v g (y l₀) l₀ := by
  set W : Γ₀ := wt v g (y l₀) l₀ with hW
  have hyne : y l₀ ≠ 0 := y_l₀_ne_zero v hmax huniq
  have hWpos : 0 < W := by rw [hW]; exact wt_y_l₀_pos v hg1 hyne
  have hWne : W ≠ 0 := ne_of_gt hWpos
  have hWWpos : 0 < W * W := mul_pos hWpos hWpos
  have hWWne : W * W ≠ 0 := ne_of_gt hWWpos
  have hgne : v g ≠ 0 := ne_of_gt (lt_trans zero_lt_one hg1)
  have hWtP : Wt v g (polyOf y) = W := by rw [hW]; exact Wt_polyOf v hmax huniq
  -- the leading monomial `L` and the remainder `R`
  set L : Polynomial F := C (y l₀) * X ^ (l₀ : ℕ) with hL
  set R : Polynomial F := polyOf y - L with hR
  have hP : polyOf y = L + R := by rw [hR]; ring
  have hWL : Wt v g L = W := by rw [hL, hW]; exact Wt_C_mul_X_pow v g (y l₀) (l₀ : ℕ)
  have hWR : Wt v g R < W := by rw [hR, hW]; exact Wt_polyOf_sub_leading v hg1 hmax huniq
  -- the three pieces of the bilinear expansion
  set A : Polynomial F := kleinQPoly a b L with hA
  set D : Polynomial F := kleinQPoly a b R with hD
  set Cross : Polynomial F := -C (a * b) * (2 * (L * R))
      + C (a ^ 2) * ((L.comp (X + C 2)) * (R.comp (X + C 3))
                      + (R.comp (X + C 2)) * (L.comp (X + C 3)))
      - C (b ^ 2) * ((L.comp (X + C 1)) * (R.comp (X + C 4))
                      + (R.comp (X + C 1)) * (L.comp (X + C 4))) with hCross
  have hQdecomp : kleinQPoly a b (polyOf y) = A + D + Cross := by
    rw [hA, hD, hCross, hP]; exact kleinQPoly_add_cross a b L R
  -- the monomial structure of `A = kleinQPoly a b L`
  have hmono := kleinQPoly_monomial_structure v hg1 ha hb hab (n := (l₀ : ℕ))
    (by have := l₀.isLt; omega) ((Valuation.ne_zero_iff v).mpr hyne)
  have hA_le : ∀ m, wt v g (A.coeff m) m ≤ W * W := by
    intro m
    have h := hmono.1 m
    rw [← hL, ← hA] at h
    rw [hW]
    simpa [pow_two] using h
  have hA_lt : ∀ m, m ≠ 2 * (l₀ : ℕ) → wt v g (A.coeff m) m < W * W := by
    intro m hm
    have h := hmono.2.1 m hm
    rw [← hL, ← hA] at h
    rw [hW]
    simpa [pow_two] using h
  have hA_val : wt v g (A.coeff (2 * (l₀ : ℕ))) (2 * (l₀ : ℕ)) = W * W := by
    have h := hmono.2.2
    rw [← hL, ← hA] at h
    rw [hW]
    simpa [pow_two] using h
  -- the bound for `kleinQPoly a b R`
  have hD_bound : Wt v g D < W * W := by
    rw [hD]
    exact lt_of_le_of_lt (Wt_kleinQPoly_le v hg1 ha hb hab R)
      (mul_lt_mul'' hWR hWR zero_le zero_le)
  have hD_le : ∀ m, wt v g (D.coeff m) m ≤ W * W := fun m =>
    le_of_lt (lt_of_le_of_lt (WtKL_wt_coeff_le_Wt v g D m) hD_bound)
  have hD_lt : ∀ m, wt v g (D.coeff m) m < W * W := fun m =>
    lt_of_le_of_lt (WtKL_wt_coeff_le_Wt v g D m) hD_bound
  -- the bound for the cross terms
  have hvab : (v (-(a * b))) ^ 5 = 1 := by
    rw [Valuation.map_neg, Valuation.map_mul, ha, hb]; norm_num
  have hva2 : (v (a ^ 2)) ^ 5 = 1 := by rw [Valuation.map_pow, ha]; norm_num
  have hvb2 : (v (b ^ 2)) ^ 5 = 1 := by rw [Valuation.map_pow, hb]; norm_num
  have hC1 : Wt v g (-C (a * b) * (2 * (L * R))) ≤ W * Wt v g R := by
    have h1 : (-C (a * b) : Polynomial F) = C (-(a * b)) := (Polynomial.C_neg (a := a * b)).symm
    rw [h1]
    refine le_trans (WtKL_Wt_C_mul_le v g (-(a * b)) (2 * (L * R))) ?_
    rw [hvab, one_mul, two_mul]
    refine le_trans (WtKL_Wt_add_le v g (L * R) (L * R)) ?_
    rw [max_self, ← hWL]
    exact WtKL_Wt_mul_le v g L R
  have hC2 : Wt v g (C (a ^ 2) * ((L.comp (X + C 2)) * (R.comp (X + C 3))
      + (R.comp (X + C 2)) * (L.comp (X + C 3)))) ≤ W * Wt v g R := by
    refine le_trans (WtKL_Wt_C_mul_le v g (a ^ 2) _) ?_
    rw [hva2, one_mul]
    refine le_trans (WtKL_Wt_add_le v g _ _) ?_
    refine max_le ?_ ?_
    · refine le_trans (WtKL_Wt_mul_le v g _ _) ?_
      rw [← hWL]
      exact mul_le_mul_of_nonneg (WtKL_Wt_comp_X_add_C_le v g hg1 2
          (by simpa using WtKL_natCast_le_one v 2) L)
        (WtKL_Wt_comp_X_add_C_le v g hg1 3
          (by simpa using WtKL_natCast_le_one v 3) R) zero_le zero_le
    · calc Wt v g (R.comp (X + C 2) * L.comp (X + C 3))
          ≤ Wt v g (R.comp (X + C 2)) * Wt v g (L.comp (X + C 3)) := WtKL_Wt_mul_le v g _ _
        _ ≤ Wt v g R * Wt v g L := mul_le_mul
            (WtKL_Wt_comp_X_add_C_le v g hg1 2
              (by simpa using WtKL_natCast_le_one v 2) R)
            (WtKL_Wt_comp_X_add_C_le v g hg1 3
              (by simpa using WtKL_natCast_le_one v 3) L) zero_le zero_le
        _ = Wt v g L * Wt v g R := mul_comm _ _
        _ = W * Wt v g R := by rw [hWL]
  have hC3 : Wt v g (C (b ^ 2) * ((L.comp (X + C 1)) * (R.comp (X + C 4))
      + (R.comp (X + C 1)) * (L.comp (X + C 4)))) ≤ W * Wt v g R := by
    refine le_trans (WtKL_Wt_C_mul_le v g (b ^ 2) _) ?_
    rw [hvb2, one_mul]
    refine le_trans (WtKL_Wt_add_le v g _ _) ?_
    refine max_le ?_ ?_
    · refine le_trans (WtKL_Wt_mul_le v g _ _) ?_
      rw [← hWL]
      exact mul_le_mul_of_nonneg (WtKL_Wt_comp_X_add_C_le v g hg1 1
          (by simpa using WtKL_natCast_le_one v 1) L)
        (WtKL_Wt_comp_X_add_C_le v g hg1 4
          (by simpa using WtKL_natCast_le_one v 4) R) zero_le zero_le
    · calc Wt v g (R.comp (X + C 1) * L.comp (X + C 4))
          ≤ Wt v g (R.comp (X + C 1)) * Wt v g (L.comp (X + C 4)) := WtKL_Wt_mul_le v g _ _
        _ ≤ Wt v g R * Wt v g L := mul_le_mul
            (WtKL_Wt_comp_X_add_C_le v g hg1 1
              (by simpa using WtKL_natCast_le_one v 1) R)
            (WtKL_Wt_comp_X_add_C_le v g hg1 4
              (by simpa using WtKL_natCast_le_one v 4) L) zero_le zero_le
        _ = Wt v g L * Wt v g R := mul_comm _ _
        _ = W * Wt v g R := by rw [hWL]
  have hCross_bound : Wt v g Cross < W * W := by
    rw [hCross]
    refine lt_of_le_of_lt (le_trans (WtKL_Wt_sub_le v g _ _) (max_le ?_ hC3)) ?_
    · exact le_trans (WtKL_Wt_add_le v g _ _) (max_le hC1 hC2)
    · exact mul_lt_mul_of_pos_left hWR hWpos
  have hC_le : ∀ m, wt v g (Cross.coeff m) m ≤ W * W := fun m =>
    le_of_lt (lt_of_le_of_lt (WtKL_wt_coeff_le_Wt v g Cross m) hCross_bound)
  have hC_lt : ∀ m, wt v g (Cross.coeff m) m < W * W := fun m =>
    lt_of_le_of_lt (WtKL_wt_coeff_le_Wt v g Cross m) hCross_bound
  -- the two pointwise bounds for `Q`
  have hkey : ∀ m, wt v g ((A + D + Cross).coeff m) m
      ≤ max (max (wt v g (A.coeff m) m) (wt v g (D.coeff m) m)) (wt v g (Cross.coeff m) m) := by
    intro m
    rw [Polynomial.coeff_add, Polynomial.coeff_add]
    exact le_trans (WtKL_wt_add v g _ _ m) (max_le_max (WtKL_wt_add v g _ _ m) le_rfl)
  have hQ_le : ∀ m, wt v g ((kleinQPoly a b (polyOf y)).coeff m) m ≤ W * W := by
    intro m
    rw [hQdecomp]
    exact le_trans (hkey m) (max_le (max_le (hA_le m) (hD_le m)) (hC_le m))
  have hQ_lt : ∀ m, m ≠ 2 * (l₀ : ℕ) →
      wt v g ((kleinQPoly a b (polyOf y)).coeff m) m < W * W := by
    intro m hm
    rw [hQdecomp]
    exact lt_of_le_of_lt (hkey m) (max_lt (max_lt (hA_lt m hm) (hD_lt m)) (hC_lt m))
  -- the exact weight of the coefficient in degree `2 * l₀`
  have hQ_val : wt v g ((kleinQPoly a b (polyOf y)).coeff (2 * (l₀ : ℕ))) (2 * (l₀ : ℕ))
      = W * W := by
    set i : ℕ := 2 * (l₀ : ℕ) with hi
    have hcoeff : (kleinQPoly a b (polyOf y)).coeff i
        = (A.coeff i + D.coeff i) + Cross.coeff i := by
      rw [hQdecomp, Polynomial.coeff_add, Polynomial.coeff_add]
    have hvA : v (A.coeff i) ≠ 0 := by
      rw [Valuation.ne_zero_iff]
      intro h0
      have hz : wt v g (A.coeff i) i = 0 := wt_zero v g (A.coeff i) i h0
      rw [hA_val] at hz
      exact hWWne hz
    have hvD : v (D.coeff i) < v (A.coeff i) :=
      (wt_lt_wt_iff (v := v) (g := g) hgne).mp (by rw [hA_val]; exact hD_lt i)
    have hvC : v (Cross.coeff i) < v (A.coeff i) :=
      (wt_lt_wt_iff (v := v) (g := g) hgne).mp (by rw [hA_val]; exact hC_lt i)
    have hAD : v (A.coeff i + D.coeff i) = v (A.coeff i) :=
      Valuation.map_add_eq_of_lt_left v hvD
    have hsum : v ((A.coeff i + D.coeff i) + Cross.coeff i) = v (A.coeff i) := by
      rw [Valuation.map_add_eq_of_lt_left v (by rw [hAD]; exact hvC), hAD]
    rw [hcoeff, show wt v g ((A.coeff i + D.coeff i) + Cross.coeff i) i
        = wt v g (A.coeff i) i from by rw [wt, wt, hsum], hA_val]
  refine ⟨?_, ?_⟩
  · refine topPart_eq_C_mul_X v g _ ?_ ?_ ?_
    · rw [Polynomial.mem_support_iff]
      intro h0
      have hz : wt v g ((kleinQPoly a b (polyOf y)).coeff (2 * (l₀ : ℕ))) (2 * (l₀ : ℕ)) = 0 :=
        wt_zero v g _ _ h0
      rw [hQ_val] at hz
      exact hWWne hz
    · intro l _
      rw [hQ_val]
      exact hQ_le l
    · intro l _ hne
      rw [hQ_val]
      exact hQ_lt l hne
  · rw [hQ_val, hW]

end Work.MotV5
