import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series

namespace Commons.Analysis.Walsh

open Finset

/-- For `u : ℝ`, `exp u + exp (-u) ≤ 2 exp (u^2 / 2)`.  This is the two-point
"Gaussian moment generating function" bound for a Rademacher variable. -/
private lemma exp_add_exp_neg_le (u : ℝ) :
    Real.exp u + Real.exp (-u) ≤ 2 * Real.exp (u ^ 2 / 2) := by
  have h := Real.cosh_le_exp_half_sq u
  rw [Real.cosh_eq] at h
  linarith

/-- `exp |y| ≤ exp y + exp (-y)`. -/
private lemma exp_abs_le (y : ℝ) : Real.exp |y| ≤ Real.exp y + Real.exp (-y) := by
  rcases lt_or_ge y 0 with h | h
  · rw [abs_of_neg h]
    exact le_add_of_nonneg_left (Real.exp_nonneg _)
  · rw [abs_of_nonneg h]
    exact le_add_of_nonneg_right (Real.exp_nonneg _)

/-- Elementary pointwise bound: for `p, a > 0` and `x ≥ 0`,
`x ^ p ≤ (p / a) ^ p * exp (a * x - p)`.  It is the standard "optimisation of
`x ^ p e^{-a x}`" bound, proved here from `log y ≤ y - 1` (in the form
`y ≤ exp (y - 1)`). -/
private lemma rpow_le_mul_exp {p a x : ℝ} (hp : 0 < p) (ha : 0 < a) (hx : 0 ≤ x) :
    x ^ p ≤ (p / a) ^ p * Real.exp (a * x - p) := by
  have hpa : 0 < p / a := div_pos hp ha
  have h1 : a * x / p ≤ Real.exp (a * x / p - 1) := by
    have h := Real.add_one_le_exp (a * x / p - 1)
    linarith
  have hkey : x ≤ (p / a) * Real.exp (a * x / p - 1) := by
    calc x = (p / a) * (a * x / p) := by field_simp
      _ ≤ (p / a) * Real.exp (a * x / p - 1) :=
          mul_le_mul_of_nonneg_left h1 (le_of_lt hpa)
  have h2 : x ^ p ≤ ((p / a) * Real.exp (a * x / p - 1)) ^ p :=
    Real.rpow_le_rpow hx hkey (le_of_lt hp)
  calc x ^ p ≤ ((p / a) * Real.exp (a * x / p - 1)) ^ p := h2
    _ = (p / a) ^ p * Real.exp (a * x / p - 1) ^ p := by
        rw [Real.mul_rpow (le_of_lt hpa) (Real.exp_nonneg _)]
    _ = (p / a) ^ p * Real.exp ((a * x / p - 1) * p) := by
        rw [← Real.exp_mul]
    _ = (p / a) ^ p * Real.exp (a * x - p) := by
        congr 1
        field_simp

/-- The exponential moment bound for a Rademacher sum: for every `t : ℝ`,
`∑_{e} exp (t * ∑_i ε_i(e) a_i) ≤ 2^n * exp (t^2/2 * ∑_i a_i^2)`. -/
private lemma mgf_le (n : ℕ) (a : Fin n → ℝ) (t : ℝ) :
    ∑ e : Fin n → Bool, Real.exp (t * ∑ i, (if e i then (1 : ℝ) else -1) * a i)
      ≤ 2 ^ n * Real.exp (t ^ 2 / 2 * ∑ i, a i ^ 2) := by
  classical
  set g : Fin n → Bool → ℝ := fun i b => Real.exp (t * (if b then a i else -a i)) with hg
  have hprod : ∀ e : Fin n → Bool,
      Real.exp (t * ∑ i, (if e i then (1 : ℝ) else -1) * a i) = ∏ i, g i (e i) := by
    intro e
    have hmul : t * ∑ i, (if e i then (1:ℝ) else -1) * a i
        = ∑ i, t * ((if e i then (1:ℝ) else -1) * a i) := by
      rw [Finset.mul_sum]
    rw [hmul, Real.exp_sum]
    apply Finset.prod_congr rfl
    intro i _
    rw [hg]
    congr 1
    by_cases h : e i <;> simp [h]
  have hstep : (∑ e : Fin n → Bool, Real.exp (t * ∑ i, (if e i then (1:ℝ) else -1) * a i))
      = ∑ e : Fin n → Bool, ∏ i, g i (e i) :=
    Finset.sum_congr rfl (fun e _ => hprod e)
  rw [hstep]
  have hstep2 : (∑ e : Fin n → Bool, ∏ i, g i (e i)) = ∏ i, ∑ b : Bool, g i b := by
    have h := Finset.sum_prod_piFinset (s := (Finset.univ : Finset Bool)) (g := g)
    rw [Fintype.piFinset_univ] at h
    simpa using h
  rw [hstep2]
  have hbool : ∀ i : Fin n, (∑ b : Bool, g i b) = Real.exp (t * a i) + Real.exp (t * (-a i)) := by
    intro i
    rw [Fintype.sum_bool]
    rw [hg]
    simp
  have hcoord : ∀ i : Fin n, (∑ b : Bool, g i b) ≤ 2 * Real.exp (t^2/2 * a i^2) := by
    intro i
    rw [hbool i, show t * (-a i) = -(t * a i) by ring]
    refine (exp_add_exp_neg_le (t * a i)).trans (le_of_eq ?_)
    congr 1
    ring_nf
  have hnonneg : ∀ i : Fin n, 0 ≤ ∑ b : Bool, g i b := by
    intro i
    rw [hbool i]
    exact add_nonneg (Real.exp_nonneg _) (Real.exp_nonneg _)
  refine (Finset.prod_le_prod₀ (fun i _ => hnonneg i) (fun i _ => hcoord i)).trans (le_of_eq ?_)
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  congr 1
  rw [← Real.exp_sum]
  congr 1
  rw [Finset.mul_sum]

theorem exists_khintchine_le_of_two_le :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (p : ℝ) (hp : 2 ≤ p) (a : Fin n → ℝ),
      ((∑ e : Fin n → Bool, |∑ i, (if e i then (1 : ℝ) else -1) * a i| ^ p) / 2 ^ n)
        ≤ (C * p) ^ (p / 2) * (∑ i, a i ^ 2) ^ (p / 2) := by
  refine ⟨2, by norm_num, ?_⟩
  intro n p hp a
  have hp0 : 0 < p := by linarith
  have hp0ne : p ≠ 0 := ne_of_gt hp0
  have hp2pos : 0 < p / 2 := by linarith
  have hp2ne : p / 2 ≠ 0 := ne_of_gt hp2pos
  set σ2 : ℝ := ∑ i, a i ^ 2 with hσ2
  have hσ2eq : (∑ i, a i ^ 2) = σ2 := hσ2.symm
  have hσ2nn : 0 ≤ σ2 := by
    rw [hσ2]; exact Finset.sum_nonneg fun i _ => sq_nonneg (a i)
  rcases eq_or_lt_of_le hσ2nn with hσ0 | hσpos
  · have hsum0 : ∑ i, a i ^ 2 = 0 := by rw [← hσ2]; exact hσ0.symm
    have hall : ∀ i, a i = 0 := by
      intro i
      have hiff := (Finset.sum_eq_zero_iff_of_nonneg (s := (Finset.univ : Finset (Fin n)))
        (f := fun i => a i ^ 2) (fun i _ => sq_nonneg (a i))).mp hsum0
      exact sq_eq_zero_iff.mp (hiff i (Finset.mem_univ i))
    have hzero : ∀ e : Fin n → Bool, |∑ i, (if e i then (1:ℝ) else -1) * a i| ^ p = 0 := by
      intro e
      have hS : (∑ i, (if e i then (1:ℝ) else -1) * a i) = 0 := by
        apply Finset.sum_eq_zero
        intro i _
        rw [hall i, mul_zero]
      rw [hS, abs_zero, Real.zero_rpow hp0ne]
    rw [Finset.sum_eq_zero (fun e _ => hzero e), zero_div, hσ0.symm,
        Real.zero_rpow hp2ne, mul_zero]
  · let S : (Fin n → Bool) → ℝ := fun e => ∑ i, (if e i then (1:ℝ) else -1) * a i
    change ((∑ e : Fin n → Bool, |S e| ^ p) / 2 ^ n)
        ≤ (2 * p) ^ (p / 2) * (∑ i, a i ^ 2) ^ (p / 2)
    set lam : ℝ := Real.sqrt (p / σ2) with hlamdef
    have hpσ2pos : 0 < p / σ2 := div_pos hp0 hσpos
    have hσ2ne : σ2 ≠ 0 := ne_of_gt hσpos
    have hlampos : 0 < lam := Real.sqrt_pos_of_pos hpσ2pos
    have hlam2 : lam ^ 2 = p / σ2 := Real.sq_sqrt hpσ2pos.le
    have h2npos : (0:ℝ) < 2 ^ n := by positivity
    have hSdef : ∀ e : Fin n → Bool, S e = ∑ i, (if e i then (1:ℝ) else -1) * a i :=
      fun e => rfl
    -- pointwise bound summed over the cube
    have hpt : ∀ e : Fin n → Bool, |S e| ^ p ≤ (p / lam) ^ p * Real.exp (lam * |S e| - p) :=
      fun e => rpow_le_mul_exp hp0 hlampos (abs_nonneg _)
    have hsum1 : (∑ e : Fin n → Bool, |S e| ^ p)
        ≤ (p / lam) ^ p * Real.exp (-p) * ∑ e : Fin n → Bool, Real.exp (lam * |S e|) := by
      calc (∑ e : Fin n → Bool, |S e| ^ p)
          ≤ ∑ e : Fin n → Bool, (p / lam) ^ p * Real.exp (lam * |S e| - p) :=
              Finset.sum_le_sum (fun e _ => hpt e)
        _ = ∑ e : Fin n → Bool, (p / lam) ^ p * (Real.exp (lam * |S e|) * Real.exp (-p)) := by
              apply Finset.sum_congr rfl
              intro e _
              congr 1
              rw [sub_eq_add_neg, Real.exp_add]
        _ = ∑ e : Fin n → Bool, ((p / lam) ^ p * Real.exp (-p)) * Real.exp (lam * |S e|) := by
              apply Finset.sum_congr rfl
              intro e _
              ring
        _ = (p / lam) ^ p * Real.exp (-p) * ∑ e : Fin n → Bool, Real.exp (lam * |S e|) := by
              rw [Finset.mul_sum]
    have hmoment1 : (∑ e : Fin n → Bool, Real.exp (lam * S e))
        ≤ 2 ^ n * Real.exp (lam ^ 2 / 2 * σ2) := by
      have hh : (∑ e : Fin n → Bool, Real.exp (lam * S e))
          ≤ 2 ^ n * Real.exp (lam ^ 2 / 2 * ∑ i, a i ^ 2) := mgf_le n a lam
      rwa [hσ2eq] at hh
    have hmoment2 : (∑ e : Fin n → Bool, Real.exp (-(lam * S e)))
        ≤ 2 ^ n * Real.exp (lam ^ 2 / 2 * σ2) := by
      have hh : (∑ e : Fin n → Bool, Real.exp (-(lam * S e)))
          ≤ 2 ^ n * Real.exp (lam ^ 2 / 2 * ∑ i, a i ^ 2) := by
        have h2 := mgf_le n a (-lam)
        rw [show (-lam) ^ 2 = lam ^ 2 by ring] at h2
        simpa only [neg_mul] using h2
      rwa [hσ2eq] at hh
    have hmoment : (∑ e : Fin n → Bool, Real.exp (lam * |S e|))
        ≤ 2 ^ (n+1) * Real.exp (lam^2/2*σ2) := by
      have h3 : (∑ e : Fin n → Bool, Real.exp (lam * |S e|))
          ≤ (∑ e : Fin n → Bool, Real.exp (lam * S e))
            + ∑ e : Fin n → Bool, Real.exp (-(lam * S e)) := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_le_sum
        intro e _
        have habs : lam * |S e| = |lam * S e| := by rw [abs_mul, abs_of_pos hlampos]
        rw [habs]
        exact exp_abs_le (lam * S e)
      calc (∑ e : Fin n → Bool, Real.exp (lam * |S e|))
          ≤ (∑ e : Fin n → Bool, Real.exp (lam * S e))
            + ∑ e : Fin n → Bool, Real.exp (-(lam * S e)) := h3
        _ ≤ 2 ^ n * Real.exp (lam^2/2*σ2) + 2 ^ n * Real.exp (lam^2/2*σ2) :=
              add_le_add hmoment1 hmoment2
        _ = 2 ^ (n+1) * Real.exp (lam^2/2*σ2) := by rw [pow_succ]; ring
    have hnorm : (∑ e : Fin n → Bool, Real.exp (lam * |S e|)) / 2 ^ n
        ≤ 2 * Real.exp (lam^2/2*σ2) := by
      rw [div_le_iff₀ h2npos]
      calc (∑ e : Fin n → Bool, Real.exp (lam * |S e|))
          ≤ 2 ^ (n+1) * Real.exp (lam^2/2*σ2) := hmoment
        _ = (2 * Real.exp (lam^2/2*σ2)) * 2 ^ n := by rw [pow_succ]; ring
    have hlam2sig : lam^2/2*σ2 = p/2 := by
      rw [hlam2]; field_simp
    have hstep : (∑ e : Fin n → Bool, |S e| ^ p) / 2 ^ n
        ≤ 2 * (p / lam) ^ p * Real.exp (-p/2) := by
      calc (∑ e : Fin n → Bool, |S e| ^ p) / 2 ^ n
          ≤ ((p / lam) ^ p * Real.exp (-p)
                * ∑ e : Fin n → Bool, Real.exp (lam * |S e|)) / 2 ^ n :=
              div_le_div_of_nonneg_right hsum1 h2npos.le
        _ = (p / lam) ^ p * Real.exp (-p)
              * ((∑ e : Fin n → Bool, Real.exp (lam * |S e|)) / 2 ^ n) := by ring
        _ ≤ (p / lam) ^ p * Real.exp (-p) * (2 * Real.exp (lam^2/2*σ2)) := by
              apply mul_le_mul_of_nonneg_left hnorm
              exact mul_nonneg
                (le_of_lt (Real.rpow_pos_of_pos (div_pos hp0 hlampos) p))
                (Real.exp_nonneg _)
        _ = 2 * (p / lam) ^ p * Real.exp (-p/2) := by
              rw [hlam2sig]
              rw [show (p / lam) ^ p * Real.exp (-p) * (2 * Real.exp (p/2))
                    = 2 * (p/lam)^p * (Real.exp (-p) * Real.exp (p/2)) by ring,
                  ← Real.exp_add, show -p + p/2 = -p/2 by ring]
    have hpl2 : (p / lam) ^ (2:ℝ) = p * σ2 := by
      rw [Real.rpow_two, div_pow, hlam2]
      field_simp
    have hple : (p / lam) ^ p = p ^ (p/2) * σ2 ^ (p/2) := by
      have h : (p / lam) ^ p = ((p / lam) ^ (2:ℝ)) ^ (p/2) := by
        have h0 := Real.rpow_mul (le_of_lt (div_pos hp0 hlampos)) (2:ℝ) (p/2)
        rwa [show (2:ℝ)*(p/2) = p by ring] at h0
      calc (p / lam) ^ p = ((p / lam) ^ (2:ℝ)) ^ (p/2) := h
        _ = (p * σ2) ^ (p/2) := by rw [hpl2]
        _ = p ^ (p/2) * σ2 ^ (p/2) := Real.mul_rpow hp0.le hσpos.le
    have hexpn : Real.exp (-p/2) ≤ 1 := by
      rw [Real.exp_le_one_iff]; linarith
    have hfinal2 : 2 * (p/lam)^p * Real.exp (-p/2) ≤ 2 * p^(p/2) * σ2^(p/2) := by
      have hbound : 2 * (p/lam)^p * Real.exp (-p/2) ≤ 2 * (p/lam)^p * 1 := by
        apply mul_le_mul_of_nonneg_left hexpn
        exact mul_nonneg (by norm_num)
          (le_of_lt (Real.rpow_pos_of_pos (div_pos hp0 hlampos) p))
      calc 2 * (p/lam)^p * Real.exp (-p/2) ≤ 2 * (p/lam)^p * 1 := hbound
        _ = 2 * p^(p/2) * σ2^(p/2) := by rw [hple]; ring
    have hfinal3 : 2 * p^(p/2) * σ2^(p/2) ≤ (2*p)^(p/2) * σ2^(p/2) := by
      rw [Real.mul_rpow (by norm_num) hp0.le]
      have h2p : (2:ℝ) ≤ 2^(p/2) := by
        calc (2:ℝ) = 2^1 := (Real.rpow_one 2).symm
          _ ≤ 2^(p/2) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      calc 2 * p^(p/2) * σ2^(p/2) = 2 * (p^(p/2)*σ2^(p/2)) := by ring
        _ ≤ 2^(p/2) * (p^(p/2)*σ2^(p/2)) :=
            mul_le_mul_of_nonneg_right h2p
              (mul_nonneg (Real.rpow_nonneg hp0.le _) (Real.rpow_nonneg hσpos.le _))
        _ = (2^(p/2)*p^(p/2)) * σ2^(p/2) := by ring
    rw [hσ2eq]
    exact hstep.trans (hfinal2.trans hfinal3)

end Commons.Analysis.Walsh