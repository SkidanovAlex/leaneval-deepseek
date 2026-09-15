import Submission.Work.GYCorr5

/-!
# The evaluation of `G'₁(0,0)` for the correlation system

`G'_1(0,0) = ∏_{q ∤ W} E_q^{(1)}(0,0)`.  For the degenerate system `θ_i(x) = W·(x + h_i) + 1` the
local factors behave very differently from the §10 case:

* for a prime `q ∤ W` we have `E_q(0,0) = 1 - s_q/q` where `s_q` is the number of distinct residue
  classes of the shifts `h_i` mod `q`; in particular `E_q(0,0) ≤ 1 - 1/q` **for every** prime
  `q ∤ W` (including the primes dividing `Δ`), whereas `E_q(0,0) = 1 + O(q^{-2})` when `q ∤ WΔ`;
* hence `E_q^{(1)}(0,0) ≤ (1-1/q)^{-(a-1)} ≤ 1 + O_a(1/q)` at the `Δ`-primes and
  `E_q^{(1)}(0,0) = 1 + O_a(q^{-5/3})` otherwise.

This gives the Green–Tao factorisation
`G'_1(0,0) ≤ K_a · ∏_{q | Δ}(1 + q^{-1/2})^{C_a}`
which is the source of the `∏_{p | Δ}(1 + O_m(p^{-1/2}))` factor in Proposition GY2.
-/

open Finset
open scoped BigOperators

set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false

namespace GYMaj
namespace Corr

open GYMaj.BoxAvg
open Commons.NumberTheory.Sieve

variable {a : ℕ}

/-! ## 1. The local count of the degenerate system is at most one -/

/-! ## 1b. The Euler factor at `z = z' = 0` -/

/-- The Euler factor of the degenerate system at `z = z' = 0` is `1 + O_a(1/q)`. -/
lemma eulerFactor_zero_le {a W q : ℕ} (hq : q.Prime) (hqW : ¬ q ∣ W) (δ : Fin a → ℤ) :
    ‖eulerFactor a (BoxAvg.vSys W (Ac a) δ) (0 : Fin a → ℂ) (0 : Fin a → ℂ) q‖
      ≤ 1 + (4 : ℝ) ^ a / (q : ℝ) := by
  have hq0 : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq.pos
  have hterm : ∀ σ : PrimeData a,
      ‖BoxAvg.eTerm W (Ac a) δ (0 : Fin a → ℂ) (0 : Fin a → ℂ) q σ‖
        ≤ (if σ = 0 then (1 : ℝ) else 0) + (q : ℝ)⁻¹ := by
    intro σ
    by_cases hσ : σ = 0
    · subst hσ
      have h1 : ‖BoxAvg.eTerm W (Ac a) δ (0 : Fin a → ℂ) (0 : Fin a → ℂ) q 0‖ = 1 := by
        rw [BoxAvg.eTerm, BoxAvg.vSys_zero]
        simp
      rw [h1, if_pos rfl]
      have := inv_nonneg.mpr (le_of_lt hq0)
      linarith
    · have hv := vSys_corr_le (a := a) hq hqW (δ := δ) hσ
      have h1 : ‖BoxAvg.eTerm W (Ac a) δ (0 : Fin a → ℂ) (0 : Fin a → ℂ) q σ‖
          = ‖BoxAvg.vSys W (Ac a) δ q σ‖ := by
        rw [BoxAvg.eTerm]
        simp
      rw [h1, if_neg hσ, zero_add]
      exact hv
  have hsum : (∑ σ : PrimeData a, (if σ = 0 then (1 : ℝ) else 0)) = 1 := by
    rw [Finset.sum_ite_eq' Finset.univ 0 (fun _ => (1 : ℝ)), if_pos (Finset.mem_univ _)]
  have hcard : (∑ _σ : PrimeData a, (q : ℝ)⁻¹) = (4 : ℝ) ^ a * (q : ℝ)⁻¹ := by
    rw [Finset.sum_const, Finset.card_univ, card_primeData, nsmul_eq_mul]
    push_cast
    ring
  rw [eulerFactor_eq_sum_eTerm]
  calc ‖∑ σ : PrimeData a, BoxAvg.eTerm W (Ac a) δ (0 : Fin a → ℂ) (0 : Fin a → ℂ) q σ‖
      ≤ ∑ σ : PrimeData a, ((if σ = 0 then (1 : ℝ) else 0) + (q : ℝ)⁻¹) :=
        le_trans (norm_sum_le _ _) (Finset.sum_le_sum (fun σ _ => hterm σ))
    _ = 1 + (4 : ℝ) ^ a * (q : ℝ)⁻¹ := by
        rw [Finset.sum_add_distrib, hsum, hcard]
    _ = 1 + (4 : ℝ) ^ a / (q : ℝ) := by rw [div_eq_mul_inv]

/-- `E_p^{(3)}` at `z = z' = 0` is `(1 - p^{-1})^a`. -/
lemma E3p_zero {a q : ℕ} (hq : q.Prime) :
    E3p (m := a) (0 : Fin a → ℂ) (0 : Fin a → ℂ) q = (1 - (q : ℂ)⁻¹) ^ a := by
  rw [E3p, if_pos hq]
  have hfac : ∀ j : Fin a, ((1 - (q : ℂ) ^ (-(1 + (0 : Fin a → ℂ) j)))
      * (1 - (q : ℂ) ^ (-(1 + (0 : Fin a → ℂ) j)))
      * (1 - (q : ℂ) ^ (-(1 + (0 : Fin a → ℂ) j + (0 : Fin a → ℂ) j)))⁻¹)
      = (1 - (q : ℂ)⁻¹) := by
    intro j
    have h1 : (-(1 + (0 : Fin a → ℂ) j) : ℂ) = -1 := by simp
    have h2 : (-(1 + (0 : Fin a → ℂ) j + (0 : Fin a → ℂ) j) : ℂ) = -1 := by simp
    rw [h1, h2, Complex.cpow_neg_one]
    have hne : (1 - (q : ℂ)⁻¹) ≠ 0 := by
      intro hc
      have h3 : (q : ℂ) = 1 := by
        have h4 := sub_eq_zero.mp hc
        rw [eq_comm] at h4
        exact inv_eq_one.mp h4
      have h5 : q = 1 := Nat.cast_eq_one.mp h3
      have := hq.two_le
      omega
    rw [show (1 - (q : ℂ)⁻¹) * (1 - (q : ℂ)⁻¹) * (1 - (q : ℂ)⁻¹)⁻¹
        = (1 - (q : ℂ)⁻¹) * ((1 - (q : ℂ)⁻¹) * (1 - (q : ℂ)⁻¹)⁻¹) by ring,
      mul_inv_cancel₀ hne, mul_one]
  rw [Finset.prod_congr rfl (fun j _ => hfac j), Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]

/-- `‖(E_p^{(3)}(0,0))^{-1}‖ ≤ 1 + 2^(a+1)/q` for `q ≥ 2`. -/
lemma E3p_zero_inv_le {a q : ℕ} (hq : 2 ≤ q) :
    ‖(E3p (m := a) (0 : Fin a → ℂ) (0 : Fin a → ℂ) q)⁻¹‖
      ≤ 1 + (2 : ℝ) ^ (a + 1) / (q : ℝ) := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hnorm : ‖(1 - (q : ℂ)⁻¹)‖ = 1 - (q : ℝ)⁻¹ := by
    have h1 : ‖(1 - (q : ℂ)⁻¹)‖ = |1 - (q : ℝ)⁻¹| := by
      have hc : (1 - (q : ℂ)⁻¹) = ((1 - (q : ℝ)⁻¹ : ℝ) : ℂ) := by
        rw [← Complex.ofReal_natCast q, ← Complex.ofReal_inv]
        push_cast
        ring
      rw [hc, Complex.norm_real, Real.norm_eq_abs]
    rw [h1, abs_of_nonneg]
    have h2 : (q : ℝ)⁻¹ ≤ 1 := by rw [inv_le_one₀ hq0]; linarith
    linarith
  by_cases hprime : q.Prime
  · rw [E3p_zero hprime, norm_inv, norm_pow, hnorm]
    have hbase : (1 - (q : ℝ)⁻¹) = ((q : ℝ) - 1) / (q : ℝ) := by field_simp
    rw [hbase, div_pow, inv_div, ← div_pow]
    have hsplit : (q : ℝ) / ((q : ℝ) - 1) = 1 + 1 / ((q : ℝ) - 1) := by
      have h : ((q : ℝ) - 1) ≠ 0 := by linarith
      field_simp
      ring
    rw [hsplit]
    have hx0 : (0 : ℝ) ≤ 1 / ((q : ℝ) - 1) :=
      div_nonneg zero_le_one (by linarith)
    have hx1 : 1 / ((q : ℝ) - 1) ≤ 1 := by
      rw [div_le_one (by linarith : (0 : ℝ) < (q : ℝ) - 1)]
      linarith
    have hb := Commons.Analysis.RealPow.one_add_pow_le_two_pow_mul a (1 / ((q : ℝ) - 1)) hx0 hx1
    refine le_trans hb ?_
    rw [mul_one_div]
    have h2q : (2 : ℝ) ^ a / ((q : ℝ) - 1) ≤ (2 : ℝ) ^ (a + 1) / (q : ℝ) := by
      rw [pow_succ, div_le_iff₀ (by linarith : (0 : ℝ) < (q : ℝ) - 1),
        div_mul_eq_mul_div, le_div_iff₀ hq0]
      have h2a : (0 : ℝ) < (2 : ℝ) ^ a := by positivity
      nlinarith [hq0, hq2, h2a]
    linarith
  · rw [E3p, if_neg hprime, inv_one, norm_one]
    have h5 : (0 : ℝ) ≤ (2 : ℝ) ^ (a + 1) / (q : ℝ) := by positivity
    linarith




/-! ## 4. The pointwise bounds for `E_q^{(1)}(0,0)` -/

/-- The additive constant of the `Δ`-prime bound. -/
noncomputable def Ca (a : ℕ) : ℝ :=
  (4 : ℝ) ^ a + (2 : ℝ) ^ (a + 1) + (4 : ℝ) ^ a * (2 : ℝ) ^ (a + 1)

/-- **The `Δ`-prime bound**: for a prime `q ∤ W`, `‖E_q^{(1)}(0,0)‖ ≤ 1 + C_a/q`. -/
lemma E1p_zero_le {a W q : ℕ} (hq : q.Prime) (hqW : ¬ q ∣ W) {δ : Fin a → ℤ} :
    ‖E1p W (Ac a) δ (0 : Fin a → ℂ) (0 : Fin a → ℂ) q‖ ≤ 1 + Ca a / (q : ℝ) := by
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq.one_le
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq.pos
  have hE := eulerFactor_zero_le (a := a) (W := W) hq hqW δ
  have h3 := E3p_zero_inv_le (a := a) (q := q) hq.two_le
  rw [E1p, if_pos ⟨hq, hqW⟩, div_eq_mul_inv, norm_mul]
  refine le_trans (mul_le_mul hE h3 (norm_nonneg _) (by positivity)) ?_
  have h4 : (0 : ℝ) < (4 : ℝ) ^ a := by positivity
  have h2 : (0 : ℝ) < (2 : ℝ) ^ (a + 1) := by positivity
  have hX : (0 : ℝ) ≤ (4 : ℝ) ^ a / (q : ℝ) := div_nonneg h4.le hq0.le
  have hY : (0 : ℝ) ≤ (2 : ℝ) ^ (a + 1) / (q : ℝ) := div_nonneg h2.le hq0.le
  have hXY : (4 : ℝ) ^ a / (q : ℝ) * ((2 : ℝ) ^ (a + 1) / (q : ℝ))
      ≤ (4 : ℝ) ^ a * (2 : ℝ) ^ (a + 1) / (q : ℝ) := by
    rw [div_mul_div_comm]
    refine div_le_div_of_nonneg_left (by positivity) hq0 ?_
    nlinarith
  have hkey : (4 : ℝ) ^ a / (q : ℝ) + (2 : ℝ) ^ (a + 1) / (q : ℝ)
      + (4 : ℝ) ^ a / (q : ℝ) * ((2 : ℝ) ^ (a + 1) / (q : ℝ))
      ≤ ((4 : ℝ) ^ a + (2 : ℝ) ^ (a + 1) + (4 : ℝ) ^ a * (2 : ℝ) ^ (a + 1)) / (q : ℝ) := by
    have h1 : (4 : ℝ) ^ a / (q : ℝ) + (2 : ℝ) ^ (a + 1) / (q : ℝ)
        = ((4 : ℝ) ^ a + (2 : ℝ) ^ (a + 1)) / (q : ℝ) := by ring
    have h2' : ((4 : ℝ) ^ a + (2 : ℝ) ^ (a + 1)) / (q : ℝ)
        + (4 : ℝ) ^ a * (2 : ℝ) ^ (a + 1) / (q : ℝ)
        = ((4 : ℝ) ^ a + (2 : ℝ) ^ (a + 1) + (4 : ℝ) ^ a * (2 : ℝ) ^ (a + 1)) / (q : ℝ) := by
      ring
    linarith [hXY, h1, h2']
  have hexpand : (1 + (4 : ℝ) ^ a / (q : ℝ)) * (1 + (2 : ℝ) ^ (a + 1) / (q : ℝ))
      = 1 + ((4 : ℝ) ^ a / (q : ℝ) + (2 : ℝ) ^ (a + 1) / (q : ℝ)
          + (4 : ℝ) ^ a / (q : ℝ) * ((2 : ℝ) ^ (a + 1) / (q : ℝ))) := by ring
  rw [hexpand, Ca]
  linarith [hkey]

/-- The multiplicative constant of the off-`Δ` bound. -/
noncomputable def Cb (a : ℕ) : ℝ := 2 * 100000 * ((a : ℝ) ^ 3 + 1) * (4 : ℝ) ^ a

/-- **The off-`Δ` bound**: for a prime `q ∤ W·Δ` with `q ≥ (6a)^2+2`,
`‖E_q^{(1)}(0,0) - 1‖ ≤ C_b(a)·q^{-4/3}`. -/
lemma E1p_zero_close {a W n : ℕ} (ha : 1 ≤ a) (hW0 : 0 < W) (hn : n.Prime) (hnW : ¬ n ∣ W)
    {δ : Fin a → ℤ} (hnΔ : ¬ n ∣ Delta δ) (hnbig : (6 * a) ^ 2 + 2 ≤ n) :
    ‖E1p W (Ac a) δ (0 : Fin a → ℂ) (0 : Fin a → ℂ) n - 1‖
      ≤ Cb a * (n : ℝ) ^ (-(4 / 3 : ℝ)) := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn.one_le
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn.pos
  have hσ0 : (0 : ℝ) ≤ 1 / (6 * (a : ℝ)) := by
    have : (0 : ℝ) < a := by exact_mod_cast (by omega : 0 < a)
    positivity
  have h4σ : 4 * (1 / (6 * (a : ℝ))) ≤ 1 := le_of_lt (sixth_small ha).1
  have hz0 : ∀ j : Fin a, -(1 / (6 * (a : ℝ))) ≤ ((0 : Fin a → ℂ) j).re := by
    intro j
    simp only [Pi.zero_apply, Complex.zero_re]
    linarith
  have hK : max 2 ((6 * a) ^ 2 + 2) ≤ n := max_le hn.two_le hnbig
  have hsmall := hsmall_of_large (σ₀ := 1 / (6 * (a : ℝ))) hσ0 h4σ ha hK
  have hb := CorrB.E1p_bound_corr (m := a) (W := W) (h := δ) ha hn hnW hW0 hnΔ hσ0 h4σ
    hz0 hz0 hsmall
  -- the two exponents
  have hexp1 : (2 : ℝ) * (1 / (6 * (a : ℝ))) * (a : ℝ) = 1 / 3 := by
    field_simp; ring
  have hexp2 : -2 + 4 * (1 / (6 * (a : ℝ))) ≤ -(4 / 3 : ℝ) := by
    have ha1 : (1 : ℝ) ≤ a := by exact_mod_cast ha
    have h6 : (0 : ℝ) < 6 * (a : ℝ) := by linarith
    have hkey : 4 * (1 / (6 * (a : ℝ))) ≤ 2 / 3 := by
      rw [show 4 * (1 / (6 * (a : ℝ))) = 4 / (6 * (a : ℝ)) by ring, div_le_iff₀ h6]
      nlinarith
    linarith
  have hupper : (n : ℝ) ^ (-2 + 4 * (1 / (6 * (a : ℝ)))) ≤ (n : ℝ) ^ (-(4 / 3 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hn1 hexp2
  have hexp1b : -2 + 2 * (1 / (6 * (a : ℝ))) * (a : ℝ) ≤ -(4 / 3 : ℝ) := by
    rw [hexp1]; norm_num
  have hlower : (n : ℝ) ^ (-2 + 2 * (1 / (6 * (a : ℝ))) * (a : ℝ)) ≤ (n : ℝ) ^ (-(4 / 3 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hn1 hexp1b
  rw [Cb]
  have hcoef : (0 : ℝ) ≤ 100000 * ((a : ℝ) ^ 3 + 1) * (4 : ℝ) ^ a := by positivity
  have hsum2 : (n : ℝ) ^ (-2 + 2 * (1 / (6 * (a : ℝ))) * (a : ℝ))
      + (n : ℝ) ^ (-2 + 4 * (1 / (6 * (a : ℝ)))) ≤ 2 * (n : ℝ) ^ (-(4 / 3 : ℝ)) := by
    linarith [hupper, hlower]
  calc ‖E1p W (Ac a) δ (0 : Fin a → ℂ) (0 : Fin a → ℂ) n - 1‖
      ≤ 100000 * ((a : ℝ) ^ 3 + 1) * (4 : ℝ) ^ a
        * ((n : ℝ) ^ (-2 + 2 * (1 / (6 * (a : ℝ))) * (a : ℝ))
          + (n : ℝ) ^ (-2 + 4 * (1 / (6 * (a : ℝ))))) := hb
    _ ≤ 100000 * ((a : ℝ) ^ 3 + 1) * (4 : ℝ) ^ a * (2 * (n : ℝ) ^ (-(4 / 3 : ℝ))) :=
        mul_le_mul_of_nonneg_left hsum2 hcoef
    _ = (2 * 100000 * ((a : ℝ) ^ 3 + 1) * (4 : ℝ) ^ a) * (n : ℝ) ^ (-(4 / 3 : ℝ)) := by ring


/-! ## 5. Two-sided pointwise bounds at the `Δ`-primes -/

/-- The Euler factor at `z = z' = 0` differs from `1 - a/q` by `O_a(1/q)`. -/
lemma eulerFactor_zero_sub {a W q : ℕ} (hq : q.Prime) (hqW : ¬ q ∣ W) {δ : Fin a → ℤ} :
    ‖eulerFactor a (vSys W (Ac a) δ) (0 : Fin a → ℂ) (0 : Fin a → ℂ) q
        - ((1 - (a : ℝ) / (q : ℝ) : ℝ) : ℂ)‖ ≤ ((4 : ℝ) ^ a + a) / (q : ℝ) := by
  have hq0 : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq.pos
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq.one_le
  have hpt : ∀ σ : PrimeData a,
      ‖eTerm W (Ac a) δ (0 : Fin a → ℂ) (0 : Fin a → ℂ) q σ
        - (if σ = 0 then (1 : ℂ) else 0)‖ ≤ (if σ = 0 then (0 : ℝ) else (q : ℝ)⁻¹) := by
    intro σ
    by_cases hσ : σ = 0
    · subst hσ
      have h0 : eTerm W (Ac a) δ (0 : Fin a → ℂ) (0 : Fin a → ℂ) q (0 : PrimeData a) = 1 := by
        rw [BoxAvg.eTerm, BoxAvg.vSys_zero]
        have hX : (0 : PrimeData a).X = ∅ := rfl
        have hX' : (0 : PrimeData a).X' = ∅ := rfl
        rw [hX, hX']
        simp
      rw [h0, if_pos rfl, sub_self, norm_zero, if_pos rfl]
    · have h1 : eTerm W (Ac a) δ (0 : Fin a → ℂ) (0 : Fin a → ℂ) q σ
          - (if σ = 0 then (1 : ℂ) else 0)
          = eTerm W (Ac a) δ (0 : Fin a → ℂ) (0 : Fin a → ℂ) q σ := by
        rw [if_neg hσ, sub_zero]
      have h2 : ‖eTerm W (Ac a) δ (0 : Fin a → ℂ) (0 : Fin a → ℂ) q σ‖
          = ‖vSys W (Ac a) δ q σ‖ := by
        rw [BoxAvg.eTerm]; simp
      rw [h1, h2, if_neg hσ]
      exact vSys_corr_le hq hqW (δ := δ) hσ
  have hsum2 : (∑ σ : PrimeData a, (if σ = 0 then (0 : ℝ) else (q : ℝ)⁻¹))
      = ((4 : ℝ) ^ a - 1) * (q : ℝ)⁻¹ := by
    rw [← Finset.sum_erase_add (Finset.univ : Finset (PrimeData a))
      (fun σ => if σ = 0 then (0 : ℝ) else (q : ℝ)⁻¹) (Finset.mem_univ (0 : PrimeData a))]
    have hf : (if (0 : PrimeData a) = 0 then (0 : ℝ) else (q : ℝ)⁻¹) = 0 := by simp
    have hrest : (∑ σ ∈ (Finset.univ : Finset (PrimeData a)).erase 0,
          (if σ = 0 then (0 : ℝ) else (q : ℝ)⁻¹)) = ((4 : ℝ) ^ a - 1) * (q : ℝ)⁻¹ := by
      have hcongr : ∀ σ ∈ (Finset.univ : Finset (PrimeData a)).erase 0,
          (if σ = 0 then (0 : ℝ) else (q : ℝ)⁻¹) = (q : ℝ)⁻¹ := by
        intro σ hσ
        rw [Finset.mem_erase] at hσ
        simp [hσ.1]
      rw [Finset.sum_congr rfl hcongr, Finset.sum_const, nsmul_eq_mul,
        Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, card_primeData]
      have h4a : (1 : ℕ) ≤ 4 ^ a := one_le_pow₀ (by norm_num)
      rw [Nat.cast_sub h4a, Nat.cast_pow, Nat.cast_ofNat]
      ring
    rw [hf, hrest, add_zero]
  have hbound : ‖(∑ σ : PrimeData a, eTerm W (Ac a) δ (0 : Fin a → ℂ) (0 : Fin a → ℂ) q σ) - 1‖
      ≤ ((4 : ℝ) ^ a - 1) * (q : ℝ)⁻¹ := by
    have hsplit : (∑ σ : PrimeData a, eTerm W (Ac a) δ (0 : Fin a → ℂ) (0 : Fin a → ℂ) q σ) - 1
        = ∑ σ : PrimeData a, (eTerm W (Ac a) δ (0 : Fin a → ℂ) (0 : Fin a → ℂ) q σ
            - (if σ = 0 then (1 : ℂ) else 0)) := by
      rw [Finset.sum_sub_distrib]
      have h0 : (∑ σ : PrimeData a, (if σ = 0 then (1 : ℂ) else 0)) = 1 := by
        rw [Finset.sum_ite_eq' Finset.univ 0 (fun _ => (1 : ℂ)), if_pos (Finset.mem_univ _)]
      rw [h0]
    rw [hsplit]
    refine le_trans (norm_sum_le _ _) ?_
    refine le_trans (Finset.sum_le_sum (fun σ _ => hpt σ)) ?_
    rw [hsum2]
  rw [eulerFactor_eq_sum_eTerm]
  have hmain : ‖(∑ σ : PrimeData a, eTerm W (Ac a) δ (0 : Fin a → ℂ) (0 : Fin a → ℂ) q σ)
      - ((1 - (a : ℝ) / (q : ℝ) : ℝ) : ℂ)‖
      ≤ ((4 : ℝ) ^ a - 1) * (q : ℝ)⁻¹ + (a : ℝ) / (q : ℝ) := by
    have h1 : (∑ σ : PrimeData a, eTerm W (Ac a) δ (0 : Fin a → ℂ) (0 : Fin a → ℂ) q σ)
        - ((1 - (a : ℝ) / (q : ℝ) : ℝ) : ℂ)
        = ((∑ σ : PrimeData a, eTerm W (Ac a) δ (0 : Fin a → ℂ) (0 : Fin a → ℂ) q σ) - 1)
          + (((a : ℝ) / (q : ℝ) : ℝ) : ℂ) := by
      push_cast
      ring
    rw [h1]
    refine le_trans (norm_add_le _ _) ?_
    have h2 : ‖(((a : ℝ) / (q : ℝ) : ℝ) : ℂ)‖ = (a : ℝ) / (q : ℝ) := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
      positivity
    rw [h2]
    linarith [hbound]
  refine le_trans hmain ?_
  have h4 : (0 : ℝ) ≤ (4 : ℝ) ^ a := by positivity
  have ha0 : (0 : ℝ) ≤ (a : ℝ) := Nat.cast_nonneg a
  rw [div_eq_mul_inv, div_eq_mul_inv, ← add_mul]
  refine mul_le_mul_of_nonneg_right ?_ (inv_nonneg.mpr hq0.le)
  linarith [h4, hq1, ha0]

/-- `(4^a + 2a)·2^a ≤ 24^a`. -/
lemma four_pow_add_mul_le {a : ℕ} (ha1 : 1 ≤ a) :
    ((4 : ℝ) ^ a + 2 * (a : ℝ)) * (2 : ℝ) ^ a ≤ (24 : ℝ) ^ a := by
  have ht : (1 : ℝ) ≤ (2 : ℝ) ^ a := one_le_pow₀ (by norm_num)
  have ht0 : (0 : ℝ) < (2 : ℝ) ^ a := lt_of_lt_of_le one_pos ht
  have ha : (a : ℝ) ≤ (2 : ℝ) ^ a := by
    have h1 : a ≤ 2 ^ a := le_of_lt Nat.lt_two_pow_self
    have h2 : (a : ℝ) ≤ ((2 ^ a : ℕ) : ℝ) := by exact_mod_cast h1
    push_cast at h2
    exact h2
  have h3 : (3 : ℝ) ≤ (3 : ℝ) ^ a := by
    have h1 : (1 : ℝ) ≤ (3 : ℝ) := by norm_num
    have h2 : (3 : ℝ) ^ 1 ≤ (3 : ℝ) ^ a := pow_le_pow_right₀ h1 ha1
    simpa using h2
  have h1 : ((4 : ℝ) ^ a + 2 * (a : ℝ)) * (2 : ℝ) ^ a
      ≤ (3 : ℝ) * ((2 : ℝ) ^ a * ((2 : ℝ) ^ a * (2 : ℝ) ^ a)) := by
    rw [show (4 : ℝ) ^ a = (2 : ℝ) ^ a * (2 : ℝ) ^ a by rw [← mul_pow]; norm_num]
    have ha2 : (a : ℝ) * (2 : ℝ) ^ a ≤ (2 : ℝ) ^ a * (2 : ℝ) ^ a :=
      mul_le_mul_of_nonneg_right ha (le_of_lt ht0)
    nlinarith [ha2, ht, ht0, sq_nonneg ((2 : ℝ) ^ a)]
  have h2 : (3 : ℝ) * ((2 : ℝ) ^ a * ((2 : ℝ) ^ a * (2 : ℝ) ^ a))
      ≤ (3 : ℝ) ^ a * ((2 : ℝ) ^ a * ((2 : ℝ) ^ a * (2 : ℝ) ^ a)) :=
    mul_le_mul_of_nonneg_right h3 (by positivity)
  have e1 : (2 : ℝ) ^ a * ((2 : ℝ) ^ a * (2 : ℝ) ^ a) = (8 : ℝ) ^ a := by
    rw [← mul_pow, ← mul_pow]
    norm_num
  have h4 : (3 : ℝ) ^ a * ((2 : ℝ) ^ a * ((2 : ℝ) ^ a * (2 : ℝ) ^ a)) = (24 : ℝ) ^ a := by
    rw [e1, ← mul_pow]
    norm_num
  linarith [h1, h2, h4.le, h4.ge]

/-- **The two-sided bound at the `Δ`-primes**: `‖E_q^{(1)}(0,0) - 1‖ ≤ 10^a/q`. -/
lemma E1p_zero_abs_le {a W q : ℕ} (ha : 1 ≤ a) (hq : q.Prime) (hqW : ¬ q ∣ W)
    {δ : Fin a → ℤ} :
    ‖E1p W (Ac a) δ (0 : Fin a → ℂ) (0 : Fin a → ℂ) q - 1‖ ≤ (24 : ℝ) ^ a / (q : ℝ) := by
  have ha0 : (0 : ℝ) < (a : ℝ) := by exact_mod_cast (by omega : 0 < a)
  have hq2 : (2 : ℕ) ≤ q := hq.two_le
  have hq0 : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq.pos
  have hqinv0 : (0 : ℝ) ≤ (q : ℝ)⁻¹ := inv_nonneg.mpr hq0.le
  have hqinv : (q : ℝ)⁻¹ ≤ 1 / 2 := by
    simpa only [one_div] using
      one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) (by exact_mod_cast hq2 : (2 : ℝ) ≤ q)
  have hF := eulerFactor_zero_sub (a := a) (W := W) hq hqW (δ := δ)
  have hBern : 1 - (a : ℝ) / (q : ℝ) ≤ (1 - (q : ℝ)⁻¹) ^ a := by
    have h2 := one_add_mul_le_pow (R := ℝ) (a := -(q : ℝ)⁻¹) (by linarith : -2 ≤ -(q : ℝ)⁻¹) a
    rw [show (1 : ℝ) + -(q : ℝ)⁻¹ = 1 - (q : ℝ)⁻¹ by ring] at h2
    calc 1 - (a : ℝ) / (q : ℝ) = 1 + (a : ℝ) * (-(q : ℝ)⁻¹) := by ring
      _ ≤ (1 - (q : ℝ)⁻¹) ^ a := h2
  have hone : (1 - (q : ℝ)⁻¹) ^ a ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
  have hGreal : E3p (m := a) (0 : Fin a → ℂ) (0 : Fin a → ℂ) q
      = (((1 - (q : ℝ)⁻¹) ^ a : ℝ) : ℂ) := by
    rw [E3p_zero hq]
    have hc : (1 - (q : ℂ)⁻¹) = ((1 - (q : ℝ)⁻¹ : ℝ) : ℂ) := by
      rw [← Complex.ofReal_natCast q, ← Complex.ofReal_inv, ← Complex.ofReal_one,
        ← Complex.ofReal_sub]
    rw [hc, ← Complex.ofReal_pow]
  have hGnorm : ‖E3p (m := a) (0 : Fin a → ℂ) (0 : Fin a → ℂ) q‖ = (1 - (q : ℝ)⁻¹) ^ a := by
    rw [hGreal, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (by linarith) _)]
  have hGinv : ((2 : ℝ)⁻¹) ^ a ≤ (1 - (q : ℝ)⁻¹) ^ a :=
    pow_le_pow_left₀ (by norm_num) (by linarith : (2 : ℝ)⁻¹ ≤ 1 - (q : ℝ)⁻¹) a
  have hB : ‖(((1 - (a : ℝ) / (q : ℝ)) : ℝ) : ℂ)
      - (((1 - (q : ℝ)⁻¹) ^ a : ℝ) : ℂ)‖ ≤ (a : ℝ) / (q : ℝ) := by
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_le]
    constructor
    · linarith [hBern, hone]
    · linarith [hBern]
  have hFG : E1p W (Ac a) δ (0 : Fin a → ℂ) (0 : Fin a → ℂ) q
      = eulerFactor a (vSys W (Ac a) δ) (0 : Fin a → ℂ) (0 : Fin a → ℂ) q
        / E3p (m := a) (0 : Fin a → ℂ) (0 : Fin a → ℂ) q := by
    rw [E1p, if_pos ⟨hq, hqW⟩]
  have hden : E3p (m := a) (0 : Fin a → ℂ) (0 : Fin a → ℂ) q ≠ 0 := by
    rw [hGreal]
    exact Complex.ofReal_ne_zero.mpr (pow_ne_zero _ (by linarith))
  have hstep : ‖E1p W (Ac a) δ (0 : Fin a → ℂ) (0 : Fin a → ℂ) q - 1‖
      = ‖eulerFactor a (vSys W (Ac a) δ) (0 : Fin a → ℂ) (0 : Fin a → ℂ) q
            - E3p (m := a) (0 : Fin a → ℂ) (0 : Fin a → ℂ) q‖
          / ‖E3p (m := a) (0 : Fin a → ℂ) (0 : Fin a → ℂ) q‖ := by
    rw [hFG, div_sub_one hden, norm_div]
  have hnum : ‖eulerFactor a (vSys W (Ac a) δ) (0 : Fin a → ℂ) (0 : Fin a → ℂ) q
        - E3p (m := a) (0 : Fin a → ℂ) (0 : Fin a → ℂ) q‖
      ≤ ((4 : ℝ) ^ a + 2 * (a : ℝ)) / (q : ℝ) := by
    have h1 : eulerFactor a (vSys W (Ac a) δ) (0 : Fin a → ℂ) (0 : Fin a → ℂ) q
          - E3p (m := a) (0 : Fin a → ℂ) (0 : Fin a → ℂ) q
        = (eulerFactor a (vSys W (Ac a) δ) (0 : Fin a → ℂ) (0 : Fin a → ℂ) q
            - (((1 - (a : ℝ) / (q : ℝ)) : ℝ) : ℂ))
          + ((((1 - (a : ℝ) / (q : ℝ)) : ℝ) : ℂ) - (((1 - (q : ℝ)⁻¹) ^ a : ℝ) : ℂ)) := by
      rw [hGreal]; ring
    rw [h1]
    refine le_trans (norm_add_le _ _) ?_
    calc ‖eulerFactor a (vSys W (Ac a) δ) (0 : Fin a → ℂ) (0 : Fin a → ℂ) q
            - (((1 - (a : ℝ) / (q : ℝ)) : ℝ) : ℂ)‖
          + ‖(((1 - (a : ℝ) / (q : ℝ)) : ℝ) : ℂ)
              - (((1 - (q : ℝ)⁻¹) ^ a : ℝ) : ℂ)‖
        ≤ ((4 : ℝ) ^ a + a) / (q : ℝ) + (a : ℝ) / (q : ℝ) := add_le_add hF hB
      _ = ((4 : ℝ) ^ a + 2 * (a : ℝ)) / (q : ℝ) := by
          rw [← add_div]; congr 1; ring
  rw [hstep]
  have hX : (0 : ℝ) ≤ ((4 : ℝ) ^ a + 2 * (a : ℝ)) / (q : ℝ) := by positivity
  have hGlev : ((2 : ℝ)⁻¹) ^ a ≤ ‖E3p (m := a) (0 : Fin a → ℂ) (0 : Fin a → ℂ) q‖ := by
    rw [hGnorm]; exact hGinv
  calc ‖eulerFactor a (vSys W (Ac a) δ) (0 : Fin a → ℂ) (0 : Fin a → ℂ) q
        - E3p (m := a) (0 : Fin a → ℂ) (0 : Fin a → ℂ) q‖
        / ‖E3p (m := a) (0 : Fin a → ℂ) (0 : Fin a → ℂ) q‖
      ≤ (((4 : ℝ) ^ a + 2 * (a : ℝ)) / (q : ℝ))
          / ‖E3p (m := a) (0 : Fin a → ℂ) (0 : Fin a → ℂ) q‖ :=
        div_le_div_of_nonneg_right hnum (norm_nonneg _)
    _ ≤ (((4 : ℝ) ^ a + 2 * (a : ℝ)) / (q : ℝ)) / (((2 : ℝ)⁻¹) ^ a) :=
        div_le_div_of_nonneg_left hX (by positivity) hGlev
    _ = ((4 : ℝ) ^ a + 2 * (a : ℝ)) * (2 : ℝ) ^ a / (q : ℝ) := by
        rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv, inv_pow, inv_inv]
        ring
    _ ≤ (24 : ℝ) ^ a / (q : ℝ) := by
        refine div_le_div_of_nonneg_right (four_pow_add_mul_le ha) hq0.le

/-! ## 6. The majorant of `E_q^{(1)}(0,0) - 1` and the product bound -/

/-- `n^{-1} ≤ n^{-1/2}` for `n ≥ 1`. -/
lemma inv_le_rpow_neg_half {n : ℕ} (hn : 1 ≤ n) : (n : ℝ)⁻¹ ≤ (n : ℝ) ^ (-(1 / 2 : ℝ)) := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have h := Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num : (-(1 : ℝ)) ≤ -(1 / 2 : ℝ))
  rwa [Real.rpow_neg_one] at h

/-- `log (1 + x) ≥ x/2` for `0 ≤ x ≤ 1`. -/
lemma half_mul_le_log_one_add {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    x / 2 ≤ Real.log (1 + x) := by
  have h1 : Real.log (1 / (1 + x)) ≤ 1 / (1 + x) - 1 :=
    Real.log_le_sub_one_of_pos (by positivity)
  have h2 : Real.log (1 / (1 + x)) = -Real.log (1 + x) := by
    rw [Real.log_div (by norm_num) (by positivity), Real.log_one, zero_sub]
  rw [h2] at h1
  have h3 : 1 / (1 + x) - 1 = -(x / (1 + x)) := by
    field_simp
    ring
  rw [h3] at h1
  have h4 : x / 2 ≤ x / (1 + x) :=
    div_le_div_of_nonneg_left hx0 (by linarith) (by linarith)
  linarith [h1, h4]

/-- `log (1 + n^{-1/2}) ≥ n^{-1/2}/2`. -/
lemma half_rpow_le_log {n : ℕ} (hn : 1 ≤ n) :
    (n : ℝ) ^ (-(1 / 2 : ℝ)) / 2 ≤ Real.log (1 + (n : ℝ) ^ (-(1 / 2 : ℝ))) := by
  refine half_mul_le_log_one_add (Real.rpow_nonneg (by positivity) _) ?_
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have h := Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num : (-(1 / 2 : ℝ)) ≤ 0)
  rwa [Real.rpow_zero] at h

/-- The multiplicative constant of the `Δ`-prime majorant.  It must dominate both the constant
`2·24^a` needed for `‖E_q^{(1)}(0,0) - 1‖ ≤ 24^a/q` and the constant `2·K0 a` needed to absorb the
uniform-in-`Δ` estimate `‖E_q^{(1)} - 1‖ ≤ K0 a · q^{-2/3}` into the factor `LamD`. -/
noncomputable def Da (a : ℕ) : ℝ := max (2 * (24 : ℝ) ^ a) (2 * K0 a)

/-- The multiplicative constant of the off-`Δ` majorant. -/
noncomputable def Cc (a : ℕ) : ℝ :=
  max (Cb a) ((24 : ℝ) ^ a * (((6 * a) ^ 2 + 2 : ℕ) : ℝ) ^ (4 / 3 : ℝ))

lemma Da_nonneg (a : ℕ) : 0 ≤ Da a := by
  unfold Da
  exact le_trans (by positivity : (0 : ℝ) ≤ 2 * (24 : ℝ) ^ a) (le_max_left _ _)
lemma Cb_nonneg (a : ℕ) : 0 ≤ Cb a := by unfold Cb; positivity
lemma Cc_nonneg (a : ℕ) : 0 ≤ Cc a :=
  le_trans (Cb_nonneg a) (le_max_left _ _)

/-- **The pointwise majorant** of `‖E_q^{(1)}(0,0) - 1‖`. -/
lemma u_le {a W n : ℕ} (ha : 1 ≤ a) (hW0 : 0 < W) {δ : Fin a → ℤ} (hΔ0 : Delta δ ≠ 0) :
    ‖E1p W (Ac a) δ (0 : Fin a → ℂ) (0 : Fin a → ℂ) n - 1‖ ≤
      if n ∈ (Delta δ).primeFactors then Da a * Real.log (1 + (n : ℝ) ^ (-(1 / 2 : ℝ)))
      else if n = 0 then 0 else Cc a * (n : ℝ) ^ (-(4 / 3 : ℝ)) := by
  by_cases hS : n ∈ (Delta δ).primeFactors
  · rw [if_pos hS]
    have hnprime : n.Prime := (Nat.mem_primeFactors.mp hS).1
    have hn1 : 1 ≤ n := hnprime.one_le
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hnprime.pos
    have hx1 : (n : ℝ) ^ (-(1 / 2 : ℝ)) ≤ 1 := by
      have h := Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn1 : (1 : ℝ) ≤ n)
        (by norm_num : (-(1 / 2 : ℝ)) ≤ 0)
      rwa [Real.rpow_zero] at h
    have hlog := half_rpow_le_log hn1
    by_cases hnW : n ∣ W
    · rw [E1p, if_neg (fun hc : n.Prime ∧ ¬ n ∣ W => hc.2 hnW), sub_self, norm_zero]
      have hx0 : (0 : ℝ) ≤ (n : ℝ) ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hn0.le _
      exact mul_nonneg (Da_nonneg a) (Real.log_nonneg (by linarith))
    · have hb := E1p_zero_abs_le (a := a) (W := W) ha hnprime hnW (δ := δ)
      refine le_trans hb ?_
      have hinv := inv_le_rpow_neg_half hn1
      have hgoal : (24 : ℝ) ^ a / (n : ℝ)
          ≤ 2 * (24 : ℝ) ^ a * ((n : ℝ) ^ (-(1 / 2 : ℝ)) / 2) := by
        have h2 : (24 : ℝ) ^ a / (n : ℝ) = (24 : ℝ) ^ a * (n : ℝ)⁻¹ := by rw [div_eq_mul_inv]
        have h3 : 2 * (24 : ℝ) ^ a * ((n : ℝ) ^ (-(1 / 2 : ℝ)) / 2)
            = (24 : ℝ) ^ a * (n : ℝ) ^ (-(1 / 2 : ℝ)) := by ring
        rw [h2, h3]
        exact mul_le_mul_of_nonneg_left hinv (by positivity)
      refine le_trans hgoal ?_
      exact mul_le_mul (le_max_left _ _) hlog (by positivity) (Da_nonneg a)
  · rw [if_neg hS]
    rcases Nat.eq_zero_or_pos n with hn0 | hnpos
    · subst hn0
      rw [if_pos rfl, E1p,
        if_neg (fun hc : (0 : ℕ).Prime ∧ ¬ 0 ∣ W => hc.1.ne_zero rfl)]
      rw [sub_self, norm_zero]
    · rw [if_neg (ne_of_gt hnpos)]
      by_cases hnp : n.Prime
      · by_cases hnW : n ∣ W
        · rw [E1p, if_neg (fun hc : n.Prime ∧ ¬ n ∣ W => hc.2 hnW), sub_self, norm_zero]
          exact mul_nonneg (Cc_nonneg a) (Real.rpow_nonneg (by positivity) _)
        · have hnΔ : ¬ n ∣ Delta δ := fun hd =>
            hS (Nat.mem_primeFactors.mpr ⟨hnp, hd, hΔ0⟩)
          have hn1 : 1 ≤ n := hnp.one_le
          have hnR0 : (0 : ℝ) < n := by exact_mod_cast hnp.pos
          by_cases hnbig : (6 * a) ^ 2 + 2 ≤ n
          · have hb := E1p_zero_close (a := a) (W := W) ha hW0 hnp hnW (δ := δ) hnΔ hnbig
            refine le_trans hb ?_
            rw [Cc]
            exact mul_le_mul_of_nonneg_right (le_max_left _ _)
              (Real.rpow_nonneg (by positivity) _)
          · have hb := E1p_zero_abs_le (a := a) (W := W) ha hnp hnW (δ := δ)
            refine le_trans hb ?_
            have hn1' : (1 : ℝ) ≤ n := by exact_mod_cast hn1
            have hK : (0 : ℝ) < (((6 * a) ^ 2 + 2 : ℕ) : ℝ) := by positivity
            have hnK : (n : ℝ) ≤ (((6 * a) ^ 2 + 2 : ℕ) : ℝ) := by
              exact_mod_cast (le_of_lt (not_le.mp hnbig))
            have hkey : (n : ℝ) ^ (1 / 3 : ℝ)
                ≤ (((6 * a) ^ 2 + 2 : ℕ) : ℝ) ^ (4 / 3 : ℝ) := by
              have h2 : (n : ℝ) ^ (1 / 3 : ℝ) ≤ (n : ℝ) ^ (4 / 3 : ℝ) :=
                Real.rpow_le_rpow_of_exponent_le hn1' (by norm_num)
              have h3 : (n : ℝ) ^ (4 / 3 : ℝ)
                  ≤ (((6 * a) ^ 2 + 2 : ℕ) : ℝ) ^ (4 / 3 : ℝ) :=
                Real.rpow_le_rpow hnR0.le hnK (by norm_num)
              linarith
            have h1 : (24 : ℝ) ^ a / (n : ℝ)
                ≤ (24 : ℝ) ^ a * ((((6 * a) ^ 2 + 2 : ℕ) : ℝ) ^ (4 / 3 : ℝ))
                    * (n : ℝ) ^ (-(4 / 3 : ℝ)) := by
              rw [div_eq_mul_inv, mul_assoc]
              refine mul_le_mul_of_nonneg_left ?_ (by positivity)
              have hfac : (n : ℝ) ^ (1 / 3 : ℝ) * (n : ℝ) ^ (-(4 / 3 : ℝ)) = (n : ℝ)⁻¹ := by
                rw [← Real.rpow_add hnR0]
                norm_num
                rw [Real.rpow_neg_one]
              rw [← hfac]
              exact mul_le_mul_of_nonneg_right hkey (Real.rpow_nonneg hnR0.le _)
            refine le_trans h1 ?_
            rw [Cc]
            exact mul_le_mul_of_nonneg_right (le_max_right _ _)
              (Real.rpow_nonneg (by positivity) _)
      · rw [E1p, if_neg (fun hc : n.Prime ∧ ¬ n ∣ W => hnp hc.1), sub_self, norm_zero]
        exact mul_nonneg (Cc_nonneg a) (Real.rpow_nonneg (by positivity) _)

/-! ## 7. The product bound for `G'₁(0,0)` -/

/-- **The Green–Tao factorisation of `G'_1(0,0)`**: the product `∏_{q ∤ W}E_q^{(1)}(0,0)` is
dominated by a constant times `∏_{q | Δ}(1 + q^{-1/2})^{D_a}`. -/
theorem G1u_zero_bound {a W : ℕ} (ha : 1 ≤ a) (hW0 : 0 < W) {δ : Fin a → ℤ}
    (hΔ0 : Delta δ ≠ 0) :
    ‖G1u W (Ac a) δ (0 : Fin a → ℂ) (0 : Fin a → ℂ)‖
      ≤ Real.exp (Cc a * (∑' n : ℕ, (n : ℝ) ^ (-(4 / 3 : ℝ))))
        * ∏ q ∈ (Delta δ).primeFactors, (1 + (q : ℝ) ^ (-(1 / 2 : ℝ))) ^ (Da a) := by
  set S : Finset ℕ := (Delta δ).primeFactors with hSdef
  set u : ℕ → ℂ := fun n => E1p W (Ac a) δ (0 : Fin a → ℂ) (0 : Fin a → ℂ) n - 1 with hudef
  set x : ℕ → ℝ := fun n => if n ∈ S then Da a * Real.log (1 + (n : ℝ) ^ (-(1 / 2 : ℝ))) else 0
    with hxdef
  set y : ℕ → ℝ := fun n =>
    if n ∈ S then 0 else (if n = 0 then 0 else Cc a * (n : ℝ) ^ (-(4 / 3 : ℝ))) with hydef
  have hx : Summable x := by
    refine summable_of_ne_finset_zero (f := x) (s := S) (fun n hn => ?_)
    rw [hxdef]
    simp [hn]
  have hy0 : ∀ n, 0 ≤ y n := by
    intro n
    simp only [hydef]
    split_ifs with h1 h2
    · exact le_refl 0
    · exact le_refl 0
    · exact mul_nonneg (Cc_nonneg a) (Real.rpow_nonneg (by positivity) _)
  have hy : Summable y := by
    have hbase : Summable (fun n : ℕ => Cc a * (n : ℝ) ^ (-(4 / 3 : ℝ))) :=
      (summable_nat_rpow_neg (c := (4 / 3 : ℝ)) (by norm_num)).mul_left (Cc a)
    refine Summable.of_nonneg_of_le hy0 (fun n => ?_) hbase
    simp only [hydef]
    split_ifs with h1 h2
    · exact mul_nonneg (Cc_nonneg a) (Real.rpow_nonneg (by positivity) _)
    · exact mul_nonneg (Cc_nonneg a) (Real.rpow_nonneg (by positivity) _)
    · exact le_refl _
  have hpt : ∀ n, ‖u n‖ ≤ x n + y n := by
    intro n
    have h := u_le (a := a) (W := W) (δ := δ) ha hW0 hΔ0 (n := n)
    rw [← hSdef] at h
    have hx0 : 0 ≤ x n := by
      simp only [hxdef]
      split_ifs with h1
      · refine mul_nonneg (Da_nonneg a) (Real.log_nonneg ?_)
        have h2 : (0 : ℝ) ≤ (n : ℝ) ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg (by positivity) _
        linarith
      · exact le_refl 0
    rw [hudef]
    by_cases hnS : n ∈ S
    · simp only [hxdef, hydef, if_pos hnS] at h ⊢
      linarith [h, hy0 n]
    · simp only [hxdef, hydef, if_neg hnS] at h ⊢
      linarith [h]
  have hu : Summable (fun n => ‖u n‖) :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) hpt (hx.add hy)
  have hsum_le : (∑' n, ‖u n‖) ≤ (∑' n, x n) + (∑' n, y n) := by
    have h1 : (∑' n, ‖u n‖) ≤ ∑' n, (x n + y n) :=
      Summable.tsum_le_tsum hpt hu (hx.add hy)
    rwa [Summable.tsum_add hx hy] at h1
  have hxsum : (∑' n, x n)
      = ∑ q ∈ S, Da a * Real.log (1 + (q : ℝ) ^ (-(1 / 2 : ℝ))) := by
    have h := tsum_eq_sum (L := SummationFilter.unconditional ℕ) (f := x) (s := S) (fun n hn => by
      rw [hxdef]
      simp [hn])
    have h2 : (∑ n ∈ S, x n) = ∑ q ∈ S, Da a * Real.log (1 + (q : ℝ) ^ (-(1 / 2 : ℝ))) := by
      refine Finset.sum_congr rfl (fun q hq => ?_)
      simp only [hxdef]
      rw [if_pos hq]
    rw [h2] at h
    simpa only [hxdef] using h
  have hysum : (∑' n : ℕ, y n) ≤ Cc a * (∑' n : ℕ, (n : ℝ) ^ (-(4 / 3 : ℝ))) := by
    have hbase : Summable (fun n : ℕ => Cc a * (n : ℝ) ^ (-(4 / 3 : ℝ))) :=
      (summable_nat_rpow_neg (c := (4 / 3 : ℝ)) (by norm_num)).mul_left (Cc a)
    have h1 : (∑' n : ℕ, y n) ≤ ∑' n : ℕ, Cc a * (n : ℝ) ^ (-(4 / 3 : ℝ)) :=
      Summable.tsum_le_tsum (fun n => by
        simp only [hydef]
        split_ifs with h1 h2
        · exact mul_nonneg (Cc_nonneg a) (Real.rpow_nonneg (by positivity) _)
        · exact mul_nonneg (Cc_nonneg a) (Real.rpow_nonneg (by positivity) _)
        · exact le_refl _) hy hbase
    calc (∑' n : ℕ, y n) ≤ ∑' n : ℕ, Cc a * (n : ℝ) ^ (-(4 / 3 : ℝ)) := h1
      _ = Cc a * ∑' n : ℕ, (n : ℝ) ^ (-(4 / 3 : ℝ)) := by rw [tsum_mul_left]
  have hexpx : Real.exp (∑' n, x n)
      = ∏ q ∈ S, (1 + (q : ℝ) ^ (-(1 / 2 : ℝ))) ^ (Da a) := by
    rw [hxsum, Real.exp_sum]
    refine Finset.prod_congr rfl (fun q _ => ?_)
    rw [mul_comm (Da a), Real.exp_mul, Real.exp_log (by positivity)]
  have hG1 : G1u W (Ac a) δ (0 : Fin a → ℂ) (0 : Fin a → ℂ) = ∏' n : ℕ, (1 + u n) := by
    rw [G1u]
    exact tprod_congr (fun n => by rw [hudef]; ring)
  rw [hG1]
  refine le_trans (Commons.Analysis.Complex.norm_tprod_one_add_le_exp u hu) ?_
  calc Real.exp (∑' n, ‖u n‖)
      ≤ Real.exp ((∑' n, x n) + (∑' n, y n)) := Real.exp_le_exp.mpr hsum_le
    _ = Real.exp (∑' n, x n) * Real.exp (∑' n, y n) := Real.exp_add _ _
    _ ≤ (∏ q ∈ S, (1 + (q : ℝ) ^ (-(1 / 2 : ℝ))) ^ (Da a))
          * Real.exp (Cc a * (∑' n : ℕ, (n : ℝ) ^ (-(4 / 3 : ℝ)))) := by
        refine mul_le_mul (le_of_eq hexpx) (Real.exp_le_exp.mpr hysum)
          (Real.exp_nonneg _) (by positivity)
    _ = Real.exp (Cc a * (∑' n : ℕ, (n : ℝ) ^ (-(4 / 3 : ℝ))))
          * ∏ q ∈ S, (1 + (q : ℝ) ^ (-(1 / 2 : ℝ))) ^ (Da a) := by ring

end Corr
end GYMaj
