import Submission.Work.GYCorr1
import Submission.Work.GYFactor9
import Submission.Commons.Analysis.Normed.norm_prod_one_add_sub_one_sub_sum_le

/-!
# The correlation majorant (Green–Tao §9, Proposition GY2)

This file continues `GYCorr1.lean`.  For the degenerate system `θ_i(x) = W(x + h_i) + 1` we
construct a **summable majorant** of `‖E_p^{(1)} - 1‖` on the strip `Re ≥ -1/(6m)`:

* for the primes `p ∤ WΔ` the sharp estimate `E1p_bound_corr` of `GYCorr1.lean` applies;
* for the finitely many `p ≤ max Δ ((6m)²+2)` we use the crude bound `E1p_crude_corr`;
* for `p | W` or composite `p` we have `E1p = 1`.

The majorant is `e1pMajorCorr Δ m`, an additively perturbed version of the §10 majorant
`e1pMajor m` (Green–Tao Lemma 10.3).  This is the only analytic input needed to transplant the
whole §10 machinery (`GYFactor6`–`GYFactor8`) to the correlation system.

★ We must carry `hΔ0 : Delta h ≠ 0` (the shifts `h_i` are pairwise distinct): if `Δ = 0` then
every prime divides `Δ` and the sharp estimate is unavailable.  That degenerate case is handled
separately in the `hgy` assembly. ★
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

variable {m : ℕ}

/-! ## 0. The local count of the degenerate system is at most one

These two lemmas (`locCount_corr_le_one`, `vSys_corr_le`) are the *only* local input of the
correlation chapter at primes `q ∤ W`: unlike in the non-degenerate §10 system, the solution of
`θ_i(x) = 0` (`i` in a nonempty subsystem) is *unique* modulo `q` (because `q ∤ W` makes
`x ↦ W(x + h_i) + 1` a bijection).  Hence `vSys` is bounded by `1/q` — the fact which makes the
whole `Δ`-dependence of the majorant of §2b collapse to `Σ_{q | Δ} q^{-1/2}`. -/

lemma locCount_corr_le_one {a q W : ℕ} [NeZero q] (hq : q.Prime) (hqW : ¬ q ∣ W)
    {δ : Fin a → ℤ} {σ : PrimeData a} (hσ : σ ≠ 0) :
    Commons.NumberTheory.Sieve.locCount W (Ac a) δ
      (fun i => if i ∈ σ.X ∪ σ.X' then q else 1) q ≤ 1 := by
  classical
  haveI : Fact q.Prime := ⟨hq⟩
  change ((Finset.univ : Finset (Fin 1 → ZMod q)).filter
    (fun x => ∀ i, q ∣ (if i ∈ σ.X ∪ σ.X' then q else 1) →
      Commons.NumberTheory.Sieve.thetaMod W (Ac a) δ q i x = 0)).card ≤ 1
  refine Finset.card_le_one.mpr ?_
  intro x hx y hy
  rw [Finset.mem_filter] at hx hy
  have hne : (σ.X ∪ σ.X').Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h
    apply hσ
    rw [Finset.union_eq_empty] at h
    obtain ⟨X, X'⟩ := σ
    simp only at h
    rw [h.1, h.2]
    rfl
  obtain ⟨i0, hi0⟩ := hne
  have h1 : thetaMod W (Ac a) δ q i0 x = 0 := hx.2 i0 (by rw [if_pos hi0])
  have h2 : thetaMod W (Ac a) δ q i0 y = 0 := hy.2 i0 (by rw [if_pos hi0])
  rw [thetaMod_eq] at h1 h2
  have hW : (W : ZMod q) ≠ 0 := by
    intro h0
    rw [show (W : ZMod q) = ((W : ℕ) : ZMod q) from rfl,
      CharP.cast_eq_zero_iff (ZMod q) q] at h0
    exact hqW h0
  have h3 : (W : ZMod q) * (y 0 + ((δ i0 : ℤ) : ZMod q)) + 1
      = (W : ZMod q) * (x 0 + ((δ i0 : ℤ) : ZMod q)) + 1 := h2.trans h1.symm
  have h4 : (W : ZMod q) * (y 0 + ((δ i0 : ℤ) : ZMod q))
      = (W : ZMod q) * (x 0 + ((δ i0 : ℤ) : ZMod q)) := add_right_cancel h3
  have h5 : y 0 + ((δ i0 : ℤ) : ZMod q) = x 0 + ((δ i0 : ℤ) : ZMod q) :=
    mul_left_cancel₀ hW h4
  have h0 : x 0 = y 0 := (add_right_cancel h5).symm
  funext j
  fin_cases j
  exact h0

lemma vSys_corr_le {a q W : ℕ} (hq : q.Prime) (hqW : ¬ q ∣ W) {δ : Fin a → ℤ}
    {σ : PrimeData a} (hσ : σ ≠ 0) :
    ‖BoxAvg.vSys W (Ac a) δ q σ‖ ≤ (q : ℝ)⁻¹ := by
  haveI : NeZero q := NeZero.of_pos hq.pos
  have hq0 : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq.pos
  have hcard := locCount_corr_le_one (a := a) hq hqW (δ := δ) hσ
  have h1 : ((Commons.NumberTheory.Sieve.locCount W (Ac a) δ
      (fun i => if i ∈ σ.X ∪ σ.X' then q else 1) q : ℕ) : ℝ) ≤ 1 := by
    exact_mod_cast hcard
  rw [BoxAvg.vSys, dif_pos hq, norm_div, norm_pow, pow_one]
  simp only [Complex.norm_natCast]
  rw [div_le_iff₀ hq0, inv_mul_cancel₀ (ne_of_gt hq0)]
  exact h1



/-! ## 1. The local factor at the primes dividing `W` -/

/-- `vSys` vanishes at a prime dividing `W` when `σ ≠ 0` (the correlation version). -/
lemma vSys_eq_zero_of_dvd_W_corr {W p : ℕ} {h : Fin m → ℤ} (hp : p.Prime) (hpW : p ∣ W)
    {σ : PrimeData m} (hσ : σ ≠ 0) : BoxAvg.vSys W (Ac m) h p σ = 0 := by
  haveI : NeZero p := NeZero.of_pos hp.pos
  rw [BoxAvg.vSys, dif_pos hp,
    Commons.NumberTheory.Sieve.locCount_ite_eq_zero_of_dvd hp W 1 (Ac m) h σ hσ le_rfl hpW,
    Nat.cast_zero, zero_div]

/-- The Euler factor at a prime dividing `W` is `1` (the correlation version). -/
lemma eulerFactor_eq_one_of_dvd_W_corr {W p : ℕ} {h : Fin m → ℤ} (hp : p.Prime) (hpW : p ∣ W)
    (z z' : Fin m → ℂ) : eulerFactor m (BoxAvg.vSys W (Ac m) h) z z' p = 1 := by
  classical
  rw [eulerFactor]
  have hzero : ∀ σ : PrimeData m, σ ≠ 0 →
      BoxAvg.vSys W (Ac m) h p σ * ((-1 : ℂ) ^ (σ.X.card + σ.X'.card)) *
        ((∏ i ∈ σ.X, (p : ℂ) ^ (-(z i))) * (∏ i ∈ σ.X', (p : ℂ) ^ (-(z' i)))) = 0 :=
    fun σ hσ => by rw [vSys_eq_zero_of_dvd_W_corr hp hpW hσ, zero_mul, zero_mul]
  rw [Finset.sum_eq_single (0 : PrimeData m) (fun σ _ hσ => hzero σ hσ)
    (fun h => absurd (Finset.mem_univ _) h)]
  rw [BoxAvg.vSys_zero]
  have hX : (0 : PrimeData m).X = ∅ := rfl
  have hX' : (0 : PrimeData m).X' = ∅ := rfl
  rw [hX, hX']
  simp

/-- **Green–Tao (10.8) for the degenerate system**: `E_p = E_p^{(1)}E_p^{(2)}E_p^{(3)}`
(the correlation version). -/
theorem eulerFactor_eq_E1p_mul_E2p_mul_E3p_corr {W : ℕ} {h : Fin m → ℤ} {σ₀ : ℝ}
    (hσ₀ : 2 * σ₀ < 1) {z z' : Fin m → ℂ} (hz : ∀ j, -σ₀ ≤ (z j).re)
    (hz' : ∀ j, -σ₀ ≤ (z' j).re) (p : ℕ) :
    eulerFactor m (BoxAvg.vSys W (Ac m) h) z z' p
      = E1p W (Ac m) h z z' p * E2p W z z' p * E3p z z' p := by
  by_cases hp : p.Prime
  · by_cases hpW : p ∣ W
    · rw [eulerFactor_eq_one_of_dvd_W_corr hp hpW, E1p, if_neg (by tauto), E2p,
        if_pos ⟨hp, hpW⟩, E3p, if_pos hp, one_mul]
      rw [← Finset.prod_mul_distrib]
      refine (Finset.prod_eq_one (fun j _ => ?_)).symm
      obtain ⟨h1, h2, h3⟩ := E3p_factors_ne_zero hp hσ₀ (hz j) (hz' j)
      rw [mul_comm (((1 - (p : ℂ) ^ (-(1 + z j)))⁻¹ * (1 - (p : ℂ) ^ (-(1 + z' j)))⁻¹)
            * (1 - (p : ℂ) ^ (-(1 + z j + z' j))))
          (((1 - (p : ℂ) ^ (-(1 + z j))) * (1 - (p : ℂ) ^ (-(1 + z' j))))
            * (1 - (p : ℂ) ^ (-(1 + z j + z' j)))⁻¹)]
      rw [show ((1 - (p : ℂ) ^ (-(1 + z j))) * (1 - (p : ℂ) ^ (-(1 + z' j))))
            * (1 - (p : ℂ) ^ (-(1 + z j + z' j)))⁻¹
            * (((1 - (p : ℂ) ^ (-(1 + z j)))⁻¹ * (1 - (p : ℂ) ^ (-(1 + z' j)))⁻¹)
              * (1 - (p : ℂ) ^ (-(1 + z j + z' j))))
          = ((1 - (p : ℂ) ^ (-(1 + z j)))⁻¹ * (1 - (p : ℂ) ^ (-(1 + z j))))
            * ((1 - (p : ℂ) ^ (-(1 + z' j)))⁻¹ * (1 - (p : ℂ) ^ (-(1 + z' j))))
            * ((1 - (p : ℂ) ^ (-(1 + z j + z' j))) * (1 - (p : ℂ) ^ (-(1 + z j + z' j)))⁻¹)
          from by ring]
      rw [inv_mul_cancel₀ h1, inv_mul_cancel₀ h2, mul_inv_cancel₀ h3]
      simp
    · rw [E1p, if_pos ⟨hp, hpW⟩, E2p, if_neg (by tauto), mul_one]
      exact (div_mul_cancel₀ _ (E3p_ne_zero hp hσ₀ hz hz')).symm
  · rw [E1p, if_neg (by tauto), E2p, if_neg (by tauto), E3p, if_neg hp, one_mul, one_mul]
    rw [eulerFactor, Finset.sum_eq_single (0 : PrimeData m)
      (fun σ _ hσ => by rw [vSys_of_not_prime W (Ac m) h p σ hp hσ, zero_mul, zero_mul])
      (fun h => absurd (Finset.mem_univ _) h)]
    rw [BoxAvg.vSys_zero]
    have hX : (0 : PrimeData m).X = ∅ := rfl
    have hX' : (0 : PrimeData m).X' = ∅ := rfl
    rw [hX, hX']
    simp

/-! ## 2. The crude bounds -/

/-- The Euler factor is bounded on the strip by `4^m p^{2σ₀m}` for every prime `p ∤ W`
(including the primes dividing `Δ`, where the sharp estimate is unavailable). -/
lemma norm_eulerFactor_corr_le {W n : ℕ} {h : Fin m → ℤ} (hn : n.Prime) (hnW : ¬ n ∣ W)
    {σ₀ : ℝ} (hσ₀ : 0 ≤ σ₀) {z z' : Fin m → ℂ} (hz : ∀ j, -σ₀ ≤ (z j).re)
    (hz' : ∀ j, -σ₀ ≤ (z' j).re) :
    ‖eulerFactor m (BoxAvg.vSys W (Ac m) h) z z' n‖
      ≤ (4 : ℝ) ^ m * (n : ℝ) ^ (2 * σ₀ * (m : ℝ)) := by
  have hn1 : 1 ≤ n := hn.one_le
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn.pos
  have hterm : ∀ σ : PrimeData m,
      ‖BoxAvg.eTerm W (Ac m) h z z' n σ‖ ≤ (n : ℝ) ^ (2 * σ₀ * (m : ℝ)) := by
    intro σ
    have hv : ‖BoxAvg.vSys W (Ac m) h n σ‖ ≤ 1 := norm_vSys_le_one W (Ac m) h n σ
    have hX := norm_prod_cpow_le (m := m) (p := n) hn1 hσ₀ hz σ.X
    have hX' := norm_prod_cpow_le (m := m) (p := n) hn1 hσ₀ hz' σ.X'
    have hcardX : (σ.X.card : ℝ) ≤ m := by
      have := Finset.card_le_univ σ.X
      rw [Fintype.card_fin] at this
      exact_mod_cast this
    have hcardX' : (σ.X'.card : ℝ) ≤ m := by
      have := Finset.card_le_univ σ.X'
      rw [Fintype.card_fin] at this
      exact_mod_cast this
    have hpow : (n : ℝ) ^ (σ₀ * (σ.X.card : ℝ)) * (n : ℝ) ^ (σ₀ * (σ.X'.card : ℝ))
        ≤ (n : ℝ) ^ (2 * σ₀ * (m : ℝ)) := by
      rw [← Real.rpow_add (by positivity)]
      refine Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn1) ?_
      nlinarith
    rw [BoxAvg.eTerm]
    simp only [norm_mul, norm_pow, norm_neg, norm_one, one_pow, mul_one, one_mul]
    calc ‖BoxAvg.vSys W (Ac m) h n σ‖ * (‖∏ i ∈ σ.X, (n : ℂ) ^ (-(z i))‖
            * ‖∏ i ∈ σ.X', (n : ℂ) ^ (-(z' i))‖)
        ≤ 1 * ((n : ℝ) ^ (σ₀ * (σ.X.card : ℝ))
            * (n : ℝ) ^ (σ₀ * (σ.X'.card : ℝ))) :=
          mul_le_mul hv (mul_le_mul hX hX' (by positivity) (by positivity)) (by positivity)
            (by norm_num)
      _ ≤ (n : ℝ) ^ (2 * σ₀ * (m : ℝ)) := by rw [one_mul]; exact hpow
  rw [eulerFactor_eq_sum_eTerm]
  calc ‖∑ σ : PrimeData m, BoxAvg.eTerm W (Ac m) h z z' n σ‖
      ≤ ∑ σ : PrimeData m, (n : ℝ) ^ (2 * σ₀ * (m : ℝ)) :=
        le_trans (norm_sum_le _ _) (Finset.sum_le_sum (fun σ _ => hterm σ))
    _ = (4 : ℝ) ^ m * (n : ℝ) ^ (2 * σ₀ * (m : ℝ)) := by
        rw [Finset.sum_const, Finset.card_univ, card_primeData m, nsmul_eq_mul, Nat.cast_pow,
          Nat.cast_ofNat]

/-- The crude bound on the strip: for every prime `p ∤ W` (in particular for `p ∣ Δ`),
`‖E_p^{(1)} - 1‖ ≤ 4^m p^{1/3} 28^m + 1`. -/
lemma E1p_crude_corr {W n : ℕ} {h : Fin m → ℤ} (hm : 1 ≤ m) (hn : n.Prime) (hnW : ¬ n ∣ W)
    {z z' : Fin m → ℂ} (hz : ∀ j, -(1 / (6 * (m : ℝ))) ≤ (z j).re)
    (hz' : ∀ j, -(1 / (6 * (m : ℝ))) ≤ (z' j).re) :
    ‖E1p W (Ac m) h z z' n - 1‖
      ≤ (4 : ℝ) ^ m * (n : ℝ) ^ (1 / 3 : ℝ) * (28 : ℝ) ^ m + 1 := by
  have hσ₀ : (0 : ℝ) ≤ 1 / (6 * (m : ℝ)) := by
    have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
    positivity
  have hexp : 2 * (1 / (6 * (m : ℝ))) * (m : ℝ) = 1 / 3 := by
    field_simp; ring
  have h1' : ‖E1p W (Ac m) h z z' n‖
      ≤ (4 : ℝ) ^ m * (n : ℝ) ^ (2 * (1 / (6 * (m : ℝ))) * (m : ℝ)) * (28 : ℝ) ^ m := by
    rw [E1p, if_pos (show n.Prime ∧ ¬ n ∣ W from ⟨hn, hnW⟩), div_eq_mul_inv, norm_mul, norm_inv,
      ← norm_inv]
    exact mul_le_mul (norm_eulerFactor_corr_le hn hnW hσ₀ hz hz') (E3p_inv_le hn hm hz hz')
      (norm_nonneg _) (by positivity)
  have h1 : ‖E1p W (Ac m) h z z' n‖
      ≤ (4 : ℝ) ^ m * (n : ℝ) ^ (1 / 3 : ℝ) * (28 : ℝ) ^ m := by
    simpa only [hexp] using h1'
  have h2 := norm_sub_le (E1p W (Ac m) h z z' n) (1 : ℂ)
  rw [norm_one] at h2
  linarith

/-! ## 2b. The uniform (in `Δ`) pointwise bound

The sharp estimate `E1p_bound_corr` applies only at the primes `n ∤ Δ` and only for `n` larger than
`(6m)²+2`.  At the remaining primes (`n ∣ Δ`, or `n` small) we use the following bound, which is
**uniform in `Δ`**: it rests on `vSys_corr_le` (`‖vSys σ‖ ≤ 1/n`) rather than on the trivial
`‖vSys σ‖ ≤ 1`.  This is what makes the summable majorant of the next section grow like
`Σ_{q | Δ} q^{-1/2}` instead of like `Δ` — an absolutely essential point, since in the correlation
step `Δ` is as large as a power of `p` while `log R` is at most `log p`. -/

/-- The numeric fact `2 ^ (-2/3) ≤ 2/3`. -/
lemma two_rpow_neg_two_thirds_le : (2 : ℝ) ^ (-(2 / 3 : ℝ)) ≤ 2 / 3 := by
  have h1 : ((2 : ℝ) ^ (-(2 / 3 : ℝ))) ^ ((3 : ℕ) : ℝ) = (2 : ℝ) ^ (-(2 : ℝ)) := by
    rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  have h2 : ((2 / 3 : ℝ)) ^ ((3 : ℕ) : ℝ) = (8 / 27 : ℝ) := by
    rw [Real.rpow_natCast]; norm_num
  have h3 : ((2 : ℝ) ^ (-(2 / 3 : ℝ))) ^ ((3 : ℕ) : ℝ) ≤ ((2 / 3 : ℝ)) ^ ((3 : ℕ) : ℝ) := by
    rw [h1, h2, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ (2 : ℝ))]
    norm_num
  exact (Real.rpow_le_rpow_iff (by positivity) (by norm_num)
    (by norm_num : (0 : ℝ) < 3)).mp h3

/-- `(1 + x)^n - 1 ≤ (x/c)((1+c)^n - 1)` for `0 ≤ x ≤ c` and `c > 0`. -/
lemma pow_one_add_sub_one_le_mul_pow {x c : ℝ} (hx : 0 ≤ x) (hc : 0 < c) (hxc : x ≤ c) (n : ℕ) :
    (1 + x) ^ n - 1 ≤ x / c * ((1 + c) ^ n - 1) := by
  have h1 := geom_sum_mul (1 + x) n
  rw [add_sub_cancel_left] at h1
  have h2 := geom_sum_mul (1 + c) n
  rw [add_sub_cancel_left] at h2
  rw [← h1, ← h2]
  have h3 : ∑ i ∈ Finset.range n, (1 + x) ^ i ≤ ∑ i ∈ Finset.range n, (1 + c) ^ i :=
    Finset.sum_le_sum (fun i _ => pow_le_pow_left₀ (by linarith) (by linarith) i)
  have h4 : x / c * ((∑ i ∈ Finset.range n, (1 + c) ^ i) * c)
      = x * ∑ i ∈ Finset.range n, (1 + c) ^ i := by
    field_simp
  rw [h4, mul_comm x (∑ i ∈ Finset.range n, (1 + c) ^ i)]
  exact mul_le_mul_of_nonneg_right h3 hx

/-- `‖∏_{i∈s} f i - 1‖ ≤ (1+B)^{|s|} - 1` when `‖f i - 1‖ ≤ B`. -/
lemma norm_prod_sub_one_le_pow {ι : Type*} (s : Finset ι) (f : ι → ℂ) (B : ℝ) (hB : 0 ≤ B)
    (hf : ∀ i ∈ s, ‖f i - 1‖ ≤ B) :
    ‖∏ i ∈ s, f i - 1‖ ≤ (1 + B) ^ s.card - 1 := by
  have hcongr : (∏ i ∈ s, f i) = ∏ i ∈ s, (1 + (f i - 1)) :=
    Finset.prod_congr rfl (fun i _ => by ring)
  rw [hcongr]
  exact Commons.Analysis.Normed.norm_prod_one_add_sub_one_le_pow s (fun i => f i - 1) B hB hf

/-- `‖(1 - u)⁻¹ - 1‖ ≤ 3‖u‖` when `‖u‖ ≤ 2/3`. -/
lemma norm_inv_one_sub_sub_one_le {u : ℂ} (hu : ‖u‖ ≤ 2 / 3) :
    ‖((1 : ℂ) - u)⁻¹ - 1‖ ≤ 3 * ‖u‖ := by
  have hne : (1 : ℂ) - u ≠ 0 := by
    intro h
    have h1 : (1 : ℂ) = u := sub_eq_zero.mp h
    rw [← h1, norm_one] at hu
    norm_num at hu
  have heq : ((1 : ℂ) - u)⁻¹ - 1 = u * ((1 : ℂ) - u)⁻¹ := by
    field_simp
    ring
  have hnorm : (1 / 3 : ℝ) ≤ ‖(1 : ℂ) - u‖ := by
    have h := norm_add_le ((1 : ℂ) - u) u
    rw [sub_add_cancel, norm_one] at h
    linarith
  have h2 : ‖((1 : ℂ) - u)⁻¹‖ ≤ 3 := by
    rw [norm_inv]
    calc (‖(1 : ℂ) - u‖)⁻¹ ≤ ((1 / 3 : ℝ))⁻¹ :=
          (inv_le_inv₀ (by positivity) (by norm_num)).mpr hnorm
      _ = 3 := by norm_num
  rw [heq, norm_mul]
  calc ‖u‖ * ‖((1 : ℂ) - u)⁻¹‖ ≤ ‖u‖ * 3 := mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
    _ = 3 * ‖u‖ := by ring

/-- On the strip, `‖n^{-(1+w)}‖ ≤ n^{-2/3}` whenever `Re w ≥ -1/(3m)` (in particular for all three
of `w = z_j`, `w = z'_j`, `w = z_j + z'_j` when `Re z_j, Re z'_j ≥ -1/(6m)`). -/
lemma norm_cpow_le_of_re {m n : ℕ} (hm : 1 ≤ m) (hn : 2 ≤ n) {w : ℂ}
    (hw : -(1 / (3 * (m : ℝ))) ≤ w.re) :
    ‖(n : ℂ) ^ (-(1 + w))‖ ≤ (n : ℝ) ^ (-(2 / 3 : ℝ)) := by
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
  have h0 := norm_cpow_neg_one_sub_le (p := n) (c := -(1 / (3 * (m : ℝ))))
    (by omega : 1 ≤ n) hw
  refine le_trans h0 ?_
  refine Real.rpow_le_rpow_of_exponent_le hn1 ?_
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have h2 : 1 / (3 * (m : ℝ)) ≤ 1 / 3 :=
    one_div_le_one_div_of_le (by norm_num) (by linarith)
  linarith

/-- The constant of the uniform (in `Δ`) crude bound at the bad primes. -/
noncomputable def K0 (m : ℕ) : ℝ :=
  (4 : ℝ) ^ m * (1000 : ℝ) ^ m + (4 : ℝ) ^ m + (1000 : ℝ) ^ m

lemma K0_pos (m : ℕ) : 0 < K0 m := by unfold K0; positivity
lemma K0_nonneg (m : ℕ) : 0 ≤ K0 m := (K0_pos m).le

/-- `‖E_p^{(3)}⁻¹ - 1‖ ≤ 1000^m p^{-2/3}` on the strip (`p` prime). -/
lemma E3p_inv_sub_one_le {n m : ℕ} (hn : n.Prime) (hm : 1 ≤ m) {z z' : Fin m → ℂ}
    (hz : ∀ j, -(1 / (6 * (m : ℝ))) ≤ (z j).re)
    (hz' : ∀ j, -(1 / (6 * (m : ℝ))) ≤ (z' j).re) :
    ‖(E3p z z' n)⁻¹ - 1‖ ≤ (1000 : ℝ) ^ m * (n : ℝ) ^ (-(2 / 3 : ℝ)) := by
  have hn2 : 2 ≤ n := hn.two_le
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn.pos
  set B : ℝ := (n : ℝ) ^ (-(2 / 3 : ℝ)) with hB
  have hB0 : 0 < B := Real.rpow_pos_of_pos hn0 (-(2 / 3 : ℝ))
  have hBle : B ≤ 2 / 3 := by
    rw [hB]
    refine le_trans (Real.rpow_le_rpow_of_nonpos (by norm_num)
      (by exact_mod_cast hn2) (by norm_num : (-(2 / 3 : ℝ)) ≤ 0))
      two_rpow_neg_two_thirds_le
  have hbnd : ∀ j : Fin m, ‖(n : ℂ) ^ (-(1 + z j))‖ ≤ B
      ∧ ‖(n : ℂ) ^ (-(1 + z' j))‖ ≤ B
      ∧ ‖(n : ℂ) ^ (-(1 + z j + z' j))‖ ≤ B := by
    intro j
    have hlow : -(1 / (3 * (m : ℝ))) ≤ -(1 / (6 * (m : ℝ))) := by
      have hm1 : (0 : ℝ) < m := by positivity
      have : (1 : ℝ) / (6 * (m : ℝ)) ≤ 1 / (3 * (m : ℝ)) :=
        one_div_le_one_div_of_le (by positivity) (by linarith)
      linarith
    have h3 : -(1 / (3 * (m : ℝ))) + -(1 / (3 * (m : ℝ)))
        ≤ -(1 / (6 * (m : ℝ))) + -(1 / (6 * (m : ℝ))) := by
      have h4 : (1 : ℝ) / (6 * (m : ℝ)) ≤ 1 / (3 * (m : ℝ)) :=
        one_div_le_one_div_of_le (by positivity) (by
          have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
          linarith)
      linarith
    refine ⟨?_, ?_, ?_⟩
    · exact norm_cpow_le_of_re hm hn2 (le_trans hlow (hz j))
    · exact norm_cpow_le_of_re hm hn2 (le_trans hlow (hz' j))
    · rw [show (-(1 + z j + z' j) : ℂ) = -(1 + (z j + z' j)) by ring]
      refine norm_cpow_le_of_re hm hn2 ?_
      rw [Complex.add_re]
      have h2 := add_le_add (hz j) (hz' j)
      have h3 : -(1 / (6 * (m : ℝ))) + -(1 / (6 * (m : ℝ))) = -(1 / (3 * (m : ℝ))) := by
        ring
      linarith
  have hfac : ∀ j : Fin m,
      ‖((1 : ℂ) - (n : ℂ) ^ (-(1 + z j)))⁻¹
          * ((1 : ℂ) - (n : ℂ) ^ (-(1 + z' j)))⁻¹
          * ((1 : ℂ) - (n : ℂ) ^ (-(1 + z j + z' j))) - 1‖ ≤ 144 * B := by
    intro j
    obtain ⟨h1, h2, h3⟩ := hbnd j
    set u1 : ℂ := (n : ℂ) ^ (-(1 + z j)) with hu1
    set u2 : ℂ := (n : ℂ) ^ (-(1 + z' j)) with hu2
    set u3 : ℂ := (n : ℂ) ^ (-(1 + z j + z' j)) with hu3
    have hA1 : ‖((1 : ℂ) - u1)⁻¹ - 1‖ ≤ 3 * B :=
      le_trans (norm_inv_one_sub_sub_one_le (u := u1) (by linarith)) (by linarith)
    have hA2 : ‖((1 : ℂ) - u2)⁻¹ - 1‖ ≤ 3 * B :=
      le_trans (norm_inv_one_sub_sub_one_le (u := u2) (by linarith)) (by linarith)
    have hA5 : ‖((1 : ℂ) - u3)‖ ≤ 2 := by
      refine le_trans (norm_sub_le _ _) ?_
      rw [norm_one]; linarith
    have hC : ‖((1 : ℂ) - u3) - 1‖ ≤ B := by
      rw [show ((1 : ℂ) - u3) - 1 = -u3 by ring, norm_neg]
      exact h3
    have key1 : ‖((1 : ℂ) - u1)⁻¹‖ ≤ 1 + 3 * B := by
      have h := norm_add_le (((1 : ℂ) - u1)⁻¹ - 1) 1
      rw [sub_add_cancel, norm_one] at h
      linarith
    have key2 : ‖((1 : ℂ) - u2)⁻¹‖ ≤ 1 + 3 * B := by
      have h := norm_add_le (((1 : ℂ) - u2)⁻¹ - 1) 1
      rw [sub_add_cancel, norm_one] at h
      linarith
    have key3 : ‖((1 : ℂ) - u3)‖ ≤ 1 + B := by
      refine le_trans (norm_sub_le _ _) ?_
      rw [norm_one]; linarith
    have key4 : ‖((1 : ℂ) - u2)⁻¹ * ((1 : ℂ) - u3)‖ ≤ 3 * 2 := by
      rw [norm_mul]
      have e1 : (1 : ℝ) + 3 * B ≤ 3 := by linarith [hBle]
      have e2 : (1 : ℝ) + B ≤ 2 := by linarith [hBle]
      nlinarith [key2, key3, norm_nonneg ((1 : ℂ) - u2)⁻¹, norm_nonneg ((1 : ℂ) - u3),
        e1, e2]
    have hexp : ((1 : ℂ) - u1)⁻¹ * ((1 : ℂ) - u2)⁻¹ * ((1 : ℂ) - u3) - 1
        = (((1 : ℂ) - u1)⁻¹ - 1) * (((1 : ℂ) - u2)⁻¹ * ((1 : ℂ) - u3))
          + (((1 : ℂ) - u2)⁻¹ - 1) * ((1 : ℂ) - u3)
          + (((1 : ℂ) - u3) - 1) := by ring
    rw [hexp]
    have hsum := norm_add_le ((((1 : ℂ) - u1)⁻¹ - 1) * (((1 : ℂ) - u2)⁻¹ * ((1 : ℂ) - u3))
        + (((1 : ℂ) - u2)⁻¹ - 1) * ((1 : ℂ) - u3)) (((1 : ℂ) - u3) - 1)
    have hsum2 := norm_add_le ((((1 : ℂ) - u1)⁻¹ - 1) * (((1 : ℂ) - u2)⁻¹ * ((1 : ℂ) - u3)))
      ((((1 : ℂ) - u2)⁻¹ - 1) * ((1 : ℂ) - u3))
    have e1' : ‖(((1 : ℂ) - u1)⁻¹ - 1) * (((1 : ℂ) - u2)⁻¹ * ((1 : ℂ) - u3))‖
        ≤ (3 * B) * (3 * 2) := by
      rw [norm_mul]
      exact mul_le_mul hA1 key4 (norm_nonneg _) (by positivity)
    have e2' : ‖(((1 : ℂ) - u2)⁻¹ - 1) * ((1 : ℂ) - u3)‖ ≤ (3 * B) * 2 := by
      rw [norm_mul]
      exact mul_le_mul hA2 hA5 (norm_nonneg _) (by positivity)
    have hsum' : ‖(((1 : ℂ) - u1)⁻¹ - 1) * (((1 : ℂ) - u2)⁻¹ * ((1 : ℂ) - u3))
        + (((1 : ℂ) - u2)⁻¹ - 1) * ((1 : ℂ) - u3)‖
        ≤ (3 * B) * (3 * 2) + (3 * B) * 2 := by
      linarith [hsum2, e1', e2']
    linarith [hsum, hsum', hC, hB0.le]
  have hone : (E3p z z' n)⁻¹
      = ∏ j : Fin m, (((1 : ℂ) - (n : ℂ) ^ (-(1 + z j)))⁻¹
          * ((1 : ℂ) - (n : ℂ) ^ (-(1 + z' j)))⁻¹
          * ((1 : ℂ) - (n : ℂ) ^ (-(1 + z j + z' j)))) := by
    rw [E3p, if_pos hn, ← Finset.prod_inv_distrib]
    refine Finset.prod_congr rfl (fun j _ => ?_)
    rw [mul_inv, mul_inv, inv_inv]
  rw [hone]
  have hprod : ‖(∏ j : Fin m, (((1 : ℂ) - (n : ℂ) ^ (-(1 + z j)))⁻¹
          * ((1 : ℂ) - (n : ℂ) ^ (-(1 + z' j)))⁻¹
          * ((1 : ℂ) - (n : ℂ) ^ (-(1 + z j + z' j))))) - 1‖
      ≤ (1 + 144 * B) ^ m - 1 := by
    have hres := norm_prod_sub_one_le_pow (Finset.univ : Finset (Fin m))
      (fun j => ((1 : ℂ) - (n : ℂ) ^ (-(1 + z j)))⁻¹
          * ((1 : ℂ) - (n : ℂ) ^ (-(1 + z' j)))⁻¹
          * ((1 : ℂ) - (n : ℂ) ^ (-(1 + z j + z' j)))) (144 * B) (by positivity)
      (fun j _ => hfac j)
    simpa only [Finset.card_univ, Fintype.card_fin] using hres
  refine le_trans hprod ?_
  have hpow := pow_one_add_sub_one_le_mul_pow (x := 144 * B) (c := 144) (by positivity)
    (by norm_num) (by linarith [hBle]) m
  refine le_trans hpow ?_
  have hfin : (144 * B) / 144 * ((1 + 144) ^ m - 1) ≤ (1000 : ℝ) ^ m * B := by
    have h1 : (144 * B) / 144 = B := by ring
    have h5 : (1 + 144 : ℝ) ^ m = (145 : ℝ) ^ m := by norm_num
    rw [h1, h5]
    have h2 : (145 : ℝ) ^ m - 1 ≤ (1000 : ℝ) ^ m := by
      have h3 : (145 : ℝ) ^ m ≤ (1000 : ℝ) ^ m :=
        pow_le_pow_left₀ (by norm_num) (by norm_num) m
      have h4 : (0 : ℝ) ≤ (145 : ℝ) ^ m := by positivity
      linarith
    calc B * ((145 : ℝ) ^ m - 1) ≤ B * (1000 : ℝ) ^ m :=
          mul_le_mul_of_nonneg_left h2 hB0.le
      _ = (1000 : ℝ) ^ m * B := by ring
  exact hfin

/-! ## 3. The correlation majorant -/

/-- **The correlation majorant**: the §10 majorant `e1pMajor m`, plus a bounded correction at the
small numbers `n ≤ (6m)²+2`, plus a `K0 m n^{-2/3}` correction at the primes dividing `Δ`.

★ The crucial point (and the reason this file had to be rewritten) is that the `Δ`-dependent part
is `K0 m · Σ_{q | Δ} q^{-2/3} = O_m(Σ_{q | Δ} q^{-1/2})`, *not* `O_m(Δ)`: the tsum is only
`O_m(1 + log log Δ)`, so `exp(∑ e1pMajorCorr) ≤ C_m ∏_{q | Δ}(1 + q^{-1/2})^{2K0 m}` is a bounded
multiple of the `Δ`-factor `LamD` rather than a tower in `Δ`. ★ -/
noncomputable def e1pMajorCorr (D m : ℕ) : ℕ → ℝ := fun n =>
  e1pMajor m n
    + (if n ≤ (6 * m) ^ 2 + 2 then K0 m else 0)
    + (if n.Prime ∧ n ∣ D then K0 m * (n : ℝ) ^ (-(2 / 3 : ℝ)) else 0)

lemma e1pMajorCorr_nonneg (D m n : ℕ) : 0 ≤ e1pMajorCorr D m n := by
  refine add_nonneg (add_nonneg ?_ ?_) ?_
  · unfold e1pMajor
    refine add_nonneg ?_ ?_
    · unfold cpowMajor; positivity
    · by_cases h : n ≤ (6 * m) ^ 2 + 2
      · simp only [if_pos h]; positivity
      · simp only [if_neg h]; norm_num
  · by_cases h : n ≤ (6 * m) ^ 2 + 2
    · simp only [if_pos h]; exact K0_nonneg m
    · simp only [if_neg h]; norm_num
  · by_cases h : n.Prime ∧ n ∣ D
    · simp only [if_pos h]
      exact mul_nonneg (K0_nonneg m) (Real.rpow_nonneg (by positivity) _)
    · simp only [if_neg h]; norm_num

lemma summable_e1pMajorCorr {m : ℕ} (hm : 1 ≤ m) {D : ℕ} (hD0 : D ≠ 0) :
    Summable (e1pMajorCorr D m) := by
  change Summable (fun n : ℕ => e1pMajor m n
    + (if n ≤ (6 * m) ^ 2 + 2 then K0 m else 0)
    + (if n.Prime ∧ n ∣ D then K0 m * (n : ℝ) ^ (-(2 / 3 : ℝ)) else 0))
  refine ((summable_e1pMajor hm).add (summable_of_ne_finset_zero
    (s := Finset.range ((6 * m) ^ 2 + 3)) (f := fun n : ℕ =>
      if n ≤ (6 * m) ^ 2 + 2 then K0 m else 0) (fun n hn => ?_))).add ?_
  · rw [Finset.mem_range] at hn
    simp only [if_neg (by omega : ¬ n ≤ (6 * m) ^ 2 + 2)]
  · refine summable_of_ne_finset_zero (s := D.primeFactors)
      (f := fun n : ℕ => if n.Prime ∧ n ∣ D then K0 m * (n : ℝ) ^ (-(2 / 3 : ℝ)) else 0)
      (fun n hn => ?_)
    rw [if_neg]
    rintro ⟨hpn, hdvd⟩
    exact hn (Nat.mem_primeFactors.mpr ⟨hpn, hdvd, hD0⟩)

/-- **Green–Tao Lemma 10.3 for the correlation system, uniform in `Δ`**: at every prime `n ∤ W`,
`‖E_n^{(1)} - 1‖ ≤ K0 m · n^{-2/3}` on the strip. -/
lemma E1p_uniform_crude {W n : ℕ} {h : Fin m → ℤ} (hm : 1 ≤ m) (hn : n.Prime) (hnW : ¬ n ∣ W)
    {z z' : Fin m → ℂ}
    (hz : ∀ j, -(1 / (6 * (m : ℝ))) ≤ (z j).re)
    (hz' : ∀ j, -(1 / (6 * (m : ℝ))) ≤ (z' j).re) :
    ‖E1p W (Ac m) h z z' n - 1‖ ≤ K0 m * (n : ℝ) ^ (-(2 / 3 : ℝ)) := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn.pos
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn.one_le
  -- `‖eulerFactor - 1‖ ≤ 4^m n^{-2/3}`
  have hEF : ‖eulerFactor m (vSys W (Ac m) h) z z' n - 1‖
      ≤ (4 : ℝ) ^ m * (n : ℝ) ^ (-(2 / 3 : ℝ)) := by
    have hterm : ∀ σ ∈ (Finset.univ : Finset (PrimeData m)).erase 0,
        ‖eTerm W (Ac m) h z z' n σ‖ ≤ (n : ℝ) ^ (-(2 / 3 : ℝ)) := by
      intro σ hσ
      rw [Finset.mem_erase] at hσ
      obtain ⟨hσ0, -⟩ := hσ
      have hv := vSys_corr_le (a := m) (q := n) (W := W) hn hnW (δ := h) hσ0
      have hX := norm_prod_cpow_le (m := m) (p := n) hn.one_le
        (by positivity : (0 : ℝ) ≤ 1 / (6 * (m : ℝ))) hz σ.X
      have hX' := norm_prod_cpow_le (m := m) (p := n) hn.one_le
        (by positivity : (0 : ℝ) ≤ 1 / (6 * (m : ℝ))) hz' σ.X'
      have hcardX : (σ.X.card : ℝ) ≤ (m : ℝ) := by
        have hcc := Finset.card_le_univ σ.X
        rw [Fintype.card_fin] at hcc
        exact_mod_cast hcc
      have hcardX' : (σ.X'.card : ℝ) ≤ (m : ℝ) := by
        have hcc := Finset.card_le_univ σ.X'
        rw [Fintype.card_fin] at hcc
        exact_mod_cast hcc
      have h4 : (1 / (6 * (m : ℝ))) * (m : ℝ) = 1 / 6 := by field_simp
      have h2' : (1 / (6 * (m : ℝ))) * (σ.X.card : ℝ) ≤ 1 / 6 := by
        rw [← h4]; exact mul_le_mul_of_nonneg_left hcardX (by positivity)
      have h3' : (1 / (6 * (m : ℝ))) * (σ.X'.card : ℝ) ≤ 1 / 6 := by
        rw [← h4]; exact mul_le_mul_of_nonneg_left hcardX' (by positivity)
      have hpq : (n : ℝ) ^ ((1 / (6 * (m : ℝ))) * (σ.X.card : ℝ))
          * (n : ℝ) ^ ((1 / (6 * (m : ℝ))) * (σ.X'.card : ℝ))
          ≤ (n : ℝ) ^ (1 / 3 : ℝ) := by
        rw [← Real.rpow_add hn0]
        refine Real.rpow_le_rpow_of_exponent_le hn1 ?_
        linarith
      rw [eTerm]
      simp only [norm_mul, norm_pow, norm_neg, norm_one, one_pow, mul_one]
      calc ‖vSys W (Ac m) h n σ‖ * (‖∏ i ∈ σ.X, (n : ℂ) ^ (-(z i))‖
              * ‖∏ i ∈ σ.X', (n : ℂ) ^ (-(z' i))‖)
          ≤ (n : ℝ)⁻¹ * ((n : ℝ) ^ ((1 / (6 * (m : ℝ))) * (σ.X.card : ℝ))
              * (n : ℝ) ^ ((1 / (6 * (m : ℝ))) * (σ.X'.card : ℝ))) :=
            mul_le_mul hv (mul_le_mul hX hX' (by positivity) (by positivity)) (by positivity)
              (inv_nonneg.mpr hn0.le)
        _ ≤ (n : ℝ)⁻¹ * (n : ℝ) ^ (1 / 3 : ℝ) :=
            mul_le_mul_of_nonneg_left hpq (inv_nonneg.mpr hn0.le)
        _ = (n : ℝ) ^ (-(2 / 3 : ℝ)) := by
            rw [← Real.rpow_neg_one, ← Real.rpow_add hn0]
            norm_num
    have hsplit : eulerFactor m (vSys W (Ac m) h) z z' n - 1
        = ∑ σ ∈ (Finset.univ : Finset (PrimeData m)).erase 0, eTerm W (Ac m) h z z' n σ := by
      have hsum := Finset.sum_erase_add (Finset.univ : Finset (PrimeData m))
        (fun σ => eTerm W (Ac m) h z z' n σ) (Finset.mem_univ (0 : PrimeData m))
      rw [eulerFactor_eq_sum_eTerm, ← hsum]
      have h0 : eTerm W (Ac m) h z z' n (0 : PrimeData m) = 1 := by
        rw [eTerm, vSys_zero]
        have hX : (0 : PrimeData m).X = ∅ := rfl
        have hX' : (0 : PrimeData m).X' = ∅ := rfl
        rw [hX, hX']
        simp
      rw [h0]
      ring
    rw [hsplit]
    refine le_trans (norm_sum_le _ _) ?_
    calc ∑ σ ∈ (Finset.univ : Finset (PrimeData m)).erase 0, ‖eTerm W (Ac m) h z z' n σ‖
        ≤ ∑ _σ ∈ (Finset.univ : Finset (PrimeData m)).erase 0,
            (n : ℝ) ^ (-(2 / 3 : ℝ)) := Finset.sum_le_sum hterm
      _ = (((Finset.univ : Finset (PrimeData m)).erase 0).card : ℝ)
            * (n : ℝ) ^ (-(2 / 3 : ℝ)) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (4 : ℝ) ^ m * (n : ℝ) ^ (-(2 / 3 : ℝ)) := by
          have hcard : ((Finset.univ : Finset (PrimeData m)).erase 0).card ≤ 4 ^ m := by
            rw [Finset.card_erase_of_mem (Finset.mem_univ _)]
            have hcc := Finset.card_univ (α := PrimeData m)
            rw [card_primeData] at hcc
            omega
          have : (((Finset.univ : Finset (PrimeData m)).erase 0).card : ℝ) ≤ (4 : ℝ) ^ m := by
            exact_mod_cast hcard
          exact mul_le_mul_of_nonneg_right this (Real.rpow_nonneg hn0.le _)
  -- `‖E3p⁻¹ - 1‖ ≤ 1000^m n^{-2/3}`
  have hE3 : ‖(E3p z z' n)⁻¹ - 1‖ ≤ (1000 : ℝ) ^ m * (n : ℝ) ^ (-(2 / 3 : ℝ)) :=
    E3p_inv_sub_one_le (m := m) hn hm hz hz'
  rw [E1p, if_pos ⟨hn, hnW⟩, div_eq_mul_inv]
  have hexp : eulerFactor m (vSys W (Ac m) h) z z' n * (E3p z z' n)⁻¹ - 1
      = (eulerFactor m (vSys W (Ac m) h) z z' n - 1) * ((E3p z z' n)⁻¹ - 1)
        + (eulerFactor m (vSys W (Ac m) h) z z' n - 1)
        + ((E3p z z' n)⁻¹ - 1) := by ring
  rw [hexp]
  have hsum := norm_add_le ((eulerFactor m (vSys W (Ac m) h) z z' n - 1)
        * ((E3p z z' n)⁻¹ - 1) + (eulerFactor m (vSys W (Ac m) h) z z' n - 1))
      ((E3p z z' n)⁻¹ - 1)
  have hsum2 := norm_add_le ((eulerFactor m (vSys W (Ac m) h) z z' n - 1)
        * ((E3p z z' n)⁻¹ - 1)) (eulerFactor m (vSys W (Ac m) h) z z' n - 1)
  have hb1 : ‖(eulerFactor m (vSys W (Ac m) h) z z' n - 1) * ((E3p z z' n)⁻¹ - 1)‖
      ≤ ((4 : ℝ) ^ m * (n : ℝ) ^ (-(2 / 3 : ℝ))) * ((1000 : ℝ) ^ m * (n : ℝ) ^ (-(2 / 3 : ℝ))) := by
    rw [norm_mul]
    exact mul_le_mul hEF hE3 (norm_nonneg _) (by positivity)
  have hn23 : (n : ℝ) ^ (-(2 / 3 : ℝ)) * (n : ℝ) ^ (-(2 / 3 : ℝ))
      ≤ (n : ℝ) ^ (-(2 / 3 : ℝ)) := by
    rw [← Real.rpow_add hn0]
    refine Real.rpow_le_rpow_of_exponent_le hn1 ?_
    norm_num
  have hb2 : ((4 : ℝ) ^ m * (n : ℝ) ^ (-(2 / 3 : ℝ)))
        * ((1000 : ℝ) ^ m * (n : ℝ) ^ (-(2 / 3 : ℝ)))
      ≤ (4 : ℝ) ^ m * (1000 : ℝ) ^ m * (n : ℝ) ^ (-(2 / 3 : ℝ)) := by
    have h1 : ((4 : ℝ) ^ m * (n : ℝ) ^ (-(2 / 3 : ℝ)))
        * ((1000 : ℝ) ^ m * (n : ℝ) ^ (-(2 / 3 : ℝ)))
        = ((4 : ℝ) ^ m * (1000 : ℝ) ^ m)
          * ((n : ℝ) ^ (-(2 / 3 : ℝ)) * (n : ℝ) ^ (-(2 / 3 : ℝ))) := by ring
    rw [h1]
    exact mul_le_mul_of_nonneg_left hn23 (by positivity)
  have hfin : (4 : ℝ) ^ m * (1000 : ℝ) ^ m * (n : ℝ) ^ (-(2 / 3 : ℝ))
      + (4 : ℝ) ^ m * (n : ℝ) ^ (-(2 / 3 : ℝ)) + (1000 : ℝ) ^ m * (n : ℝ) ^ (-(2 / 3 : ℝ))
      ≤ K0 m * (n : ℝ) ^ (-(2 / 3 : ℝ)) := by
    rw [K0]
    nlinarith [Real.rpow_nonneg hn0.le (-(2 / 3 : ℝ)), pow_nonneg (by norm_num : (0:ℝ) ≤ 4) m,
      pow_nonneg (by norm_num : (0:ℝ) ≤ 1000) m]
  linarith [hsum, hsum2, hb1, hb2, hE3, hEF, hfin]

/-- **The pointwise majorant bound**: on the strip, `‖E_n^{(1)} - 1‖ ≤ e1pMajorCorr Δ m n` for
EVERY `n` (not only primes). -/
lemma E1p_sub_one_le_major_corr {W : ℕ} {h : Fin m → ℤ} (hm : 1 ≤ m) (hW0 : 0 < W)
    (hΔ0 : Delta h ≠ 0) (n : ℕ) {z z' : Fin m → ℂ}
    (hz : ∀ j, -(1 / (6 * (m : ℝ))) ≤ (z j).re)
    (hz' : ∀ j, -(1 / (6 * (m : ℝ))) ≤ (z' j).re) :
    ‖E1p W (Ac m) h z z' n - 1‖ ≤ e1pMajorCorr (Delta h) m n := by
  have hpos : (0 : ℝ) ≤ 1 / (6 * (m : ℝ)) := by positivity
  have h4σ : 4 * (1 / (6 * (m : ℝ))) ≤ 1 := le_of_lt (sixth_small hm).1
  have hmono : e1pMajor m n + (if n ≤ (6 * m) ^ 2 + 2 then K0 m else 0)
      + (if n.Prime ∧ n ∣ Delta h then K0 m * (n : ℝ) ^ (-(2 / 3 : ℝ)) else 0)
      = e1pMajorCorr (Delta h) m n := rfl
  rw [← hmono]
  have hE : (0 : ℝ) ≤ e1pMajor m n := e1pMajor_nonneg m n
  have hK : (0 : ℝ) ≤ (if n ≤ (6 * m) ^ 2 + 2 then K0 m else 0) := by
    by_cases h : n ≤ (6 * m) ^ 2 + 2
    · simp only [if_pos h]; exact K0_nonneg m
    · simp only [if_neg h]; norm_num
  have hD' : (0 : ℝ) ≤ (if n.Prime ∧ n ∣ Delta h then K0 m * (n : ℝ) ^ (-(2 / 3 : ℝ))
      else 0) := by
    by_cases h : n.Prime ∧ n ∣ Delta h
    · simp only [if_pos h]
      exact mul_nonneg (K0_nonneg m) (Real.rpow_nonneg (by positivity) _)
    · simp only [if_neg h]; norm_num
  by_cases hn : n.Prime
  · by_cases hnW : n ∣ W
    · rw [E1p, if_neg (fun hc : n.Prime ∧ ¬ n ∣ W => hc.2 hnW), sub_self, norm_zero]
      linarith
    · by_cases hnD : n ∣ Delta h
      · have hif : (if n.Prime ∧ n ∣ Delta h then K0 m * (n : ℝ) ^ (-(2 / 3 : ℝ)) else 0)
            = K0 m * (n : ℝ) ^ (-(2 / 3 : ℝ)) := if_pos ⟨hn, hnD⟩
        rw [hif]
        have hb := E1p_uniform_crude (m := m) (W := W) (h := h) hm hn hnW hz hz'
        linarith
      · have hif : (if n.Prime ∧ n ∣ Delta h then K0 m * (n : ℝ) ^ (-(2 / 3 : ℝ)) else 0) = 0 :=
          if_neg (fun hc => hnD hc.2)
        rw [hif]
        by_cases hnbig : (6 * m) ^ 2 + 2 < n
        · have hif2 : (if n ≤ (6 * m) ^ 2 + 2 then K0 m else 0) = 0 :=
            if_neg (not_le.mpr hnbig)
          rw [hif2]
          have hK' : max 2 ((6 * m) ^ 2 + 2) ≤ n := max_le hn.two_le (by omega)
          have hsmall := hsmall_of_large (σ₀ := 1 / (6 * (m : ℝ))) hpos h4σ hm hK'
          have hb := CorrB.E1p_bound_corr (m := m) (W := W) (h := h) hm hn hnW hW0 hnD hpos
            h4σ hz hz' hsmall
          have heqm : e1pMajor m n = cpowMajor m n := by
            unfold e1pMajor; rw [if_neg (not_le.mpr hnbig), add_zero]
          rw [heqm]
          refine le_trans hb ?_
          unfold cpowMajor
          linarith
        · have hif2 : (if n ≤ (6 * m) ^ 2 + 2 then K0 m else 0) = K0 m := if_pos (by omega)
          rw [hif2]
          have hb := E1p_uniform_crude (m := m) (W := W) (h := h) hm hn hnW hz hz'
          have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn.one_le
          have hB1 : (n : ℝ) ^ (-(2 / 3 : ℝ)) ≤ 1 := by
            have h := Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num : (-(2 / 3 : ℝ)) ≤ 0)
            rwa [Real.rpow_zero] at h
          have hstep : K0 m * (n : ℝ) ^ (-(2 / 3 : ℝ)) ≤ K0 m :=
            mul_le_of_le_one_right (K0_nonneg m) hB1
          linarith
  · rw [E1p, if_neg (fun hc : n.Prime ∧ ¬ n ∣ W => hn hc.1), sub_self, norm_zero]
    linarith


end Corr
end GYMaj
