import Submission.Work.GYFactor8
import Submission.Work.GYCount
import Submission.Commons.Data.Nat.prod_inv_one_sub_inv_primeFactors
import Submission.Commons.Analysis.Complex.norm_tprod_one_add_sub_one_le_exp

/-!
# Green–Tao §10, step 3: the constant `G₁(0,0)·G₂(0,0) = (1+o(1))(W/φ(W))^m`

`Submission/Work/GYFactor8.lean` proves Green–Tao (10.2) = (ddr):

`mainSum R W A b = G₁(0,0)·G₂(0,0)·(log R)^m + O(C^m·B·(1+(log R)^{m-1}) + C^m·B·e^{-δ√(log R)})`.

This file evaluates the constant:
* `G₂(0,0) = (W/φ(W))^m` exactly (for `W ≠ 0`), because `E_p^{(2)}(0,0) = (1-1/p)^{-m}` for
  `p ∣ W` and `1` otherwise, and `∏_{p | W} (1-1/p) = φ(W)/W`;
* `‖G₁(0,0) − 1‖ ≤ e^{η} − 1` where `η` is the tail of the `E^{(1)}` majorant beyond `w`, whenever
  every prime `≤ w` divides `W`.  Since `W = ∏_{p ≤ w} p` with `w` arbitrarily large, this is
  `o(1)`.

Feeding these into `mainSum_eq_logR` yields `hmain`, the divisor-sum input of
`boxAvgGood_of_hmain`.
-/

open Finset
open scoped BigOperators

set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false

namespace GYMaj
namespace BoxAvg

variable {m t : ℕ}
variable {W Amax : ℕ} {A : Fin m → Fin t → ℤ} {b : Fin m → ℤ}

open Commons.NumberTheory.Sieve

/-! ## 1. `E^{(2)}` and `G₂` at `z = z' = 0` -/

/-- `E_p^{(2)}` at `z = z' = 0` for a prime `p ∣ W`. -/
lemma E2p_zero_prime {W p : ℕ} (h : p.Prime ∧ p ∣ W) :
    E2p (m := m) W 0 0 p = ((1 - (p : ℂ)⁻¹)⁻¹) ^ m := by
  rw [E2p, if_pos h]
  have hfac : ∀ j : Fin m,
      ((1 - (p : ℂ) ^ (-(1 + (0 : Fin m → ℂ) j)))⁻¹
          * (1 - (p : ℂ) ^ (-(1 + (0 : Fin m → ℂ) j)))⁻¹
          * (1 - (p : ℂ) ^ (-(1 + (0 : Fin m → ℂ) j + (0 : Fin m → ℂ) j))))
        = (1 - (p : ℂ)⁻¹)⁻¹ := by
    intro j
    have h1 : (-(1 + (0 : Fin m → ℂ) j) : ℂ) = -1 := by simp
    have h2 : (-(1 + (0 : Fin m → ℂ) j + (0 : Fin m → ℂ) j) : ℂ) = -1 := by simp
    rw [h1, h2, Complex.cpow_neg_one]
    have hne : (1 - (p : ℂ)⁻¹) ≠ 0 := by
      intro hc
      have h2 : (p : ℂ) = 1 := by
        have := sub_eq_zero.mp hc
        rw [eq_comm] at this
        exact inv_eq_one.mp this
      have h3 : p = 1 := Nat.cast_eq_one.mp h2
      have := h.1.two_le
      omega
    rw [mul_assoc, inv_mul_cancel₀ hne, mul_one]
  rw [Finset.prod_congr rfl (fun j _ => hfac j), Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]

/-- `E_p^{(2)}` at `z = z' = 0` when `p` is not a prime divisor of `W`. -/
lemma E2p_zero_not {W p : ℕ} (h : ¬(p.Prime ∧ p ∣ W)) :
    E2p (m := m) W 0 0 p = 1 := by
  rw [E2p, if_neg h]

/-- `E_p^{(2)}` evaluated at `z = z' = 0`. -/
lemma E2p_zero (W p : ℕ) :
    E2p (m := m) W 0 0 p = if p.Prime ∧ p ∣ W then ((1 - (p : ℂ)⁻¹)⁻¹) ^ m else 1 := by
  by_cases h : p.Prime ∧ p ∣ W
  · rw [E2p_zero_prime h, if_pos h]
  · rw [E2p_zero_not h, if_neg h]

/-- **`G₂(0,0) = (W/φ(W))^m`** (Green–Tao, the exact evaluation of the `E^{(2)}` product). -/
theorem G2u_zero (H : LocHyp W Amax A b) :
    G2u (m := m) W 0 0 = ((W : ℂ) / (Nat.totient W : ℂ)) ^ m := by
  have hW0 : W ≠ 0 := ne_of_gt H.hW0
  rw [G2u_eq_prod H 0 0]
  -- only the prime divisors of `W` contribute
  have hstep : ∏ n ∈ W.divisors, E2p (m := m) W 0 0 n
      = ∏ n ∈ W.divisors.filter Nat.Prime, E2p (m := m) W 0 0 n := by
    rw [← Finset.prod_filter_mul_prod_filter_not (s := W.divisors) (p := fun n => n.Prime)
      (f := fun n => E2p (m := m) W 0 0 n)]
    have hz : ∏ n ∈ W.divisors.filter (fun n => ¬ n.Prime), E2p (m := m) W 0 0 n = 1 := by
      refine Finset.prod_eq_one (fun n hn => ?_)
      rw [Finset.mem_filter] at hn
      rw [E2p_zero, if_neg]
      exact fun hc => hn.2 hc.1
    rw [hz, mul_one]
  rw [hstep]
  have hpf : W.divisors.filter Nat.Prime = W.primeFactors := by
    ext p
    rw [Finset.mem_filter, Nat.mem_divisors, Nat.mem_primeFactors]
    constructor
    · rintro ⟨⟨h1, _⟩, h2⟩; exact ⟨h2, h1, hW0⟩
    · rintro ⟨h1, h2, _⟩; exact ⟨⟨h2, hW0⟩, h1⟩
  rw [hpf]
  have hval : ∀ p ∈ W.primeFactors, E2p (m := m) W 0 0 p = ((1 - (p : ℂ)⁻¹)⁻¹) ^ m := by
    intro p hp
    rw [E2p_zero, if_pos ⟨(Nat.mem_primeFactors.mp hp).1, (Nat.mem_primeFactors.mp hp).2.1⟩]
  rw [Finset.prod_congr rfl hval, Finset.prod_pow, Commons.Data.Nat.prod_inv_one_sub_inv_primeFactors W hW0]


/-! ## 2. `G₁(0,0) = 1 + o(1)` -/

/-- The tail of the `E^{(1)}` majorant beyond `w`. -/
noncomputable def tailMajor (m w : ℕ) : ℝ := ∑' k : ℕ, e1pMajor m (k + (w + 1))

lemma e1pMajor_nonneg (m n : ℕ) : 0 ≤ e1pMajor m n := by
  refine add_nonneg (by unfold cpowMajor; positivity) ?_
  by_cases h : n ≤ (6 * m) ^ 2 + 2
  · simp only [if_pos h]; positivity
  · simp [if_neg h]

lemma tailMajor_nonneg (m w : ℕ) : 0 ≤ tailMajor m w :=
  tsum_nonneg (fun k => e1pMajor_nonneg m (k + (w + 1)))

/-- The `if`-form of the tail of the majorant. -/
lemma summable_ite_e1pMajor {m : ℕ} (hm : 1 ≤ m) (w : ℕ) :
    Summable (fun n : ℕ => if n ≤ w then (0 : ℝ) else e1pMajor m n) := by
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) (summable_e1pMajor hm)
  · by_cases h : n ≤ w
    · simp [h]
    · simp [h, e1pMajor_nonneg]
  · by_cases h : n ≤ w
    · simp [h, e1pMajor_nonneg]
    · simp [h]

/-- The `if`-form of the tail is `tailMajor`. -/
lemma tsum_ite_e1pMajor {m : ℕ} (hm : 1 ≤ m) (w : ℕ) :
    (∑' n : ℕ, if n ≤ w then (0 : ℝ) else e1pMajor m n) = tailMajor m w := by
  set h : ℕ → ℝ := fun n => if n ≤ w then 0 else e1pMajor m n with hh
  have hsum : Summable h := summable_ite_e1pMajor hm w
  have h1 := Summable.sum_add_tsum_nat_add (f := h) (k := w + 1) hsum
  have hzero : ∑ i ∈ Finset.range (w + 1), h i = 0 := by
    refine Finset.sum_eq_zero (fun i hi => ?_)
    rw [Finset.mem_range] at hi
    rw [hh]
    simp only
    rw [if_pos (by omega)]
  have hpt : ∀ i : ℕ, h (i + (w + 1)) = e1pMajor m (i + (w + 1)) := by
    intro i
    rw [hh]
    simp only
    rw [if_neg (by omega)]
  rw [hzero, zero_add] at h1
  rw [tailMajor, ← h1]
  exact tsum_congr hpt

/-- **`G₁(0,0)` is `1` up to the tail of the majorant**: if every prime `≤ w` divides `W` then
`‖G₁(0,0) - 1‖ ≤ e^{tailMajor m w} - 1`. -/
theorem G1u_zero_close (H : LocHyp W Amax A b) {w : ℕ}
    (hw : ∀ q : ℕ, q.Prime → q ≤ w → q ∣ W) :
    ‖G1u (m := m) W A b 0 0 - 1‖ ≤ Real.exp (tailMajor m w) - 1 := by
  have hm : 1 ≤ m := H.hm
  have hpos := sixth_pos hm
  have hz0 : ∀ j : Fin m, -(1 / (6 * (m : ℝ))) ≤ ((0 : Fin m → ℂ) j).re := by
    intro j
    rw [Pi.zero_apply, Complex.zero_re]
    linarith [hpos]
  set u : ℕ → ℂ := fun n => E1p (m := m) W A b 0 0 n - 1 with hu
  have hsum : Summable (fun n : ℕ => ‖u n‖) := by
    have h := E1p_summable H (σ₀ := 1 / (6 * (m : ℝ))) (le_of_lt hpos) (sixth_small hm).1
      (sixth_small hm).2 hz0 hz0
    simpa [hu] using h
  have hpt : ∀ n : ℕ, ‖u n‖ ≤ if n ≤ w then (0 : ℝ) else e1pMajor m n := by
    intro n
    by_cases hn : n ≤ w
    · rw [if_pos hn]
      have hE : E1p (m := m) W A b 0 0 n = 1 := by
        by_cases hnp : n.Prime
        · rw [E1p, if_neg (fun hc : n.Prime ∧ ¬ n ∣ W => hc.2 (hw n hnp hn))]
        · rw [E1p, if_neg (fun hc : n.Prime ∧ ¬ n ∣ W => hnp hc.1)]
      rw [hu]
      simp only [hE, sub_self, norm_zero, le_refl]
    · rw [if_neg hn]
      have hb := E1p_sub_one_le_major' H n (z := 0) (z' := 0) hz0 hz0
      simpa [hu] using hb
  have hle : (∑' n : ℕ, ‖u n‖) ≤ tailMajor m w := by
    have h2 := Summable.tsum_le_tsum (fun n => hpt n) hsum (summable_ite_e1pMajor hm w)
    rwa [tsum_ite_e1pMajor hm w] at h2
  have hprod : G1u (m := m) W A b 0 0 = ∏' n : ℕ, (1 + u n) := by
    rw [G1u]
    refine tprod_congr (fun n => ?_)
    rw [hu]
    simp only
    ring
  rw [hprod]
  refine le_trans (Commons.Analysis.Complex.norm_tprod_one_add_sub_one_le_exp u hsum) ?_
  have := Real.exp_le_exp_of_le hle
  linarith

/-! ## 3. The uniform constants of Green–Tao Lemma 10.4 -/

/-- The pair of constants produced by `zeta_bound_m_strip_sixth`, as a function of `m` alone. -/
noncomputable def zbPair (m : ℕ) : ℝ × ℝ :=
  if h : 1 ≤ m then
    (Classical.choose (Commons.NumberTheory.Zeta.zeta_bound_m_strip_sixth m h),
      Classical.choose (Classical.choose_spec (Commons.NumberTheory.Zeta.zeta_bound_m_strip_sixth m h)))
  else (1, 1)

/-- The `δ` of Green–Tao Lemma 10.4 (uniform in all the other data). -/
noncomputable def zbD (m : ℕ) : ℝ := (zbPair m).1

/-- The `C` of Green–Tao Lemma 10.4 (uniform in all the other data). -/
noncomputable def zbC (m : ℕ) : ℝ := (zbPair m).2

lemma zbD_eq {m : ℕ} (hm : 1 ≤ m) :
    zbD m = Classical.choose (Commons.NumberTheory.Zeta.zeta_bound_m_strip_sixth m hm) := by
  unfold zbD zbPair
  rw [dif_pos hm]

lemma zbC_eq {m : ℕ} (hm : 1 ≤ m) :
    zbC m = Classical.choose
      (Classical.choose_spec (Commons.NumberTheory.Zeta.zeta_bound_m_strip_sixth m hm)) := by
  unfold zbC zbPair
  rw [dif_pos hm]

lemma zbD_pos {m : ℕ} (hm : 1 ≤ m) : 0 < zbD m := by
  rw [zbD_eq hm]
  exact (Classical.choose_spec (Classical.choose_spec
    (Commons.NumberTheory.Zeta.zeta_bound_m_strip_sixth m hm))).1

lemma zbC_pos {m : ℕ} (hm : 1 ≤ m) : 0 < zbC m := by
  rw [zbC_eq hm]
  exact (Classical.choose_spec (Classical.choose_spec
    (Commons.NumberTheory.Zeta.zeta_bound_m_strip_sixth m hm))).2.1

/-! ## 4. Green–Tao (10.2) = (ddr) with the uniform constants -/

/-- **Green–Tao (10.2) = (ddr)** with the constants `zbD`, `zbC` explicit. -/
theorem mainSum_eq_logR_expl (H : LocHyp W Amax A b) {R : ℕ} (hR : 3 ≤ R) :
      ‖(mainSum (m := m) (t := t) R W A b : ℂ)
          - (G1u W A b 0 0 * G2u (m := m) W 0 0) * (Real.log (R : ℝ)) ^ m‖
        ≤ (zbC m) ^ m * stripBound W m * (1 + (Real.log (R : ℝ)) ^ (m - 1))
          + (zbC m) ^ m * stripBound W m
              * Real.exp (-(zbD m * Real.sqrt (Real.log (R : ℝ)))) := by
  have hspec := (Classical.choose_spec (Classical.choose_spec
    (Commons.NumberTheory.Zeta.zeta_bound_m_strip_sixth m H.hm))).2
  have hR1 : (1 : ℝ) < (R : ℝ) := by exact_mod_cast (by omega : 1 < R)
  have hRpos : (0 : ℝ) < (R : ℝ) := by linarith
  have hlog : 0 < Real.log (R : ℝ) := Real.log_pos hR1
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hlog3one : (1 : ℝ) < Real.log 3 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 3)]
    exact Real.exp_one_lt_three
  have ha : 0 < 1 / Real.log (R : ℝ) := by positivity
  have hlogle : Real.log 3 ≤ Real.log (R : ℝ) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hR)
  have hab : 1 / Real.log (R : ℝ) ≤ 1 + (m : ℝ) := by
    have h1 : 1 / Real.log (R : ℝ) ≤ 1 / Real.log 3 :=
      one_div_le_one_div_of_le hlog3 hlogle
    have h2 : 1 / Real.log 3 ≤ 1 := by
      rw [div_le_one hlog3]; exact le_of_lt hlog3one
    have hm : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast H.hm
    linarith
  have hRc : (R : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt (by omega : 0 < R))
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast H.hm
  have hc1m : (1 : ℝ) < 1 + (m : ℝ) := by linarith
  have hmain' := hspec.2 (R : ℝ) (by exact_mod_cast hR)
    (fun z z' => G1u W A b z z' * G2u W z z') (stripBound W m)
    (by unfold stripBound; positivity)
    (((continuousOn_G1u H).mul (continuousOn_G2u H)).mono
      (fun x hx => ⟨fun i => (hx.1 i).1, fun i => (hx.2 i).1⟩))
    (fun j z z' hz hz' =>
      (differentiableAt_G1u_curve₁ H (fun i => (hz i).1) (fun i => (hz' i).1)).mul
        (differentiableAt_G2u_curve₁ H (fun i => (hz i).1) (fun i => (hz' i).1)))
    (fun j z z' hz hz' =>
      (differentiableAt_G1u_curve₂ H (fun i => (hz i).1) (fun i => (hz' i).1)).mul
        (differentiableAt_G2u_curve₂ H (fun i => (hz i).1) (fun i => (hz' i).1)))
    (fun z z' hz hz' => by
      rw [norm_mul]
      exact mul_le_mul (norm_G1u_le H (fun i => le_of_lt (hz i).1) (fun i => le_of_lt (hz' i).1))
        (norm_G2u_le H (fun i => le_of_lt (hz i).1) (fun i => le_of_lt (hz' i).1))
        (norm_nonneg _) (Real.exp_nonneg _))
  rw [mainSum_eq_contour (m := m) (t := t) H.hm (c := 1 + (m : ℝ)) (by linarith) R W A b
      H.ht H.hA H.hne H.hW0, ContourInt_eq]
  rw [show (∫ t_ : Fin m → ℝ, ∫ t_' : Fin m → ℝ,
        Eker (t := t) (1 + (m : ℝ)) R W A b (fun i => (t_ i, t_' i)))
      = ∫ t_ : Fin m → ℝ, ∫ t_' : Fin m → ℝ,
        Psi R W A b (fun i => sline (1 + (m : ℝ)) (t_ i))
          (fun i => sline (1 + (m : ℝ)) (t_' i)) by
    simp_rw [Eker_eq_Psi hc1m H R]]
  rw [show (∫ t_ : Fin m → ℝ, ∫ t_' : Fin m → ℝ,
        Psi R W A b (fun i => sline (1 + (m : ℝ)) (t_ i))
          (fun i => sline (1 + (m : ℝ)) (t_' i)))
      = ∫ t_ : Fin m → ℝ, ∫ t_' : Fin m → ℝ,
        Psi R W A b (fun i => sline (1 / Real.log (R : ℝ)) (t_ i))
          (fun i => sline (1 / Real.log (R : ℝ)) (t_' i)) from
    contourShift_Psi H hR ha hab]
  -- move `I^m * I^m` inside the two integrals
  simp_rw [← MeasureTheory.integral_mul_const]
  -- identify the integrand with the one of Green–Tao Lemma 10.4
  have hI : (∫ t_ : Fin m → ℝ, ∫ t_' : Fin m → ℝ,
        Psi R W A b (fun i => sline (1 / Real.log (R : ℝ)) (t_ i))
          (fun i => sline (1 / Real.log (R : ℝ)) (t_' i)) * (Complex.I ^ m * Complex.I ^ m))
      = (∫ t_ : Fin m → ℝ, ∫ t_' : Fin m → ℝ,
          (G1u W A b (fun j => Commons.NumberTheory.Zeta.zetaM1Eta (R : ℝ) (t_ j))
              (fun j => Commons.NumberTheory.Zeta.zetaM1Eta (R : ℝ) (t_' j))
            * G2u W (fun j => Commons.NumberTheory.Zeta.zetaM1Eta (R : ℝ) (t_ j))
              (fun j => Commons.NumberTheory.Zeta.zetaM1Eta (R : ℝ) (t_' j)))
          * (∏ j, (riemannZeta (1 + Commons.NumberTheory.Zeta.zetaM1Eta (R : ℝ) (t_ j)
                + Commons.NumberTheory.Zeta.zetaM1Eta (R : ℝ) (t_' j))
              / (riemannZeta (1 + Commons.NumberTheory.Zeta.zetaM1Eta (R : ℝ) (t_ j))
                  * riemannZeta (1 + Commons.NumberTheory.Zeta.zetaM1Eta (R : ℝ) (t_' j)))))
          * (((R : ℝ)) : ℂ) ^ (∑ j, (Commons.NumberTheory.Zeta.zetaM1Eta (R : ℝ) (t_ j)
              + Commons.NumberTheory.Zeta.zetaM1Eta (R : ℝ) (t_' j)))
          * (∏ j, ((Commons.NumberTheory.Zeta.zetaM1Eta (R : ℝ) (t_ j)) ^ 2
                * (Commons.NumberTheory.Zeta.zetaM1Eta (R : ℝ) (t_' j)) ^ 2)⁻¹)
          * Complex.I ^ m * Complex.I ^ m) := by
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun t_ => ?_)
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun t_' => ?_)
    exact Psi_mul_I_eq hRc t_ t_'
  rw [hI]
  rw [zbC_eq H.hm, zbD_eq H.hm]
  exact hmain'


/-! ## 5. `hmain`: the divisor-sum main term from the constants -/

/-- **Green–Tao (ddr) in the shape required by `boxAvgGood_of_hmain`**, from the explicit
inequalities `htail` (smallness of `G₁(0,0) - 1`) and `herr` (smallness of the contour error).

`hw` says that every prime `≤ w` divides `W` (so `W = ∏_{p ≤ w} p` is typical), `hwbig` that `w`
is at least `2·(k!·k)²` (so that `LocHyp.hWdiv` holds for the coefficient bound `k!·k`). -/
theorem hmain_of_bounds (k R W : ℕ) (ε : ℝ) (hR : 3 ≤ R) (hε : 0 < ε) (hW0 : 0 < W)
    {w : ℕ} (hw2 : 2 ≤ w) (hw : ∀ q : ℕ, q.Prime → q ≤ w → q ∣ W)
    (hwbig : 2 * (k.factorial * k) ^ 2 ≤ w)
    (htail : ∀ m : ℕ, 1 ≤ m → m ≤ k * 2 ^ (k - 1) → Real.exp (tailMajor m w) - 1 ≤ ε / 4)
    (herr : ∀ m : ℕ, 1 ≤ m → m ≤ k * 2 ^ (k - 1) →
      (zbC m) ^ m * stripBound W m * (1 + (Real.log (R : ℝ)) ^ (m - 1))
        + (zbC m) ^ m * stripBound W m * Real.exp (-(zbD m * Real.sqrt (Real.log (R : ℝ))))
      ≤ (ε / 4) * ((W : ℝ) * Real.log (R : ℝ) / (Nat.totient W : ℝ)) ^ m) :
    ∀ (m t : ℕ) (A : Fin m → Fin t → ℤ) (b : Fin m → ℤ) (l r : Fin t → ℤ),
      BoxData k R W m t A b l r →
      |mainSum R W A b - ((W : ℝ) * Real.log (R : ℝ) / (Nat.totient W : ℝ)) ^ m|
        ≤ (ε / 2) * ((W : ℝ) * Real.log (R : ℝ) / (Nat.totient W : ℝ)) ^ m := by
  intro m t A b l r hD
  obtain ⟨hm1, hmK, ht1, ht2, hne, hprop, hbound, hside, hpos⟩ := hD
  have hφpos : (0 : ℝ) < (Nat.totient W : ℝ) :=
    Nat.cast_pos.mpr (Nat.totient_pos.mpr hW0)
  have H : LocHyp W (k.factorial * k) A b :=
    { hm := hm1, ht := by omega, hW0 := hW0, hA := hbound, hne := hne, hprop := hprop,
      hWdiv := fun q hq hqle => hw q hq (le_trans hqle hwbig) }
  have hex := mainSum_eq_logR_expl (m := m) (t := t) H hR
  have hG2 := G2u_zero (m := m) H
  have hG1 : ‖G1u (m := m) W A b 0 0 - 1‖ ≤ ε / 4 :=
    le_trans (G1u_zero_close (m := m) H hw) (htail m hm1 hmK)
  have hR1 : (1 : ℝ) < (R : ℝ) := by exact_mod_cast (by omega : 1 < R)
  have hlogpos : (0 : ℝ) ≤ Real.log (R : ℝ) := (Real.log_pos hR1).le
  have hPnn : 0 ≤ (W : ℝ) * Real.log (R : ℝ) / (Nat.totient W : ℝ) := by positivity
  set P : ℝ := (W : ℝ) * Real.log (R : ℝ) / (Nat.totient W : ℝ) with hP
  have hQ : (P : ℂ) ^ m
      = ((W : ℂ) / (Nat.totient W : ℂ)) ^ m * (Real.log (R : ℝ) : ℂ) ^ m := by
    have h1 : (P : ℂ) = ((W : ℂ) / (Nat.totient W : ℂ)) * (Real.log (R : ℝ) : ℂ) := by
      rw [hP]
      push_cast
      ring
    rw [h1, mul_pow]
  have hT : (G1u (m := m) W A b 0 0 * G2u (m := m) W 0 0) * (Real.log (R : ℝ) : ℂ) ^ m
      = G1u (m := m) W A b 0 0 * (P : ℂ) ^ m := by
    rw [hG2, hQ]
    ring
  have hsplit : (mainSum (m := m) (t := t) R W A b : ℂ) - (P : ℂ) ^ m
      = ((mainSum (m := m) (t := t) R W A b : ℂ)
            - (G1u (m := m) W A b 0 0 * G2u (m := m) W 0 0)
              * (Real.log (R : ℝ) : ℂ) ^ m)
        + ((G1u (m := m) W A b 0 0 * G2u (m := m) W 0 0)
              * (Real.log (R : ℝ) : ℂ) ^ m - (P : ℂ) ^ m) := by ring
  have hB : ‖(G1u (m := m) W A b 0 0 * G2u (m := m) W 0 0)
        * (Real.log (R : ℝ) : ℂ) ^ m - (P : ℂ) ^ m‖ ≤ (ε / 4) * P ^ m := by
    rw [hT, show G1u (m := m) W A b 0 0 * (P : ℂ) ^ m - (P : ℂ) ^ m
      = (G1u (m := m) W A b 0 0 - 1) * (P : ℂ) ^ m by ring]
    rw [norm_mul, Complex.norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hPnn]
    exact mul_le_mul_of_nonneg_right hG1 (pow_nonneg hPnn m)
  have hA : ‖(mainSum (m := m) (t := t) R W A b : ℂ)
        - (G1u (m := m) W A b 0 0 * G2u (m := m) W 0 0)
          * (Real.log (R : ℝ) : ℂ) ^ m‖ ≤ (ε / 4) * P ^ m :=
    le_trans hex (herr m hm1 hmK)
  have key : ‖(mainSum (m := m) (t := t) R W A b : ℂ) - (P : ℂ) ^ m‖ ≤ (ε / 2) * P ^ m := by
    rw [hsplit]
    refine le_trans (norm_add_le _ _) ?_
    linarith
  have hnorm : ‖(mainSum (m := m) (t := t) R W A b : ℂ) - (P : ℂ) ^ m‖
      = |mainSum (m := m) (t := t) R W A b - P ^ m| := by
    rw [← Complex.ofReal_pow, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  rw [hnorm] at key
  exact key


/-! ## 6. `BoxAvgGood` from the explicit constants -/

lemma stripBound_pos (W m : ℕ) : 0 < stripBound W m := by
  unfold stripBound; positivity

/-- **Green–Tao Proposition 9.5** (`BoxAvgGood`) from the explicit numeric conditions, with `W`
an arbitrary positive integer divisible by all primes `≤ w` and `w` large enough for the
`E^{(1)}` tail (`htail`) and the coefficient bound (`hwbig`), and `R` large enough (`herr`,
`hsmall`). -/
theorem boxAvgGood_of_consts (k R W : ℕ) (ε : ℝ) (hR : 3 ≤ R) (hRk : 3 * k ≤ R)
    (hW : 1 ≤ W) (hε : 0 < ε)
    (hsmall : 6 * (3 * (k : ℝ)) * (Real.log (R : ℝ)) ^ (k * 2 ^ (k - 1))
      ≤ ε * (R : ℝ) ^ 6)
    {w : ℕ} (hw2 : 2 ≤ w) (hw : ∀ q : ℕ, q.Prime → q ≤ w → q ∣ W)
    (hwbig : 2 * (k.factorial * k) ^ 2 ≤ w)
    (htail : ∀ m : ℕ, 1 ≤ m → m ≤ k * 2 ^ (k - 1) → Real.exp (tailMajor m w) - 1 ≤ ε / 4)
    (herr : ∀ m : ℕ, 1 ≤ m → m ≤ k * 2 ^ (k - 1) →
      (zbC m) ^ m * stripBound W m * (1 + (Real.log (R : ℝ)) ^ (m - 1))
        + (zbC m) ^ m * stripBound W m * Real.exp (-(zbD m * Real.sqrt (Real.log (R : ℝ))))
      ≤ (ε / 4) * ((W : ℝ) * Real.log (R : ℝ) / (Nat.totient W : ℝ)) ^ m) :
    BoxAvgGood k R W ε :=
  boxAvgGood_of_hmain k R W ε hR hRk hW hε hsmall
    (hmain_of_bounds k R W ε hR hε (by omega) hw2 hw hwbig htail herr)

end BoxAvg
end GYMaj
