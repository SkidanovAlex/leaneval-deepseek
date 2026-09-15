import Submission.Work.GYFactor4
import Submission.Commons.NumberTheory.Sieve.locCount_one_active
import Submission.Commons.NumberTheory.Sieve.locCount_ite_eq_zero_of_dvd
import Submission.Commons.NumberTheory.Sieve.not_proportional_zmod_of_small
import Submission.Commons.NumberTheory.Sieve.locCount_ite_le_two
import Submission.Commons.NumberTheory.Sieve.sum_filter_card_one
import Submission.Commons.NumberTheory.Sieve.sum_univ_eq_sum_three
import Submission.Commons.Analysis.Complex.inv_prod_three_expansion
import Submission.Commons.NumberTheory.Sieve.card_omega_ge_two_le
import Submission.Commons.NumberTheory.Zeta.tprod_E3_eq_zeta_ratio
import Submission.Commons.Analysis.Complex.inv_one_sub_approx
import Submission.Commons.Analysis.Complex.norm_prod_one_add_sub_one_sub_sum_le
import Submission.Commons.Analysis.Complex.norm_tprod_one_add_le_exp

/-!
# Green–Tao Lemma 10.3: the local factor analysis of the §10 Euler product

Green–Tao (10.8) factorises the local factor `E_p(z,z') = Σ_σ vSys p σ (-1)^{|X|+|X'|} p^{-(Σ z)}`
of the Dirichlet series as `E_p = E_p^{(1)} E_p^{(2)} E_p^{(3)}`, where
* `E_p^{(3)} = ∏_j (1-p^{-1-z_j})(1-p^{-1-z'_j})(1-p^{-1-z_j-z'_j})⁻¹` (`E3p`), whose Euler product
  is the ratio of zeta values (Green–Tao (10.9), commons `tprod_E3_eq_zeta_ratio`),
* `E_p^{(2)} = ∏_j (1-p^{-1-z_j})⁻¹(1-p^{-1-z'_j})⁻¹(1-p^{-1-z_j-z'_j})` for `p | W` and `1`
  otherwise (`E2p`) — a FINITE Euler product, since the primes dividing `W` are finite,
* `E_p^{(1)} = E_p/E_p^{(3)}` for `p ∤ W` and `1` otherwise (`E1p`), with the key estimate
  `E_p^{(1)}(z,z') = 1 + O_m(p^{-2+2σ₀})` on the strip `-σ₀ ≤ Re z_j ≤ 100`.

## The local data on the strip

The analysis rests on Green–Tao Lemma 9.2, i.e. the local counts `vSys`:
* `vSys p 0 = 1` always;
* `vSys p σ = 0` for `p | W` and `σ ≠ 0` (because `θ_i ≡ 1 mod p` when `p | W`);
* for `p ∤ W`: `vSys p σ = 1/p` when `|σ.X ∪ σ.X'| = 1` (`locCount_one_active`) and
  `‖vSys p σ‖ ≤ p^{-2}` when `|σ.X ∪ σ.X'| ≥ 2` (`card_omega_ge_two_le` together with
  `not_proportional_zmod_of_small`).

The non-proportionality needs `2·Amax² < p`; this is supplied by the hypothesis that **every prime
`≤ 2·Amax²` divides `W`** (the formal counterpart of Green–Tao's choice `W = ∏_{p ≤ w} p` with
`|L_{ij}| ≤ √w/2`, see `LocHyp.hWdiv` and the ROADMAP note of session 29b).
-/

open Finset
open scoped BigOperators

set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false

namespace GYMaj
namespace BoxAvg

variable {m t : ℕ}

open Commons.NumberTheory.Sieve

/-! ## 1. The three local factors of Green–Tao (10.8) -/

/-- The third local factor `E_p^{(3)}`. -/
noncomputable def E3p (z z' : Fin m → ℂ) (p : ℕ) : ℂ :=
  if p.Prime then
    ∏ j, ((1 - (p : ℂ) ^ (-(1 + z j))) * (1 - (p : ℂ) ^ (-(1 + z' j)))
        * (1 - (p : ℂ) ^ (-(1 + z j + z' j)))⁻¹)
  else 1

/-- The second local factor `E_p^{(2)}`. -/
noncomputable def E2p (W : ℕ) (z z' : Fin m → ℂ) (p : ℕ) : ℂ :=
  if p.Prime ∧ p ∣ W then
    ∏ j, (((1 - (p : ℂ) ^ (-(1 + z j)))⁻¹ * (1 - (p : ℂ) ^ (-(1 + z' j)))⁻¹
        * (1 - (p : ℂ) ^ (-(1 + z j + z' j)))))
  else 1

/-- The first local factor `E_p^{(1)} := E_p/(E_p^{(2)}E_p^{(3)})`. -/
noncomputable def E1p (W : ℕ) (A : Fin m → Fin t → ℤ) (b : Fin m → ℤ) (z z' : Fin m → ℂ)
    (p : ℕ) : ℂ :=
  if p.Prime ∧ ¬ p ∣ W then eulerFactor m (vSys W A b) z z' p / E3p z z' p else 1

/-! ## 2. The local weight `vSys` on the strip -/

/-- The local-data hypotheses of the §10 analysis, bundled.  `hWdiv` is the formal counterpart of
Green–Tao's choice of `W`: every prime `≤ 2·Amax²` divides `W`, so the primes with `p ∤ W` are large
enough for the rational-vs-`ZMod p` non-degeneracy of the forms. -/
structure LocHyp (W Amax : ℕ) (A : Fin m → Fin t → ℤ) (b : Fin m → ℤ) : Prop where
  hm : 1 ≤ m
  ht : 1 ≤ t
  hW0 : 0 < W
  hA : ∀ i j, (A i j).natAbs ≤ Amax
  hne : ∀ i, ∃ j, A i j ≠ 0
  hprop : ∀ i i', i ≠ i' → ¬ ∃ lam : ℚ, ∀ j, (A i' j : ℚ) = lam * (A i j : ℚ)
  hWdiv : ∀ q : ℕ, q.Prime → q ≤ 2 * Amax ^ 2 → q ∣ W

variable {W Amax : ℕ} {A : Fin m → Fin t → ℤ} {b : Fin m → ℤ}

lemma LocHyp.one_le_Amax (H : LocHyp W Amax A b) : 1 ≤ Amax := by
  have hm : 1 ≤ m := H.hm
  obtain ⟨j, hj⟩ := H.hne ⟨0, by omega⟩
  have h1 : (A ⟨0, by omega⟩ j).natAbs ≠ 0 := by
    simpa [Int.natAbs_eq_zero] using hj
  exact le_trans (Nat.one_le_iff_ne_zero.mpr h1) (H.hA _ j)

lemma LocHyp.lt_of_not_dvd (H : LocHyp W Amax A b) {p : ℕ} (hp : p.Prime) (h : ¬ p ∣ W) :
    2 * Amax ^ 2 < p := by
  by_contra hcon
  exact h (H.hWdiv p hp (le_of_not_gt hcon))

lemma LocHyp.Amax_lt_of_not_dvd (H : LocHyp W Amax A b) {p : ℕ} (hp : p.Prime) (h : ¬ p ∣ W) :
    Amax < p := by
  have h1 := H.lt_of_not_dvd hp h
  have h2 := H.one_le_Amax
  by_cases h3 : Amax = 1
  · rw [h3]; exact hp.one_lt
  · have h4 : 2 ≤ Amax := by omega
    have h5 : Amax < 2 * Amax ^ 2 := by nlinarith
    omega

/-- `vSys` vanishes at primes dividing `W` when `σ ≠ 0`. -/
lemma vSys_eq_zero_of_dvd_W (H : LocHyp W Amax A b) {p : ℕ} (hp : p.Prime) (hpW : p ∣ W)
    {σ : PrimeData m} (hσ : σ ≠ 0) : vSys W A b p σ = 0 := by
  haveI : NeZero p := NeZero.of_pos hp.pos
  rw [vSys, dif_pos hp,
    Commons.NumberTheory.Sieve.locCount_ite_eq_zero_of_dvd hp W Amax A b σ hσ H.ht hpW,
    Nat.cast_zero, zero_div]

/-- `vSys` equals the density `1/p` when exactly one index is active and `p ∤ W`. -/
lemma vSys_eq_inv_of_card_one (H : LocHyp W Amax A b) {p : ℕ} (hp : p.Prime) (hpW : ¬ p ∣ W)
    {σ : PrimeData m} (hcard : (σ.X ∪ σ.X').card = 1) : vSys W A b p σ = ((p : ℂ))⁻¹ := by
  haveI : NeZero p := NeZero.of_pos hp.pos
  rw [vSys, dif_pos hp,
    Commons.NumberTheory.Sieve.locCount_one_active hp W Amax A b σ H.ht H.hA H.hne H.hW0 hpW
      (H.Amax_lt_of_not_dvd hp hpW) hcard]
  rw [Nat.cast_pow, div_eq_mul_inv]
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hp.pos)
  have hpw : (p : ℂ) ^ t = (p : ℂ) ^ (t - 1) * (p : ℂ) := by
    conv_lhs => rw [(Nat.sub_add_cancel H.ht).symm]
    rw [pow_succ]
  rw [hpw, mul_inv, ← mul_assoc,
    mul_inv_cancel₀ (pow_ne_zero _ hp0), one_mul]

/-- If two distinct indices are active then `t ≥ 2` (two non-proportional forms need two
variables). -/
lemma two_le_t_of_card_two (H : LocHyp W Amax A b) {X : Finset (Fin m)} (hX : 2 ≤ X.card) :
    2 ≤ t := by
  by_contra hcon
  have ht1 : t ≤ 1 := by omega
  haveI : Subsingleton (Fin t) := ⟨fun a b => by
    have ha : a.val = 0 := by omega
    have hb : b.val = 0 := by omega
    exact Fin.ext (by omega)⟩
  obtain ⟨i, _, i', _, hii'⟩ := Finset.one_lt_card.mp (by omega : 1 < X.card)
  obtain ⟨j, hj⟩ := H.hne i
  refine H.hprop i i' hii' ⟨(A i' j : ℚ) / (A i j : ℚ), fun j' => ?_⟩
  have hj' : j' = j := Subsingleton.elim j' j
  rw [hj']
  have hij : (A i j : ℚ) ≠ 0 := by exact_mod_cast hj
  field_simp

/-- `‖vSys p σ‖ ≤ p^{-2}` when at least two indices are active and `p ∤ W`. -/
lemma vSys_norm_le_inv_sq (H : LocHyp W Amax A b) {p : ℕ} (hp : p.Prime) (hpW : ¬ p ∣ W)
    {σ : PrimeData m} (hcard : 2 ≤ (σ.X ∪ σ.X').card) :
    ‖vSys W A b p σ‖ ≤ (p : ℝ) ^ (-2 : ℤ) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have ht2 : 2 ≤ t := two_le_t_of_card_two H hcard
  have h2 : 2 * Amax ^ 2 < p := H.lt_of_not_dvd hp hpW
  have hcount := Commons.NumberTheory.Sieve.locCount_ite_le_two (p := p) W Amax A b σ W
    ht2 H.hA H.hne H.hprop H.hW0 hpW h2 hcard
  rw [vSys, dif_pos hp, norm_div, Complex.norm_natCast, Complex.norm_pow,
    Complex.norm_natCast, div_eq_mul_inv]
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hcountR : ((@locCount m t W A b (fun i => if i ∈ σ.X ∪ σ.X' then p else 1) p
      (NeZero.of_pos hp.pos) : ℕ) : ℝ) ≤ (p : ℝ) ^ (t - 2) := by exact_mod_cast hcount
  have hstep : ((p : ℝ) ^ (t - 2)) * ((p : ℝ) ^ t)⁻¹ = ((p : ℝ) ^ 2)⁻¹ := by
    rw [show (p : ℝ) ^ t = (p : ℝ) ^ (t - 2) * (p : ℝ) ^ 2 by
      rw [← pow_add, Nat.sub_add_cancel ht2]]
    rw [mul_inv, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ (ne_of_gt hp0)), one_mul]
  calc ((@locCount m t W A b (fun i => if i ∈ σ.X ∪ σ.X' then p else 1) p
          (NeZero.of_pos hp.pos) : ℕ) : ℝ) * ((p : ℝ) ^ t)⁻¹
      ≤ (p : ℝ) ^ (t - 2) * ((p : ℝ) ^ t)⁻¹ :=
        mul_le_mul_of_nonneg_right hcountR (by positivity)
    _ = ((p : ℝ) ^ 2)⁻¹ := hstep
    _ = (p : ℝ) ^ (-2 : ℤ) := by rw [zpow_neg, zpow_ofNat]

/-- The `σ`-th summand of the Euler factor. -/
noncomputable def eTerm (W : ℕ) (A : Fin m → Fin t → ℤ) (b : Fin m → ℤ) (z z' : Fin m → ℂ)
    (p : ℕ) (σ : PrimeData m) : ℂ :=
  vSys W A b p σ * ((-1 : ℂ) ^ (σ.X.card + σ.X'.card)) *
    ((∏ i ∈ σ.X, (p : ℂ) ^ (-(z i))) * (∏ i ∈ σ.X', (p : ℂ) ^ (-(z' i))))

lemma eulerFactor_eq_sum_eTerm (W : ℕ) (A : Fin m → Fin t → ℤ) (b : Fin m → ℤ)
    (z z' : Fin m → ℂ) (p : ℕ) :
    eulerFactor m (vSys W A b) z z' p = ∑ σ : PrimeData m, eTerm W A b z z' p σ := rfl

/-- `∏_{i ∈ X} p^{-z_i}` is bounded by `p^{σ₀ |X|}` on the strip. -/
lemma norm_prod_cpow_le {p : ℕ} (hp : 1 ≤ p) {σ₀ : ℝ} (hσ₀ : 0 ≤ σ₀) {z : Fin m → ℂ}
    (hz : ∀ j, -σ₀ ≤ (z j).re) (X : Finset (Fin m)) :
    ‖∏ i ∈ X, (p : ℂ) ^ (-(z i))‖ ≤ (p : ℝ) ^ (σ₀ * (X.card : ℝ)) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (by omega : 0 < p)
  rw [norm_prod]
  have h1 : ∀ i ∈ X, ‖(p : ℂ) ^ (-(z i))‖ ≤ (p : ℝ) ^ σ₀ := by
    intro i _
    rw [← Complex.ofReal_natCast,
      Complex.norm_cpow_eq_rpow_re_of_pos (by positivity : (0 : ℝ) < (p : ℝ))]
    have hre : (-(z i)).re = -(z i).re := by simp
    rw [hre]
    exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hp) (by linarith [hz i])
  calc ∏ i ∈ X, ‖(p : ℂ) ^ (-(z i))‖ ≤ ∏ _i ∈ X, (p : ℝ) ^ σ₀ :=
        Finset.prod_le_prod (fun i _ => norm_nonneg _) h1
    _ = ((p : ℝ) ^ σ₀) ^ X.card := by rw [Finset.prod_const]
    _ = (p : ℝ) ^ (σ₀ * (X.card : ℝ)) := by
        rw [← Real.rpow_natCast ((p : ℝ) ^ σ₀) X.card, ← Real.rpow_mul (le_of_lt hp0)]

/-- Every `σ`-summand with `2 ≤ |σ.X ∪ σ.X'|` is bounded by `p^{-2+2σ₀m}` on the strip. -/
lemma norm_eTerm_le (H : LocHyp W Amax A b) {p : ℕ} (hp : p.Prime) (hpW : ¬ p ∣ W)
    {σ₀ : ℝ} (hσ₀ : 0 ≤ σ₀) {z z' : Fin m → ℂ}
    (hz : ∀ j, -σ₀ ≤ (z j).re) (hz' : ∀ j, -σ₀ ≤ (z' j).re) {σ : PrimeData m}
    (hcard : 2 ≤ (σ.X ∪ σ.X').card) :
    ‖eTerm W A b z z' p σ‖ ≤ (p : ℝ) ^ (-2 + 2 * σ₀ * (m : ℝ)) := by
  have hp1n : 1 ≤ p := hp.one_le
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hp1lt : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hv : ‖vSys W A b p σ‖ ≤ (p : ℝ) ^ (-2 : ℝ) := by
    have h1 := vSys_norm_le_inv_sq H hp hpW hcard
    have h2 : (p : ℝ) ^ (-2 : ℤ) = (p : ℝ) ^ (-2 : ℝ) := by
      rw [show (-2 : ℝ) = ((-2 : ℤ) : ℝ) by norm_num, Real.rpow_intCast]
    rw [← h2]
    exact h1
  have hX := norm_prod_cpow_le (m := m) (p := p) hp1n hσ₀ hz σ.X
  have hX' := norm_prod_cpow_le (m := m) (p := p) hp1n hσ₀ hz' σ.X'
  have hcardX : (σ.X.card : ℝ) ≤ m := by
    have := Finset.card_le_univ σ.X
    rw [Fintype.card_fin] at this
    exact_mod_cast this
  have hcardX' : (σ.X'.card : ℝ) ≤ m := by
    have := Finset.card_le_univ σ.X'
    rw [Fintype.card_fin] at this
    exact_mod_cast this
  have hpow : (p : ℝ) ^ (σ₀ * (σ.X.card : ℝ)) * (p : ℝ) ^ (σ₀ * (σ.X'.card : ℝ))
      ≤ (p : ℝ) ^ (2 * σ₀ * (m : ℝ)) := by
    rw [← Real.rpow_add (by positivity)]
    refine Real.rpow_le_rpow_of_exponent_le (le_of_lt hp1lt) ?_
    nlinarith
  rw [eTerm]
  simp only [norm_mul, norm_pow, norm_neg, norm_one, one_pow, mul_one, one_mul]
  calc ‖vSys W A b p σ‖ * (‖∏ i ∈ σ.X, (p : ℂ) ^ (-(z i))‖
          * ‖∏ i ∈ σ.X', (p : ℂ) ^ (-(z' i))‖)
      ≤ (p : ℝ) ^ (-2 : ℝ) * ((p : ℝ) ^ (σ₀ * (σ.X.card : ℝ))
          * (p : ℝ) ^ (σ₀ * (σ.X'.card : ℝ))) :=
        mul_le_mul hv (mul_le_mul hX hX' (by positivity) (by positivity)) (by positivity)
          (by positivity)
    _ ≤ (p : ℝ) ^ (-2 : ℝ) * (p : ℝ) ^ (2 * σ₀ * (m : ℝ)) :=
        mul_le_mul_of_nonneg_left hpow (by positivity)
    _ = (p : ℝ) ^ (-2 + 2 * σ₀ * (m : ℝ)) := by
        rw [← Real.rpow_add (by positivity)]

/-! ## 3. The expansion of the Euler factor (Green–Tao (10.8)) -/

/-- The linear part of the Euler-factor expansion. -/
noncomputable def eLin (z z' : Fin m → ℂ) (p : ℕ) : ℂ :=
  ∑ j, ((p : ℂ) ^ (-(1 + z j)) + (p : ℂ) ^ (-(1 + z' j)) - (p : ℂ) ^ (-(1 + z j + z' j)))

/-- `p^{-1} · p^{-z} = p^{-(1+z)}`. -/
lemma inv_mul_cpow (p : ℕ) (hp : (p : ℂ) ≠ 0) (z : ℂ) :
    ((p : ℂ))⁻¹ * (p : ℂ) ^ (-z) = (p : ℂ) ^ (-(1 + z)) := by
  rw [← Complex.cpow_neg_one, ← Complex.cpow_add _ _ hp]
  congr 1
  ring

lemma eTerm_single_left (H : LocHyp W Amax A b) {p : ℕ} (hp : p.Prime) (hpW : ¬ p ∣ W)
    (z z' : Fin m → ℂ) (j : Fin m) :
    eTerm W A b z z' p ⟨{j}, ∅⟩ = -((p : ℂ) ^ (-(1 + z j))) := by
  have hcard : ((⟨{j}, ∅⟩ : PrimeData m).X ∪ (⟨{j}, ∅⟩ : PrimeData m).X').card = 1 := by simp
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.pos.ne'
  rw [eTerm, vSys_eq_inv_of_card_one H hp hpW hcard]
  simp only [Finset.card_singleton, Finset.card_empty, add_zero, Finset.prod_singleton,
    Finset.prod_empty, mul_one]
  rw [show (-1 : ℂ) ^ (1 + 0) = -1 by norm_num]
  rw [show (p : ℂ)⁻¹ * -1 * (p : ℂ) ^ (-(z j)) = -((p : ℂ)⁻¹ * (p : ℂ) ^ (-(z j))) by ring,
    inv_mul_cpow p hp0 (z j)]

lemma eTerm_single_right (H : LocHyp W Amax A b) {p : ℕ} (hp : p.Prime) (hpW : ¬ p ∣ W)
    (z z' : Fin m → ℂ) (j : Fin m) :
    eTerm W A b z z' p ⟨∅, {j}⟩ = -((p : ℂ) ^ (-(1 + z' j))) := by
  have hcard : ((⟨∅, {j}⟩ : PrimeData m).X ∪ (⟨∅, {j}⟩ : PrimeData m).X').card = 1 := by simp
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.pos.ne'
  rw [eTerm, vSys_eq_inv_of_card_one H hp hpW hcard]
  simp only [Finset.card_singleton, Finset.card_empty, zero_add, Finset.prod_singleton,
    Finset.prod_empty, mul_one]
  rw [show (-1 : ℂ) ^ (0 + 1) = -1 by norm_num]
  rw [one_mul, show (p : ℂ)⁻¹ * -1 * (p : ℂ) ^ (-(z' j))
      = -((p : ℂ)⁻¹ * (p : ℂ) ^ (-(z' j))) by ring, inv_mul_cpow p hp0 (z' j)]

lemma eTerm_single_both (H : LocHyp W Amax A b) {p : ℕ} (hp : p.Prime) (hpW : ¬ p ∣ W)
    (z z' : Fin m → ℂ) (j : Fin m) :
    eTerm W A b z z' p ⟨{j}, {j}⟩ = (p : ℂ) ^ (-(1 + z j + z' j)) := by
  have hcard : ((⟨{j}, {j}⟩ : PrimeData m).X ∪ (⟨{j}, {j}⟩ : PrimeData m).X').card = 1 := by
    simp
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.pos.ne'
  rw [eTerm, vSys_eq_inv_of_card_one H hp hpW hcard]
  simp only [Finset.card_singleton, Finset.prod_singleton]
  rw [show (-1 : ℂ) ^ (1 + 1) = 1 by norm_num, mul_one]
  rw [show ((p : ℂ))⁻¹ * ((p : ℂ) ^ (-(z j)) * (p : ℂ) ^ (-(z' j)))
      = ((p : ℂ))⁻¹ * (p : ℂ) ^ (-(z j)) * (p : ℂ) ^ (-(z' j)) by ring]
  rw [inv_mul_cpow p hp0 (z j), ← Complex.cpow_add _ _ hp0]
  congr 1
  ring

/-- The number of local data is `4^m`. -/
def primeDataEquiv (m : ℕ) : PrimeData m ≃ Finset (Fin m) × Finset (Fin m) where
  toFun σ := (σ.X, σ.X')
  invFun p := ⟨p.1, p.2⟩
  left_inv σ := by cases σ; rfl
  right_inv p := by cases p; rfl

lemma card_primeData (m : ℕ) : Fintype.card (PrimeData m) = 4 ^ m := by
  rw [Fintype.card_congr (primeDataEquiv m), Fintype.card_prod, Fintype.card_finset,
    Fintype.card_fin, ← mul_pow]
  norm_num

/-- The sum over the `σ` with `|σ.X ∪ σ.X'| = 1` is minus the linear part `eLin`. -/
lemma sum_card_one_eTerm (H : LocHyp W Amax A b) {p : ℕ} (hp : p.Prime) (hpW : ¬ p ∣ W)
    (z z' : Fin m → ℂ) :
    (∑ σ ∈ Finset.univ.filter (fun σ : PrimeData m => (σ.X ∪ σ.X').card = 1),
        eTerm W A b z z' p σ) = - eLin z z' p := by
  rw [Commons.NumberTheory.Sieve.sum_filter_card_one,
    Finset.sum_congr rfl (fun j _ => eTerm_single_left H hp hpW z z' j),
    Finset.sum_congr rfl (fun j _ => eTerm_single_right H hp hpW z z' j),
    Finset.sum_congr rfl (fun j _ => eTerm_single_both H hp hpW z z' j)]
  simp only [eLin, Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_neg_distrib]
  ring

/-- **Green–Tao (10.8)**, second form: at a prime `p ∤ W` on the strip the Euler factor is
`1 - eLin + R` with `‖R‖ ≤ 4^m p^{-2+2σ₀m}`. -/
theorem eulerFactor_expansion (H : LocHyp W Amax A b) {p : ℕ} (hp : p.Prime) (hpW : ¬ p ∣ W)
    {σ₀ : ℝ} (hσ₀ : 0 ≤ σ₀) {z z' : Fin m → ℂ}
    (hz : ∀ j, -σ₀ ≤ (z j).re) (hz' : ∀ j, -σ₀ ≤ (z' j).re) :
    ∃ R : ℂ, ‖R‖ ≤ (4 : ℝ) ^ m * (p : ℝ) ^ (-2 + 2 * σ₀ * (m : ℝ)) ∧
      eulerFactor m (vSys W A b) z z' p = 1 - eLin z z' p + R := by
  refine ⟨∑ σ ∈ Finset.univ.filter (fun σ : PrimeData m => 2 ≤ (σ.X ∪ σ.X').card),
    eTerm W A b z z' p σ, ?_, ?_⟩
  · have hcard : (Finset.univ.filter (fun σ : PrimeData m => 2 ≤ (σ.X ∪ σ.X').card)).card
        ≤ 4 ^ m := by
      refine le_trans (Finset.card_filter_le _ _) ?_
      rw [Finset.card_univ, card_primeData]
    have hterms : ∀ σ ∈ Finset.univ.filter (fun σ : PrimeData m => 2 ≤ (σ.X ∪ σ.X').card),
        ‖eTerm W A b z z' p σ‖ ≤ (p : ℝ) ^ (-2 + 2 * σ₀ * (m : ℝ)) :=
      fun σ hσ => norm_eTerm_le H hp hpW hσ₀ hz hz' (Finset.mem_filter.mp hσ).2
    calc ‖∑ σ ∈ Finset.univ.filter (fun σ : PrimeData m => 2 ≤ (σ.X ∪ σ.X').card),
            eTerm W A b z z' p σ‖
        ≤ ∑ σ ∈ Finset.univ.filter (fun σ : PrimeData m => 2 ≤ (σ.X ∪ σ.X').card),
            ‖eTerm W A b z z' p σ‖ := norm_sum_le _ _
      _ ≤ ((Finset.univ.filter (fun σ : PrimeData m => 2 ≤ (σ.X ∪ σ.X').card)).card : ℝ)
            * (p : ℝ) ^ (-2 + 2 * σ₀ * (m : ℝ)) := by
          simpa [nsmul_eq_mul] using Finset.sum_le_card_nsmul _ _ _ hterms
      _ ≤ (4 : ℝ) ^ m * (p : ℝ) ^ (-2 + 2 * σ₀ * (m : ℝ)) := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          exact_mod_cast hcard
  · have h0 : eTerm W A b z z' p (0 : PrimeData m) = 1 := by
      have hX : (0 : PrimeData m).X = ∅ := rfl
      have hX' : (0 : PrimeData m).X' = ∅ := rfl
      rw [eTerm, vSys_zero, hX, hX']
      simp
    rw [eulerFactor_eq_sum_eTerm, Commons.NumberTheory.Sieve.sum_univ_eq_sum_three, h0,
      sum_card_one_eTerm H hp hpW z z']
    ring

/-- **Green–Tao (10.9)**: the Euler product of the third local factors is the ratio of zeta
values (immediate from the commons lemma `Commons.NumberTheory.Zeta.tprod_E3_eq_zeta_ratio`). -/
theorem tprod_E3p_eq (z z' : Fin m → ℂ) (hz : ∀ j, 0 < (z j).re) (hz' : ∀ j, 0 < (z' j).re) :
    (∏' p : ℕ, E3p z z' p)
      = ∏ j, riemannZeta (1 + z j + z' j)
          / (riemannZeta (1 + z j) * riemannZeta (1 + z' j)) :=
  Commons.NumberTheory.Zeta.tprod_E3_eq_zeta_ratio m z z' hz hz'

/-! ## 3. Non-vanishing and the factorisation `E_p = E_p^{(1)} E_p^{(2)} E_p^{(3)}` -/

/-- On the strip, `‖p^{-1-z}‖ ≤ p^{-1-c}` for `Re z ≥ c`. -/
lemma norm_cpow_neg_one_sub_le {p : ℕ} (hp : 1 ≤ p) {c : ℝ} {z : ℂ} (hz : c ≤ z.re) :
    ‖(p : ℂ) ^ (-(1 + z))‖ ≤ (p : ℝ) ^ (-1 - c) := by
  rw [← Complex.ofReal_natCast,
    Complex.norm_cpow_eq_rpow_re_of_pos (by positivity : (0 : ℝ) < (p : ℝ))]
  have hre : (-(1 + z)).re = -(1 + z.re) := by simp
  rw [hre]
  refine Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hp) ?_
  linarith

/-- On the strip, `‖p^{-1-z}‖ < 1` when `c < 1`. -/
lemma cpow_neg_one_sub_lt_one {p : ℕ} (hp : 2 ≤ p) {c : ℝ} (hc : -1 < c) {z : ℂ}
    (hz : c ≤ z.re) : ‖(p : ℂ) ^ (-(1 + z))‖ < 1 := by
  refine lt_of_le_of_lt (norm_cpow_neg_one_sub_le (by omega : 1 ≤ p) hz) ?_
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (by omega : 1 < p)
  have hexp : -1 - c = -(1 + c) := by ring
  rw [hexp, Real.rpow_neg (by positivity : (0 : ℝ) ≤ (p : ℝ))]
  exact inv_lt_one_of_one_lt₀ (Real.one_lt_rpow hp1 (by linarith))

/-- The three factors occurring in `E_p^{(3)}` are nonzero on the strip `Re ≥ -σ₀` with
`2σ₀ < 1`. -/
lemma E3p_factors_ne_zero {p : ℕ} (hp : p.Prime) {σ₀ : ℝ} (hσ₀ : 2 * σ₀ < 1) {z : ℂ} {z' : ℂ}
    (hz : -σ₀ ≤ z.re) (hz' : -σ₀ ≤ z'.re) :
    (1 - (p : ℂ) ^ (-(1 + z))) ≠ 0 ∧ (1 - (p : ℂ) ^ (-(1 + z'))) ≠ 0 ∧
      (1 - (p : ℂ) ^ (-(1 + z + z'))) ≠ 0 := by
  have hp2 : 2 ≤ p := hp.two_le
  have H1 : ‖(p : ℂ) ^ (-(1 + z))‖ < 1 :=
    cpow_neg_one_sub_lt_one hp2 (by linarith : -1 < -σ₀) hz
  have H2 : ‖(p : ℂ) ^ (-(1 + z'))‖ < 1 :=
    cpow_neg_one_sub_lt_one hp2 (by linarith : -1 < -σ₀) hz'
  have H3 : ‖(p : ℂ) ^ (-(1 + z + z'))‖ < 1 := by
    have h1 : ‖(p : ℂ) ^ (-(1 + (z + z')))‖ < 1 :=
      cpow_neg_one_sub_lt_one hp2 (by linarith : -1 < -2 * σ₀)
        (by rw [Complex.add_re]; linarith)
    rwa [show -(1 + (z + z')) = -(1 + z + z') by ring] at h1
  refine ⟨?_, ?_, ?_⟩
  · intro h
    have hh : (p : ℂ) ^ (-(1 + z)) = 1 := (sub_eq_zero.mp h).symm
    rw [hh, norm_one] at H1
    exact lt_irrefl 1 H1
  · intro h
    have hh : (p : ℂ) ^ (-(1 + z')) = 1 := (sub_eq_zero.mp h).symm
    rw [hh, norm_one] at H2
    exact lt_irrefl 1 H2
  · intro h
    have hh : (p : ℂ) ^ (-(1 + z + z')) = 1 := (sub_eq_zero.mp h).symm
    rw [hh, norm_one] at H3
    exact lt_irrefl 1 H3

/-- The product `∏_j (1-p^{-1-z_j})(1-p^{-1-z'_j})(1-p^{-1-z_j-z'_j})⁻¹` is nonzero on the
strip. -/
lemma prod_E3_ne_zero {p : ℕ} (hp : p.Prime) {σ₀ : ℝ} (hσ₀ : 2 * σ₀ < 1) {z z' : Fin m → ℂ}
    (hz : ∀ j, -σ₀ ≤ (z j).re) (hz' : ∀ j, -σ₀ ≤ (z' j).re) :
    (∏ j, ((1 - (p : ℂ) ^ (-(1 + z j))) * (1 - (p : ℂ) ^ (-(1 + z' j)))
        * (1 - (p : ℂ) ^ (-(1 + z j + z' j)))⁻¹)) ≠ 0 := by
  refine Finset.prod_ne_zero_iff.mpr (fun j _ => ?_)
  obtain ⟨h1, h2, h3⟩ := E3p_factors_ne_zero hp hσ₀ (hz j) (hz' j)
  exact mul_ne_zero (mul_ne_zero h1 h2) (inv_ne_zero h3)

/-- `E_p^{(3)}` is nonzero on the strip. -/
lemma E3p_ne_zero {p : ℕ} (hp : p.Prime) {σ₀ : ℝ} (hσ₀ : 2 * σ₀ < 1) {z z' : Fin m → ℂ}
    (hz : ∀ j, -σ₀ ≤ (z j).re) (hz' : ∀ j, -σ₀ ≤ (z' j).re) : E3p z z' p ≠ 0 := by
  rw [E3p, if_pos hp]
  exact prod_E3_ne_zero hp hσ₀ hz hz'

/-- The Euler factors of the expansion are bounded on the strip:
`‖p^{-(1+z_j)}‖, ‖p^{-(1+z'_j)}‖ ≤ p^{-1+σ₀}` and `‖p^{-(1+z_j+z'_j)}‖ ≤ p^{-1+2σ₀}`. -/
lemma cpow_bounds {p : ℕ} (hp : 1 ≤ p) {σ₀ : ℝ} {z z' : Fin m → ℂ}
    (hz : ∀ j, -σ₀ ≤ (z j).re) (hz' : ∀ j, -σ₀ ≤ (z' j).re) :
    (∀ j, ‖(p : ℂ) ^ (-(1 + z j))‖ ≤ (p : ℝ) ^ (-1 + σ₀)) ∧
    (∀ j, ‖(p : ℂ) ^ (-(1 + z' j))‖ ≤ (p : ℝ) ^ (-1 + σ₀)) ∧
    (∀ j, ‖(p : ℂ) ^ (-(1 + z j + z' j))‖ ≤ (p : ℝ) ^ (-1 + 2 * σ₀)) := by
  refine ⟨fun j => ?_, fun j => ?_, fun j => ?_⟩
  · have h := norm_cpow_neg_one_sub_le (p := p) hp (c := -σ₀) (z := z j) (by linarith [hz j])
    simpa using h
  · have h := norm_cpow_neg_one_sub_le (p := p) hp (c := -σ₀) (z := z' j) (by linarith [hz' j])
    simpa using h
  · have h2 : -2 * σ₀ ≤ (z j + z' j).re := by rw [Complex.add_re]; linarith [hz j, hz' j]
    have h := norm_cpow_neg_one_sub_le (p := p) hp (c := -2 * σ₀) (z := z j + z' j) h2
    have hrew : (-1 - -2 * σ₀) = (-1 + 2 * σ₀) := by ring
    rw [hrew] at h
    rwa [show (1 : ℂ) + (z j + z' j) = 1 + z j + z' j by ring] at h

/-- `‖eLin z z' p‖ ≤ m·(2·p^{-1+σ₀} + p^{-1+2σ₀})` on the strip. -/
lemma norm_eLin_le {p : ℕ} (hp : 1 ≤ p) {σ₀ : ℝ} {z z' : Fin m → ℂ}
    (hz : ∀ j, -σ₀ ≤ (z j).re) (hz' : ∀ j, -σ₀ ≤ (z' j).re) :
    ‖eLin z z' p‖ ≤ (m : ℝ) * (2 * (p : ℝ) ^ (-1 + σ₀) + (p : ℝ) ^ (-1 + 2 * σ₀)) := by
  obtain ⟨h1, h2, h3⟩ := cpow_bounds (m := m) hp hz hz'
  have h4 : ‖eLin z z' p‖ ≤ ∑ _j : Fin m,
      (2 * (p : ℝ) ^ (-1 + σ₀) + (p : ℝ) ^ (-1 + 2 * σ₀)) := by
    rw [eLin]
    refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum (fun j _ => ?_))
    have h5 : ((p : ℂ) ^ (-(1 + z j)) + (p : ℂ) ^ (-(1 + z' j))
        - (p : ℂ) ^ (-(1 + z j + z' j)))
        = (p : ℂ) ^ (-(1 + z j)) + ((p : ℂ) ^ (-(1 + z' j))
            + (-(p : ℂ) ^ (-(1 + z j + z' j)))) := by ring
    rw [h5]
    calc ‖(p : ℂ) ^ (-(1 + z j)) + ((p : ℂ) ^ (-(1 + z' j))
          + -(p : ℂ) ^ (-(1 + z j + z' j)))‖
        ≤ ‖(p : ℂ) ^ (-(1 + z j))‖ + ‖(p : ℂ) ^ (-(1 + z' j))
            + -(p : ℂ) ^ (-(1 + z j + z' j))‖ := norm_add_le _ _
      _ ≤ ‖(p : ℂ) ^ (-(1 + z j))‖ + (‖(p : ℂ) ^ (-(1 + z' j))‖
            + ‖(p : ℂ) ^ (-(1 + z j + z' j))‖) := by
          refine add_le_add le_rfl ?_
          calc ‖(p : ℂ) ^ (-(1 + z' j)) + -(p : ℂ) ^ (-(1 + z j + z' j))‖
              ≤ ‖(p : ℂ) ^ (-(1 + z' j))‖ + ‖-(p : ℂ) ^ (-(1 + z j + z' j))‖ :=
                norm_add_le _ _
            _ = ‖(p : ℂ) ^ (-(1 + z' j))‖ + ‖(p : ℂ) ^ (-(1 + z j + z' j))‖ := by rw [norm_neg]
      _ ≤ (p : ℝ) ^ (-1 + σ₀) + ((p : ℝ) ^ (-1 + σ₀) + (p : ℝ) ^ (-1 + 2 * σ₀)) := by
          refine add_le_add (h1 j) (add_le_add (h2 j) (h3 j))
      _ = 2 * (p : ℝ) ^ (-1 + σ₀) + (p : ℝ) ^ (-1 + 2 * σ₀) := by ring
  rwa [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h4

/-- The Euler factor at a prime dividing `W` is `1` (Green–Tao Lemma 9.2: `θ_i ≡ 1 mod p`). -/
lemma eulerFactor_eq_one_of_dvd_W (H : LocHyp W Amax A b) {p : ℕ} (hp : p.Prime) (hpW : p ∣ W)
    (z z' : Fin m → ℂ) : eulerFactor m (vSys W A b) z z' p = 1 := by
  classical
  rw [eulerFactor]
  have hzero : ∀ σ : PrimeData m, σ ≠ 0 →
      vSys W A b p σ * ((-1 : ℂ) ^ (σ.X.card + σ.X'.card)) *
        ((∏ i ∈ σ.X, (p : ℂ) ^ (-(z i))) * (∏ i ∈ σ.X', (p : ℂ) ^ (-(z' i)))) = 0 :=
    fun σ hσ => by rw [vSys_eq_zero_of_dvd_W H hp hpW hσ, zero_mul, zero_mul]
  rw [Finset.sum_eq_single (0 : PrimeData m) (fun σ _ hσ => hzero σ hσ)
    (fun h => absurd (Finset.mem_univ _) h)]
  rw [vSys_zero]
  have hX : (0 : PrimeData m).X = ∅ := rfl
  have hX' : (0 : PrimeData m).X' = ∅ := rfl
  rw [hX, hX']
  simp

/-- **Green–Tao (10.8)**: on the strip the local Euler factor factorises as
`E_p = E_p^{(1)} E_p^{(2)} E_p^{(3)}`. -/
theorem eulerFactor_eq_E1p_mul_E2p_mul_E3p (H : LocHyp W Amax A b) {σ₀ : ℝ} (hσ₀ : 2 * σ₀ < 1)
    {z z' : Fin m → ℂ} (hz : ∀ j, -σ₀ ≤ (z j).re) (hz' : ∀ j, -σ₀ ≤ (z' j).re) (p : ℕ) :
    eulerFactor m (vSys W A b) z z' p = E1p W A b z z' p * E2p W z z' p * E3p z z' p := by
  by_cases hp : p.Prime
  · by_cases hpW : p ∣ W
    · rw [eulerFactor_eq_one_of_dvd_W H hp hpW, E1p, if_neg (by tauto), E2p, if_pos ⟨hp, hpW⟩,
        E3p, if_pos hp, one_mul]
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
      (fun σ _ hσ => by rw [vSys_of_not_prime W A b p σ hp hσ, zero_mul, zero_mul])
      (fun h => absurd (Finset.mem_univ _) h)]
    rw [vSys_zero]
    have hX : (0 : PrimeData m).X = ∅ := rfl
    have hX' : (0 : PrimeData m).X' = ∅ := rfl
    rw [hX, hX']
    simp

/-! ## 4. The `E^{(1)}` estimate of Green–Tao Lemma 10.3 -/

/-- Triangle inequality for the six-term expression occurring in the `E^{(1)}` expansion
(`S - L² - LS + R + RL + RS`). -/
lemma norm_six_le (a b c d e f : ℂ) :
    ‖a - b - c + d + e + f‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ + ‖e‖ + ‖f‖ := by
  have h1 : ‖a - b - c + d + e + f‖ ≤ ‖a - b - c + d + e‖ + ‖f‖ := norm_add_le _ _
  have h2 : ‖a - b - c + d + e‖ ≤ ‖a - b - c + d‖ + ‖e‖ := norm_add_le _ _
  have h3 : ‖a - b - c + d‖ ≤ ‖a - b - c‖ + ‖d‖ := norm_add_le _ _
  have h4 : ‖a - b - c‖ ≤ ‖a - b‖ + ‖c‖ := norm_sub_le _ _
  have h5 : ‖a - b‖ ≤ ‖a‖ + ‖b‖ := norm_sub_le _ _
  linarith

/-- **Green–Tao Lemma 10.3, the key `E^{(1)}` estimate**: for a prime `p ∤ W` and `z, z'` on the
strip `Re ≥ -σ₀` (with `4σ₀ ≤ 1`), the first local factor satisfies
`E_p^{(1)} = 1 + O_m(p^{-2+2σ₀m} + p^{-2+4σ₀})`. -/
theorem E1p_bound (H : LocHyp W Amax A b) {p : ℕ} (hp : p.Prime) (hpW : ¬ p ∣ W)
    {σ₀ : ℝ} (hσ₀ : 0 ≤ σ₀) (hσ₀1 : 4 * σ₀ ≤ 1) {z z' : Fin m → ℂ}
    (hz : ∀ j, -σ₀ ≤ (z j).re) (hz' : ∀ j, -σ₀ ≤ (z' j).re)
    (hsmall : (m : ℝ) * (2 * (p : ℝ) ^ (-1 + σ₀) + (p : ℝ) ^ (-1 + 2 * σ₀)) ≤ 1 / 2) :
    ‖E1p W A b z z' p - 1‖ ≤ 100000 * ((m : ℝ) ^ 3 + 1) * (4 : ℝ) ^ m
      * ((p : ℝ) ^ (-2 + 2 * σ₀ * (m : ℝ)) + (p : ℝ) ^ (-2 + 4 * σ₀)) := by
  have hp1R : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.one_le
  have hp0R : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
  have hm1R : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast H.hm
  have h4m0 : (0 : ℝ) ≤ (4 : ℝ) ^ m := by positivity
  obtain ⟨hca, hcb, hcc⟩ := cpow_bounds (m := m) (p := p) hp.one_le (σ₀ := σ₀) hz hz'
  have hA0 : (0 : ℝ) ≤ (p : ℝ) ^ (-1 + σ₀) := Real.rpow_nonneg (le_of_lt hp0R) _
  have hC0 : (0 : ℝ) ≤ (p : ℝ) ^ (-1 + 2 * σ₀) := Real.rpow_nonneg (le_of_lt hp0R) _
  have hA1 : (p : ℝ) ^ (-1 + σ₀) ≤ 1 := by
    have h := Real.rpow_le_rpow_of_exponent_le hp1R (show -1 + σ₀ ≤ 0 by linarith)
    rwa [Real.rpow_zero] at h
  have hC1 : (p : ℝ) ^ (-1 + 2 * σ₀) ≤ 1 := by
    have h := Real.rpow_le_rpow_of_exponent_le hp1R (show -1 + 2 * σ₀ ≤ 0 by linarith)
    rwa [Real.rpow_zero] at h
  obtain ⟨S, hS, hSeq⟩ := Commons.Analysis.Complex.inv_prod_three_expansion (m := m) z z'
    (A := (p : ℝ) ^ (-1 + σ₀)) (C := (p : ℝ) ^ (-1 + 2 * σ₀)) hA0 hC0 hA1 hC1 hsmall
    hca hcb hcc
  obtain ⟨R, hR, hReq⟩ := eulerFactor_expansion H hp hpW hσ₀ hz hz'
  have hE3def : E3p z z' p = ∏ j, ((1 - (p : ℂ) ^ (-(1 + z j)))
      * (1 - (p : ℂ) ^ (-(1 + z' j))) * (1 - (p : ℂ) ^ (-(1 + z j + z' j)))⁻¹) := by
    rw [E3p, if_pos hp]
  have hE3inv : (E3p z z' p)⁻¹ = 1 + eLin z z' p + S := by
    rw [hE3def, hSeq, eLin]
  have hE1def : E1p W A b z z' p = eulerFactor m (vSys W A b) z z' p / E3p z z' p := by
    rw [E1p, if_pos ⟨hp, hpW⟩]
  have hId : E1p W A b z z' p - 1
      = S - (eLin z z' p) ^ 2 - eLin z z' p * S + R + R * eLin z z' p + R * S := by
    rw [hE1def, div_eq_mul_inv, hE3inv, hReq]
    ring
  have htri : ‖E1p W A b z z' p - 1‖ ≤ ‖S‖ + ‖eLin z z' p‖ ^ 2 + ‖eLin z z' p‖ * ‖S‖
      + ‖R‖ + ‖R‖ * ‖eLin z z' p‖ + ‖R‖ * ‖S‖ := by
    rw [hId]
    have h := norm_six_le S ((eLin z z' p) ^ 2) (eLin z z' p * S) R (R * eLin z z' p) (R * S)
    simpa only [norm_pow, norm_mul] using h
  have hLhalf : ‖eLin z z' p‖ ≤ 1 / 2 := by
    have h := norm_eLin_le (m := m) (p := p) hp.one_le (σ₀ := σ₀) hz hz'
    linarith [h, hsmall]
  have hD0 : (0 : ℝ) ≤ (p : ℝ) ^ (-2 + 2 * σ₀ * (m : ℝ)) + (p : ℝ) ^ (-2 + 4 * σ₀) :=
    add_nonneg (Real.rpow_nonneg (le_of_lt hp0R) _) (Real.rpow_nonneg (le_of_lt hp0R) _)
  have hD2le : (p : ℝ) ^ (-2 + 4 * σ₀)
      ≤ (p : ℝ) ^ (-2 + 2 * σ₀ * (m : ℝ)) + (p : ℝ) ^ (-2 + 4 * σ₀) :=
    le_add_of_nonneg_left (Real.rpow_nonneg (le_of_lt hp0R) _)
  have hD1le : (p : ℝ) ^ (-2 + 2 * σ₀ * (m : ℝ))
      ≤ (p : ℝ) ^ (-2 + 2 * σ₀ * (m : ℝ)) + (p : ℝ) ^ (-2 + 4 * σ₀) :=
    le_add_of_nonneg_right (Real.rpow_nonneg (le_of_lt hp0R) _)
  have hA2eq : ((p : ℝ) ^ (-1 + σ₀)) ^ 2 = (p : ℝ) ^ (-2 + 2 * σ₀) := by
    rw [sq, ← Real.rpow_add hp0R]; congr 1; ring
  have hACeq : (p : ℝ) ^ (-1 + σ₀) * (p : ℝ) ^ (-1 + 2 * σ₀) = (p : ℝ) ^ (-2 + 3 * σ₀) := by
    rw [← Real.rpow_add hp0R]; congr 1; ring
  have hC2eq : ((p : ℝ) ^ (-1 + 2 * σ₀)) ^ 2 = (p : ℝ) ^ (-2 + 4 * σ₀) := by
    rw [sq, ← Real.rpow_add hp0R]; congr 1; ring
  have hA2le : ((p : ℝ) ^ (-1 + σ₀)) ^ 2 ≤ (p : ℝ) ^ (-2 + 4 * σ₀) := by
    rw [hA2eq]; exact Real.rpow_le_rpow_of_exponent_le hp1R (by linarith)
  have hACle : (p : ℝ) ^ (-1 + σ₀) * (p : ℝ) ^ (-1 + 2 * σ₀) ≤ (p : ℝ) ^ (-2 + 4 * σ₀) := by
    rw [hACeq]; exact Real.rpow_le_rpow_of_exponent_le hp1R (by linarith)
  have hC2le : ((p : ℝ) ^ (-1 + 2 * σ₀)) ^ 2 ≤ (p : ℝ) ^ (-2 + 4 * σ₀) := by rw [hC2eq]
  have hS2 : ‖S‖ ≤ 30000 * ((m : ℝ) ^ 2 + m) * (p : ℝ) ^ (-2 + 4 * σ₀) := by
    have hsum : ((p : ℝ) ^ (-1 + σ₀)) ^ 2 + (p : ℝ) ^ (-1 + σ₀) * (p : ℝ) ^ (-1 + 2 * σ₀)
        + ((p : ℝ) ^ (-1 + 2 * σ₀)) ^ 2 ≤ 3 * (p : ℝ) ^ (-2 + 4 * σ₀) := by
      linarith [hA2le, hACle, hC2le]
    calc ‖S‖ ≤ 10000 * ((m : ℝ) ^ 2 + m)
          * (((p : ℝ) ^ (-1 + σ₀)) ^ 2 + (p : ℝ) ^ (-1 + σ₀) * (p : ℝ) ^ (-1 + 2 * σ₀)
              + ((p : ℝ) ^ (-1 + 2 * σ₀)) ^ 2) := hS
      _ ≤ 10000 * ((m : ℝ) ^ 2 + m) * (3 * (p : ℝ) ^ (-2 + 4 * σ₀)) :=
          mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = 30000 * ((m : ℝ) ^ 2 + m) * (p : ℝ) ^ (-2 + 4 * σ₀) := by ring
  have hS1 : ‖S‖ ≤ 30000 * ((m : ℝ) ^ 2 + m)
      * ((p : ℝ) ^ (-2 + 2 * σ₀ * (m : ℝ)) + (p : ℝ) ^ (-2 + 4 * σ₀)) :=
    le_trans hS2 (mul_le_mul_of_nonneg_left hD2le (by positivity))
  have hLsq : ‖eLin z z' p‖ ^ 2 ≤ 9 * (m : ℝ) ^ 2
      * ((p : ℝ) ^ (-2 + 2 * σ₀ * (m : ℝ)) + (p : ℝ) ^ (-2 + 4 * σ₀)) := by
    have h1 : ‖eLin z z' p‖ ^ 2
        ≤ ((m : ℝ) * (2 * (p : ℝ) ^ (-1 + σ₀) + (p : ℝ) ^ (-1 + 2 * σ₀))) ^ 2 := by
      have h := norm_eLin_le (m := m) (p := p) hp.one_le (σ₀ := σ₀) hz hz'
      have h0 : (0 : ℝ) ≤ (m : ℝ) * (2 * (p : ℝ) ^ (-1 + σ₀) + (p : ℝ) ^ (-1 + 2 * σ₀)) :=
        mul_nonneg (by positivity) (by linarith [hA0, hC0])
      nlinarith [h, norm_nonneg (eLin z z' p), h0]
    have h4 : (2 * (p : ℝ) ^ (-1 + σ₀) + (p : ℝ) ^ (-1 + 2 * σ₀)) ^ 2
        ≤ 9 * (p : ℝ) ^ (-2 + 4 * σ₀) := by
      have hsq : (2 * (p : ℝ) ^ (-1 + σ₀) + (p : ℝ) ^ (-1 + 2 * σ₀)) ^ 2
          = 4 * ((p : ℝ) ^ (-1 + σ₀)) ^ 2
            + 4 * ((p : ℝ) ^ (-1 + σ₀) * (p : ℝ) ^ (-1 + 2 * σ₀))
            + ((p : ℝ) ^ (-1 + 2 * σ₀)) ^ 2 := by ring
      rw [hsq]; linarith [hA2le, hACle, hC2le]
    calc ‖eLin z z' p‖ ^ 2
        ≤ ((m : ℝ) * (2 * (p : ℝ) ^ (-1 + σ₀) + (p : ℝ) ^ (-1 + 2 * σ₀))) ^ 2 := h1
      _ = (m : ℝ) ^ 2 * (2 * (p : ℝ) ^ (-1 + σ₀) + (p : ℝ) ^ (-1 + 2 * σ₀)) ^ 2 := by ring
      _ ≤ (m : ℝ) ^ 2 * (9 * (p : ℝ) ^ (-2 + 4 * σ₀)) :=
          mul_le_mul_of_nonneg_left h4 (by positivity)
      _ ≤ 9 * (m : ℝ) ^ 2
            * ((p : ℝ) ^ (-2 + 2 * σ₀ * (m : ℝ)) + (p : ℝ) ^ (-2 + 4 * σ₀)) := by
          nlinarith [hD2le, sq_nonneg (m : ℝ)]
  have hLS : ‖eLin z z' p‖ * ‖S‖ ≤ 15000 * ((m : ℝ) ^ 2 + m)
      * ((p : ℝ) ^ (-2 + 2 * σ₀ * (m : ℝ)) + (p : ℝ) ^ (-2 + 4 * σ₀)) := by
    have h := mul_le_mul hLhalf hS2 (norm_nonneg S) (by norm_num : (0 : ℝ) ≤ 1 / 2)
    refine le_trans h ?_
    have he : (1 / 2 : ℝ) * (30000 * ((m : ℝ) ^ 2 + m) * (p : ℝ) ^ (-2 + 4 * σ₀))
        = 15000 * ((m : ℝ) ^ 2 + m) * (p : ℝ) ^ (-2 + 4 * σ₀) := by ring
    rw [he]
    exact mul_le_mul_of_nonneg_left hD2le (by positivity)
  have hR1 : ‖R‖ ≤ (4 : ℝ) ^ m
      * ((p : ℝ) ^ (-2 + 2 * σ₀ * (m : ℝ)) + (p : ℝ) ^ (-2 + 4 * σ₀)) :=
    le_trans hR (mul_le_mul_of_nonneg_left hD1le h4m0)
  have hRL : ‖R‖ * ‖eLin z z' p‖ ≤ (4 : ℝ) ^ m
      * ((p : ℝ) ^ (-2 + 2 * σ₀ * (m : ℝ)) + (p : ℝ) ^ (-2 + 4 * σ₀)) := by
    have h := mul_le_mul hR hLhalf (norm_nonneg _)
      (mul_nonneg h4m0 (Real.rpow_nonneg (le_of_lt hp0R) _))
    have h2 : ((4 : ℝ) ^ m * (p : ℝ) ^ (-2 + 2 * σ₀ * (m : ℝ))) * (1 / 2)
        ≤ (4 : ℝ) ^ m * (p : ℝ) ^ (-2 + 2 * σ₀ * (m : ℝ)) := by
      have hpos := Real.rpow_nonneg (le_of_lt hp0R) (-2 + 2 * σ₀ * (m : ℝ))
      nlinarith [h4m0, hpos]
    calc ‖R‖ * ‖eLin z z' p‖
        ≤ ((4 : ℝ) ^ m * (p : ℝ) ^ (-2 + 2 * σ₀ * (m : ℝ))) * (1 / 2) := h
      _ ≤ (4 : ℝ) ^ m * (p : ℝ) ^ (-2 + 2 * σ₀ * (m : ℝ)) := h2
      _ ≤ (4 : ℝ) ^ m * ((p : ℝ) ^ (-2 + 2 * σ₀ * (m : ℝ)) + (p : ℝ) ^ (-2 + 4 * σ₀)) :=
          mul_le_mul_of_nonneg_left hD1le h4m0
  have hRS : ‖R‖ * ‖S‖ ≤ 30000 * (4 : ℝ) ^ m * ((m : ℝ) ^ 2 + m)
      * ((p : ℝ) ^ (-2 + 2 * σ₀ * (m : ℝ)) + (p : ℝ) ^ (-2 + 4 * σ₀)) := by
    have h := mul_le_mul hR hS2 (norm_nonneg _)
      (mul_nonneg h4m0 (Real.rpow_nonneg (le_of_lt hp0R) _))
    have hD1D2 : (p : ℝ) ^ (-2 + 2 * σ₀ * (m : ℝ)) * (p : ℝ) ^ (-2 + 4 * σ₀)
        ≤ (p : ℝ) ^ (-2 + 2 * σ₀ * (m : ℝ)) := by
      rw [← Real.rpow_add hp0R]
      exact Real.rpow_le_rpow_of_exponent_le hp1R (by linarith [hσ₀1])
    calc ‖R‖ * ‖S‖
        ≤ ((4 : ℝ) ^ m * (p : ℝ) ^ (-2 + 2 * σ₀ * (m : ℝ)))
            * (30000 * ((m : ℝ) ^ 2 + m) * (p : ℝ) ^ (-2 + 4 * σ₀)) := h
      _ = 30000 * (4 : ℝ) ^ m * ((m : ℝ) ^ 2 + m)
            * ((p : ℝ) ^ (-2 + 2 * σ₀ * (m : ℝ)) * (p : ℝ) ^ (-2 + 4 * σ₀)) := by ring
      _ ≤ 30000 * (4 : ℝ) ^ m * ((m : ℝ) ^ 2 + m)
            * (p : ℝ) ^ (-2 + 2 * σ₀ * (m : ℝ)) :=
          mul_le_mul_of_nonneg_left hD1D2 (by positivity)
      _ ≤ 30000 * (4 : ℝ) ^ m * ((m : ℝ) ^ 2 + m)
            * ((p : ℝ) ^ (-2 + 2 * σ₀ * (m : ℝ)) + (p : ℝ) ^ (-2 + 4 * σ₀)) :=
          mul_le_mul_of_nonneg_left hD1le (by positivity)
  have hsum : ‖S‖ + ‖eLin z z' p‖ ^ 2 + ‖eLin z z' p‖ * ‖S‖ + ‖R‖ + ‖R‖ * ‖eLin z z' p‖
      + ‖R‖ * ‖S‖
      ≤ (30000 * ((m : ℝ) ^ 2 + m) + 9 * (m : ℝ) ^ 2 + 15000 * ((m : ℝ) ^ 2 + m)
          + (4 : ℝ) ^ m + (4 : ℝ) ^ m + 30000 * (4 : ℝ) ^ m * ((m : ℝ) ^ 2 + m))
        * ((p : ℝ) ^ (-2 + 2 * σ₀ * (m : ℝ)) + (p : ℝ) ^ (-2 + 4 * σ₀)) := by
    nlinarith [hS1, hLsq, hLS, hR1, hRL, hRS, hD0]
  have hconst : 30000 * ((m : ℝ) ^ 2 + m) + 9 * (m : ℝ) ^ 2 + 15000 * ((m : ℝ) ^ 2 + m)
      + (4 : ℝ) ^ m + (4 : ℝ) ^ m + 30000 * (4 : ℝ) ^ m * ((m : ℝ) ^ 2 + m)
      ≤ 100000 * ((m : ℝ) ^ 3 + 1) * (4 : ℝ) ^ m := by
    have h4m : (1 : ℝ) ≤ (4 : ℝ) ^ m := one_le_pow₀ (by norm_num)
    have hkey : (m : ℝ) ^ 2 + m ≤ (m : ℝ) ^ 3 + 1 := by
      have h := mul_nonneg (sq_nonneg ((m : ℝ) - 1)) (show (0 : ℝ) ≤ (m : ℝ) + 1 by linarith)
      nlinarith [h]
    have hm2' : (m : ℝ) ^ 2 ≤ (m : ℝ) ^ 3 + 1 := by nlinarith [hkey, hm1R, sq_nonneg (m : ℝ)]
    have hP1 : (1 : ℝ) ≤ (m : ℝ) ^ 3 + 1 := by nlinarith [hm1R, sq_nonneg (m : ℝ)]
    nlinarith [h4m, hm1R, hkey, hm2', hP1, sq_nonneg (m : ℝ)]
  refine le_trans htri (le_trans hsum ?_)
  exact mul_le_mul_of_nonneg_right hconst hD0



/-- Summability of `p^{-c}` over `ℕ` for `c > 1` (companion of
`Real.summable_nat_rpow_inv`). -/
lemma summable_nat_rpow_neg {c : ℝ} (hc : 1 < c) :
    Summable (fun p : ℕ => (p : ℝ) ^ (-c)) := by
  have h : Summable (fun n : ℕ => ((n : ℝ) ^ c)⁻¹) :=
    (Real.summable_nat_rpow_inv (p := c)).mpr hc
  exact h.congr (fun n => by rw [Real.rpow_neg (Nat.cast_nonneg n)])

/-- The size condition of `E1p_bound` holds for all `p` above an explicit threshold. -/
lemma hsmall_of_large {p m : ℕ} {σ₀ : ℝ} (hσ₀ : 0 ≤ σ₀) (hσ₀4 : 4 * σ₀ ≤ 1) (hm : 1 ≤ m)
    (hp : max 2 ((6 * m) ^ 2 + 2) ≤ p) :
    (m : ℝ) * (2 * (p : ℝ) ^ (-1 + σ₀) + (p : ℝ) ^ (-1 + 2 * σ₀)) ≤ 1 / 2 := by
  have hm1R : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hp1n : 1 ≤ p := by omega
  have hp1R : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp1n
  have hp0R : (0 : ℝ) < (p : ℝ) := by positivity
  have hplarge : ((6 * m) ^ 2 : ℕ) ≤ p := by omega
  have hplargeR : ((6 * (m : ℝ)) ^ 2) ≤ (p : ℝ) := by
    have h : (((6 * m) ^ 2 : ℕ) : ℝ) ≤ (p : ℝ) := by exact_mod_cast hplarge
    simpa using h
  have hsq : 6 * (m : ℝ) ≤ (p : ℝ) ^ ((1:ℝ)/2) := by
    have hs := Real.sqrt_le_sqrt hplargeR
    rw [Real.sqrt_sq (by positivity), Real.sqrt_eq_rpow] at hs
    exact hs
  have hhalfpos : (0 : ℝ) < (6 * (m : ℝ))⁻¹ := by positivity
  have hinv : (p : ℝ) ^ (-(1/2) : ℝ) ≤ (6 * (m : ℝ))⁻¹ := by
    rw [Real.rpow_neg (le_of_lt hp0R) (1/2)]
    exact (inv_le_inv₀ (by positivity) (by positivity)).mpr hsq
  have hA : (p : ℝ) ^ (-1 + σ₀) ≤ (6 * (m : ℝ))⁻¹ :=
    le_trans (Real.rpow_le_rpow_of_exponent_le hp1R (by linarith)) hinv
  have hC : (p : ℝ) ^ (-1 + 2 * σ₀) ≤ (6 * (m : ℝ))⁻¹ :=
    le_trans (Real.rpow_le_rpow_of_exponent_le hp1R (by linarith)) hinv
  have hthree : (m : ℝ) * 3 * (6 * (m : ℝ))⁻¹ = 1 / 2 := by
    rw [show (6 * (m : ℝ))⁻¹ = 1 / (6 * (m : ℝ)) by ring]
    field_simp
    ring
  nlinarith [hA, hC, hthree, hm1R, hhalfpos]

/-- The majorant of the `E^{(1)}` remainders is summable (`2σ₀m < 1`, `4σ₀ < 1`). -/
lemma summable_E1p_major {σ₀ : ℝ} (hσ₀1 : 4 * σ₀ < 1) (hσ₀m : 2 * σ₀ * (m : ℝ) < 1) :
    Summable (fun p : ℕ => 100000 * ((m : ℝ) ^ 3 + 1) * (4 : ℝ) ^ m
      * ((p : ℝ) ^ (-2 + 2 * σ₀ * (m : ℝ)) + (p : ℝ) ^ (-2 + 4 * σ₀))) := by
  have h1 : Summable (fun p : ℕ => (p : ℝ) ^ (-(2 - 2 * σ₀ * (m : ℝ)))) :=
    summable_nat_rpow_neg (c := 2 - 2 * σ₀ * (m : ℝ)) (by linarith)
  have h2 : Summable (fun p : ℕ => (p : ℝ) ^ (-(2 - 4 * σ₀))) :=
    summable_nat_rpow_neg (c := 2 - 4 * σ₀) (by linarith)
  have h1' : Summable (fun p : ℕ => (p : ℝ) ^ (-2 + 2 * σ₀ * (m : ℝ))) :=
    h1.congr (fun p => by rw [show -(2 - 2 * σ₀ * (m : ℝ)) = -2 + 2 * σ₀ * (m : ℝ) by ring])
  have h2' : Summable (fun p : ℕ => (p : ℝ) ^ (-2 + 4 * σ₀)) :=
    h2.congr (fun p => by rw [show -(2 - 4 * σ₀) = -2 + 4 * σ₀ by ring])
  exact (h1'.add h2').mul_left (100000 * ((m : ℝ) ^ 3 + 1) * (4 : ℝ) ^ m)

theorem E1p_summable (H : LocHyp W Amax A b) {σ₀ : ℝ} (hσ₀ : 0 ≤ σ₀) (hσ₀1 : 4 * σ₀ < 1)
    (hσ₀m : 2 * σ₀ * (m : ℝ) < 1) {z z' : Fin m → ℂ}
    (hz : ∀ j, -σ₀ ≤ (z j).re) (hz' : ∀ j, -σ₀ ≤ (z' j).re) :
    Summable (fun p : ℕ => ‖E1p W A b z z' p - 1‖) := by
  have hm1 : 1 ≤ m := H.hm
  have hm1R : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm1
  have hm0R : (0 : ℝ) < (m : ℝ) := by linarith
  have h4 : 4 * σ₀ ≤ 1 := le_of_lt hσ₀1
  have hg := summable_E1p_major (m := m) hσ₀1 hσ₀m
  have hmajor : ∀ᶠ p : ℕ in Filter.atTop,
      ‖(E1p W A b z z' p - 1 : ℂ)‖ ≤ 100000 * ((m : ℝ) ^ 3 + 1) * (4 : ℝ) ^ m
        * ((p : ℝ) ^ (-2 + 2 * σ₀ * (m : ℝ)) + (p : ℝ) ^ (-2 + 4 * σ₀)) := by
    rw [Filter.eventually_atTop]
    refine ⟨max (W + 1) (max 2 ((6 * m) ^ 2 + 2)), fun p hp => ?_⟩
    have hp1n : 1 ≤ p := by omega
    have hp1R : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp1n
    have hp0R : (0 : ℝ) < (p : ℝ) := by positivity
    have hplarge : ((6 * m) ^ 2 : ℕ) ≤ p := by omega
    have hplargeR : ((6 * (m : ℝ)) ^ 2) ≤ (p : ℝ) := by
      have h : (((6 * m) ^ 2 : ℕ) : ℝ) ≤ (p : ℝ) := by exact_mod_cast hplarge
      simpa using h
    have hsq : 6 * (m : ℝ) ≤ (p : ℝ) ^ ((1:ℝ)/2) := by
      have hs := Real.sqrt_le_sqrt hplargeR
      rw [Real.sqrt_sq (by positivity), Real.sqrt_eq_rpow] at hs
      exact hs
    have hsmall : (m : ℝ) * (2 * (p : ℝ) ^ (-1 + σ₀) + (p : ℝ) ^ (-1 + 2 * σ₀)) ≤ 1 / 2 :=
      hsmall_of_large hσ₀ h4 hm1 (by omega)
    by_cases hpp : p.Prime
    · by_cases hpd : p ∣ W
      · have hE : E1p W A b z z' p = 1 := by
          rw [E1p, if_neg (by tauto : ¬ (p.Prime ∧ ¬ p ∣ W))]
        rw [hE, sub_self, norm_zero]
        refine mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) ?_) ?_) ?_
        · positivity
        · positivity
        · exact add_nonneg (Real.rpow_nonneg (le_of_lt hp0R) _)
            (Real.rpow_nonneg (le_of_lt hp0R) _)
      · exact E1p_bound H hpp hpd hσ₀ h4 hz hz' hsmall
    · have hE : E1p W A b z z' p = 1 := by
        rw [E1p, if_neg (by tauto : ¬ (p.Prime ∧ ¬ p ∣ W))]
      rw [hE, sub_self, norm_zero]
      refine mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) ?_) ?_) ?_
      · positivity
      · positivity
      · exact add_nonneg (Real.rpow_nonneg (le_of_lt hp0R) _)
          (Real.rpow_nonneg (le_of_lt hp0R) _)
  exact (Summable.of_norm_bounded_eventually_nat
    (f := fun p : ℕ => (E1p W A b z z' p - 1 : ℂ)) hg hmajor).norm

end BoxAvg
end GYMaj
