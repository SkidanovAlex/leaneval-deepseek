import Mathlib
import Submission.Work.RHContract.Corpus

/-!
# `ca_exp_eq_two_of_between`

Let `ε > 0`, let `ξ = ξ(ε) = caXi ε ≥ 1530` be the largest prime in the colossally
abundant support of `ε`, and let `ξ₂ = caXi2 ε` be the largest prime whose CA exponent
is `≥ 2`.  Then every prime `p` with `√ξ < p ≤ ξ₂` has CA exponent exactly `2`.

The proof has two halves.

* *Lower bound* `2 ≤ ⌊μ(p,ε)⌋₊`: `ξ₂` is (the maximum of) a prime of the support with
  exponent `≥ 2`, and the CA exponent is non-increasing in the prime
  (`Commons.NumberTheory.Robin.caExp_anti_p`), so `p ≤ ξ₂` gives `2 ≤ ⌊μ(p,ε)⌋₊`.

* *Upper bound* `⌊μ(p,ε)⌋₊ < 3`: if `μ(p,ε) ≥ 3` then (Nicolas' criterion
  `Commons.NumberTheory.Robin.caMu_ge_iff_caF`, `k = 3`) `ε ≤ F₃(p) ≤ 1/(p³ log p)`.
  But `ξ` is the *largest* prime of the support, so the next prime `q` after `ξ`
  (Bertrand: `q ≤ 2ξ`) has exponent `0`, whence `ε > g(2ξ) ≥ 1/((2ξ+1)·log(2ξ))`.
  Combining with `p > √ξ`:
  `p³ log p > ξ√ξ·(log ξ)/2 ≥ (2ξ+1)·log(2ξ) > 1/ε ≥ p³ log p`, a contradiction.
-/

namespace Work.RHContract.A

open scoped BigOperators

noncomputable section

/-- `caF p k = log((p^{k+1} − 1)/(p^{k+1} − p))/log p`, the CA level-`k` threshold at the
prime `p`; this is verbatim the right-hand side of
`Commons.NumberTheory.Robin.caMu_ge_iff_caF`. -/
private def caF (p : ℕ) (k : ℕ) : ℝ :=
  Real.log (((p : ℝ) ^ (k + 1 : ℕ) - 1) / ((p : ℝ) ^ (k + 1 : ℕ) - (p : ℝ))) / Real.log (p : ℝ)

/-- `caG t = log(1 + 1/t)/log t`, the `k = 1` threshold on the reals. -/
private def caG (t : ℝ) : ℝ := Real.log (1 + 1 / t) / Real.log t

/-- Nicolas' criterion in the vocabulary of `Work.RHPlan.caMu` (the definitions agree). -/
private lemma caMu_ge_iff {p : ℕ} {ε : ℝ} {k : ℕ} (hp : 2 ≤ p) (hε : 0 < ε) (hk : 1 ≤ k) :
    (k : ℝ) ≤ Work.RHPlan.caMu p ε ↔ ε ≤ caF p k := by
  simp only [Work.RHPlan.caMu, caF]
  exact Commons.NumberTheory.Robin.caMu_ge_iff_caF p ε k hp hε hk

/-- `Work.RHPlan.caMu p ε > 0` for `p ≥ 2`, `ε > 0`. -/
private lemma caMu_pos' {p : ℕ} {ε : ℝ} (hp : 2 ≤ p) (hε : 0 < ε) :
    0 < Work.RHPlan.caMu p ε := by
  simpa only [Work.RHPlan.caMu] using Commons.NumberTheory.Robin.caMu_pos hp hε

/-- The CA exponent is non-increasing in the prime. -/
private lemma caExp_anti {p q : ℕ} {ε : ℝ} (hp : 2 ≤ p) (hq : 2 ≤ q) (hε : 0 < ε)
    (hlt : p < q) : ⌊Work.RHPlan.caMu q ε⌋₊ ≤ ⌊Work.RHPlan.caMu p ε⌋₊ := by
  simpa only [Work.RHPlan.caMu] using
    Commons.NumberTheory.Robin.caExp_anti_p (p := p) (q := q) (ε := ε) hp hq hε hlt

/-- `caF p 1 = caG p`. -/
private lemma caF_one_eq (p : ℕ) (hp : 2 ≤ p) : caF p 1 = caG p := by
  unfold caF caG
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 1 < p)
  have hmain : (((p : ℝ) ^ (1 + 1 : ℕ) - 1) / ((p : ℝ) ^ (1 + 1 : ℕ) - (p : ℝ)))
      = 1 + 1 / (p : ℝ) := by
    have h2 : ((p : ℝ) ^ (1 + 1 : ℕ)) = (p : ℝ) ^ 2 := by norm_num
    rw [h2]
    have hnum : (p : ℝ) ^ 2 - 1 = ((p : ℝ) + 1) * ((p : ℝ) - 1) := by ring
    have hden : (p : ℝ) ^ 2 - (p : ℝ) = (p : ℝ) * ((p : ℝ) - 1) := by ring
    rw [hnum, hden]
    have hp0 : (p : ℝ) ≠ 0 := by positivity
    have hpm1 : (p : ℝ) - 1 ≠ 0 := by linarith
    field_simp
  rw [hmain]

/-- `caF p 3 = log(1 + 1/(p + p² + p³))/log p`. -/
private lemma caF_three_eq (p : ℕ) (hp : 2 ≤ p) :
    caF p 3 = Real.log (1 + 1 / ((p : ℝ) + (p : ℝ) ^ 2 + (p : ℝ) ^ 3)) / Real.log (p : ℝ) := by
  unfold caF
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 1 < p)
  have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
  have hmain : (((p : ℝ) ^ (3 + 1 : ℕ) - 1) / ((p : ℝ) ^ (3 + 1 : ℕ) - (p : ℝ)))
      = 1 + 1 / ((p : ℝ) + (p : ℝ) ^ 2 + (p : ℝ) ^ 3) := by
    have h4 : ((p : ℝ) ^ (3 + 1 : ℕ)) = (p : ℝ) ^ 4 := by norm_num
    rw [h4]
    have hden : (p : ℝ) ^ 4 - (p : ℝ) ≠ 0 := by
      have he : (p : ℝ) ^ 4 - (p : ℝ) = (p : ℝ) * ((p : ℝ) ^ 3 - 1) := by ring
      rw [he]
      have h3 : (1 : ℝ) < (p : ℝ) ^ 3 := one_lt_pow₀ hp1 (by norm_num)
      exact ne_of_gt (mul_pos hp0 (by linarith))
    rw [div_eq_iff hden]
    field_simp
    ring
  rw [hmain]

/-! ## Numeric bounds -/

/-- For `ξ ≥ 1530`: `(2ξ+1)·log(2ξ) ≤ ξ·√ξ·log ξ/2`. -/
private lemma two_xi_plus_one_log_le {ξ : ℝ} (hξ : 1530 ≤ ξ) :
    (2 * ξ + 1) * Real.log (2 * ξ) ≤ ξ * Real.sqrt ξ * Real.log ξ / 2 := by
  have hξ1 : (1 : ℝ) ≤ ξ := by linarith
  have hξ0 : (0 : ℝ) < ξ := by linarith
  have hL7 : (7 : ℝ) ≤ Real.log ξ := by
    have h1 := Commons.Analysis.Log.log_1530_bounds.1
    have h2 : Real.log 1530 ≤ Real.log ξ := Real.log_le_log (by norm_num) hξ
    linarith
  have hLpos : (0 : ℝ) < Real.log ξ := by linarith
  have hs39 : (39 : ℝ) ≤ Real.sqrt ξ := by
    have h1 : Real.sqrt 1530 ≤ Real.sqrt ξ := Real.sqrt_le_sqrt hξ
    have h2 : (39 : ℝ) ≤ Real.sqrt 1530 := by
      rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
    linarith
  have hlog2 : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
  have hlog2xi : Real.log (2 * ξ) = Real.log 2 + Real.log ξ := by
    rw [Real.log_mul (by norm_num) (ne_of_gt hξ0)]
  rw [hlog2xi]
  have hstep1 : (2 * ξ + 1) * (Real.log 2 + Real.log ξ) ≤ (2.5 * ξ) * (1 + Real.log ξ) := by
    have hA : 2 * ξ + 1 ≤ 2.5 * ξ := by linarith
    have hB : Real.log 2 + Real.log ξ ≤ 1 + Real.log ξ := by linarith
    calc (2 * ξ + 1) * (Real.log 2 + Real.log ξ)
        ≤ (2.5 * ξ) * (Real.log 2 + Real.log ξ) :=
          mul_le_mul_of_nonneg_right hA (by positivity)
      _ ≤ (2.5 * ξ) * (1 + Real.log ξ) :=
          mul_le_mul_of_nonneg_left hB (by linarith)
  have hstep2 : (2.5 * ξ) * (1 + Real.log ξ) ≤ ξ * Real.sqrt ξ * Real.log ξ / 2 := by
    have hkey : 2.5 * (1 + Real.log ξ) ≤ Real.sqrt ξ * Real.log ξ / 2 := by
      nlinarith [hL7, hs39, hLpos]
    calc (2.5 * ξ) * (1 + Real.log ξ) = ξ * (2.5 * (1 + Real.log ξ)) := by ring
      _ ≤ ξ * (Real.sqrt ξ * Real.log ξ / 2) := mul_le_mul_of_nonneg_left hkey (by linarith)
      _ = ξ * Real.sqrt ξ * Real.log ξ / 2 := by ring
  linarith

/-- For `ξ ≥ 1530` and `p > √ξ`: `ξ·√ξ·log ξ/2 < p³·log p`. -/
private lemma xi_sqrt_log_lt_cube {ξ : ℝ} (hξ : 1530 ≤ ξ) {p : ℕ}
    (hp : Real.sqrt ξ < (p : ℝ)) : ξ * Real.sqrt ξ * Real.log ξ / 2 < (p : ℝ) ^ 3 * Real.log (p : ℝ) := by
  have hξ0 : (0 : ℝ) < ξ := by linarith
  have hξ1 : (1 : ℝ) < ξ := by linarith
  have hs0 : (0 : ℝ) ≤ Real.sqrt ξ := Real.sqrt_nonneg ξ
  have hspos : (0 : ℝ) < Real.sqrt ξ := Real.sqrt_pos.mpr hξ0
  have hp0 : (0 : ℝ) < (p : ℝ) := lt_trans hspos hp
  have hcube : ξ * Real.sqrt ξ < (p : ℝ) ^ 3 := by
    have h1 : (Real.sqrt ξ) ^ 3 < (p : ℝ) ^ 3 :=
      pow_lt_pow_left₀ hp hs0 (by norm_num : (3 : ℕ) ≠ 0)
    have hsq : (Real.sqrt ξ) ^ 2 = ξ := Real.sq_sqrt (le_of_lt hξ0)
    have h2 : (Real.sqrt ξ) ^ 3 = ξ * Real.sqrt ξ := by
      rw [show (3 : ℕ) = 2 + 1 by norm_num, pow_succ, hsq]
    linarith [h1, h2.le, h2.ge]
  have hlog : Real.log ξ / 2 < Real.log (p : ℝ) := by
    have h1 : Real.log (Real.sqrt ξ) < Real.log (p : ℝ) := Real.log_lt_log hspos hp
    rwa [Real.log_sqrt (le_of_lt hξ0)] at h1
  have hlogpos : (0 : ℝ) < Real.log ξ / 2 := by
    have h := Real.log_pos hξ1; linarith
  calc ξ * Real.sqrt ξ * Real.log ξ / 2 = (ξ * Real.sqrt ξ) * (Real.log ξ / 2) := by ring
    _ < (p : ℝ) ^ 3 * Real.log (p : ℝ) :=
        mul_lt_mul hcube (le_of_lt hlog) hlogpos (le_of_lt (pow_pos hp0 3))

/-- For `ξ ≥ 1530`: `1/((2ξ+1)·log(2ξ)) < caG (2ξ)`. -/
private lemma inv_lt_caG_two_xi {ξ : ℝ} (hξ : 1530 ≤ ξ) :
    1 / ((2 * ξ + 1) * Real.log (2 * ξ)) < caG (2 * ξ) := by
  have h2ξ0 : (0 : ℝ) < 2 * ξ := by linarith
  have h2ξ1 : (1 : ℝ) < 2 * ξ := by linarith
  have hlog : 0 < Real.log (2 * ξ) := Real.log_pos h2ξ1
  have hb : 1 / (2 * ξ + 1) < Real.log (1 + 1 / (2 * ξ)) :=
    (Commons.Analysis.Real.log_one_add_inv_bounds (t := 2 * ξ) h2ξ0).1
  have hgoal : 1 / (2 * ξ + 1) / Real.log (2 * ξ) < caG (2 * ξ) := by
    rw [caG]
    exact div_lt_div_of_pos_right hb hlog
  rwa [div_div] at hgoal

/-! ## The lower bound on `ε` from the maximality of `ξ` -/

/-- A prime above `ξ(ε)` has CA exponent `0`. -/
private lemma caExp_eq_zero_of_gt_xi {ε : ℝ} (hε : 0 < ε) {q : ℕ} (hq : Nat.Prime q)
    (hgt : Work.RHPlan.caXi ε < q) : ⌊Work.RHPlan.caMu q ε⌋₊ = 0 := by
  by_cases hb : Nat.ceil (Real.exp (2 / ε)) + 2 ≤ q
  · simpa only [Work.RHPlan.caMu] using
      Commons.NumberTheory.Robin.caExp_eq_zero_of_ge_bound q ε hq.two_le hε hb
  · push_neg at hb
    have hnotmem : ¬ (q ∈ Work.RHPlan.caSupport ε) := by
      intro hmem
      have hle : q ≤ Work.RHPlan.caXi ε := by
        rw [Work.RHPlan.caXi]
        exact Finset.le_sup (f := id) hmem
      omega
    by_contra hne0
    have hge : 1 ≤ ⌊Work.RHPlan.caMu q ε⌋₊ := Nat.one_le_iff_ne_zero.mpr hne0
    exact hnotmem (Finset.mem_filter.mpr
      ⟨Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hb, hq⟩, hge⟩)

/-- `caG (2ξ(ε)) < ε`: the maximality of `ξ(ε)` in the support (Bertrand gives a prime
`q` with `ξ < q ≤ 2ξ`, whose exponent is `0`) forces `ε > g(2ξ) ≥ 1/((2ξ+1)log(2ξ))`. -/
private lemma caG_two_xi_lt_eps {ε : ℝ} (hε : 0 < ε)
    (hξ : 1530 ≤ (Work.RHPlan.caXi ε : ℝ)) :
    caG (2 * (Work.RHPlan.caXi ε : ℝ)) < ε := by
  have hne : Work.RHPlan.caXi ε ≠ 0 := by
    intro h
    rw [h] at hξ
    norm_num at hξ
  obtain ⟨q, hq, hgt, hle2⟩ := Nat.exists_prime_lt_and_le_two_mul (Work.RHPlan.caXi ε) hne
  have hzero : ⌊Work.RHPlan.caMu q ε⌋₊ = 0 := caExp_eq_zero_of_gt_xi hε hq hgt
  have hmu_lt : Work.RHPlan.caMu q ε < 1 := Nat.floor_eq_zero.mp hzero
  have hq2 : 2 ≤ q := hq.two_le
  have hnot : ¬ (((1 : ℕ) : ℝ) ≤ Work.RHPlan.caMu q ε) := by
    rw [Nat.cast_one]
    exact not_le.mpr hmu_lt
  have hgtF : caF q 1 < ε :=
    not_le.mp ((caMu_ge_iff (p := q) (ε := ε) (k := 1) hq2 hε (le_refl 1)).not.mp hnot)
  rw [caF_one_eq q hq2] at hgtF
  have hmono : caG (2 * (Work.RHPlan.caXi ε : ℝ)) ≤ caG (q : ℝ) := by
    have hq1 : (1 : ℝ) < (q : ℝ) := by exact_mod_cast hq.one_lt
    have h2ξ1 : (1 : ℝ) < 2 * (Work.RHPlan.caXi ε : ℝ) := by linarith
    rcases lt_or_eq_of_le (by exact_mod_cast hle2 : (q : ℝ) ≤ 2 * (Work.RHPlan.caXi ε : ℝ)) with
      hlt | heq
    · simpa only [caG] using le_of_lt
        (Commons.Analysis.Real.log_one_add_inv_div_log_strictAntiOn hq1 h2ξ1 hlt)
    · rw [heq]
  linarith

/-! ## The lower bound on the exponent -/

/-- If `p ≤ ξ₂(ε)` is a prime then `2 ≤ μ(p,ε)`. -/
private lemma two_le_caMu_of_le_caXi2 {ε : ℝ} (hε : 0 < ε) {p : ℕ} (hp : Nat.Prime p)
    (h2 : p ≤ Work.RHContract.Margin.caXi2 ε) : (2 : ℝ) ≤ Work.RHPlan.caMu p ε := by
  have hp2 : 2 ≤ p := hp.two_le
  set T : Finset ℕ :=
    (Work.RHPlan.caSupport ε).filter (fun q => 2 ≤ ⌊Work.RHPlan.caMu q ε⌋₊) with hT
  have hxi2 : Work.RHContract.Margin.caXi2 ε = T.sup id := by rw [hT]; rfl
  have hTne : T.Nonempty := by
    rcases Finset.eq_empty_or_nonempty T with h | h
    · exfalso
      rw [hxi2, h] at h2
      simp at h2
      omega
    · exact h
  have hx2T : Work.RHContract.Margin.caXi2 ε ∈ T := by
    have hx2 : Work.RHContract.Margin.caXi2 ε = T.max' hTne := by
      rw [hxi2, Finset.max'_eq_sup', Finset.sup'_eq_sup hTne]
    rw [hx2]
    exact Finset.max'_mem T hTne
  have hx2S : Work.RHContract.Margin.caXi2 ε ∈ Work.RHPlan.caSupport ε :=
    (Finset.mem_filter.mp hx2T).1
  have hx2exp : 2 ≤ ⌊Work.RHPlan.caMu (Work.RHContract.Margin.caXi2 ε) ε⌋₊ :=
    (Finset.mem_filter.mp hx2T).2
  have hx2prime : Nat.Prime (Work.RHContract.Margin.caXi2 ε) :=
    (Finset.mem_filter.mp (Finset.mem_filter.mp hx2S).1).2
  have hx22 : 2 ≤ Work.RHContract.Margin.caXi2 ε := hx2prime.two_le
  rcases eq_or_lt_of_le h2 with heq | hlt
  · have : (2 : ℝ) ≤ Work.RHPlan.caMu (Work.RHContract.Margin.caXi2 ε) ε :=
      le_trans (by exact_mod_cast hx2exp) (Nat.floor_le (le_of_lt (caMu_pos' hx22 hε)))
    rwa [← heq] at this
  · have hle : ⌊Work.RHPlan.caMu (Work.RHContract.Margin.caXi2 ε) ε⌋₊ ≤
        ⌊Work.RHPlan.caMu p ε⌋₊ := caExp_anti hp2 hx22 hε hlt
    have hfloor : 2 ≤ ⌊Work.RHPlan.caMu p ε⌋₊ := le_trans hx2exp hle
    exact le_trans (by exact_mod_cast hfloor) (Nat.floor_le (le_of_lt (caMu_pos' hp2 hε)))

/-! ## The target -/

theorem ca_exp_eq_two_of_between (ε : ℝ) (hε : 0 < ε) (hξ : 1530 ≤ (Work.RHPlan.caXi ε : ℝ))
    {p : ℕ} (hp : Nat.Prime p) (h1 : Real.sqrt (Work.RHPlan.caXi ε : ℝ) < (p : ℝ))
    (h2 : p ≤ Work.RHContract.Margin.caXi2 ε) : ⌊Work.RHPlan.caMu p ε⌋₊ = 2 := by
  have hp2 : 2 ≤ p := hp.two_le
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp.one_lt
  have hge : 2 ≤ ⌊Work.RHPlan.caMu p ε⌋₊ :=
    Nat.le_floor (two_le_caMu_of_le_caXi2 hε hp h2)
  have hlt : ⌊Work.RHPlan.caMu p ε⌋₊ < 3 := by
    rw [Nat.floor_lt' (by norm_num : (3 : ℕ) ≠ 0)]
    by_contra hcon
    push_neg at hcon
    have hlogp : 0 < Real.log (p : ℝ) := Real.log_pos hp1
    -- `ε ≤ F₃(p)`
    have hF3 : ε ≤ caF p 3 :=
      (caMu_ge_iff (p := p) (ε := ε) (k := 3) hp2 hε (by norm_num)).mp hcon
    rw [caF_three_eq p hp2] at hF3
    -- `ε·log p ≤ log(1 + 1/(p+p²+p³)) ≤ 1/p³`
    have hSpos : (0 : ℝ) < (p : ℝ) + (p : ℝ) ^ 2 + (p : ℝ) ^ 3 := by positivity
    have hlogbound : Real.log (1 + 1 / ((p : ℝ) + (p : ℝ) ^ 2 + (p : ℝ) ^ 3)) ≤ 1 / (p : ℝ) ^ 3 := by
      have h1' : Real.log (1 + 1 / ((p : ℝ) + (p : ℝ) ^ 2 + (p : ℝ) ^ 3))
          ≤ 1 / ((p : ℝ) + (p : ℝ) ^ 2 + (p : ℝ) ^ 3) := by
        have h := Real.log_le_sub_one_of_pos
          (show (0 : ℝ) < 1 + 1 / ((p : ℝ) + (p : ℝ) ^ 2 + (p : ℝ) ^ 3) by positivity)
        linarith
      have h2' : 1 / ((p : ℝ) + (p : ℝ) ^ 2 + (p : ℝ) ^ 3) ≤ 1 / (p : ℝ) ^ 3 := by
        apply one_div_le_one_div_of_le (by positivity)
        nlinarith [hp1]
      linarith
    have hepslog : ε * Real.log (p : ℝ) ≤ 1 / (p : ℝ) ^ 3 := by
      have h := mul_le_mul_of_nonneg_right hF3 (le_of_lt hlogp)
      rw [div_mul_cancel₀ _ (ne_of_gt hlogp)] at h
      linarith
    have hcube_log : (p : ℝ) ^ 3 * Real.log (p : ℝ) ≤ 1 / ε := by
      rw [le_div_iff₀ hε]
      have h := mul_le_mul_of_nonneg_left hepslog (show (0 : ℝ) ≤ (p : ℝ) ^ 3 by positivity)
      have h2'' : (p : ℝ) ^ 3 * (1 / (p : ℝ) ^ 3) = 1 := by
        have : (0:ℝ) < (p : ℝ) ^ 3 := by positivity
        field_simp
      nlinarith [h, h2'']
    -- `1/ε < (2ξ+1)·log(2ξ)`
    have hDpos : 0 < (2 * (Work.RHPlan.caXi ε : ℝ) + 1) * Real.log (2 * (Work.RHPlan.caXi ε : ℝ)) := by
      have : 0 < Real.log (2 * (Work.RHPlan.caXi ε : ℝ)) :=
        Real.log_pos (by linarith)
      positivity
    have hDgt : 1 / ε < (2 * (Work.RHPlan.caXi ε : ℝ) + 1) * Real.log (2 * (Work.RHPlan.caXi ε : ℝ)) := by
      have h3 : 1 / ((2 * (Work.RHPlan.caXi ε : ℝ) + 1) * Real.log (2 * (Work.RHPlan.caXi ε : ℝ)))
          < ε := lt_trans (inv_lt_caG_two_xi hξ) (caG_two_xi_lt_eps hε hξ)
      have h4 : 1 < ε * ((2 * (Work.RHPlan.caXi ε : ℝ) + 1) * Real.log (2 * (Work.RHPlan.caXi ε : ℝ))) :=
        (div_lt_iff₀ hDpos).mp h3
      exact (div_lt_iff₀ hε).mpr (by nlinarith [h4])
    linarith [hcube_log, hDgt, two_xi_plus_one_log_le hξ, xi_sqrt_log_lt_cube hξ h1]
  omega

end

end Work.RHContract.A
