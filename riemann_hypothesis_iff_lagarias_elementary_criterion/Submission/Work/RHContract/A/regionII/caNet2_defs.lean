import Mathlib
import Submission.Work.RHContract.Corpus
import Submission.Work.RHContract.A.regionII.Defs
import Submission.Work.RHContract.A.caXi2_le_sqrt
import Submission.Work.RHContract.A.caLevel_le
import Submission.Work.RHContract.A.ca_margin_lower
import Submission.Work.RHContract.Helper.exp_le_caExp
import Submission.Work.Analysis.Primes.sum_primes_le_third
import Submission.Work.NumberTheory.Chebyshev.theta_deficit_upper
import Submission.Work.RHContract.A.regionII.final_arith2
import Submission.Commons.NumberTheory.Chebyshev.theta_bracket_finite_range
import Submission.Commons.NumberTheory.Chebyshev.psi_sub_theta_eventually_le
/-!
# `Work.RHContract.A.regionII.caNet2_defs`

Definitions and numerical helpers for the `Net₂ ≥ 0` argument of Region II.

## The overall shape of the argument

For `ε > 0` with `ξ := (caXi ε : ℝ) ∈ [10^5, 10^8)`, `s := √ξ`, `L := log ξ`,
`c := (caC ε) = (1 − 3/√ξ)/(ψ ξ · log ψ ξ)`, `ξ₂ := caXi2 ε`, the quantity to control is

`Net₂ = ∑_{p ∈ netS ε} netF c p`,  `netF c p = c log p − 1/(2p(p−1))`,

where `netS ε = {p prime : netM ξ < p ≤ ξ₂}` and `netM ξ = ⌊√ξ⌋₊`.  The summands are *not*
individually nonnegative: `netF c p < 0` for the few primes just above `√ξ`.  The argument
splits `netS ε` at `netPf ξ = ⌊1.15√ξ⌋₊`:

* **loss region** `p ≤ netPf ξ`: every term is at worst `−(h(p) − c)^+ log p` with
  `h(p) = 1/(2p(p−1)log p)`.  Since `h(p) ≤ B/(p(p−1))` with `B = 1/(2log(m+1))`, `m = netM ξ`,
  the prime sum is compared with the integer sum over `[m−2, Pf]` via
  `Work.Analysis.Primes.sum_primes_le_third` (`∑_{primes} ≤ (1/3)∑_{all n}`), then telescoped
  (`∑ 1/(n(n−1)) = 1/(m−3) − 1/N`, `sum_Icc_telescope`) and maximised by AM–GM, giving
  `(√(B/(m−3)) − √(c(m−3)))² ≤ δ²/(m−3)` with
  `δ = max(1/√L − 0.9375/√(L+0.0941), 1.04/√(L−0.105361) − 1/√(L+0.006329))`
  (bound `caNet2_delta`).  Hence the loss is at least `−(1/3)log(Pf)·δ²/(m−3) ≥ −netY L/(s−4)`
  with `netY L = (1/3)(L/2 + 0.15)(0.0045/L)` (uses `log Pf ≤ L/2 + 0.15`).

* **gain region** `p > netPf ξ`: here all summands are positive.  Writing
  `θ(Nf) − θ(Pf) = ∑_{Pf < p ≤ Nf} log p` with `Nf = netNf ξ = ⌊√(2ξ)(1 − log2/(2log ξ))⌋₊`
  (justified by `Commons.NumberTheory.Robin.ca_level_two_lower`, i.e. `netMemS`), Chebyshev's
  bounds `θ Nf ≥ Nf − 2.1√Nf` (`Work.NumberTheory.Chebyshev.theta_deficit_upper`) and
  `θ Pf ≤ Pf − 0.5√Pf` (`theta_deficit_half`, above) give
  `θ(Nf) − θ(Pf) ≥ netMasslb s L`; and `1/(2p(p−1)) ≤ netHb ξ · log p` for `p > Pf` with
  `netHb ξ = 0.38/(ξ(L/2 + 0.1397))`.  Since `c − netHb ξ ≥ netK L/s²` with
  `netK L = (0.07075L + 0.090181)/((L + 0.0941)(L/2 + 0.1397))`, the gain is at least
  `(netK L/s²)·netMasslb s L`.

* **assembly**: `Net₂ ≥ −netY L/(s−4) + (netK L/s²)·netMasslb s L`
  `≥ (netK L·ν(L) − netY L)/(s−4) ≥ 0`, where `ν(L) = netNuA L` for `s ≤ 1000` and
  `ν(L) = netNuB L` for `s ≥ 1000` (lemmas `netMassA`, `netMassB`), and the final rational
  inequality `netY L ≤ netK L·ν L` is `caNet2_arith_A` / `caNet2_arith_B`.

## The elementary constant bounds used

`net_log_log3_le`: `log(log 3) ≤ 0.0941`; `net_log_115_ge`/`net_log_115_le`:
`0.1397 ≤ log(23/20) ≤ 0.15`; `net_log_10_9_le`: `log(10/9) ≤ 0.105361`;
`net_sqrt2_log2_half`: `(√2·log 2)/2 ≤ 0.49013`.  The c-bounds themselves are
`caC ε ≥ 0.9015/(ξ(L+0.0941))` (from `ψ ξ ≤ log 3·ξ`) and
`caC ε ≤ 1/(0.9·ξ·(L−0.105361))` (from `θ ξ ≥ 0.9ξ ≤ ψ ξ`).
-/


open scoped BigOperators
open Commons.NumberTheory.Chebyshev Commons.NumberTheory.Chebyshev.ThetaBracket

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Work.RHContract.A.regionII

noncomputable section

/-! ## Part 2: numerical helpers and the `Net₂` quantities -/

/-- `log (log 3) ≤ 941/10000 = 0.0941`. -/
lemma net_log_log3_le : Real.log (Real.log 3) ≤ 941 / 10000 := by
  have h3 : Real.log 3 ≤ (1.0986122888 : ℝ) := le_of_lt Real.log_three_lt_d9
  have h3pos : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hmono : Real.log (Real.log 3) ≤ Real.log (1.0986122888 : ℝ) := Real.log_le_log h3pos h3
  have hb : Real.log (1.0986122888 : ℝ) ≤ 941 / 10000 := by
    have hx : (1.0986122888 : ℝ) = 1 + 0.0986122888 := by norm_num
    rw [hx]
    have hcub := @Commons.Analysis.Real.log_one_add_le_cubic (0.0986122888) (by norm_num)
    norm_num at hcub ⊢
    linarith
  linarith

/-- `0.1397 ≤ log (115/100) = log 1.15`, from the logarithm series to four terms. -/
lemma net_log_115_ge : (1397 / 10000 : ℝ) ≤ Real.log (115 / 100) := by
  have hv0 : (0 : ℝ) ≤ 3 / 23 := by norm_num
  have hs := Real.hasSum_pow_div_log_of_abs_lt_one (x := (3 / 23 : ℝ))
    (by rw [abs_of_nonneg hv0]; norm_num)
  have hle : ∑ n ∈ Finset.range 4, (3 / 23 : ℝ) ^ (n + 1) / ((n : ℝ) + 1)
      ≤ ∑' (n : ℕ), (3 / 23 : ℝ) ^ (n + 1) / ((n : ℝ) + 1) :=
    Summable.sum_le_tsum (Finset.range 4) (fun i _ => by positivity) hs.summable
  rw [hs.tsum_eq] at hle
  have hsum : ∑ n ∈ Finset.range 4, (3 / 23 : ℝ) ^ (n + 1) / ((n : ℝ) + 1)
      = (3 / 23 : ℝ) + (3 / 23) ^ 2 / 2 + (3 / 23) ^ 3 / 3 + (3 / 23) ^ 4 / 4 := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    norm_num
  rw [hsum] at hle
  have hkey : Real.log (1 - 3 / 23 : ℝ) = - Real.log (115 / 100) := by
    have h1 : (1 - 3 / 23 : ℝ) = 20 / 23 := by norm_num
    rw [h1]
    have : (20 : ℝ) / 23 = (115 / 100)⁻¹ := by norm_num
    rw [this, Real.log_inv]
  rw [hkey] at hle
  norm_num at hle ⊢
  linarith

/-- `log (115/100) ≤ 0.15`. -/
lemma net_log_115_le : Real.log (115 / 100) ≤ 15 / 100 := by
  have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 115 / 100 by norm_num)
  norm_num at h ⊢
  linarith

/-- `log 10 - 2 log 3 = log (10/9) ≤ 0.105361`. -/
lemma net_log_10_9_le : Real.log 10 - 2 * Real.log 3 ≤ 105361 / 1000000 := by
  have h10 : Real.log 10 = Real.log 2 + Real.log 5 := Real.log_ten_eq
  have h1 : Real.log 10 ≤ 2.3025850934 := by
    rw [h10]; linarith [Real.log_two_lt_d9, Real.log_five_lt_d9]
  have h3 : (1.0986122885 : ℝ) ≤ Real.log 3 := le_of_lt Real.log_three_gt_d9
  linarith

/-- `(√2 · log 2)/2 ≤ 0.49013`. -/
lemma net_sqrt2_log2_half : Real.sqrt 2 * Real.log 2 / 2 ≤ 49013 / 100000 := by
  have h2 : Real.sqrt 2 ≤ 1.414214 := by rw [Real.sqrt_le_iff]; norm_num
  have hl2 : Real.log 2 ≤ 0.6931471808 := le_of_lt Real.log_two_lt_d9
  have h2p : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hl2p : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  nlinarith [h2, hl2, h2p, hl2p]

/-- `m = ⌊√ξ⌋₊`. -/
noncomputable def netM (ξ : ℝ) : ℕ := ⌊Real.sqrt ξ⌋₊

/-- `Pf = ⌊(115/100)√ξ⌋₊`, the cut between the loss region and the gain region. -/
noncomputable def netPf (ξ : ℝ) : ℕ := ⌊(115 / 100 : ℝ) * Real.sqrt ξ⌋₊

/-- `qlo = √(2ξ)(1 − log 2/(2 log ξ))`, the proved lower bound for `ξ₂ = caXi2 ε`. -/
noncomputable def netQlo (ξ : ℝ) : ℝ :=
  Real.sqrt 2 * Real.sqrt ξ * (1 - Real.log 2 / (2 * Real.log ξ))

/-- `Nf = ⌊qlo⌋₊`. -/
noncomputable def netNf (ξ : ℝ) : ℕ := ⌊netQlo ξ⌋₊

/-- `hb = 0.38/(s²(L/2 + 0.1397))`, the weight that dominates `1/(2p(p−1)log p)` on
the gain region. -/
noncomputable def netHb (ξ : ℝ) : ℝ := 38 / 100 / (ξ * (Real.log ξ / 2 + 1397 / 10000))

/-- The loss coefficient on `L ≤ 2 log 1000`. -/
noncomputable def netNuA (L : ℝ) : ℝ := 1488 / 10000 - 483906 / 1000000 / L

/-- The loss coefficient on `L ≥ 2 log 1000`. -/
noncomputable def netNuB (L : ℝ) : ℝ := 20036 / 100000 - 48817 / 100000 / L

/-- The boundary-loss bound `Y(L)`. -/
noncomputable def netY (L : ℝ) : ℝ :=
  (1 / 3) * (L / 2 + 15 / 100) * ((45 / 10000) / L)

/-- The gain coefficient `K(L)`. -/
noncomputable def netK (L : ℝ) : ℝ :=
  (7075 / 100000 * L + 90181 / 1000000) / ((L + 941 / 10000) * (L / 2 + 1397 / 10000))




/-- The summand of `Net₂`: `c·log p − 1/(2p(p−1))`. -/
noncomputable def netF (c : ℝ) (p : ℕ) : ℝ :=
  c * Real.log (p : ℝ) - 1 / (2 * (p : ℝ) * ((p : ℝ) - 1))

/-- The index set `{√ξ < p ≤ ξ₂}` of `Net₂`. -/
noncomputable def netS (ε : ℝ) : Finset ℕ :=
  (Nat.primesLE (Work.RHContract.Margin.caXi2 ε)).filter
    (fun q => netM (Work.RHPlan.caXi ε : ℝ) < q)

/-- The lower bound for `θ(Nf) − θ(Pf)`, the "mass" of the gain region. -/
noncomputable def netMasslb (s L : ℝ) : ℝ :=
  26421 / 100000 * s - 49013 / 100000 * s / L - 1 - 196189 / 100000 * Real.sqrt s

/-! ## Part 1: the certified deficit bound `θ t ≤ t − (1/2)√t` on `[360, 12000]` -/

/-- One prime gap `pr = ((a, ·), (b, ·))` of the upper Chebyshev table: `a.1` is a prime and
`b.2` is the cumulative upper bound `Σ_{q ≤ a} utOf q ≥ 10^9 θ(a)`.  The check (ignored for
`a.1 > 12000`) verifies `10^9 θ(a) ≤ 10^9 (a − (1/2)√a)`, i.e.
`(10^9 a − b.2)² ≥ (5·10^8)² a` in integer arithmetic. -/
def gapDefCheck (pr : (ℕ × ℕ) × (ℕ × ℕ)) : Bool :=
  decide (12000 < pr.1.1) ||
    (decide (pr.2.2 ≤ pr.1.1 * 10 ^ 9) &&
      decide (10 ^ 18 * pr.1.1 ≤ 4 * (pr.1.1 * 10 ^ 9 - pr.2.2) ^ 2))

theorem gapDefCheck_all : (CU.zip CU.tail).all gapDefCheck = true := by decide

lemma gapDefCheck_spec (pr : (ℕ × ℕ) × (ℕ × ℕ)) (h : pr ∈ CU.zip CU.tail) :
    gapDefCheck pr = true := List.all_eq_true.mp gapDefCheck_all pr h

/-- The integer form of the certified deficit bound. -/
lemma int_deficit_half (n : ℕ) (h1 : 360 ≤ n) (h2 : n ≤ 12000) :
    Chebyshev.theta (n : ℝ) ≤ (n : ℝ) - (1 / 2) * Real.sqrt (n : ℝ) := by
  have hsent : sentCU ∈ CU := List.mem_append_right _ (by simp)
  have hlt : n < sentCU.1 := by simp [sentCU]; omega
  have hex : ∃ e ∈ CU, n < e.1 := ⟨sentCU, hsent, hlt⟩
  have hhead : ∀ e, CU.head? = some e → e.1 ≤ n := by
    intro e he
    rw [CU_head] at he
    simp only [Option.some.injEq] at he
    subst he
    omega
  have hisSome : (bnd2 CU n).isSome = true := bnd2_isSome_of CU n hhead hex
  obtain ⟨⟨a, b⟩, hc⟩ := Option.isSome_iff_exists.mp hisSome
  obtain ⟨hmem, ha_le, hn_lt⟩ := bnd2_spec CU n hc
  have hbnd : ThetaFinite.bnd CU n = some b := bnd2_snd_eq_bnd CU n hc
  have hbspec : b.2 = (CU.head?.map Prod.snd).getD 0 + psumF utOf CU n :=
    bnd_spec_gen utOf CU n CU_chain hbnd
  rw [CU_head] at hbspec
  simp only [Option.map_some, Option.getD_some, Nat.zero_add] at hbspec
  -- the table entry `a` lies in the certified range
  have ha_le' : a.1 ≤ 12000 := by omega
  have hchk := gapDefCheck_spec (a, b) hmem
  rw [gapDefCheck, Bool.or_eq_true] at hchk
  rcases hchk with hbad | hgood
  · simp only [decide_eq_true_eq] at hbad; omega
  · rw [Bool.and_eq_true] at hgood
    obtain ⟨hg1, hg2⟩ := hgood
    simp only [decide_eq_true_eq] at hg1 hg2
    -- cast the two integer facts to `ℝ`
    have hcast : ((a.1 * 10 ^ 9 - b.2 : ℕ) : ℝ) = (a.1 : ℝ) * 10 ^ 9 - (b.2 : ℝ) := by
      rw [Nat.cast_sub hg1]; push_cast; ring
    have hsq : ((a.1 : ℝ) * 10 ^ 9 - (b.2 : ℝ)) ^ 2 ≥ ((5 : ℝ) * 10 ^ 8) ^ 2 * (a.1 : ℝ) := by
      have h2 : ((4 * (a.1 * 10 ^ 9 - b.2) ^ 2 : ℕ) : ℝ)
          = 4 * (((a.1 * 10 ^ 9 - b.2 : ℕ) : ℝ)) ^ 2 := by push_cast; ring
      have h1 : ((10 ^ 18 * a.1 : ℕ) : ℝ) ≤ 4 * (((a.1 * 10 ^ 9 - b.2 : ℕ) : ℝ)) ^ 2 :=
        le_trans (by exact_mod_cast hg2) (le_of_eq h2)
      have h3 : ((10 ^ 18 * a.1 : ℕ) : ℝ) = 10 ^ 18 * (a.1 : ℝ) := by push_cast; ring
      rw [h3, hcast] at h1
      nlinarith [h1]
    have hz0 : 0 ≤ (a.1 : ℝ) * 10 ^ 9 - (b.2 : ℝ) := by
      have : ((b.2 : ℕ) : ℝ) ≤ ((a.1 * 10 ^ 9 : ℕ) : ℝ) := by exact_mod_cast hg1
      push_cast at this; linarith
    have hsqrt : (5 : ℝ) * 10 ^ 8 * Real.sqrt (a.1 : ℝ)
        ≤ (a.1 : ℝ) * 10 ^ 9 - (b.2 : ℝ) := by
      have hsqrta : (Real.sqrt (a.1 : ℝ)) ^ 2 = (a.1 : ℝ) := Real.sq_sqrt (by positivity)
      have hw2 : ((5 : ℝ) * 10 ^ 8 * Real.sqrt (a.1 : ℝ)) ^ 2
          ≤ ((a.1 : ℝ) * 10 ^ 9 - (b.2 : ℝ)) ^ 2 := by
        rw [mul_pow, hsqrta]; linarith [hsq]
      have hw0 : (0 : ℝ) ≤ (5 : ℝ) * 10 ^ 8 * Real.sqrt (a.1 : ℝ) := by positivity
      by_contra hcon
      push_neg at hcon
      nlinarith [hw2, hw0, hz0, hcon]
    -- θ n ≤ b.2/10^9 ≤ a.1 - (1/2)√a.1
    have hthetan : (10 : ℝ) ^ 9 * Chebyshev.theta (n : ℝ) ≤ (b.2 : ℝ) := by
      rw [hbspec]
      have := theta_le_psumU n (by omega)
      linarith
    have hstep : Chebyshev.theta (n : ℝ) ≤ (a.1 : ℝ) - (1 / 2) * Real.sqrt (a.1 : ℝ) := by
      have h10 : (0 : ℝ) < 10 ^ 9 := by norm_num
      have h2 : (b.2 : ℝ) ≤ (a.1 : ℝ) * 10 ^ 9 - (5 : ℝ) * 10 ^ 8 * Real.sqrt (a.1 : ℝ) := by
        linarith [hsqrt]
      have h5 : (10 : ℝ) ^ 9 * Chebyshev.theta (n : ℝ)
          ≤ (a.1 : ℝ) * 10 ^ 9 - (5 : ℝ) * 10 ^ 8 * Real.sqrt (a.1 : ℝ) := by
        linarith [hthetan, h2]
      have h6 : Chebyshev.theta (n : ℝ)
          ≤ ((a.1 : ℝ) * 10 ^ 9 - (5 : ℝ) * 10 ^ 8 * Real.sqrt (a.1 : ℝ)) / 10 ^ 9 := by
        rw [le_div_iff₀ h10]; linarith [h5]
      have h4 : ((a.1 : ℝ) * 10 ^ 9 - (5 : ℝ) * 10 ^ 8 * Real.sqrt (a.1 : ℝ)) / 10 ^ 9
          = (a.1 : ℝ) - (1 / 2) * Real.sqrt (a.1 : ℝ) := by ring
      rw [h4] at h6
      exact h6
    -- monotonicity in the argument
    have hmono : (a.1 : ℝ) - (1 / 2) * Real.sqrt (a.1 : ℝ) ≤ (n : ℝ) - (1 / 2) * Real.sqrt (n : ℝ) := by
      have ha0 : (0 : ℝ) ≤ (a.1 : ℝ) := by positivity
      have hn0 : (0 : ℝ) ≤ (n : ℝ) := by positivity
      have han : (a.1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast ha_le
      have h1' : (Real.sqrt (n:ℝ) - Real.sqrt (a.1:ℝ)) * (Real.sqrt (n:ℝ) + Real.sqrt (a.1:ℝ))
          = (n:ℝ) - (a.1:ℝ) := by
        have hx := Real.sq_sqrt hn0
        have hy := Real.sq_sqrt ha0
        nlinarith
      have h2' : (1/2 : ℝ) ≤ Real.sqrt (n:ℝ) + Real.sqrt (a.1:ℝ) := by
        have h18 : (18 : ℝ) ≤ Real.sqrt (n : ℝ) := by
          rw [Real.le_sqrt (by norm_num) hn0]
          have hn36 : (360 : ℝ) ≤ (n : ℝ) := by exact_mod_cast h1
          linarith
        linarith [Real.sqrt_nonneg (a.1:ℝ)]
      have h3' : 0 ≤ Real.sqrt (n:ℝ) - Real.sqrt (a.1:ℝ) := by
        have := Real.sqrt_le_sqrt han; linarith
      have hpos : 0 < Real.sqrt (n:ℝ) + Real.sqrt (a.1:ℝ) := by linarith [h2']
      have hnn : 0 ≤ (n:ℝ) - (a.1:ℝ) := by linarith
      have heq : Real.sqrt (n:ℝ) - Real.sqrt (a.1:ℝ)
          = ((n:ℝ) - (a.1:ℝ)) / (Real.sqrt (n:ℝ) + Real.sqrt (a.1:ℝ)) := by
        rw [eq_div_iff hpos.ne']
        linarith [h1']
      have hkey : Real.sqrt (n:ℝ) - Real.sqrt (a.1:ℝ) ≤ 2 * ((n:ℝ) - (a.1:ℝ)) := by
        rw [heq, div_le_iff₀ hpos]
        nlinarith [hnn, h2']
      linarith [hkey, h3']
    linarith [hstep, hmono]

/-- **Certified deficit bound.**  `θ t ≤ t − (1/2)√t` for `t ∈ [360, 12000]`.
This is a finite verification against the Chebyshev upper table `CU`. -/
theorem theta_deficit_half (t : ℝ) (h1 : 360 ≤ t) (h2 : t ≤ 12000) :
    Chebyshev.theta t ≤ t - (1 / 2) * Real.sqrt t := by
  have ht0 : (0 : ℝ) ≤ t := by linarith
  have hn1 : 360 ≤ ⌊t⌋₊ := Nat.le_floor h1
  have hn2 : ⌊t⌋₊ ≤ 12000 := by
    have h : ((⌊t⌋₊ : ℕ) : ℝ) ≤ ((12000 : ℕ) : ℝ) := by
      have : ((⌊t⌋₊ : ℕ) : ℝ) ≤ t := Nat.floor_le ht0
      push_cast
      linarith
    exact_mod_cast h
  have htheta : Chebyshev.theta t = Chebyshev.theta ((⌊t⌋₊ : ℕ) : ℝ) := by
    simp only [Chebyshev.theta_eq_sum_primesLE, Nat.floor_natCast]
  have hint := int_deficit_half ⌊t⌋₊ hn1 hn2
  have hfl : ((⌊t⌋₊ : ℕ) : ℝ) ≤ t := Nat.floor_le ht0
  have hmono : ((⌊t⌋₊ : ℕ) : ℝ) - (1 / 2) * Real.sqrt ((⌊t⌋₊ : ℕ) : ℝ)
      ≤ t - (1 / 2) * Real.sqrt t := by
    have ha1 : (1 : ℝ) ≤ ((⌊t⌋₊ : ℕ) : ℝ) := by
      have : (1 : ℝ) ≤ (360 : ℝ) := by norm_num
      have h : (360 : ℝ) ≤ ((⌊t⌋₊ : ℕ) : ℝ) := by exact_mod_cast hn1
      linarith
    have hs : Real.sqrt ((⌊t⌋₊ : ℕ) : ℝ) ≤ Real.sqrt t := Real.sqrt_le_sqrt hfl
    have h1' : (Real.sqrt t - Real.sqrt ((⌊t⌋₊ : ℕ) : ℝ))
        * (Real.sqrt t + Real.sqrt ((⌊t⌋₊ : ℕ) : ℝ)) = t - ((⌊t⌋₊ : ℕ) : ℝ) := by
      have hx := Real.sq_sqrt ht0
      have hy := Real.sq_sqrt (by linarith : (0:ℝ) ≤ ((⌊t⌋₊ : ℕ) : ℝ))
      nlinarith
    have h2' : (2 : ℝ) ≤ Real.sqrt t + Real.sqrt ((⌊t⌋₊ : ℕ) : ℝ) := by
      have a := Real.one_le_sqrt.mpr ha1
      have b := Real.one_le_sqrt.mpr (by linarith : (1:ℝ) ≤ t)
      linarith
    have h3' : 0 ≤ Real.sqrt t - Real.sqrt ((⌊t⌋₊ : ℕ) : ℝ) := by linarith
    nlinarith [h1', h2', h3', hfl]
  rw [htheta]
  linarith [hint, hmono]

/-! ## Part 2: the numeric lemmas of the final estimate -/

/-- First branch of `δ(L)`: `1/√L − 0.936/√(L + 0.094048) ≤ 0.0725/√L` on `[11.5, ∞)`. -/
theorem delta_branch_a_bound (L : ℝ) (h1 : (115 / 10 : ℝ) ≤ L) :
    1 / Real.sqrt L - (9360 / 10000) / Real.sqrt (L + 94048 / 1000000)
      ≤ 0.0725 / Real.sqrt L := by
  have hL : 0 < L := by linarith
  have hsL : 0 < Real.sqrt L := Real.sqrt_pos.mpr hL
  have hkey : (9360 / 10000 : ℝ) * Real.sqrt (L / (L + 94048 / 1000000)) ≥ (9275 / 10000) := by
    have hx : (115 / 10 : ℝ) / ((115 / 10) + 94048 / 1000000) ≤ L / (L + 94048 / 1000000) := by
      rw [div_le_div_iff₀ (by norm_num) (by linarith)]
      nlinarith [h1]
    have hs := Real.sqrt_le_sqrt hx
    have hbase : (9275 / 10000 : ℝ) ≤ (9360 / 10000) * Real.sqrt ((115 / 10 : ℝ) / ((115 / 10) + 94048 / 1000000)) := by
      rw [show (115 / 10 : ℝ) / ((115 / 10) + 94048 / 1000000) = (11500000 : ℝ) / 11594048 by norm_num]
      have hsq : ((9275 / 10000 : ℝ) / (9360 / 10000)) ^ 2 ≤ (11500000 : ℝ) / 11594048 := by norm_num
      have hsqr : (9275 / 10000 : ℝ) / (9360 / 10000) ≤ Real.sqrt ((11500000 : ℝ) / 11594048) := by
        rw [Real.le_sqrt (by norm_num) (by norm_num)]
        exact hsq
      nlinarith [hsqr]
    calc (9275 / 10000 : ℝ) ≤ (9360 / 10000) * Real.sqrt ((115 / 10 : ℝ) / ((115 / 10) + 94048 / 1000000)) := hbase
      _ ≤ (9360 / 10000) * Real.sqrt (L / (L + 94048 / 1000000)) :=
          mul_le_mul_of_nonneg_left hs (by norm_num)
  rw [le_div_iff₀ hsL]
  have hsplit : (1 / Real.sqrt L - (9360 / 10000) / Real.sqrt (L + 94048 / 1000000)) * Real.sqrt L
      = 1 - (9360 / 10000) * Real.sqrt (L / (L + 94048 / 1000000)) := by
    rw [sub_mul, one_div_mul_cancel (ne_of_gt hsL), div_mul_eq_mul_div, mul_div_assoc,
      ← Real.sqrt_div (le_of_lt hL) (L + 94048 / 1000000)]
  rw [hsplit]
  linarith [hkey]

/-- Second branch of `δ(L)`: `1.045/√(L − 0.105361) − 1/√(L + 0.006329) ≤ 0.0725/√L`. -/
theorem delta_branch_b_bound (L : ℝ) (h1 : (115 / 10 : ℝ) ≤ L) :
    (10450 / 10000) / Real.sqrt (L - 105361 / 1000000) - 1 / Real.sqrt (L + 6329 / 1000000)
      ≤ 0.0725 / Real.sqrt L := by
  have hL : 0 < L := by linarith
  have hsL : 0 < Real.sqrt L := Real.sqrt_pos.mpr hL
  have hc1 : 0 < L - 105361 / 1000000 := by linarith
  have hc2 : 0 < L + 6329 / 1000000 := by linarith
  have hkey : (10450 / 10000 : ℝ) * Real.sqrt (L / (L - 105361 / 1000000))
      - Real.sqrt (L / (L + 6329 / 1000000)) ≤ 0.0725 := by
    have hx1 : L / (L - 105361 / 1000000) ≤ (115 / 10 : ℝ) / ((115 / 10) - 105361 / 1000000) := by
      rw [div_le_div_iff₀ hc1 (by norm_num)]
      nlinarith [h1]
    have hx2 : (115 / 10 : ℝ) / ((115 / 10) + 6329 / 1000000) ≤ L / (L + 6329 / 1000000) := by
      rw [div_le_div_iff₀ (by norm_num) hc2]
      nlinarith [h1]
    have hs1 := Real.sqrt_le_sqrt hx1
    have hs2 := Real.sqrt_le_sqrt hx2
    have hb1 : (10450 / 10000 : ℝ) * Real.sqrt (L / (L - 105361 / 1000000))
        ≤ (10450 / 10000) * Real.sqrt ((115 / 10 : ℝ) / ((115 / 10) - 105361 / 1000000)) :=
      mul_le_mul_of_nonneg_left hs1 (by norm_num)
    have hnum : (10450 / 10000 : ℝ) * Real.sqrt ((115 / 10 : ℝ) / ((115 / 10) - 105361 / 1000000))
        - Real.sqrt ((115 / 10 : ℝ) / ((115 / 10) + 6329 / 1000000)) ≤ 0.0725 := by
      rw [show (115 / 10 : ℝ) / ((115 / 10) - 105361 / 1000000) = (11500000 : ℝ) / 11394639 by norm_num,
        show (115 / 10 : ℝ) / ((115 / 10) + 6329 / 1000000) = (11500000 : ℝ) / 11506329 by norm_num]
      have h1' : (10450 / 10000 : ℝ) * Real.sqrt ((11500000 : ℝ) / 11394639) ≤ 1.0499 := by
        have h2' : Real.sqrt ((11500000 : ℝ) / 11394639) ≤ 1.00462 := by
          rw [Real.sqrt_le_iff]
          exact ⟨by norm_num, by norm_num⟩
        nlinarith [h2']
      have h3' : (0.999724 : ℝ) ≤ Real.sqrt ((11500000 : ℝ) / 11506329) := by
        rw [Real.le_sqrt (by norm_num) (by norm_num)]
        norm_num
      linarith
    linarith
  rw [le_div_iff₀ hsL]
  have hA : ((10450 / 10000 : ℝ) / Real.sqrt (L - 105361 / 1000000)) * Real.sqrt L
      = (10450 / 10000) * Real.sqrt (L / (L - 105361 / 1000000)) := by
    rw [div_mul_eq_mul_div, mul_div_assoc, ← Real.sqrt_div (le_of_lt hL) (L - 105361 / 1000000)]
  have hB : (1 / Real.sqrt (L + 6329 / 1000000)) * Real.sqrt L
      = Real.sqrt (L / (L + 6329 / 1000000)) := by
    rw [one_div_mul_eq_div, ← Real.sqrt_div (le_of_lt hL) (L + 6329 / 1000000)]
  rw [sub_mul, hA, hB]
  exact hkey

/-- **The certified bound `δ(L)` for the boundary loss**: on `[11.5, 19]`,
`max(1/√L − 0.936/√(L + 0.094048), 1.045/√(L − 0.105361) − 1/√(L + 0.006329))² ≤ 0.00528/L`. -/
theorem delta_sq_bound (L : ℝ) (h1 : (115 / 10 : ℝ) ≤ L) (h2 : L ≤ 19) :
    (max (1 / Real.sqrt L - (9360 / 10000) / Real.sqrt (L + 94048 / 1000000))
         ((10450 / 10000) / Real.sqrt (L - 105361 / 1000000)
            - 1 / Real.sqrt (L + 6329 / 1000000))) ^ 2
      ≤ (528 / 100000) / L := by
  have hL : 0 < L := by linarith
  have hsL : 0 < Real.sqrt L := Real.sqrt_pos.mpr hL
  have ha := delta_branch_a_bound L h1
  have hb := delta_branch_b_bound L h1
  have hmax : max (1 / Real.sqrt L - (9360 / 10000) / Real.sqrt (L + 94048 / 1000000))
      ((10450 / 10000) / Real.sqrt (L - 105361 / 1000000) - 1 / Real.sqrt (L + 6329 / 1000000))
      ≤ 0.0725 / Real.sqrt L := max_le ha hb
  have hmaxpos : 0 < max (1 / Real.sqrt L - (9360 / 10000) / Real.sqrt (L + 94048 / 1000000))
      ((10450 / 10000) / Real.sqrt (L - 105361 / 1000000) - 1 / Real.sqrt (L + 6329 / 1000000)) := by
    have h1' : (0:ℝ) < 1 / Real.sqrt L - (9360 / 10000) / Real.sqrt (L + 94048 / 1000000) := by
      have hc : (0:ℝ) < L + 94048 / 1000000 := by linarith
      have hsq : Real.sqrt L ≤ Real.sqrt (L + 94048 / 1000000) := Real.sqrt_le_sqrt (by linarith)
      have h1'' : (9360 / 10000) / Real.sqrt (L + 94048 / 1000000) ≤ (9360 / 10000) / Real.sqrt L :=
        div_le_div_of_nonneg_left (by norm_num) hsL hsq
      have h2'' : (1:ℝ) / Real.sqrt L - (9360 / 10000) / Real.sqrt L = (64 / 1000) / Real.sqrt L := by
        rw [← sub_div]; norm_num
      have h3'' : (0:ℝ) < (64 / 1000) / Real.sqrt L := by positivity
      linarith [h1'', h2'', h3'']
    exact lt_of_lt_of_le h1' (le_max_left _ _)
  have hsq : (max (1 / Real.sqrt L - (9360 / 10000) / Real.sqrt (L + 94048 / 1000000))
      ((10450 / 10000) / Real.sqrt (L - 105361 / 1000000) - 1 / Real.sqrt (L + 6329 / 1000000))) ^ 2
      ≤ (0.0725 / Real.sqrt L) ^ 2 :=
    pow_le_pow_left₀ (le_of_lt hmaxpos) hmax 2
  have hsq2 : (0.0725 / Real.sqrt L) ^ 2 = (0.00525625 : ℝ) / L := by
    rw [div_pow, Real.sq_sqrt (le_of_lt hL)]
    norm_num
  rw [hsq2] at hsq
  have hfin : (0.00525625 : ℝ) ≤ 0.00528 := by norm_num
  calc (max (1 / Real.sqrt L - (9360 / 10000) / Real.sqrt (L + 94048 / 1000000))
      ((10450 / 10000) / Real.sqrt (L - 105361 / 1000000) - 1 / Real.sqrt (L + 6329 / 1000000))) ^ 2
      ≤ (0.00525625 : ℝ) / L := hsq
    _ ≤ ((528 / 100000 : ℝ)) / L := by
        exact div_le_div_of_nonneg_right (by norm_num) (le_of_lt hL)

/-- **Exponential decay bound** used for the mass: for `L ≥ 11.5`,
`(19612/10000)·exp(−L/4) ≤ (4438/10000)/(L − 15/2)`. -/
theorem exp_quarter_bound (L : ℝ) (h : (115 / 10 : ℝ) ≤ L) :
    (19612 / 10000) * Real.exp (-(L/4)) ≤ (4438 / 10000)/(L - 15/2) := by
  have hL : 0 < L - 15/2 := by linarith
  have hexp2 : (17.699 : ℝ) ≤ Real.exp (2.875:ℝ) := by
    have h' := Real.sum_le_exp_of_nonneg (x := (2.875:ℝ)) (by norm_num) 10
    have hsum : (17.699 : ℝ) ≤ (∑ i ∈ Finset.range 10, (2.875:ℝ)^i / (i.factorial : ℝ)) := by norm_num
    linarith
  have hsplit : Real.exp (-(L/4)) = Real.exp (-(2.875:ℝ)) * Real.exp (-((L - 115/10)/4)) := by
    rw [← Real.exp_add]; congr 1; ring
  have h1 : Real.exp (-(2.875:ℝ)) ≤ (1:ℝ)/17.699 := by
    rw [Real.exp_neg, one_div]
    rw [inv_le_inv₀ (Real.exp_pos _) (by norm_num)]
    exact hexp2
  have h2 : Real.exp (-((L - 115/10)/4)) ≤ 1/(1 + (L - 115/10)/4) := by
    have h3 : 1 + (L - 115/10)/4 ≤ Real.exp ((L - 115/10)/4) := by
      have := Real.add_one_le_exp ((L - 115/10)/4); linarith
    rw [Real.exp_neg, one_div]
    rw [inv_le_inv₀ (Real.exp_pos _) (by linarith)]
    exact h3
  have hsimp : 1/(1 + (L - 115/10)/4) = 4/(L - 15/2) := by
    rw [show (1:ℝ) + (L - 115/10)/4 = (L - 15/2)/4 by ring, one_div_div]
  have hchain' : Real.exp (-(2.875:ℝ)) * Real.exp (-((L - 115/10)/4))
      ≤ (1/17.699) * (4/(L - 15/2)) := by
    have := mul_le_mul h1 h2 (by positivity) (by norm_num)
    rwa [hsimp] at this
  calc (19612/10000 : ℝ) * Real.exp (-(L/4))
      = (19612/10000) * (Real.exp (-(2.875:ℝ)) * Real.exp (-((L - 115/10)/4))) := by rw [hsplit]
    _ ≤ (19612/10000) * ((1/17.699) * (4/(L - 15/2))) :=
        mul_le_mul_of_nonneg_left hchain' (by norm_num)
    _ ≤ (4438/10000)/(L - 15/2) := by
        rw [le_div_iff₀ hL]
        have hkey : (19612/10000 : ℝ) * ((1/17.699) * (4/(L - 15/2))) * (L - 15/2)
            = 19612/10000 * (4/17.699) := by
          field_simp
          exact div_self (by linarith : (L * 2 - 15 : ℝ) ≠ 0)
        rw [hkey]
        norm_num

/-- **`ν(L)` is a valid lower bound for `μ(s,L)·(1 − 4/s)`**, where `μ(s,L)` is the explicit
lower bound for `Nf − (21/10)√Nf − Pf + (1/2)√Pf` divided by `s = √ξ`, and
`L = log ξ = 2 log s` (so that `1/√s = exp(−L/4)`). -/
theorem nu_le_mu (s L : ℝ) (hs : 316 ≤ s) (hL : (115 / 10 : ℝ) ≤ L)
    (hexp : Real.exp (L / 2) = s) :
    (25755 / 100000 : ℝ) - (490129 / 1000000) / L - (4438 / 10000) / (L - 15 / 2)
      ≤ (0.26421 - 0.490129 / L - 1.9612 / Real.sqrt s + 0.4327738 / (Real.sqrt s * L)
          - 1 / s - 0.5 / (s * Real.sqrt (1.15 * s))) * (1 - 4 / s) := by
  have hs0 : 0 < s := by linarith
  have hs4 : 0 ≤ 1 - 4 / s := by
    rw [sub_nonneg, div_le_one hs0]; linarith
  have hsqrt : Real.sqrt s = Real.exp (L/4) := by
    rw [← hexp, ← Real.exp_half]
    congr 1; ring
  have hsqrt' : 1 / Real.sqrt s = Real.exp (-(L/4)) := by
    rw [hsqrt, one_div, ← Real.exp_neg]
  have hF1 : 1.9612 / Real.sqrt s ≤ (4438/10000)/(L - 15/2) := by
    have h := exp_quarter_bound L hL
    have he : 1.9612 / Real.sqrt s = 1.9612 * Real.exp (-(L/4)) := by
      rw [hsqrt, div_eq_mul_inv, ← Real.exp_neg]
    have hcon : (1.9612 : ℝ) = (19612:ℝ)/10000 := by norm_num
    rw [he, hcon]
    linarith
  have hF2 : 1/s + 0.5/(s * Real.sqrt (1.15*s)) + 4*(0.26421:ℝ)/s ≤ 0.00666 := by
    have h1 : 1/s ≤ 1/316 := one_div_le_one_div_of_le (by norm_num) hs
    have h2 : Real.sqrt (1.15*316) ≤ Real.sqrt (1.15*s) := Real.sqrt_le_sqrt (by linarith)
    have h2pos : 0 < Real.sqrt (1.15*316) := Real.sqrt_pos.mpr (by norm_num)
    have h3 : 0.5/(s * Real.sqrt (1.15*s)) ≤ 0.5/(316 * Real.sqrt (1.15*316)) := by
      apply div_le_div_of_nonneg_left (by norm_num)
      · positivity
      · nlinarith
    have h4 : (0.5/(316 * Real.sqrt (1.15*316)) : ℝ) ≤ 0.0001 := by
      have h19 : (19:ℝ) ≤ Real.sqrt (1.15*316) := by
        rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
      rw [div_le_iff₀ (by positivity : (0:ℝ) < 316 * Real.sqrt (1.15*316))]
      nlinarith
    have h5 : 4*(0.26421:ℝ)/s ≤ 4*0.26421/316 := by
      apply div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs
    have h6 : (1/316 + 0.0001 + 4*0.26421/316 : ℝ) ≤ 0.00666 := by norm_num
    linarith
  have hX : 0.26421 - 0.490129/L - 1.9612/Real.sqrt s - 1/s - 0.5/(s*Real.sqrt (1.15*s))
      ≤ (0.26421:ℝ) := by
    have h1 : 0 ≤ 0.490129/L := by positivity
    have h2 : 0 ≤ 1.9612/Real.sqrt s := by positivity
    have h3 : 0 ≤ 1/s := by positivity
    have h4 : 0 ≤ 0.5/(s*Real.sqrt (1.15*s)) := by positivity
    linarith
  have hstep : (25755/100000 : ℝ) - (490129/1000000)/L - (4438/10000)/(L-15/2)
      ≤ (0.26421 - 0.490129/L - 1.9612/Real.sqrt s - 1/s - 0.5/(s*Real.sqrt (1.15*s)))
        - 4*(0.26421:ℝ)/s := by
    have hc : (25755/100000 : ℝ) = 0.26421 - 0.00666 := by norm_num
    rw [hc]; linarith [hF1, hF2]
  have hstep2 : (0.26421 - 0.490129/L - 1.9612/Real.sqrt s - 1/s - 0.5/(s*Real.sqrt (1.15*s)))
        - 4*(0.26421:ℝ)/s
      ≤ (0.26421 - 0.490129/L - 1.9612/Real.sqrt s - 1/s - 0.5/(s*Real.sqrt (1.15*s)))
        * (1 - 4/s) := by
    have heq : (0.26421 - 0.490129/L - 1.9612/Real.sqrt s - 1/s - 0.5/(s*Real.sqrt (1.15*s)))
          * (1 - 4/s)
        = (0.26421 - 0.490129/L - 1.9612/Real.sqrt s - 1/s - 0.5/(s*Real.sqrt (1.15*s)))
          - 4*(0.26421 - 0.490129/L - 1.9612/Real.sqrt s - 1/s
              - 0.5/(s*Real.sqrt (1.15*s)))/s := by ring
    rw [heq]
    have h4 : 4*(0.26421 - 0.490129/L - 1.9612/Real.sqrt s - 1/s - 0.5/(s*Real.sqrt (1.15*s)))/s
        ≤ 4*(0.26421:ℝ)/s := by
      apply div_le_div_of_nonneg_right _ (le_of_lt hs0)
      linarith [hX]
    linarith
  have hstep3 : (0.26421 - 0.490129/L - 1.9612/Real.sqrt s - 1/s - 0.5/(s*Real.sqrt (1.15*s)))
        * (1 - 4/s)
      ≤ (0.26421 - 0.490129/L - 1.9612/Real.sqrt s + 0.4327738/(Real.sqrt s * L)
          - 1/s - 0.5/(s*Real.sqrt (1.15*s))) * (1 - 4/s) := by
    apply mul_le_mul_of_nonneg_right _ hs4
    have : (0:ℝ) ≤ 0.4327738/(Real.sqrt s * L) := by positivity
    linarith
  linarith [hstep, hstep2, hstep3]


/-- Telescoping sum `∑_{n ∈ Icc (m-2) Pf} 1/(n(n-1)) = 1/(m-3) - 1/Pf`. -/
lemma sum_Icc_telescope (m Pf : ℕ) (hm : 4 ≤ m) (hmP : m - 2 ≤ Pf) :
    ∑ n ∈ Finset.Icc (m-2) Pf, (1/((n:ℝ)*((n:ℝ)-1))) = 1/((m:ℝ)-3) - 1/(Pf:ℝ) := by
  have hab : m - 2 ≤ Pf := hmP
  rw [Finset.Icc_eq_cons_Ico hab, Finset.sum_cons]
  have hsub : ∀ i ∈ Finset.Ico (m-2) Pf, (1/((i:ℝ)*((i:ℝ)-1)))
      = - ((fun t : ℕ => 1/((t:ℝ) - 1)) (i+1) - (fun t : ℕ => 1/((t:ℝ) - 1)) i) := by
    intro i hi
    have hi2 : (2:ℕ) ≤ i := by have := (Finset.mem_Ico.mp hi).1; omega
    have hi1 : (1:ℝ) < (i:ℝ) := by exact_mod_cast (by omega : 1 < i)
    have hne : (i:ℝ) ≠ 0 := by linarith
    have hne2 : (i:ℝ) - 1 ≠ 0 := by linarith
    rw [show (1:ℝ)/((i:ℝ)*((i:ℝ)-1)) = -(1/(i:ℝ) - 1/((i:ℝ)-1)) by
      rw [div_sub_div _ _ hne hne2]; ring]
    push_cast
    ring
  rw [Finset.sum_congr rfl hsub, Finset.sum_neg_distrib,
    Finset.sum_Ico_sub (fun t : ℕ => 1/((t:ℝ) - 1)) hab]
  rw [show (((m-2 : ℕ)) : ℝ) = (m:ℝ) - 2 by
    rw [Nat.cast_sub (show 2 ≤ m by omega)]; norm_num]
  have hm3 : (3:ℝ) < (m:ℝ) := by exact_mod_cast (by omega : 3 < m)
  have hPf1 : (1:ℝ) < (Pf:ℝ) := by
    have : (1:ℕ) < Pf := by omega
    exact_mod_cast this
  have hPf0 : (Pf:ℝ) ≠ 0 := by linarith
  have hPf1' : (Pf:ℝ) - 1 ≠ 0 := by linarith
  field_simp
  ring

/-- **The final explicit arithmetic step.**  For `L ∈ [11.5, 19]`, the certified lower bound for
`c − h(Pf+1)` (the constant `(0.07168 L + 0.09034)/((L+0.094048)(L/2+0.13976))`) dominates the
certified upper bound for the boundary loss `(1/3)(L/2 + 0.139762)(0.00528/L)`, via the lower
bound `0.2589 − 0.490129/L − 0.4438/(L − 7.5)` for the mass term.  Proved by writing the
difference as a Bernstein polynomial on `[11.5,19]` with positive coefficients. -/
lemma final_step (L : ℝ) (h1 : (115 / 10 : ℝ) ≤ L) (h2 : L ≤ 19) :
    (1 / 3) * (L / 2 + 139762 / 1000000) * ((528 / 100000) / L)
      ≤ ((7168 / 100000 * L + 9034 / 100000) / ((L + 94048 / 1000000) * (L / 2 + 13976 / 100000)))
        * (2589 / 10000 - (490129 / 1000000) / L - (4438 / 10000) / (L - 15 / 2)) := by
  have hL : (0:ℝ) < L := by linarith
  have hL2 : (0:ℝ) < L - 15/2 := by linarith
  have ha : (0:ℝ) < L + 94048/1000000 := by linarith
  have hb : (0:ℝ) < L/2 + 13976/100000 := by linarith
  set u : ℝ := (L - 115/10)/(75/10) with hudef
  have hu0 : 0 ≤ u := by rw [hudef]; apply div_nonneg <;> linarith
  have hu1 : 0 ≤ 1 - u := by
    rw [hudef, sub_nonneg, div_le_one (by norm_num)]
    linarith
  -- Bernstein coefficients (exact)
  have hD : (0:ℝ) ≤ (7168/100000*L + 9034/100000) *
        ((2589/10000)*(L*(L - 15/2)) - (490129/1000000)*(L - 15/2) - (4438/10000)*L)
      - (1/3)*(L/2 + 139762/1000000)*(528/100000)*(L + 94048/1000000)*(L/2 + 13976/100000)*(L - 15/2) := by
    have hident : (7168/100000*L + 9034/100000) *
        ((2589/10000)*(L*(L - 15/2)) - (490129/1000000)*(L - 15/2) - (4438/10000)*L)
      - (1/3)*(L/2 + 139762/1000000)*(528/100000)*(L + 94048/1000000)*(L/2 + 13976/100000)*(L - 15/2)
      = (122091965485705543/76293945312500000)*(1-u)^4
        + 4*(94637862886417206043/19531250000000000000)*u*(1-u)^3
        + 6*(98639313789459865289/9765625000000000000)*u^2*(1-u)^2
        + 4*(341918771311672411363/19531250000000000000)*u^3*(1-u)
        + (126027016511281116787/4882812500000000000)*u^4 := by
      rw [hudef]
      field_simp
      ring
    rw [hident]
    have h0 : (0:ℝ) ≤ (122091965485705543/76293945312500000)*(1-u)^4 := by positivity
    have h3 : (0:ℝ) ≤ 4*(94637862886417206043/19531250000000000000)*u*(1-u)^3 := by positivity
    have h4 : (0:ℝ) ≤ 6*(98639313789459865289/9765625000000000000)*u^2*(1-u)^2 := by positivity
    have h5 : (0:ℝ) ≤ 4*(341918771311672411363/19531250000000000000)*u^3*(1-u) := by positivity
    have h6 : (0:ℝ) ≤ (126027016511281116787/4882812500000000000)*u^4 := by positivity
    linarith
  have hA : (1 / 3) * (L / 2 + 139762 / 1000000) * ((528 / 100000) / L)
      = ((1 / 3) * (L / 2 + 139762 / 1000000) * (528 / 100000)) / L := by ring
  rw [hA, div_le_iff₀ hL]
  have hrew : ((7168/100000*L + 9034/100000) / ((L + 94048/1000000) * (L/2 + 13976/100000)))
        * (2589/10000 - (490129/1000000)/L - (4438/10000)/(L - 15/2)) * L
      = ((7168/100000*L + 9034/100000) *
          ((2589/10000)*(L*(L - 15/2)) - (490129/1000000)*(L - 15/2) - (4438/10000)*L))
        / ((L + 94048/1000000) * (L/2 + 13976/100000) * (L - 15/2)) := by
    have hne : L * 2 - 15 ≠ 0 := by linarith
    have hne2 : L * 2 ≠ 0 := by linarith
    field_simp
  rw [hrew, le_div_iff₀ (by positivity : (0:ℝ) < (L + 94048/1000000) * (L/2 + 13976/100000) * (L - 15/2))]
  linarith [hD]

/-- `u * log u ≤ v * log v` for `1 ≤ u ≤ v`. -/
lemma mul_log_le {u v : ℝ} (hu : 1 ≤ u) (huv : u ≤ v) :
    u * Real.log u ≤ v * Real.log v := by
  have hu0 : 0 < u := by linarith
  have hv0 : 0 < v := by linarith
  have hlu : 0 ≤ Real.log u := Real.log_nonneg hu
  have hluv : Real.log u ≤ Real.log v := Real.log_le_log hu0 huv
  have h1 : u * Real.log u ≤ v * Real.log u := mul_le_mul_of_nonneg_right huv hlu
  have h2 : v * Real.log u ≤ v * Real.log v := mul_le_mul_of_nonneg_left hluv (le_of_lt hv0)
  linarith

/-- `log 3 > 1`. -/
lemma log_three_gt_one : (1:ℝ) < Real.log 3 := by
  have h : Real.exp 1 < (3:ℝ) := by linarith [Real.exp_one_lt_d9]
  exact (Real.lt_log_iff_exp_lt (by norm_num)).mpr h


end

end Work.RHContract.A.regionII
