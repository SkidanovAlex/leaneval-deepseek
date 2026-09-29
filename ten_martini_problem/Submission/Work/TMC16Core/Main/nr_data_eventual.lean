import Mathlib
import Submission.Work.TMC16Core.Assembly.Consts
import Submission.Work.TMC16Core.CF.cf_data_bridge

/-!
# The eventual numerical data estimate for the non-resonant branch

This file proves `Work.TMC16Core.Main.nr_data_eventual`: for the continued-fraction
denominators `q` of a Diophantine frequency (growing at most like
`q(m+1) ≤ exp ((b₀+ε') q m)`), and for every `s ≥ 1` with `(q n)^{8/9} ≤ 2 s q(n-1)`,
the three numerical requirements of the C16 non-resonant patch hold for all
sufficiently large `n`:

* `10^6 ≤ csm · (q n)^2`;
* `log (q n) ≤ (b₀+ε') q(n-1)`;
* the bookkeeping rate
  `2 log 2 / Q + 2 log Q / Q + 200 log Q / Q
     + 2 (log (1/csm) + 100 + 20 log (q n + 2)) / (s Q) + 200 / Q ≤ δ + L/100`
  (`Q = q (n-1)`).

The first two are immediate from the growth of `q`; the last one is a limiting
statement: every summand has a denominator that grows (uniformly in `s`, using
`(q n)^{8/9} ≤ 2 s q(n-1)` for the `log (q n + 2)` term) while the right-hand side
`δ + L/100` is a fixed positive number.  The `(2/9)(b₀+ε') ≤ L/8 - δ` hypothesis is
not needed for this purely quantitative statement.
-/

namespace Work.TMC16Core.Main

/-- `(2 log 2 + 202 log u + 200 + 2 B)/u → 0` as `u → +∞`. -/
lemma nrde_tendsto_rateG1 (B : ℝ) :
    Filter.Tendsto (fun u : ℝ => (2 * Real.log 2 + 202 * Real.log u + 200 + 2 * B) / u)
      Filter.atTop (nhds 0) := by
  have hlog : Filter.Tendsto (fun u : ℝ => Real.log u / u) Filter.atTop (nhds 0) := by
    have h := (isLittleO_log_rpow_atTop (show (0:ℝ) < 1 by norm_num)).tendsto_div_nhds_zero
    simpa [Real.rpow_one] using h
  have h2 : Filter.Tendsto (fun u : ℝ => (2*Real.log 2 + 200 + 2*B)/u) Filter.atTop (nhds 0) :=
    Filter.Tendsto.div_atTop tendsto_const_nhds Filter.tendsto_id
  have h3 : Filter.Tendsto (fun u : ℝ => 202 * (Real.log u / u)) Filter.atTop (nhds 0) := by
    simpa using hlog.const_mul (202:ℝ)
  have h4 : Filter.Tendsto (fun u : ℝ => (2*Real.log 2 + 200 + 2*B)/u + 202 * (Real.log u / u))
      Filter.atTop (nhds (0+0)) := h2.add h3
  rw [add_zero] at h4
  refine h4.congr' ?_
  filter_upwards with u
  ring

/-- `80 log (v+2)/v^{8/9} → 0` as `v → +∞`. -/
lemma nrde_tendsto_rateG2 :
    Filter.Tendsto (fun v : ℝ => 80 * Real.log (v + 2) / v ^ (8 / 9 : ℝ))
      Filter.atTop (nhds 0) := by
  have hlog2 : Filter.Tendsto (fun v : ℝ => 80 * Real.log 2 / v ^ (8/9:ℝ)) Filter.atTop (nhds 0) := by
    have h := Filter.Tendsto.div_atTop (f := fun _ : ℝ => 80 * Real.log 2) tendsto_const_nhds
      (tendsto_rpow_atTop (show (0:ℝ) < 8/9 by norm_num))
    simpa using h
  have hlogv : Filter.Tendsto (fun v : ℝ => 80 * (Real.log v / v ^ (8/9:ℝ))) Filter.atTop (nhds 0) := by
    have h := (isLittleO_log_rpow_atTop (show (0:ℝ) < 8/9 by norm_num)).tendsto_div_nhds_zero
    simpa using h.const_mul (80:ℝ)
  have hg : Filter.Tendsto (fun v : ℝ => 80 * Real.log 2 / v ^ (8/9:ℝ) + 80 * (Real.log v / v ^ (8/9:ℝ)))
      Filter.atTop (nhds (0+0)) := hlog2.add hlogv
  rw [add_zero] at hg
  refine squeeze_zero' ?_ ?_ hg
  · filter_upwards [Filter.eventually_ge_atTop (1:ℝ)] with v hv
    have hvpos : (0:ℝ) < v ^ (8/9:ℝ) := Real.rpow_pos_of_pos (by linarith) _
    have hlog : 0 ≤ Real.log (v + 2) := Real.log_nonneg (by linarith)
    apply div_nonneg
    · nlinarith [hlog]
    · exact le_of_lt hvpos
  · filter_upwards [Filter.eventually_ge_atTop (2:ℝ)] with v hv
    have hvpos : (0:ℝ) < v := by linarith
    have h2v : v + 2 ≤ 2 * v := by linarith
    have hlog : Real.log (v + 2) ≤ Real.log (2 * v) := Real.log_le_log (by linarith) h2v
    have hlogm : Real.log (2 * v) = Real.log 2 + Real.log v :=
      Real.log_mul (by norm_num) (ne_of_gt hvpos)
    rw [hlogm] at hlog
    have hpowpos : (0:ℝ) < v ^ (8/9:ℝ) := Real.rpow_pos_of_pos hvpos _
    have h1 : 80 * Real.log (v + 2) / v ^ (8/9:ℝ) ≤ 80 * (Real.log 2 + Real.log v) / v ^ (8/9:ℝ) := by
      apply div_le_div_of_nonneg_right _ (le_of_lt hpowpos)
      nlinarith [hlog]
    have h2 : 80 * (Real.log 2 + Real.log v) / v ^ (8/9:ℝ)
        = 80 * Real.log 2 / v ^ (8/9:ℝ) + 80 * (Real.log v / v ^ (8/9:ℝ)) := by ring
    rw [h2] at h1
    exact h1

/-- The numerical core: under `(q n)^{8/9} ≤ 2 s Q` and the two eventual bounds,
the bookkeeping rate is at most `ε`. -/
lemma nrde_rate_data_bound {R Q s c1 ε : ℝ} (hR : 0 < R) (hQ : 0 < Q) (hs : 1 ≤ s)
    (hcon : R ^ (8 / 9 : ℝ) ≤ 2 * s * Q)
    (hG1 : (2 * Real.log 2 + 202 * Real.log Q + 200 + 2 * |c1|) / Q ≤ ε / 2)
    (hG2 : 80 * Real.log (R + 2) / R ^ (8 / 9 : ℝ) ≤ ε / 2) :
    2 * Real.log 2 / Q + 2 * Real.log Q / Q + 200 * Real.log Q / Q
      + 2 * (c1 + 20 * Real.log (R + 2)) / (s * Q) + 200 / Q ≤ ε := by
  have hsQ : 0 < s * Q := mul_pos (by linarith) hQ
  have hRp : 0 < R ^ (8 / 9 : ℝ) := Real.rpow_pos_of_pos hR _
  have hlogR2 : 0 ≤ Real.log (R + 2) := Real.log_nonneg (by linarith)
  have hinv : 1 / (s * Q) ≤ 2 / R ^ (8 / 9 : ℝ) := by
    rw [div_le_div_iff₀ hsQ hRp]
    nlinarith [hcon]
  have hQle : Q ≤ s * Q := by nlinarith [hs, hQ]
  have hA : 2 * c1 / (s * Q) ≤ 2 * |c1| / Q := by
    have h1 : 2 * c1 / (s * Q) ≤ 2 * |c1| / (s * Q) := by
      apply div_le_div_of_nonneg_right
      · nlinarith [le_abs_self c1]
      · exact le_of_lt hsQ
    have h2 : 2 * |c1| / (s * Q) ≤ 2 * |c1| / Q := by
      rw [div_le_div_iff₀ hsQ hQ]
      exact mul_le_mul_of_nonneg_left hQle (by positivity)
    linarith
  have hB : 40 * Real.log (R + 2) / (s * Q) ≤ 80 * Real.log (R + 2) / R ^ (8 / 9 : ℝ) := by
    have h1 : 40 * Real.log (R + 2) * (1 / (s * Q))
        ≤ 40 * Real.log (R + 2) * (2 / R ^ (8 / 9 : ℝ)) :=
      mul_le_mul_of_nonneg_left hinv (by linarith)
    have h2 : 40 * Real.log (R + 2) * (2 / R ^ (8 / 9 : ℝ))
        = 80 * Real.log (R + 2) / R ^ (8 / 9 : ℝ) := by ring
    have h3 : 40 * Real.log (R + 2) * (1 / (s * Q)) = 40 * Real.log (R + 2) / (s * Q) := by ring
    rw [h3, h2] at h1
    exact h1
  have hsplit : 2 * Real.log 2 / Q + 2 * Real.log Q / Q + 200 * Real.log Q / Q
        + 2 * (c1 + 20 * Real.log (R + 2)) / (s * Q) + 200 / Q
      = (2 * Real.log 2 / Q + 2 * Real.log Q / Q + 200 * Real.log Q / Q + 200 / Q)
        + (2 * c1 / (s * Q) + 40 * Real.log (R + 2) / (s * Q)) := by ring
  have hmid : (2 * Real.log 2 / Q + 2 * Real.log Q / Q + 200 * Real.log Q / Q + 200 / Q)
        + (2 * c1 / (s * Q) + 40 * Real.log (R + 2) / (s * Q))
      ≤ (2 * Real.log 2 / Q + 2 * Real.log Q / Q + 200 * Real.log Q / Q + 200 / Q)
        + (2 * |c1| / Q + 80 * Real.log (R + 2) / R ^ (8 / 9 : ℝ)) := by linarith [hA, hB]
  have hfinal : (2 * Real.log 2 / Q + 2 * Real.log Q / Q + 200 * Real.log Q / Q + 200 / Q)
        + (2 * |c1| / Q + 80 * Real.log (R + 2) / R ^ (8 / 9 : ℝ))
      = (2 * Real.log 2 + 202 * Real.log Q + 200 + 2 * |c1|) / Q
        + 80 * Real.log (R + 2) / R ^ (8 / 9 : ℝ) := by
    field_simp
    ring
  calc 2 * Real.log 2 / Q + 2 * Real.log Q / Q + 200 * Real.log Q / Q
        + 2 * (c1 + 20 * Real.log (R + 2)) / (s * Q) + 200 / Q
      = _ := hsplit
    _ ≤ _ := hmid
    _ = (2 * Real.log 2 + 202 * Real.log Q + 200 + 2 * |c1|) / Q
        + 80 * Real.log (R + 2) / R ^ (8 / 9 : ℝ) := hfinal
    _ ≤ ε / 2 + ε / 2 := by linarith [hG1, hG2]
    _ = ε := by ring

theorem nr_data_eventual {b₀ ε' L δ : ℝ} {q : ℕ → ℕ} {csm : ℝ}
    (hL : 0 < L) (hcsm : 0 < csm) (hcsm1 : csm ≤ 1) (hδ : 0 < δ)
    (hδb : (2 / 9) * (b₀ + ε') ≤ L / 8 - δ)
    (hqpos : ∀ i, 0 < q i) (hmono : StrictMono q)
    (hgr : ∀ᶠ m : ℕ in Filter.atTop, (q (m + 1) : ℝ) ≤ Real.exp ((b₀ + ε') * (q m : ℝ))) :
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → ∀ s : ℕ, 1 ≤ s →
      (q n : ℝ) ^ (8 / 9 : ℝ) ≤ 2 * (s : ℝ) * (q (n - 1) : ℝ) →
      10 ^ 6 ≤ csm * (q n : ℝ) ^ 2 ∧
      Real.log (q n : ℝ) ≤ (b₀ + ε') * (q (n - 1) : ℝ) ∧
      2 * Real.log 2 / (q (n - 1) : ℝ)
        + 2 * Real.log (q (n - 1) : ℝ) / (q (n - 1) : ℝ)
        + 200 * Real.log (q (n - 1) : ℝ) / (q (n - 1) : ℝ)
        + 2 * (Real.log (1 / csm) + 100 + 20 * Real.log ((q n : ℝ) + 2))
          / ((s : ℝ) * (q (n - 1) : ℝ))
        + 200 / (q (n - 1) : ℝ) ≤ δ + L / 100 := by
  obtain ⟨Mgr, hMgr⟩ := Filter.eventually_atTop.mp hgr
  -- `q` grows at least linearly, hence `q k → ∞`
  have hq_ge : ∀ k, k ≤ q k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        have hlt : q k < q (k + 1) := hmono (Nat.lt_succ_self k)
        omega
  have hv : Filter.Tendsto (fun n : ℕ => (q n : ℝ)) Filter.atTop Filter.atTop :=
    tendsto_natCast_atTop_atTop.comp hmono.tendsto_atTop
  have hu : Filter.Tendsto (fun n : ℕ => (q (n - 1) : ℝ)) Filter.atTop Filter.atTop :=
    hv.comp (Filter.tendsto_sub_atTop_nat 1)
  have hε2 : (0:ℝ) < (δ + L / 100) / 2 := by linarith
  have hG1ev : ∀ᶠ n in Filter.atTop,
      (2 * Real.log 2 + 202 * Real.log (q (n - 1) : ℝ) + 200
        + 2 * |Real.log (1 / csm) + 100|) / (q (n - 1) : ℝ) ≤ (δ + L / 100) / 2 :=
    hu.eventually ((nrde_tendsto_rateG1 |Real.log (1 / csm) + 100|).eventually
      (eventually_le_nhds hε2))
  have hG2ev : ∀ᶠ n in Filter.atTop,
      80 * Real.log ((q n : ℝ) + 2) / (q n : ℝ) ^ (8 / 9 : ℝ) ≤ (δ + L / 100) / 2 :=
    hv.eventually (nrde_tendsto_rateG2.eventually (eventually_le_nhds hε2))
  obtain ⟨Nc, hNc⟩ := Filter.eventually_atTop.mp (hG1ev.and hG2ev)
  refine ⟨max (Nat.ceil (10 ^ 6 / csm) + 1) (max (Mgr + 1) Nc), ?_⟩
  intro n hn s hs1 hcon
  have hn_a : Nat.ceil (10 ^ 6 / csm) + 1 ≤ n := le_trans (le_max_left _ _) hn
  have hn_b : Mgr + 1 ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hn
  have hn_c : Nc ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hn
  have hn1 : 1 ≤ n := by omega
  have hqnpos : (0:ℝ) < (q n : ℝ) := by exact_mod_cast hqpos n
  have hQpos : (0:ℝ) < (q (n - 1) : ℝ) := by exact_mod_cast hqpos (n - 1)
  refine ⟨?_, ?_, ?_⟩
  · -- `10^6 ≤ csm · (q n)^2`
    have hKn : Nat.ceil (10 ^ 6 / csm) + 1 ≤ q n := le_trans hn_a (hq_ge n)
    have hKcast : ((Nat.ceil (10 ^ 6 / csm) + 1 : ℕ) : ℝ) ≤ (q n : ℝ) := by exact_mod_cast hKn
    have hlt : (10 ^ 6 : ℝ) / csm < ((Nat.ceil (10 ^ 6 / csm) + 1 : ℕ) : ℝ) := by
      have h1 : (10 ^ 6 : ℝ) / csm ≤ (Nat.ceil (10 ^ 6 / csm) : ℝ) := Nat.le_ceil _
      have h2 : ((Nat.ceil (10 ^ 6 / csm) + 1 : ℕ) : ℝ) = (Nat.ceil (10 ^ 6 / csm) : ℝ) + 1 := by
        push_cast; ring
      rw [h2]; linarith
    have hbig : (10 ^ 6 : ℝ) / csm ≤ (q n : ℝ) := le_of_lt (lt_of_lt_of_le hlt hKcast)
    have h1 : (1:ℝ) ≤ (q n : ℝ) := by
      have : (1:ℕ) ≤ q n := by omega
      exact_mod_cast this
    have hsq : (q n : ℝ) ≤ (q n : ℝ) ^ 2 := by nlinarith [h1]
    have hstep1 : csm * ((10 ^ 6 : ℝ) / csm) ≤ csm * (q n : ℝ) :=
      mul_le_mul_of_nonneg_left hbig (le_of_lt hcsm)
    have hstep2 : csm * (q n : ℝ) ≤ csm * (q n : ℝ) ^ 2 :=
      mul_le_mul_of_nonneg_left hsq (le_of_lt hcsm)
    have heq : csm * ((10 ^ 6 : ℝ) / csm) = 10 ^ 6 := by field_simp
    linarith
  · -- `log (q n) ≤ (b₀+ε') q(n-1)`
    have hm : Mgr ≤ n - 1 := by omega
    have h1 := hMgr (n - 1) hm
    have h2 : n - 1 + 1 = n := by omega
    rw [h2] at h1
    have h3 : Real.log (q n : ℝ) ≤ Real.log (Real.exp ((b₀ + ε') * (q (n - 1) : ℝ))) :=
      Real.log_le_log hqnpos h1
    rwa [Real.log_exp] at h3
  · -- bookkeeping rate
    have hG1 := (hNc n hn_c).1
    have hG2 := (hNc n hn_c).2
    exact nrde_rate_data_bound hqnpos hQpos (by exact_mod_cast hs1) hcon hG1 hG2

end Work.TMC16Core.Main
