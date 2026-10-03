import Mathlib
import Submission.Work.Analysis.Probability.jumpCount

/-!
# A dyadic level of large oscillation carried by the `r`-variation

Given a path `x : ℕ → ℝ` whose pairwise oscillations are bounded by `t > 0`
(`∀ s s', |x s' - x s| ≤ t`) and with `t < VpathR x r` (so the `r`-variation of `x` exceeds `t`,
`r > 1`), there is a dyadic level `k` at which the number of `t / 2 ^ (k+1)`-oscillations is
strictly bigger than `((1 - 2 ^ (1-r)) / 2^r) * 2^k`.

This is the elementary layer-cake ("dyadic decomposition of the variation") step: if `d ≤ t` is a
single oscillation, then with `q = 2 ^ (-r)` and `m` the unique dyadic layer of `d`
(`t / 2 ^ (m+1) < d ≤ t / 2 ^ m`) one has `d ^ r ≤ t ^ r * q ^ m`, and `q ^ m` is the `m`-th term
of the geometric series `∑ k, q^k · 1_{t / 2 ^ (k+1) < d}`; summing over the path and comparing
with `∑ k, q^k A_k`, where `A_k` counts the oscillations exceeding the level `t / 2 ^ (k+1)`,
gives the result: if every `A_k` were bounded by `((1 - 2 ^ (1-r)) / 2^r) * 2^k`, then
`∑ d^r ≤ t^r · 2^{-r} < t^r`, contradicting `t^r < ∑ d^r`.
-/

open scoped ENNReal BigOperators Topology
open Finset Filter

namespace Work.Analysis.Probability

/-- The dyadic weight `2 ^ (-r)` attached to the level `r`. -/
noncomputable def dyw (r : ℝ) : ℝ := (2:ℝ)^(-(r:ℝ))

lemma dyw_pos (r : ℝ) : 0 < dyw r := by rw [dyw]; positivity

lemma dyw_lt_one {r : ℝ} (hr : 0 < r) : dyw r < 1 := by
  rw [dyw]; exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)

lemma two_rpow_one_sub_eq (r : ℝ) : (2:ℝ)^(1-r) = 2 * dyw r := by
  rw [dyw, sub_eq_add_neg, Real.rpow_add (show (0:ℝ) < 2 by norm_num), Real.rpow_one]

lemma dyw_mul_two_eq (r : ℝ) : dyw r * 2 = (2:ℝ)^(1-r) := by rw [two_rpow_one_sub_eq]; ring

lemma two_rpow_one_sub_lt_one {r : ℝ} (hr : 1 < r) : (2:ℝ)^(1-r) < 1 :=
  Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)

lemma two_rpow_one_sub_pos (r : ℝ) : 0 < (2:ℝ)^(1-r) := by positivity

lemma one_sub_two_rpow_pos {r : ℝ} (hr : 1 < r) : 0 < 1 - (2:ℝ)^(1-r) := by
  linarith [two_rpow_one_sub_lt_one hr]

lemma one_div_two_rpow (r : ℝ) : 1 / (2:ℝ)^r = dyw r := by
  rw [dyw, Real.rpow_neg (show (0:ℝ) ≤ 2 by norm_num), one_div]

/-- A real power of a natural power of `2` is that power of the real power. -/
lemma two_npow_rpow (r : ℝ) (m : ℕ) :
    ((2:ℝ)^(m:ℕ))^(r:ℝ) = ((2:ℝ)^(r:ℝ))^(m:ℕ) := by
  rw [← Real.rpow_natCast 2 m, ← Real.rpow_mul (show (0:ℝ) ≤ 2 by norm_num) (m:ℝ) r,
      ← Real.rpow_natCast ((2:ℝ)^r) m, ← Real.rpow_mul (show (0:ℝ) ≤ 2 by norm_num) r (m:ℝ),
      mul_comm]

/-- Extraction of a witness from a strict inequality with a supremum. -/
lemma exists_lt_iSup {ι : Sort*} {a : ℝ≥0∞} {f : ι → ℝ≥0∞} (h : a < ⨆ i, f i) : ∃ i, a < f i := by
  by_contra hc
  push Not at hc
  exact absurd (iSup_le hc) (not_le.mpr h)

/-- The dyadic layer of a positive real `d ≤ t`. -/
lemma exists_layer {t d : ℝ} (ht : 0 < t) (hdt : d ≤ t) (hd : 0 < d) :
    ∃ m : ℕ, t / 2^(m+1) < d ∧ d ≤ t / 2^m := by
  classical
  have hex : ∃ k : ℕ, ¬ (d ≤ t / 2^k) := by
    obtain ⟨n, hn⟩ := exists_nat_gt (t / d)
    refine ⟨n, ?_⟩
    rw [not_le, div_lt_iff₀ (by positivity : (0:ℝ) < 2^n)]
    calc t = d * (t / d) := by field_simp
      _ < d * n := mul_lt_mul_of_pos_left hn hd
      _ ≤ d * 2^n := mul_le_mul_of_nonneg_left
          (by exact_mod_cast (Nat.lt_pow_self (by norm_num : 1 < 2)).le) hd.le
  let k₀ := Nat.find hex
  have hk₀ : t / 2^k₀ < d := not_le.mp (Nat.find_spec hex)
  have hk₀pos : 0 < k₀ := by
    rcases Nat.eq_zero_or_pos k₀ with h | h
    · exact absurd (by rw [h, pow_zero, div_one] at hk₀; exact hk₀) (not_lt.mpr hdt)
    · exact h
  refine ⟨k₀ - 1, ?_, ?_⟩
  · rw [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hk₀pos.ne')]
    exact hk₀
  · exact not_not.mp (Nat.find_min hex (Nat.sub_one_lt hk₀pos.ne'))

/-- Layer-cake bound for a single oscillation: `d ^ r ≤ t ^ r * q ^ m` on the layer `m`. -/
lemma rpow_le_mul_weight {r t d : ℝ} (hr : 0 ≤ r) (ht : 0 ≤ t) (hd : 0 ≤ d) (m : ℕ)
    (h : d ≤ t / 2^m) : d ^ r ≤ t ^ r * (dyw r)^m := by
  calc d ^ r ≤ (t / 2^m) ^ r := Real.rpow_le_rpow hd h hr
    _ = t ^ r * (dyw r)^m := by
        rw [div_eq_mul_inv, Real.mul_rpow ht (by positivity : (0:ℝ) ≤ ((2:ℝ)^m)⁻¹),
          Real.inv_rpow (show (0:ℝ) ≤ (2:ℝ)^m by positivity), two_npow_rpow r m, ← inv_pow,
          ← Real.rpow_neg (show (0:ℝ) ≤ 2 by norm_num) r]
        rw [dyw]

/-- A sum of `q`-weighted indicator terms equals `q` times the cardinality of the filter. -/
lemma sum_ite_card (q : ℝ) (p : ℕ → Prop) [DecidablePred p] (J : ℕ) :
    ∑ j ∈ Finset.range J, (if p j then q else 0) = q * ((Finset.filter p (Finset.range J)).card : ℝ) := by
  rw [← Finset.sum_boole (R := ℝ) p (Finset.range J), Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  by_cases hp : p j <;> simp [hp]

lemma ite_zero_nonneg {q : ℝ} (hq : 0 ≤ q) (p : Prop) [Decidable p] : 0 ≤ (if p then q else 0) := by
  by_cases hp : p <;> simp [hp, hq]

/-- Pointwise layer-cake with a truncated geometric series. -/
lemma pointwise_finite {r t d : ℝ} (hr : 0 < r) (ht : 0 < t) (hd : 0 ≤ d) (hdt : d ≤ t) (K : ℕ) :
    d ^ r ≤ t ^ r * (∑ k ∈ Finset.range K, (if t / 2^(k+1) < d then (dyw r)^k else 0)
      + (dyw r)^K) := by
  have htr : 0 ≤ t ^ r := Real.rpow_nonneg ht.le r
  have hsum : 0 ≤ ∑ k ∈ Finset.range K, (if t / 2^(k+1) < d then (dyw r)^k else 0) :=
    Finset.sum_nonneg (fun k _ => ite_zero_nonneg (pow_nonneg (dyw_pos r).le k) _)
  rcases eq_or_lt_of_le hd with h0 | hpos
  · have hdz : d ^ r = 0 := by rw [← h0, Real.zero_rpow hr.ne']
    rw [hdz]
    exact mul_nonneg htr (add_nonneg hsum (pow_nonneg (dyw_pos r).le K))
  · obtain ⟨m, hm1, hm2⟩ := exists_layer ht hdt hpos
    have hkey : d ^ r ≤ t ^ r * (dyw r)^m := rpow_le_mul_weight hr.le ht.le hd m hm2
    rcases lt_or_ge m K with hmK | hKm
    · have hmem : m ∈ Finset.range K := Finset.mem_range.mpr hmK
      have hterm : (if t / 2^(m+1) < d then (dyw r)^m else 0) = (dyw r)^m := if_pos hm1
      have hle : (dyw r)^m ≤ ∑ k ∈ Finset.range K, (if t / 2^(k+1) < d then (dyw r)^k else 0) := by
        have h := Finset.single_le_sum (s := Finset.range K)
          (f := fun k => (if t / 2^(k+1) < d then (dyw r)^k else 0))
          (fun i _ => ite_zero_nonneg (pow_nonneg (dyw_pos r).le i) _) hmem
        rwa [hterm] at h
      calc d ^ r ≤ t ^ r * (dyw r)^m := hkey
        _ ≤ t ^ r * (∑ k ∈ Finset.range K, (if t / 2^(k+1) < d then (dyw r)^k else 0) + (dyw r)^K) := by
            apply mul_le_mul_of_nonneg_left _ htr
            linarith [hle, pow_nonneg (dyw_pos r).le K]
    · have hq : (dyw r)^m ≤ (dyw r)^K :=
        pow_le_pow_of_le_one (dyw_pos r).le (dyw_lt_one hr).le hKm
      calc d ^ r ≤ t ^ r * (dyw r)^m := hkey
        _ ≤ t ^ r * (∑ k ∈ Finset.range K, (if t / 2^(k+1) < d then (dyw r)^k else 0) + (dyw r)^K) := by
            apply mul_le_mul_of_nonneg_left _ htr
            linarith [hq, hsum]

/-- Summed layer-cake with a truncated geometric series. -/
lemma sum_finite_le {r t : ℝ} (hr : 0 < r) (ht : 0 < t) (J K : ℕ) (d : ℕ → ℝ)
    (hd : ∀ j, 0 ≤ d j) (hdt : ∀ j, d j ≤ t) :
    ∑ j ∈ Finset.range J, d j ^ r ≤
      t ^ r * (∑ k ∈ Finset.range K, (dyw r)^k *
          ((Finset.filter (fun j => t / 2^(k+1) < d j) (Finset.range J)).card : ℝ)
        + (J : ℝ) * (dyw r)^K) := by
  classical
  calc ∑ j ∈ Finset.range J, d j ^ r
      ≤ ∑ j ∈ Finset.range J, t ^ r *
          (∑ k ∈ Finset.range K, (if t / 2^(k+1) < d j then (dyw r)^k else 0) + (dyw r)^K) :=
        Finset.sum_le_sum (fun j _ => pointwise_finite hr ht (hd j) (hdt j) K)
    _ = t ^ r * ∑ j ∈ Finset.range J,
          (∑ k ∈ Finset.range K, (if t / 2^(k+1) < d j then (dyw r)^k else 0) + (dyw r)^K) := by
        rw [← Finset.mul_sum]
    _ = t ^ r * (∑ j ∈ Finset.range J, ∑ k ∈ Finset.range K,
            (if t / 2^(k+1) < d j then (dyw r)^k else 0) + ∑ j ∈ Finset.range J, (dyw r)^K) := by
        rw [Finset.sum_add_distrib]
    _ = t ^ r * (∑ k ∈ Finset.range K, ∑ j ∈ Finset.range J,
            (if t / 2^(k+1) < d j then (dyw r)^k else 0) + (J : ℝ) * (dyw r)^K) := by
        rw [Finset.sum_comm, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ = t ^ r * (∑ k ∈ Finset.range K, (dyw r)^k *
          ((Finset.filter (fun j => t / 2^(k+1) < d j) (Finset.range J)).card : ℝ)
        + (J : ℝ) * (dyw r)^K) := by
        rw [Finset.sum_congr rfl (fun k _ => sum_ite_card ((dyw r)^k) (fun j => t / 2^(k+1) < d j) J)]

/-- Summed layer-cake, letting the truncation parameter tend to infinity. -/
lemma sum_le_tsum_agg {r t : ℝ} (hr : 1 < r) (ht : 0 < t) (J : ℕ) (d : ℕ → ℝ)
    (hd : ∀ j, 0 ≤ d j) (hdt : ∀ j, d j ≤ t) :
    ∑ j ∈ Finset.range J, d j ^ r ≤ t ^ r * ∑' k : ℕ,
      (dyw r)^k * ((Finset.filter (fun j => t / 2^(k+1) < d j) (Finset.range J)).card : ℝ) := by
  classical
  have hr0 : 0 < r := by linarith
  have hq0 : 0 ≤ dyw r := (dyw_pos r).le
  have hq1 : dyw r < 1 := dyw_lt_one hr0
  have hcard_le : ∀ k, ((Finset.filter (fun j => t / 2^(k+1) < d j) (Finset.range J)).card : ℝ) ≤ J := by
    intro k
    have h := Finset.card_le_card (Finset.filter_subset (fun j => t / 2^(k+1) < d j) (Finset.range J))
    rw [Finset.card_range] at h
    exact_mod_cast h
  have hAn0 : ∀ k, 0 ≤ (dyw r)^k *
      ((Finset.filter (fun j => t / 2^(k+1) < d j) (Finset.range J)).card : ℝ) :=
    fun k => mul_nonneg (pow_nonneg hq0 k) (by positivity)
  have hsummable : Summable (fun k =>
      (dyw r)^k * ((Finset.filter (fun j => t / 2^(k+1) < d j) (Finset.range J)).card : ℝ)) :=
    Summable.of_nonneg_of_le hAn0
      (fun k => by simpa [mul_comm] using mul_le_mul_of_nonneg_left (hcard_le k) (pow_nonneg hq0 k))
      (Summable.mul_left (J:ℝ) (summable_geometric_of_lt_one hq0 hq1))
  have hK : ∀ K, ∑ j ∈ Finset.range J, d j ^ r ≤
      t ^ r * (∑ k ∈ Finset.range K, (dyw r)^k *
          ((Finset.filter (fun j => t / 2^(k+1) < d j) (Finset.range J)).card : ℝ)
        + (J:ℝ) * (dyw r)^K) := fun K => sum_finite_le hr0 ht J K d hd hdt
  have hlim2 : Tendsto (fun K : ℕ => (J:ℝ) * (dyw r)^K) atTop (𝓝 0) := by
    simpa using Tendsto.const_mul (J:ℝ) (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1)
  have hlim : Tendsto (fun K : ℕ => ∑ k ∈ Finset.range K, (dyw r)^k *
        ((Finset.filter (fun j => t / 2^(k+1) < d j) (Finset.range J)).card : ℝ) + (J:ℝ) * (dyw r)^K)
      atTop (𝓝 (∑' k, (dyw r)^k *
        ((Finset.filter (fun j => t / 2^(k+1) < d j) (Finset.range J)).card : ℝ) + 0)) :=
    hsummable.tendsto_sum_tsum_nat.add hlim2
  have := le_of_tendsto_of_tendsto tendsto_const_nhds (hlim.const_mul (t^r))
    (Filter.Eventually.of_forall hK)
  simpa using this

/-- The comparison series bound: if `A k ≤ ((1 - 2^(1-r)) / 2^r) * 2^k`, then
`∑ k, q^k A_k ≤ 2^{-r}`. -/
lemma tsum_weight_le {r : ℝ} (hr : 1 < r) (An : ℕ → ℝ) (hAn0 : ∀ k, 0 ≤ An k)
    (hAn : ∀ k, An k ≤ ((1 - (2:ℝ)^(1-r)) / 2^r) * 2^k) :
    ∑' k : ℕ, (dyw r)^k * An k ≤ 1 / 2^r := by
  have hz0 : 0 ≤ (2:ℝ)^(1-r) := (two_rpow_one_sub_pos r).le
  have hz1 : (2:ℝ)^(1-r) < 1 := two_rpow_one_sub_lt_one hr
  have hzpos : 0 < 1 - (2:ℝ)^(1-r) := one_sub_two_rpow_pos hr
  have hstep : ∀ k, (dyw r)^k * An k ≤ ((1 - (2:ℝ)^(1-r)) / 2^r) * ((2:ℝ)^(1-r))^k := by
    intro k
    calc (dyw r)^k * An k
        ≤ (dyw r)^k * (((1 - (2:ℝ)^(1-r)) / 2^r) * 2^k) :=
          mul_le_mul_of_nonneg_left (hAn k) (pow_nonneg (dyw_pos r).le k)
      _ = ((1 - (2:ℝ)^(1-r)) / 2^r) * ((2:ℝ)^(1-r))^k := by
          have h1 : (dyw r)^k * (((1 - (2:ℝ)^(1-r)) / 2^r) * 2^k)
              = ((1 - (2:ℝ)^(1-r)) / 2^r) * ((dyw r * 2)^k) := by rw [mul_pow]; ring
          rw [h1, dyw_mul_two_eq]
  have hsumm1 : Summable fun k => ((1 - (2:ℝ)^(1-r)) / 2^r) * ((2:ℝ)^(1-r))^k :=
    Summable.mul_left _ (summable_geometric_of_lt_one hz0 hz1)
  have hsumm2 : Summable fun k => (dyw r)^k * An k :=
    Summable.of_nonneg_of_le (fun k => mul_nonneg (pow_nonneg (dyw_pos r).le k) (hAn0 k)) hstep hsumm1
  calc ∑' k, (dyw r)^k * An k
      ≤ ∑' k, ((1 - (2:ℝ)^(1-r)) / 2^r) * ((2:ℝ)^(1-r))^k :=
        Summable.tsum_le_tsum hstep hsumm2 hsumm1
    _ = ((1 - (2:ℝ)^(1-r)) / 2^r) * ∑' k, ((2:ℝ)^(1-r))^k := tsum_mul_left
    _ = ((1 - (2:ℝ)^(1-r)) / 2^r) * (1 - (2:ℝ)^(1-r))⁻¹ := by rw [tsum_geometric_of_lt_one hz0 hz1]
    _ = 1 / 2^r := by
        rw [div_mul_eq_mul_div, mul_inv_cancel₀ (ne_of_gt hzpos), one_div]

theorem exists_level_of_Vpath_gt (x : ℕ → ℝ) {r t : ℝ} (hr : 1 < r) (ht : 0 < t)
    (hrange : ∀ s s', |x s' - x s| ≤ t) (hV : ENNReal.ofReal t < Work.Analysis.Probability.VpathR x r) :
    ∃ k : ℕ, ENNReal.ofReal (((1 - (2:ℝ)^(1-r)) / 2^r) * 2^k)
      < Work.Analysis.Probability.Kpath x (t / 2^(k+1)) := by
  classical
  rw [VpathR] at hV
  obtain ⟨u, hu⟩ := exists_lt_iSup hV
  obtain ⟨J, hJ⟩ := exists_lt_iSup hu
  set d : ℕ → ℝ := fun j => |x (u.1 (j+1)) - x (u.1 j)| with hd
  have hd0 : ∀ j, 0 ≤ d j := fun j => abs_nonneg _
  have hdt : ∀ j, d j ≤ t := fun j => hrange _ _
  have hS0 : 0 ≤ ∑ j ∈ Finset.range J, d j ^ r :=
    Finset.sum_nonneg (fun j _ => Real.rpow_nonneg (hd0 j) r)
  have hJ' : t < (∑ j ∈ Finset.range J, d j ^ r) ^ (1/r) :=
    (ENNReal.ofReal_lt_ofReal_iff_of_nonneg ht.le).mp hJ
  have hS1 : 0 < (∑ j ∈ Finset.range J, d j ^ r) ^ (1/r) := lt_of_lt_of_le ht hJ'.le
  have htr : t ^ r < ∑ j ∈ Finset.range J, d j ^ r := by
    have h := (Real.rpow_lt_rpow_iff ht.le hS1.le (by linarith : (0:ℝ) < r)).mpr hJ'
    rwa [← Real.rpow_mul hS0 (1/r) r, div_mul_cancel₀ (1:ℝ) (by linarith : (0:ℝ) < r).ne', Real.rpow_one] at h
  by_contra hcon
  push Not at hcon
  set An : ℕ → ℝ := fun k => ((Finset.filter (fun j => t / 2^(k+1) < d j) (Finset.range J)).card : ℝ)
    with hAn
  have hKpath : ∀ k, ENNReal.ofReal (An k) ≤ Kpath x (t / 2^(k+1)) := by
    intro k
    rw [hAn, ENNReal.ofReal_natCast, Kpath]
    exact le_iSup_of_le u (le_iSup_of_le J le_rfl)
  have hcpos : ∀ k, 0 < ((1 - (2:ℝ)^(1-r)) / 2^r) * 2^k := by
    intro k
    exact mul_pos (div_pos (one_sub_two_rpow_pos hr) (by positivity)) (by positivity)
  have hAn_le : ∀ k, An k ≤ ((1 - (2:ℝ)^(1-r)) / 2^r) * 2^k := by
    intro k
    exact (ENNReal.ofReal_le_ofReal_iff (hcpos k).le).mp (le_trans (hKpath k) (hcon k))
  have hAn0 : ∀ k, 0 ≤ An k := fun k => Nat.cast_nonneg _
  have hmain : ∑ j ∈ Finset.range J, d j ^ r ≤ t ^ r * ∑' k : ℕ, (dyw r)^k * An k := by
    simpa only [hAn] using sum_le_tsum_agg hr ht J d hd0 hdt
  have hbound : ∑' k : ℕ, (dyw r)^k * An k ≤ 1 / 2^r := tsum_weight_le hr An hAn0 hAn_le
  have hL1 : ∑' k : ℕ, (dyw r)^k * An k < 1 := by
    refine lt_of_le_of_lt hbound ?_
    rw [one_div_two_rpow]
    exact dyw_lt_one (by linarith : (0:ℝ) < r)
  have hfin : ∑ j ∈ Finset.range J, d j ^ r < t ^ r :=
    lt_of_le_of_lt hmain (by
      have h := mul_lt_mul_of_pos_left hL1 (Real.rpow_pos_of_pos ht r)
      rwa [mul_one] at h)
  linarith [htr, hfin]

end Work.Analysis.Probability
