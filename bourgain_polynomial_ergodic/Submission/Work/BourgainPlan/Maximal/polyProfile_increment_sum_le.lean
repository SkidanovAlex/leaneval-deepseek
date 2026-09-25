import Mathlib
import Submission.Work.BourgainPlan.Maximal.l2_defs
import Submission.Work.BourgainPlan.Maximal.polyProfile_sub_one_le
import Submission.Work.BourgainPlan.Maximal.polyProfile_step_diff_decay
import Submission.Work.BourgainPlan.Maximal.polyProfile_step_diff_small

/-!
# Summability of the dyadic increments of the polynomial profile

For `P : ℤ[X]` of degree `d ≥ 2` with positive leading coefficient, the oscillatory profile
`Φ_N(β) = polyProfile P N β` satisfies

`∑_{k<K} ‖Φ_{2^{k+1}}(β) - Φ_{2^k}(β)‖ ≤ C`

with `C` independent of `β : ℝ` and of `K : ℕ` — the profile has bounded dyadic variation,
uniformly in the frequency.

The two inputs are the step estimates already available:
* `polyProfile_step_diff_decay`: in the regime `|β| (2^k)^d ≥ 1` the difference is bounded by the
  van der Corput decay `(|β| (2^k)^d)^{-1/d}`;
* `polyProfile_step_diff_small`: always the difference is bounded by `|β| (2^{k+1})^d` (the
  mean-value bound at the origin).

Balancing the two at each scale leaves, with `q = 2^d` and `t = |β|`, the summand
`min 1 (min (q^{k+1} t) ((q^k t)^{-1/d}))`, whose dyadic sum is bounded by the elementary
geometric-series lemma `geomMinSumLe` below.
-/

open Finset

namespace Work.BourgainPlan.Maximal

/-! ## Elementary geometric series with a `min 1` cap -/

/-- A geometric series with ratio `r ∈ [0,1)` is bounded by `(1-r)⁻¹`. -/
private lemma sum_range_pow_le_inv {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (N : ℕ) :
    ∑ j ∈ Finset.range N, r ^ j ≤ (1 - r)⁻¹ := by
  have h1mr : 0 < 1 - r := by linarith
  have hmul : (∑ j ∈ Finset.range N, r ^ j) * (1 - r) = 1 - r ^ N := geom_sum_mul_neg r N
  have hle : 1 - r ^ N ≤ 1 := by
    have : 0 ≤ r ^ N := pow_nonneg hr0 N
    linarith
  calc ∑ j ∈ Finset.range N, r ^ j
      = (1 - r ^ N) / (1 - r) := by
        rw [eq_div_iff (ne_of_gt h1mr)]
        exact hmul
    _ ≤ 1 / (1 - r) := div_le_div_of_nonneg_right hle h1mr.le
    _ = (1 - r)⁻¹ := one_div _

/-- One step of the geometric recursion `(q^{m+1} t)^{-1/d} = q^{-1/d} (q^m t)^{-1/d}`. -/
private lemma u_step (q t : ℝ) (d : ℕ) (hq : 0 ≤ q) (ht : 0 ≤ t) (m : ℕ) :
    (q ^ (m + 1) * t) ^ (-(1 / (d : ℝ)))
      = q ^ (-(1 / (d : ℝ))) * (q ^ m * t) ^ (-(1 / (d : ℝ))) := by
  have hqt : (0:ℝ) ≤ q ^ m * t := mul_nonneg (pow_nonneg hq m) ht
  have h1 : q ^ (m + 1) * t = q * (q ^ m * t) := by rw [pow_succ]; ring
  rw [h1, Real.mul_rpow hq hqt]

/-- Iterated form of `u_step`. -/
private lemma u_pow (q t : ℝ) (d : ℕ) (hq : 0 ≤ q) (ht : 0 ≤ t) (n i : ℕ) :
    (q ^ (n + i) * t) ^ (-(1 / (d : ℝ)))
      = (q ^ (-(1 / (d : ℝ)))) ^ i * (q ^ n * t) ^ (-(1 / (d : ℝ))) := by
  induction i with
  | zero => simp
  | succ i ih =>
      have hstep : (q ^ (n + i).succ * t) ^ (-(1 / (d : ℝ)))
          = q ^ (-(1 / (d : ℝ))) * (q ^ (n + i) * t) ^ (-(1 / (d : ℝ))) := by
        have hqt : (0:ℝ) ≤ q ^ (n + i) * t := mul_nonneg (pow_nonneg hq (n + i)) ht
        have h1 : q ^ (n + i).succ * t = q * (q ^ (n + i) * t) := by rw [pow_succ]; ring
        rw [h1, Real.mul_rpow hq hqt]
      rw [Nat.add_succ, hstep, ih, pow_succ']
      ring

/-- **The dyadic geometric sum with a `min 1` cap.**  For `q ≥ 2`, `d ≥ 1` there is a constant
bounding `∑_{m<M} min 1 (min (q^{m+1} t) ((q^m t)^{-1/d}))` uniformly over `t ≥ 0` and `M : ℕ`. -/
private lemma geomMinSumLe {q : ℝ} (hq : 2 ≤ q) {d : ℕ} (hd : 1 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (t : ℝ), 0 ≤ t → ∀ M : ℕ,
      ∑ m ∈ Finset.range M, min 1 (min (q ^ (m + 1) * t) ((q ^ m * t) ^ (-(1 / (d : ℝ))))) ≤ C := by
  classical
  have hq1 : 1 < q := by linarith
  have hq0 : 0 < q := by linarith
  have hdpos : (0:ℝ) < (d:ℝ) := by exact_mod_cast (by omega : 0 < d)
  have hexp_lt : -(1 / (d : ℝ)) < 0 := by
    have : (0:ℝ) < 1 / (d:ℝ) := by positivity
    linarith
  have hr0 : 0 ≤ q ^ (-(1 / (d : ℝ))) := Real.rpow_nonneg hq0.le _
  have hr1 : q ^ (-(1 / (d : ℝ))) < 1 := Real.rpow_lt_one_of_one_lt_of_neg hq1 hexp_lt
  have hCpos : 0 < q ^ 2 / (q - 1) + (1 - q ^ (-(1 / (d : ℝ))))⁻¹ := by
    have h1 : 0 < q ^ 2 / (q - 1) := by
      apply div_pos (by positivity)
      linarith
    have h2 : 0 < (1 - q ^ (-(1 / (d : ℝ))))⁻¹ := by
      apply inv_pos.mpr
      linarith [hr1]
    linarith
  refine ⟨q ^ 2 / (q - 1) + (1 - q ^ (-(1 / (d : ℝ))))⁻¹, hCpos, ?_⟩
  intro t ht M
  set f : ℕ → ℝ := fun m => min 1 (min (q ^ (m + 1) * t) ((q ^ m * t) ^ (-(1 / (d : ℝ))))) with hf
  by_cases ht0 : t = 0
  · have hz : ∀ m, f m = 0 := by
      intro m
      subst ht0
      show min 1 (min (q ^ (m + 1) * 0) ((q ^ m * 0) ^ (-(1 / (d : ℝ))))) = 0
      rw [mul_zero, mul_zero, Real.zero_rpow (ne_of_lt hexp_lt), min_self,
        min_eq_right (zero_le_one)]
    rw [Finset.sum_eq_zero (fun m _ => hz m)]
    exact hCpos.le
  · have htpos : 0 < t := lt_of_le_of_ne ht (fun h => ht0 h.symm)
    have hexists : ∃ n : ℕ, 1 ≤ q ^ n * t := by
      have htend : Filter.Tendsto (fun n : ℕ => q ^ n) Filter.atTop Filter.atTop :=
        tendsto_pow_atTop_atTop_of_one_lt hq1
      have h1 : ∀ᶠ n in Filter.atTop, (1:ℝ) ≤ q ^ n * t := by
        filter_upwards [htend.eventually_ge_atTop (1 / t)] with n hn
        have h2 : (1 / t) * t ≤ q ^ n * t := mul_le_mul_of_nonneg_right hn ht
        rwa [one_div_mul_cancel (ne_of_gt htpos)] at h2
      exact h1.exists
    set K0 : ℕ := Nat.find hexists with hK0def
    have hK0spec : 1 ≤ q ^ K0 * t := Nat.find_spec hexists
    have hK0min : ∀ m, m < K0 → q ^ m * t < 1 := fun m hm =>
      not_le.mp (Nat.find_min hexists hm)
    set L : ℕ := min M K0 with hLdef
    have hLleK : L ≤ K0 := by rw [hLdef]; exact min_le_right _ _
    have hLleM : L ≤ M := by rw [hLdef]; exact min_le_left _ _
    have hsplit : ∑ m ∈ Finset.range M, f m
        = ∑ m ∈ Finset.range L, f m + ∑ m ∈ Finset.Ico L M, f m := by
      rw [← Finset.sum_range_add_sum_Ico f (m := L) (n := M) hLleM]
    rw [hsplit]
    have partA : ∑ m ∈ Finset.range L, f m ≤ q ^ 2 / (q - 1) := by
      rcases Nat.eq_zero_or_pos L with hL0 | hLpos
      · rw [hL0, Finset.sum_range_zero]
        apply div_nonneg (by positivity)
        linarith
      · have hstep : ∀ m ∈ Finset.range L, f m ≤ q ^ (m + 1) * t := fun m _ =>
          le_trans (min_le_right _ _) (min_le_left _ _)
        calc ∑ m ∈ Finset.range L, f m
            ≤ ∑ m ∈ Finset.range L, q ^ (m + 1) * t := Finset.sum_le_sum hstep
          _ = ∑ m ∈ Finset.range L, (q * t) * q ^ m := by
              apply Finset.sum_congr rfl
              intro m _
              rw [pow_succ]; ring
          _ = (q * t) * ∑ m ∈ Finset.range L, q ^ m := by rw [Finset.mul_sum]
          _ ≤ (q * t) * (q ^ L / (q - 1)) := by
              apply mul_le_mul_of_nonneg_left _ (by positivity)
              rw [geom_sum_eq (by linarith : q ≠ 1) L]
              apply div_le_div_of_nonneg_right _ (by linarith : (0:ℝ) < q - 1).le
              linarith [pow_pos hq0 L]
          _ ≤ q ^ 2 / (q - 1) := by
              have hqL : q ^ L * t < q := by
                have hm : L - 1 < K0 := lt_of_lt_of_le (Nat.pred_lt hLpos.ne') hLleK
                have h2 : q ^ (L - 1) * t < 1 := hK0min (L - 1) hm
                have h3 : q ^ L * t = q * (q ^ (L - 1) * t) := by
                  conv_lhs => rw [show L = (L - 1) + 1 by omega, pow_succ']
                  ring
                rw [h3]; nlinarith [h2, hq0]
              have hqsub : (0:ℝ) < q - 1 := by linarith
              calc (q * t) * (q ^ L / (q - 1))
                  = q * (q ^ L * t) / (q - 1) := by ring
                _ ≤ q * q / (q - 1) := by
                    apply div_le_div_of_nonneg_right _ hqsub.le
                    nlinarith [hqL, hq0]
                _ = q ^ 2 / (q - 1) := by ring
    have partB : ∑ m ∈ Finset.Ico L M, f m ≤ (1 - q ^ (-(1 / (d : ℝ))))⁻¹ := by
      rcases lt_or_ge M K0 with hMK | hKM
      · have hLK : L = M := by rw [hLdef]; exact min_eq_left hMK.le
        rw [hLK, Finset.Ico_self, Finset.sum_empty]
        exact inv_nonneg.mpr (by linarith [hr1])
      · have hLK : L = K0 := by rw [hLdef]; exact min_eq_right hKM
        rw [hLK]
        have hstep : ∀ m ∈ Finset.Ico K0 M, f m = (q ^ m * t) ^ (-(1 / (d : ℝ))) := by
          intro m hm
          rw [Finset.mem_Ico] at hm
          have h1 : 1 ≤ q ^ m * t := by
            have hmono : q ^ K0 ≤ q ^ m := pow_le_pow_right₀ hq1.le hm.1
            have := mul_le_mul_of_nonneg_right hmono ht
            linarith
          have hu1 : (q ^ m * t) ^ (-(1 / (d : ℝ))) ≤ 1 :=
            Real.rpow_le_one_of_one_le_of_nonpos h1 hexp_lt.le
          have ha : (q ^ m * t) ^ (-(1 / (d : ℝ))) ≤ q ^ (m + 1) * t := by
            have hq2 : q ≤ q ^ (m + 1) * t := by
              have hh : q ^ (m + 1) * t = q * (q ^ m * t) := by rw [pow_succ]; ring
              rw [hh]; nlinarith [h1, hq0]
            linarith [hu1, hq1, hq2]
          simp only [hf]
          exact le_antisymm (le_trans (min_le_right _ _) (min_le_right _ _))
            (le_min hu1 (le_min ha le_rfl))
        have hcongr : ∑ m ∈ Finset.Ico K0 M, f m
            = ∑ m ∈ Finset.Ico K0 M, (q ^ m * t) ^ (-(1 / (d : ℝ))) :=
          Finset.sum_congr rfl hstep
        rw [hcongr, Finset.sum_Ico_eq_sum_range]
        have hpow : ∀ k : ℕ, (q ^ (K0 + k) * t) ^ (-(1 / (d : ℝ)))
            = (q ^ (-(1 / (d : ℝ)))) ^ k * (q ^ K0 * t) ^ (-(1 / (d : ℝ))) :=
          fun k => u_pow q t d hq0.le ht K0 k
        have hcongr2 : ∑ k ∈ Finset.range (M - K0), (q ^ (K0 + k) * t) ^ (-(1 / (d : ℝ)))
            = ∑ k ∈ Finset.range (M - K0),
                (q ^ (-(1 / (d : ℝ)))) ^ k * (q ^ K0 * t) ^ (-(1 / (d : ℝ))) :=
          Finset.sum_congr rfl (fun k _ => hpow k)
        rw [hcongr2]
        have hfac : (∑ k ∈ Finset.range (M - K0),
                (q ^ (-(1 / (d : ℝ)))) ^ k * (q ^ K0 * t) ^ (-(1 / (d : ℝ))))
            = (∑ k ∈ Finset.range (M - K0), (q ^ (-(1 / (d : ℝ)))) ^ k)
                * (q ^ K0 * t) ^ (-(1 / (d : ℝ))) := by rw [Finset.sum_mul]
        rw [hfac]
        have huK0 : (q ^ K0 * t) ^ (-(1 / (d : ℝ))) ≤ 1 :=
          Real.rpow_le_one_of_one_le_of_nonpos hK0spec hexp_lt.le
        calc (∑ k ∈ Finset.range (M - K0), (q ^ (-(1 / (d : ℝ)))) ^ k)
                * (q ^ K0 * t) ^ (-(1 / (d : ℝ)))
            ≤ (1 - q ^ (-(1 / (d : ℝ))))⁻¹ * (q ^ K0 * t) ^ (-(1 / (d : ℝ))) :=
              mul_le_mul_of_nonneg_right (sum_range_pow_le_inv hr0 hr1 _) (by positivity)
          _ ≤ (1 - q ^ (-(1 / (d : ℝ))))⁻¹ * 1 :=
              mul_le_mul_of_nonneg_left huK0 (by positivity)
          _ = (1 - q ^ (-(1 / (d : ℝ))))⁻¹ := mul_one _
    exact add_le_add partA partB

/-! ## The main theorem -/

theorem polyProfile_increment_sum_le (P : Polynomial ℤ) (hc : 0 < P.leadingCoeff)
    (hd : 2 ≤ P.natDegree) :
    ∃ C : ℝ, 0 < C ∧ ∀ (β : ℝ) (K : ℕ),
      ∑ k ∈ Finset.range K, ‖polyProfile P (2 ^ (k + 1)) β - polyProfile P (2 ^ k) β‖ ≤ C := by
  have hd1 : 1 ≤ P.natDegree := by omega
  have hd0 : (0:ℝ) < (P.natDegree : ℝ) := by exact_mod_cast (by omega : 0 < P.natDegree)
  have hexp_lt : -(1 / (P.natDegree : ℝ)) < 0 := by
    have : (0:ℝ) < 1 / (P.natDegree : ℝ) := one_div_pos.mpr hd0
    linarith
  obtain ⟨Cdec, hCdecpos, hdec⟩ := polyProfile_step_diff_decay P hd
  obtain ⟨Csm, hCsmpos, hsmall⟩ := polyProfile_step_diff_small P hd
  set q : ℝ := (2:ℝ) ^ P.natDegree with hqdef
  have hq1 : 1 < q := by
    rw [hqdef]
    exact one_lt_pow₀ (by norm_num) (by omega)
  have hq0 : 0 < q := by linarith
  have hq2 : 2 ≤ q := by
    rw [hqdef]
    calc (2:ℝ) = (2:ℝ)^1 := (pow_one 2).symm
      _ ≤ (2:ℝ)^P.natDegree := pow_le_pow_right₀ (by norm_num) hd1
  obtain ⟨Cg, hCgpos, hgeom⟩ := geomMinSumLe hq2 hd1
  set Kc : ℝ := max Cdec (max Csm 2) with hKcdef
  have hKcpos : 0 < Kc := by
    rw [hKcdef]
    exact lt_of_lt_of_le (by norm_num) (le_trans (le_max_right Csm 2) (le_max_right Cdec _))
  have hKcge2 : 2 ≤ Kc := by
    rw [hKcdef]
    exact le_trans (le_max_right Csm 2) (le_max_right Cdec _)
  have hKcgeCdec : Cdec ≤ Kc := by rw [hKcdef]; exact le_max_left _ _
  have hKcgeCsm : Csm ≤ Kc := by
    rw [hKcdef]; exact le_trans (le_max_left Csm 2) (le_max_right Cdec _)
  have hqk : ∀ k : ℕ, q ^ k = ((2:ℝ) ^ k) ^ P.natDegree := by
    intro k
    rw [hqdef, ← pow_mul, ← pow_mul]
    congr 1
    ring
  refine ⟨Kc * Cg, mul_pos hKcpos hCgpos, ?_⟩
  intro β K
  rcases eq_or_ne β 0 with hβ0 | hβ0
  · subst hβ0
    have hzero : ∀ k : ℕ, ‖polyProfile P (2 ^ (k + 1)) 0 - polyProfile P (2 ^ k) 0‖ = 0 := by
      intro k
      rw [polyProfile_zero, polyProfile_zero, sub_self, norm_zero]
    rw [Finset.sum_eq_zero (fun k _ => hzero k)]
    exact mul_nonneg hKcpos.le hCgpos.le
  set t : ℝ := |β| with htdef
  have htpos : 0 < t := by rw [htdef]; exact abs_pos.mpr hβ0
  have ht0 : 0 ≤ t := le_of_lt htpos
  have hterm : ∀ k : ℕ,
      ‖polyProfile P (2 ^ (k + 1)) β - polyProfile P (2 ^ k) β‖
        ≤ Kc * min 1 (min (q ^ (k + 1) * t)
            ((q ^ k * t) ^ (-(1 / (P.natDegree : ℝ))))) := by
    intro k
    set A : ℝ := q ^ (k + 1) * t with hAdef
    set u : ℝ := (q ^ k * t) ^ (-(1 / (P.natDegree : ℝ))) with hudef
    have hA : ‖polyProfile P (2 ^ (k + 1)) β - polyProfile P (2 ^ k) β‖ ≤ Kc * 1 := by
      have h2 : ‖polyProfile P (2 ^ (k + 1)) β - polyProfile P (2 ^ k) β‖ ≤ 2 := by
        calc ‖polyProfile P (2 ^ (k + 1)) β - polyProfile P (2 ^ k) β‖
            ≤ ‖polyProfile P (2 ^ (k + 1)) β‖ + ‖polyProfile P (2 ^ k) β‖ := norm_sub_le _ _
          _ ≤ 1 + 1 := add_le_add (norm_polyProfile_le_one P _ _) (norm_polyProfile_le_one P _ _)
          _ = 2 := by norm_num
      rw [mul_one]
      linarith
    have hB : ‖polyProfile P (2 ^ (k + 1)) β - polyProfile P (2 ^ k) β‖ ≤ Kc * A := by
      have hs' := hsmall k (k + 1) (by omega) β
      have hcd : ((2:ℝ) ^ (k + 1)) ^ P.natDegree = q ^ (k + 1) := (hqk (k + 1)).symm
      rw [hcd, ← htdef] at hs'
      calc ‖polyProfile P (2 ^ (k + 1)) β - polyProfile P (2 ^ k) β‖
          ≤ Csm * (t * q ^ (k + 1)) := hs'
        _ ≤ Kc * (t * q ^ (k + 1)) := mul_le_mul_of_nonneg_right hKcgeCsm (by positivity)
        _ = Kc * A := by rw [hAdef]; ring
    by_cases hreg : 1 ≤ q ^ k * t
    · have hreg' : 1 ≤ |β| * ((2:ℝ) ^ k) ^ P.natDegree := by
        have h := hreg
        rw [hqk k, htdef] at h
        rwa [mul_comm] at h
      have hd' := hdec k (k + 1) (by omega) β hreg'
      have hcast : (|β| * ((2:ℝ) ^ k) ^ P.natDegree) = q ^ k * t := by
        rw [hqk k, htdef]; ring
      rw [hcast] at hd'
      have hC : ‖polyProfile P (2 ^ (k + 1)) β - polyProfile P (2 ^ k) β‖ ≤ Kc * u := by
        rw [hudef]
        exact le_trans hd' (mul_le_mul_of_nonneg_right hKcgeCdec (Real.rpow_nonneg (by positivity) _))
      have hu1 : u ≤ 1 := by
        rw [hudef]; exact Real.rpow_le_one_of_one_le_of_nonpos hreg hexp_lt.le
      have hAq : A = q * (q ^ k * t) := by rw [hAdef, pow_succ]; ring
      have huA : u ≤ A := by rw [hAq]; nlinarith [hu1, hreg, hq0, hq1]
      have hminval : min 1 (min A u) = u :=
        le_antisymm (le_trans (min_le_right 1 _) (min_le_right _ _))
          (le_min hu1 (le_min huA le_rfl))
      rw [hminval]; exact hC
    · have hlt : q ^ k * t < 1 := not_le.mp hreg
      have hupos : 0 < q ^ k * t := mul_pos (pow_pos hq0 k) htpos
      have hu_gt1 : 1 < u := by
        rw [hudef]
        exact Real.one_lt_rpow_of_pos_of_lt_one_of_neg hupos hlt hexp_lt
      rcases le_or_gt A 1 with hA1 | hA1
      · calc ‖polyProfile P (2 ^ (k + 1)) β - polyProfile P (2 ^ k) β‖ ≤ Kc * A := hB
          _ ≤ Kc * min 1 (min A u) :=
              mul_le_mul_of_nonneg_left
                (le_min hA1 (le_min le_rfl (le_trans hA1 (le_of_lt hu_gt1)))) hKcpos.le
      · have hme : min 1 (min A u) = 1 :=
          le_antisymm (min_le_left 1 _)
            (le_min le_rfl (le_min (le_of_lt hA1) (le_of_lt hu_gt1)))
        calc ‖polyProfile P (2 ^ (k + 1)) β - polyProfile P (2 ^ k) β‖ ≤ Kc * 1 := hA
          _ = Kc * min 1 (min A u) := by rw [hme]
  calc ∑ k ∈ Finset.range K, ‖polyProfile P (2 ^ (k + 1)) β - polyProfile P (2 ^ k) β‖
      ≤ ∑ k ∈ Finset.range K, Kc * min 1 (min (q ^ (k + 1) * t)
          ((q ^ k * t) ^ (-(1 / (P.natDegree : ℝ))))) := Finset.sum_le_sum (fun k _ => hterm k)
    _ = Kc * ∑ k ∈ Finset.range K, min 1 (min (q ^ (k + 1) * t)
          ((q ^ k * t) ^ (-(1 / (P.natDegree : ℝ))))) := by rw [Finset.mul_sum]
    _ ≤ Kc * Cg := mul_le_mul_of_nonneg_left (hgeom t ht0 K) hKcpos.le

end Work.BourgainPlan.Maximal
