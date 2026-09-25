import Mathlib
import Submission.Work.BourgainPlan.Maximal.l2_defs
import Submission.Work.BourgainPlan.Maximal.polyProfile_decay_sharp
import Submission.Work.BourgainPlan.Maximal.polyProfile_sub_one_le
import Submission.Work.BourgainPlan.Maximal.polyProfile_step_diff_decay
import Submission.Work.BourgainPlan.Maximal.polyProfile_step_diff_small

/-!
# Summability of the polynomial profile along a `2^i`-spaced dyadic family

For `P : ℤ[X]` of degree `d ≥ 2` the oscillatory profile `Φ_N(β) = polyProfile P N β` satisfies

`∑_{m<M} ‖Φ_{2^{K+(m+1)2^i}}(β) - Φ_{2^{K+m·2^i}}(β)‖ ≤ C`

with `C` independent of the offset `K`, of the length `M`, and of the frequency `β`.  This is the
coarser variant (`i` fixed, steps of `2^i` scales) of `polyProfile_increment_sum_le`; it is what the
`i`-th block of the dyadic decomposition needs.

Writing `X_m = |β| · ((2^{K+m·2^i})^d)` the summand is bounded by
`min 1 (min X_{m+1} (X_m^{-1/d}))`, and the elementary geometric-series lemma `geomMinSumLe` below
bounds its sum uniformly in `X_0` and `M`.
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
bounding `∑_{m<M} min 1 (min (q^{m+1} t) ((q^m t)^{-1/d}))` uniformly over `t ≥ 0` and `M : ℕ`.
-/
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

theorem polyProfile_family_sum_le (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree) (i : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (K M : ℕ) (β : ℝ),
      ∑ m ∈ Finset.range M, ‖polyProfile P (2 ^ (K + (m + 1) * 2 ^ i)) β
          - polyProfile P (2 ^ (K + m * 2 ^ i)) β‖ ≤ C := by
  have hd1 : 1 ≤ P.natDegree := by omega
  obtain ⟨Cdec, hCdecpos, hdec⟩ := polyProfile_step_diff_decay P hd
  obtain ⟨Csm, hCsmpos, hsmall⟩ := polyProfile_step_diff_small P hd
  set Q : ℝ := ((2 : ℝ) ^ (2 ^ i)) ^ P.natDegree with hQdef
  have hQ2 : 2 ≤ Q := by
    rw [hQdef]
    have hb : (2:ℝ) ≤ (2:ℝ) ^ (2 ^ i) := by
      calc (2:ℝ) = (2:ℝ)^1 := (pow_one 2).symm
        _ ≤ (2:ℝ)^(2^i) := pow_le_pow_right₀ (by norm_num) Nat.one_le_two_pow
    calc (2:ℝ) ≤ (2:ℝ) ^ (2 ^ i) := hb
      _ = ((2:ℝ) ^ (2 ^ i)) ^ 1 := (pow_one _).symm
      _ ≤ ((2:ℝ) ^ (2 ^ i)) ^ P.natDegree :=
          pow_le_pow_right₀ (one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2)) hd1
  obtain ⟨Cg, hCgpos, hgeom⟩ := geomMinSumLe hQ2 hd1
  have hexp_lt : -(1 / (P.natDegree : ℝ)) < 0 := by
    have : (0:ℝ) < 1 / (P.natDegree : ℝ) := by positivity
    linarith
  set Kc : ℝ := max Cdec (max Csm 2) with hKcdef
  have hKcge2 : 2 ≤ Kc := by
    rw [hKcdef]
    exact le_trans (le_max_right Csm 2) (le_max_right Cdec (max Csm 2))
  have hKcpos : 0 < Kc := lt_of_lt_of_le (by norm_num) hKcge2
  have hKcgeCdec : Cdec ≤ Kc := by rw [hKcdef]; exact le_max_left _ _
  have hKcgeCsm : Csm ≤ Kc := by
    rw [hKcdef]; exact le_trans (le_max_left Csm 2) (le_max_right Cdec _)
  refine ⟨Kc * Cg, mul_pos hKcpos hCgpos, ?_⟩
  intro K M β
  by_cases hβ : β = 0
  · have hzero : ∀ m : ℕ,
        ‖polyProfile P (2 ^ (K + (m + 1) * 2 ^ i)) β
          - polyProfile P (2 ^ (K + m * 2 ^ i)) β‖ = 0 := by
      intro m
      rw [hβ]
      simp [polyProfile_zero]
    rw [Finset.sum_eq_zero (fun m _ => hzero m)]
    exact mul_nonneg hKcpos.le hCgpos.le
  · have hβpos : 0 < |β| := abs_pos.mpr hβ
    set X : ℕ → ℝ := fun m => |β| * ((2:ℝ) ^ (K + m * 2 ^ i)) ^ P.natDegree with hXdef
    have hXval : ∀ m, X m = |β| * ((2:ℝ) ^ (K + m * 2 ^ i)) ^ P.natDegree := fun m => rfl
    have hX0 : 0 ≤ X 0 := by rw [hXval 0]; positivity
    have hXpos : ∀ m, 0 < X m := by
      intro m; rw [hXval m]
      exact mul_pos hβpos (pow_pos (by positivity) _)
    have hXrec : ∀ m, X (m + 1) = Q * X m := by
      intro m
      have hA : K + (m + 1) * 2 ^ i = (K + m * 2 ^ i) + 2 ^ i := by ring
      rw [hXval (m + 1), hQdef, hA, pow_add, mul_pow]
      ring
    have hXclosed : ∀ m, X m = Q ^ m * X 0 := by
      intro m
      induction m with
      | zero => simp
      | succ m ih => rw [hXrec, ih, pow_succ]; ring
    have hterm : ∀ m : ℕ,
        ‖polyProfile P (2 ^ (K + (m + 1) * 2 ^ i)) β - polyProfile P (2 ^ (K + m * 2 ^ i)) β‖
          ≤ Kc * min 1 (min (X (m + 1)) ((X m) ^ (-(1 / (P.natDegree : ℝ))))) := by
      intro m
      have hle : K + m * 2 ^ i ≤ K + (m + 1) * 2 ^ i :=
        Nat.add_le_add_left (Nat.mul_le_mul_right _ (Nat.le_succ m)) K
      have hA : ‖polyProfile P (2 ^ (K + (m + 1) * 2 ^ i)) β
          - polyProfile P (2 ^ (K + m * 2 ^ i)) β‖ ≤ Kc * 1 := by
        have h2 : ‖polyProfile P (2 ^ (K + (m + 1) * 2 ^ i)) β
            - polyProfile P (2 ^ (K + m * 2 ^ i)) β‖ ≤ 2 := by
          calc ‖polyProfile P (2 ^ (K + (m + 1) * 2 ^ i)) β
                - polyProfile P (2 ^ (K + m * 2 ^ i)) β‖
              ≤ ‖polyProfile P (2 ^ (K + (m + 1) * 2 ^ i)) β‖
                + ‖polyProfile P (2 ^ (K + m * 2 ^ i)) β‖ := norm_sub_le _ _
            _ ≤ 1 + 1 := add_le_add (norm_polyProfile_le_one P _ _) (norm_polyProfile_le_one P _ _)
            _ = 2 := by norm_num
        rw [mul_one]
        linarith
      have hB : ‖polyProfile P (2 ^ (K + (m + 1) * 2 ^ i)) β
          - polyProfile P (2 ^ (K + m * 2 ^ i)) β‖ ≤ Kc * X (m + 1) := by
        have hs' := hsmall (K + m * 2 ^ i) (K + (m + 1) * 2 ^ i) hle β
        rw [hXval (m + 1)]
        exact le_trans hs' (mul_le_mul_of_nonneg_right hKcgeCsm (by positivity))
      by_cases hreg : 1 ≤ X m
      · have hXm1 : 1 ≤ X (m + 1) := by rw [hXrec m]; nlinarith [hreg, hQ2]
        have hd' := hdec (K + m * 2 ^ i) (K + (m + 1) * 2 ^ i) hle β
          (by rw [← hXval m]; exact hreg)
        have hC : ‖polyProfile P (2 ^ (K + (m + 1) * 2 ^ i)) β
            - polyProfile P (2 ^ (K + m * 2 ^ i)) β‖
            ≤ Kc * (X m) ^ (-(1 / (P.natDegree : ℝ))) := by
          rw [hXval m]
          exact le_trans hd' (mul_le_mul_of_nonneg_right hKcgeCdec
            (Real.rpow_nonneg (by positivity) _))
        have hv1 : (X m) ^ (-(1 / (P.natDegree : ℝ))) ≤ 1 :=
          Real.rpow_le_one_of_one_le_of_nonpos hreg hexp_lt.le
        have hvu : (X m) ^ (-(1 / (P.natDegree : ℝ))) ≤ X (m + 1) := le_trans hv1 hXm1
        exact le_trans hC (mul_le_mul_of_nonneg_left
          (le_min hv1 (le_min hvu le_rfl)) hKcpos.le)
      · have hlt : X m < 1 := not_le.mp hreg
        have hvgt : 1 < (X m) ^ (-(1 / (P.natDegree : ℝ))) :=
          Real.one_lt_rpow_of_pos_of_lt_one_of_neg (hXpos m) hlt hexp_lt
        have hminval : min 1 (min (X (m + 1)) ((X m) ^ (-(1 / (P.natDegree : ℝ)))))
            = min 1 (X (m + 1)) := by
          refine le_antisymm ?_ ?_
          · exact le_min (min_le_left _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
          · refine le_min (min_le_left _ _) (le_min (min_le_right _ _) ?_)
            exact le_trans (min_le_left _ _) (le_of_lt hvgt)
        rw [hminval]
        rcases lt_or_ge (1:ℝ) (X (m + 1)) with h1 | h1
        · rw [min_eq_left h1.le]; exact hA
        · rw [min_eq_right h1]; exact hB
    calc ∑ m ∈ Finset.range M, ‖polyProfile P (2 ^ (K + (m + 1) * 2 ^ i)) β
          - polyProfile P (2 ^ (K + m * 2 ^ i)) β‖
        ≤ ∑ m ∈ Finset.range M,
            Kc * min 1 (min (X (m + 1)) ((X m) ^ (-(1 / (P.natDegree : ℝ))))) :=
          Finset.sum_le_sum (fun m _ => hterm m)
      _ = Kc * ∑ m ∈ Finset.range M,
            min 1 (min (X (m + 1)) ((X m) ^ (-(1 / (P.natDegree : ℝ))))) := by
          rw [Finset.mul_sum]
      _ = Kc * ∑ m ∈ Finset.range M,
            min 1 (min (Q ^ (m + 1) * X 0) ((Q ^ m * X 0) ^ (-(1 / (P.natDegree : ℝ))))) := by
          congr 1
          apply Finset.sum_congr rfl
          intro m _
          rw [hXclosed (m + 1), hXclosed m]
      _ ≤ Kc * Cg := mul_le_mul_of_nonneg_left (hgeom (X 0) hX0 M) hKcpos.le

end Work.BourgainPlan.Maximal
