/-
# The tail of the truncated occupancy statistic

`ncp_tail_bound`: the truncated class-sum statistic
`Y f = occSlice G f v D - occSlice G f v ncpJ` of the naive colouring procedure deviates from
its mean by `ω/18` (with `ω = ncpOmega G k D v = (|nonAdjPairs G v|/2)/k · ((k-1)/k)^(2D)`)
with probability at most `exp (-(log (D+2))^4/5000 - 2)`.

## The route

Write `N_j f = ncpN G f v j` for the number of colours occurring on at least `j` retained
neighbours of `v`, and `L = log (D+2)`, `T = L^4/5000 + 2`, `J = ncpJlev D`, `R = ncpRR D`.

* `occSlice_sub_eq` rewrites `Y f = ∑_{j ∈ Icc 19 D} occW j · N_j f`; every coefficient `occW j`
  is negative for `j ≥ 19`, so `Y ≤ 0` and `-Y = ∑_{j ≥ 19} |occW j| · N_j`.
* `ncpN_expect_le` and the series bound `ncp_series_bound` give `𝔼[Y] ≥ -(1/1000)·ω/18`
  (using `pow_ratio_ge` for the crude `((k-1)/k)^(2D) ≥ 1/256`); since `Y ≤ 0`, the deviation
  event is contained in `{-Y ≥ ω/18}`.
* If in addition no colour class of `v` has `J` retained members, then `N_j = 0` for `j ≥ J`,
  so `-Y` is the sum over the slices `j < J`, and comparing with the thresholds
  `K_j = ncpKj G k v D j = max (3⌈μ_j⌉) ⌈R⌉` yields: either `-Y < ∑_{j<J} |occW j| K_j ≤ ω/18`
  (the *budget*, using `ncp_budget_arith` for `(R+4)J^3 ≤ L^4√D/2`, `ncp_omega_lower` for
  `L^4√D ≤ 10·ω/18`, `ncp_series_bound` and `ncpN_expect_le` for the `μ_j`-part, and a cubic
  bound for `∑_{j<J} |occW j|`), or some slice has `N_j ≥ K_j`.
* The remaining two events are each exponentially small: a colour class of size `≥ J` forces
  `4·D·2^J/J! ≥ exp(-T)/2` many expected heavy colours (`occRaw_tail`, `ncp_level_bound`),
  and `N_j ≥ K_j` has probability `μ_j^{K_j}/K_j! ≤ exp(-(T + log(2J) + 10))` (`ncpN_tail`,
  the Stirling bound `K! ≥ (K/e)^K` and `K_j ≥ max (3μ_j) R`).
-/
import Submission.Work.Deep.Sparse.Prelude
import Submission.Work.Deep.Sparse.NcpDefs
import Submission.Work.Deep.Sparse.ncpTailDefs
import Submission.Work.Deep.Sparse.ProbBasic
import Submission.Work.Deep.Sparse.ProbModel
import Submission.Work.Deep.Sparse.occRaw_tail
import Submission.Work.Deep.Sparse.log_large_of_growth
import Submission.Work.Deep.Sparse.ncp_azuma_exponents
import Submission.Work.Deep.Sparse.occSlice_sub_eq
import Submission.Work.Deep.Sparse.ncp_core_tail
import Submission.Work.Deep.Sparse.ncp_series_bound
import Submission.Work.Deep.Sparse.ncp_level_bound
import Submission.Work.Deep.Sparse.ncp_budget_arith
import Submission.Work.Deep.Sparse.ncp_omega_lower

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000

open scoped BigOperators

namespace Work.Deep.Sparse

/-- `occW j < 0` for `j ≥ 19`. -/
lemma occW_neg_of_nineteen {j : ℕ} (hj : 19 ≤ j) : occW j < 0 := by
  unfold occW
  have h1 : (0 : ℝ) < (j : ℝ) - 1 := by
    have : (1 : ℝ) < (j : ℝ) := by exact_mod_cast (by omega : 1 < j)
    linarith
  have h2 : (4 : ℝ) - (j : ℝ) < 0 := by
    have : (19 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
    linarith
  exact div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg h1 h2) (by norm_num)

/-- `occW j ≤ 0` for `j ≥ 4`. -/
lemma occW_nonpos_of_four {j : ℕ} (hj : 4 ≤ j) : occW j ≤ 0 := by
  unfold occW
  have h1 : (0 : ℝ) ≤ (j : ℝ) - 1 := by
    have : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast (by omega : 1 ≤ j)
    linarith
  have h2 : (4 : ℝ) - (j : ℝ) ≤ 0 := by
    have : (4 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
    linarith
  exact div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos h1 h2) (by norm_num)

/-- `∑_{j ≤ J} j^2 ≤ (3/8) J^3` for `J ≥ 13`. -/
lemma sum_sq_range_le (J : ℕ) (hJ : 13 ≤ J) :
    ∑ j ∈ Finset.range (J + 1), ((j : ℕ) : ℝ) ^ 2 ≤ (3 / 8 : ℝ) * (J : ℝ) ^ 3 := by
  induction J, hJ using Nat.le_induction with
  | base => norm_num [Finset.sum_range_succ]
  | succ J hJ ih =>
      rw [Finset.sum_range_succ]
      have hJ13 : (13 : ℝ) ≤ (J : ℝ) := by exact_mod_cast hJ
      have hcast : (((J + 1 : ℕ)) : ℝ) = (J : ℝ) + 1 := by push_cast; ring
      have hstep : (((J + 1 : ℕ)) : ℝ) ^ 2
          ≤ (3 / 8 : ℝ) * (((J + 1 : ℕ)) : ℝ) ^ 3 - (3 / 8 : ℝ) * (J : ℝ) ^ 3 := by
        rw [hcast]
        nlinarith [hJ13, sq_nonneg ((J : ℝ) - 6)]
      linarith

/-- `∑_{j ∈ Icc 19 (J-1)} |occW j| ≤ (3/16) J^3` for `J ≥ 19`. -/
lemma sum_absoccW_le (J : ℕ) (hJ : 19 ≤ J) :
    ∑ j ∈ Finset.Icc 19 (J - 1), |occW j| ≤ (3 / 16 : ℝ) * (J : ℝ) ^ 3 := by
  have hJ13 : 13 ≤ J := by omega
  have h1 : ∑ j ∈ Finset.Icc 19 (J - 1), |occW j|
      ≤ ∑ j ∈ Finset.Icc 19 (J - 1), ((j : ℕ) : ℝ) ^ 2 / 2 := by
    refine Finset.sum_le_sum (fun j hj => ?_)
    rw [Finset.mem_Icc] at hj
    have h4 : 4 ≤ j := by omega
    have hneg : occW j ≤ 0 := occW_nonpos_of_four h4
    rw [abs_of_nonpos hneg]
    unfold occW
    have hjR : (4 : ℝ) ≤ (j : ℝ) := by exact_mod_cast h4
    nlinarith [hjR]
  have h2 : ∑ j ∈ Finset.Icc 19 (J - 1), ((j : ℕ) : ℝ) ^ 2 / 2
      ≤ ∑ j ∈ Finset.range (J + 1), ((j : ℕ) : ℝ) ^ 2 / 2 := by
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
    · intro j hj
      rw [Finset.mem_Icc] at hj
      rw [Finset.mem_range]
      omega
    · intro j _ _
      positivity
  have h3 : ∑ j ∈ Finset.range (J + 1), ((j : ℕ) : ℝ) ^ 2 / 2
      = (1 / 2 : ℝ) * ∑ j ∈ Finset.range (J + 1), ((j : ℕ) : ℝ) ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  have h4 := sum_sq_range_le J hJ13
  rw [h3] at h2
  linarith

/-- `exp (1/11) ≤ 11/10`. -/
private lemma exp_one_div_eleven_le : Real.exp ((1 : ℝ) / 11) ≤ 11 / 10 := by
  have h := Real.exp_bound' (x := (1 : ℝ) / 11) (by norm_num) (by norm_num) (n := 3) (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  linarith

/-- `1/11 ≤ log 5 - 1`. -/
private lemma one_div_eleven_le_log_five_sub_one : (1 : ℝ) / 11 ≤ Real.log 5 - 1 := by
  have h5 : Real.exp (1 + (1 : ℝ) / 11) ≤ 5 := by
    rw [Real.exp_add]
    have h2 := exp_one_div_eleven_le
    have h1 := exp_one_le_68_div_25
    have h3 : Real.exp 1 * Real.exp ((1 : ℝ) / 11) ≤ (68 / 25) * (11 / 10) := by
      exact mul_le_mul h1 h2 (Real.exp_pos _).le (by norm_num)
    have h4 : (68 / 25 : ℝ) * (11 / 10) ≤ 5 := by norm_num
    linarith
  have hlog := (Real.le_log_iff_exp_le (by norm_num : (0 : ℝ) < 5)).mpr h5
  linarith

/-- The expectation commutes with a finite sum. -/
private lemma expect_finset_sum {Ω : Type*} [Fintype Ω] (P : FinSpace Ω) {ι : Type*}
    (s : Finset ι) (X : ι → Ω → ℝ) :
    P.expect (fun ω => ∑ i ∈ s, X i ω) = ∑ i ∈ s, P.expect (X i) := by
  classical
  simp only [FinSpace.expect, Finset.mul_sum]
  rw [Finset.sum_comm]

/-- A two-event union bound. -/
private lemma prob_union_le {Ω : Type*} [Fintype Ω] (P : FinSpace Ω) (A B : Set Ω) :
    P.prob (A ∪ B) ≤ P.prob A + P.prob B := by
  classical
  rw [FinSpace.prob, FinSpace.prob, FinSpace.prob, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum (fun ω _ => ?_)
  by_cases hA : ω ∈ A
  · have hAB : ω ∈ A ∪ B := Or.inl hA
    rw [Set.indicator_of_mem (s := A ∪ B) (f := P.mass) hAB,
      Set.indicator_of_mem (s := A) (f := P.mass) hA]
    linarith [FinSpace.ind_nonneg P B ω]
  · by_cases hB : ω ∈ B
    · have hAB : ω ∈ A ∪ B := Or.inr hB
      rw [Set.indicator_of_mem (s := A ∪ B) (f := P.mass) hAB,
        Set.indicator_of_notMem (s := A) (f := P.mass) hA,
        Set.indicator_of_mem (s := B) (f := P.mass) hB]
      linarith [P.mass_nonneg ω]
    · rw [Set.indicator_of_notMem (s := A) (f := P.mass) hA,
        Set.indicator_of_notMem (s := B) (f := P.mass) hB,
        Set.indicator_of_notMem (s := A ∪ B) (f := P.mass) (by simp [hA, hB])]
      norm_num

set_option maxHeartbeats 4000000 in
theorem ncp_tail_bound {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {k D : ℕ} (hk : 0 < k) (hD : 0 < D) (hDk : D ≤ 2 * k) (hkD : (k : ℝ) ≤ 2 * D)
    [Nonempty (V → Fin k)] (hdeg : ∀ x : V, G.degree x ≤ D) (v : V)
    {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (hsp : (δ / 2) * (D : ℝ) ^ 2 / 2 ≤ ((nonAdjPairs G v).card : ℝ) / 2)
    (hbig : (10 : ℝ) ^ 6 * (Real.log ((D : ℝ) + 2)) ^ 8 ≤ δ ^ 2 * (D : ℝ)) :
    (colSpace (V := V) k).prob {f : V → Fin k |
        (1 / 3) * ((1 / 6) * ncpOmega G k D v)
          ≤ |(occSlice G f v D - occSlice G f v ncpJ)
              - (colSpace (V := V) k).expect (fun f => occSlice G f v D - occSlice G f v ncpJ)|}
      ≤ Real.exp (-((Real.log ((D : ℝ) + 2)) ^ 4) / 5000 - 2) := by
  classical
  -- ===================== 0. Setup =====================
  set L : ℝ := ncpL D with hLdef
  set T : ℝ := ncpT D with hTdef
  set J : ℕ := ncpJlev D with hJdef
  set R : ℝ := ncpRR D with hRdef
  set m : ℝ := ((nonAdjPairs G v).card : ℝ) / 2 with hmdef
  set om : ℝ := ncpOmega G k D v with homdef
  set t : ℝ := (1 / 3) * ((1 / 6) * om) with htdef
  set Y : (V → Fin k) → ℝ := fun f => occSlice G f v D - occSlice G f v ncpJ with hYdef
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hDR : (0 : ℝ) < (D : ℝ) := by exact_mod_cast hD
  -- ===================== 1. log (D+2) ≥ 44 =====================
  have hδ2 : δ ^ 2 ≤ 1 := by nlinarith [hδ0, hδ1]
  have hbig' : (10 : ℝ) ^ 6 * (Real.log ((D : ℝ) + 2)) ^ 8 ≤ (D : ℝ) := by
    have h3 := mul_le_mul_of_nonneg_right hδ2 (le_of_lt hDR)
    have h4 : δ ^ 2 * (D : ℝ) ≤ (D : ℝ) := by simpa using h3
    linarith
  have hL44 : 44 ≤ L := by
    rw [hLdef]
    exact log_large_of_growth (by exact_mod_cast hD : (1 : ℝ) ≤ (D : ℝ)) hbig'
  have hL44' : 44 ≤ Real.log ((D : ℝ) + 2) := by
    have h := hL44
    rw [hLdef, ncpL] at h
    exact h
  -- ===================== 2. D ≥ 18 =====================
  have hD18 : ncpJ ≤ D := by
    have hexp : Real.exp 44 ≤ (D : ℝ) + 2 :=
      (Real.le_log_iff_exp_le (by positivity : (0 : ℝ) < (D : ℝ) + 2)).mp hL44'
    have h45 : (45 : ℝ) ≤ (D : ℝ) + 2 := by linarith [Real.add_one_le_exp 44, hexp]
    have h43 : (43 : ℝ) ≤ (D : ℝ) := by linarith
    have h43n : 43 ≤ D := by exact_mod_cast h43
    simp only [ncpJ]
    omega
  -- ===================== 3. the explicit shape of `ω`, `t` =====================
  have hom' : om = m / (k : ℝ) * (((k : ℝ) - 1) / (k : ℝ)) ^ (2 * D) := by
    rw [homdef, ncpOmega, hmdef]; ring
  have ht' : t = (m / (k : ℝ)) * (((k : ℝ) - 1) / (k : ℝ)) ^ (2 * D) / 18 := by
    rw [htdef, hom']; ring
  have hm_nonneg : 0 ≤ m := by rw [hmdef]; positivity
  have hk1R : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hom_nonneg : 0 ≤ om := by
    rw [hom']
    exact mul_nonneg (div_nonneg hm_nonneg (le_of_lt hkR))
      (pow_nonneg (div_nonneg (by linarith) (le_of_lt hkR)) _)
  have ht_nonneg : 0 ≤ t := by
    rw [htdef]
    exact mul_nonneg (by norm_num) (mul_nonneg (by norm_num) hom_nonneg)
  -- `D ≥ 10^6`, `k ≥ 5`, and the crude power bound
  have hDge6 : 1000000 ≤ D := by
    have hL1 : (1 : ℝ) ≤ L := by linarith
    have hL8 : (1 : ℝ) ≤ L ^ 8 := one_le_pow₀ hL1
    have h1 : (10 : ℝ) ^ 6 ≤ (10 : ℝ) ^ 6 * L ^ 8 := le_mul_of_one_le_right (by norm_num) hL8
    have hbigL : (10 : ℝ) ^ 6 * L ^ 8 ≤ (D : ℝ) := by
      rw [hLdef, ncpL]; exact hbig'
    have h2 : (10 : ℝ) ^ 6 ≤ (D : ℝ) := le_trans h1 hbigL
    have h3 : ((1000000 : ℕ) : ℝ) ≤ (D : ℝ) := by norm_num at h2 ⊢; exact h2
    exact_mod_cast h3
  have hk5 : 5 ≤ k := by omega
  have hpow_ratio : (1 : ℝ) / 256 ≤ (((k : ℝ) - 1) / (k : ℝ)) ^ (2 * D) :=
    pow_ratio_ge hk5 hDk
  have hmk_le : m / (k : ℝ) ≤ 4608 * t := by
    have haux : (0 : ℝ) ≤ m / (k : ℝ) := by positivity
    rw [ht']
    nlinarith [hpow_ratio, haux]
  -- ===================== 4. the pointwise identity and sign =====================
  have hYpoint : ∀ f : V → Fin k, Y f = ∑ j ∈ Finset.Icc 19 D, occW j * (ncpN G f v j : ℝ) := by
    intro f
    have h := occSlice_sub_eq G hD18 f v
    have h19 : ncpJ + 1 = 19 := by norm_num [ncpJ]
    rw [h19] at h
    exact h
  have hYnonpos : ∀ f : V → Fin k, Y f ≤ 0 := by
    intro f
    rw [hYpoint f]
    refine Finset.sum_nonpos (fun j hj => ?_)
    rw [Finset.mem_Icc] at hj
    exact mul_nonpos_of_nonpos_of_nonneg (le_of_lt (occW_neg_of_nineteen hj.1)) (Nat.cast_nonneg _)
  have hYneg : ∀ f : V → Fin k, -Y f
      = ∑ j ∈ Finset.Icc 19 D, (-(occW j)) * (ncpN G f v j : ℝ) := by
    intro f
    rw [hYpoint f, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  -- ===================== 5. the mean of `Y` =====================
  have hYeq : Y = fun f => ∑ j ∈ Finset.Icc 19 D, occW j * (ncpN G f v j : ℝ) := funext hYpoint
  have hEY_expand : (colSpace (V := V) k).expect Y
      = ∑ j ∈ Finset.Icc 19 D, occW j *
          (colSpace (V := V) k).expect (fun f => (ncpN G f v j : ℝ)) := by
    rw [hYeq, expect_finset_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    simp only [FinSpace.expect]
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun f _ => by ring)
  have hEY_nonpos : (colSpace (V := V) k).expect Y ≤ 0 := by
    have h := FinSpace.expect_mono (colSpace (V := V) k) (fun f => hYnonpos f)
    rwa [FinSpace.expect_const] at h
  have hμ_eq : ∀ j : ℕ, ncpMuT G k v j = (m / (k : ℝ)) * ((2 : ℝ) ^ j / (j.factorial : ℝ)) := by
    intro j
    rw [ncpMuT, hmdef]; ring
  have hmins : ∀ j : ℕ, 2 ≤ j → (0 : ℝ) ≤ ncpMuT G k v j := by
    intro j hj
    rw [hμ_eq j]
    exact mul_nonneg (div_nonneg hm_nonneg (le_of_lt hkR)) (by positivity)
  have hμsum_gen : ∀ n : ℕ, ∑ j ∈ Finset.Icc 19 n, (-(occW j)) * ncpMuT G k v j
      ≤ m / (k : ℝ) * ((1 : ℝ) / 10000000) := by
    intro n
    have hsplit : ∑ j ∈ Finset.Icc 19 n, (-(occW j)) * ncpMuT G k v j
        = (m / (k : ℝ)) * ∑ j ∈ Finset.Icc 19 n,
            (-(occW j)) * ((2 : ℝ) ^ j / (j.factorial : ℝ)) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [hμ_eq j]; ring
    rw [hsplit]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have hseries := ncp_series_bound n
    calc ∑ j ∈ Finset.Icc 19 n, (-(occW j)) * ((2 : ℝ) ^ j / (j.factorial : ℝ))
        = ∑ j ∈ Finset.Icc 19 n, |occW j| * ((2 : ℝ) ^ j / (j.factorial : ℝ)) := by
          refine Finset.sum_congr rfl (fun j hj => ?_)
          rw [Finset.mem_Icc] at hj
          rw [abs_of_neg (occW_neg_of_nineteen hj.1)]
      _ ≤ (1 : ℝ) / 10000000 := hseries
  have hμsum := hμsum_gen (J - 1)
  have hEY_lower0 : -(∑ j ∈ Finset.Icc 19 D, (-(occW j)) * ncpMuT G k v j)
      ≤ (colSpace (V := V) k).expect Y := by
    rw [hEY_expand, ← Finset.sum_neg_distrib]
    refine Finset.sum_le_sum (fun j hj => ?_)
    rw [Finset.mem_Icc] at hj
    have hμj : (colSpace (V := V) k).expect (fun f => (ncpN G f v j : ℝ)) ≤ ncpMuT G k v j :=
      ncpN_expect_le (G := G) hk hDk hdeg v (by omega : 2 ≤ j)
    have hE0 : 0 ≤ (colSpace (V := V) k).expect (fun f => (ncpN G f v j : ℝ)) :=
      FinSpace.expect_nonneg _ (fun f => Nat.cast_nonneg _)
    have hw : occW j < 0 := occW_neg_of_nineteen hj.1
    nlinarith [hμj, hE0, hw]
  have hEY_lower : -(t / 1000) ≤ (colSpace (V := V) k).expect Y := by
    have h2 : m / (k : ℝ) * ((1 : ℝ) / 10000000) ≤ t / 1000 := by
      have h3 := mul_le_mul_of_nonneg_right hmk_le (by norm_num : (0 : ℝ) ≤ (1 : ℝ) / 10000000)
      linarith
    linarith [hEY_lower0, hμsum_gen D, h2]
  -- ===================== 6. the deviation event is contained in `{-Y ≥ t}` =====================
  have hevent_sub : {f : V → Fin k | t ≤ |Y f - (colSpace (V := V) k).expect Y|}
      ⊆ {f : V → Fin k | t ≤ -Y f} := by
    intro f hf
    simp only [Set.mem_ofPred_eq] at hf ⊢
    rcases lt_or_ge 0 (Y f - (colSpace (V := V) k).expect Y) with hpos | hneg
    · rw [abs_of_pos hpos] at hf
      exfalso
      linarith [hEY_lower, hYnonpos f, hf]
    · rw [abs_of_nonpos hneg] at hf
      linarith [hEY_nonpos]
  -- ===================== 7. the thresholds =====================
  set Kf : ℕ → ℕ := fun j => max (⌈5 * ncpMuT G k v j⌉₊) ⌈R⌉₊ with hKfdef
  have hJ19 : 19 ≤ J := by rw [hJdef, ncpJlev]; omega
  have hR_ge : (132 : ℝ) ≤ R := by
    rw [hRdef, ncpRR]
    have hT2 : (2 : ℝ) ≤ ncpT D := by
      rw [ncpT]
      have h : (0 : ℝ) ≤ (ncpL D) ^ 4 / 5000 := by positivity
      linarith
    have hlog0 : (0 : ℝ) ≤ Real.log (2 * (ncpJlev D)) := by
      apply Real.log_nonneg
      have h2 : (19 : ℕ) ≤ ncpJlev D := by rw [ncpJlev]; omega
      have h3 : (19 : ℝ) ≤ (ncpJlev D : ℝ) := by exact_mod_cast h2
      linarith
    linarith
  have hRpos : 0 < R := by linarith
  have hKf_pos : ∀ j, 0 < Kf j := by
    intro j
    rw [hKfdef]
    have h2 : (1 : ℝ) ≤ (⌈R⌉₊ : ℝ) := le_trans (by linarith : (1 : ℝ) ≤ R) (Nat.le_ceil R)
    have h3 : 1 ≤ ⌈R⌉₊ := by exact_mod_cast h2
    exact lt_of_lt_of_le h3 (le_max_right _ _)
  have hKf_ge_R : ∀ j, R ≤ (Kf j : ℝ) := by
    intro j
    rw [hKfdef]
    refine le_trans (Nat.le_ceil R) ?_
    exact_mod_cast le_max_right _ _
  have hKf_ge_mu : ∀ j, 5 * ncpMuT G k v j ≤ (Kf j : ℝ) := by
    intro j
    rw [hKfdef]
    refine le_trans (Nat.le_ceil (5 * ncpMuT G k v j)) ?_
    exact_mod_cast le_max_left _ _
  have hKf_le : ∀ j, (Kf j : ℝ) ≤ 5 * ncpMuT G k v j + (R + 4) := by
    intro j
    have h6 : (⌈5 * ncpMuT G k v j⌉₊ : ℝ) ≤ 5 * ncpMuT G k v j + 1 := by
      have hμ0 : (0 : ℝ) ≤ ncpMuT G k v j := by
        rw [hμ_eq j]
        exact mul_nonneg (div_nonneg hm_nonneg (le_of_lt hkR)) (by positivity)
      have := Nat.ceil_lt_add_one (by linarith : (0 : ℝ) ≤ 5 * ncpMuT G k v j)
      linarith
    have h7 : (⌈R⌉₊ : ℝ) ≤ R + 1 := by
      have := Nat.ceil_lt_add_one (le_of_lt hRpos); linarith
    have h2 : ((max (⌈5 * ncpMuT G k v j⌉₊) ⌈R⌉₊ : ℕ) : ℝ)
        ≤ (⌈5 * ncpMuT G k v j⌉₊ : ℝ) + (⌈R⌉₊ : ℝ) := by
      have h := max_le (Nat.le_add_right (⌈5 * ncpMuT G k v j⌉₊) ⌈R⌉₊)
        (Nat.le_add_left ⌈R⌉₊ ⌈5 * ncpMuT G k v j⌉₊)
      exact_mod_cast h
    rw [hKfdef]
    linarith
  -- ===================== 8. the budget =====================
  have hbudget : ∑ j ∈ Finset.Icc 19 (J - 1), (-(occW j)) * (Kf j : ℝ) ≤ t := by
    have hterm : ∑ j ∈ Finset.Icc 19 (J - 1), (-(occW j)) * (Kf j : ℝ)
        ≤ 5 * (∑ j ∈ Finset.Icc 19 (J - 1), (-(occW j)) * ncpMuT G k v j)
          + (R + 4) * (∑ j ∈ Finset.Icc 19 (J - 1), (-(occW j))) := by
      have h1 : ∀ j ∈ Finset.Icc 19 (J - 1),
          (-(occW j)) * (Kf j : ℝ) ≤ (-(occW j)) * (5 * ncpMuT G k v j + (R + 4)) := by
        intro j hj
        rw [Finset.mem_Icc] at hj
        exact mul_le_mul_of_nonneg_left (hKf_le j) (by linarith [occW_neg_of_nineteen hj.1])
      calc ∑ j ∈ Finset.Icc 19 (J - 1), (-(occW j)) * (Kf j : ℝ)
          ≤ ∑ j ∈ Finset.Icc 19 (J - 1),
              (-(occW j)) * (5 * ncpMuT G k v j + (R + 4)) := Finset.sum_le_sum h1
        _ = 5 * (∑ j ∈ Finset.Icc 19 (J - 1), (-(occW j)) * ncpMuT G k v j)
              + (R + 4) * (∑ j ∈ Finset.Icc 19 (J - 1), (-(occW j))) := by
            rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
            exact Finset.sum_congr rfl (fun j _ => by ring)
    have hJ19 : 19 ≤ J := by rw [hJdef, ncpJlev]; omega
    have hsumabs : ∑ j ∈ Finset.Icc 19 (J - 1), (-(occW j)) ≤ (3 / 16 : ℝ) * (J : ℝ) ^ 3 := by
      have h1 : ∑ j ∈ Finset.Icc 19 (J - 1), (-(occW j))
          = ∑ j ∈ Finset.Icc 19 (J - 1), |occW j| := by
        refine Finset.sum_congr rfl (fun j hj => ?_)
        rw [Finset.mem_Icc] at hj
        rw [abs_of_neg (occW_neg_of_nineteen hj.1)]
      rw [h1]
      exact sum_absoccW_le J hJ19
    have hbud2 : 5 * (∑ j ∈ Finset.Icc 19 (J - 1), (-(occW j)) * ncpMuT G k v j)
        + (R + 4) * (∑ j ∈ Finset.Icc 19 (J - 1), (-(occW j)))
        ≤ 5 * (4608 * t * ((1 : ℝ) / 10000000)) + (R + 4) * ((3 / 16 : ℝ) * (J : ℝ) ^ 3) := by
      have h1 := mul_le_mul_of_nonneg_right hmk_le (by norm_num : (0 : ℝ) ≤ (1 : ℝ) / 10000000)
      have h2 : (0 : ℝ) ≤ R + 4 := by linarith
      have h3 := mul_le_mul_of_nonneg_left hμsum (by norm_num : (0 : ℝ) ≤ 5)
      have h4 := mul_le_mul_of_nonneg_left hsumabs h2
      linarith
    have hbud3 : 5 * (4608 * t * ((1 : ℝ) / 10000000)) + (R + 4) * ((3 / 16 : ℝ) * (J : ℝ) ^ 3) ≤ t := by
      have hRL : R = ncpRR D := by rw [hRdef]
      have hJL : J = ncpJlev D := by rw [hJdef]
      have hL' : 44 ≤ ncpL D := by rw [← hLdef]; exact hL44
      have hb1 := ncp_budget_arith D hL'
      have hb2 := ncp_omega_lower (G := G) hk hD hDk hkD v hδ0 hδ1 hsp hbig hL'
      rw [← hRL, ← hJL] at hb1
      have hb1' : (R + 4) * (3 / 16 : ℝ) * (J : ℝ) ^ 3 ≤ (3 / 16 : ℝ) * ((1 / 2 : ℝ) * L ^ 4 * Real.sqrt (D : ℝ)) := by
        have h := hb1
        rw [← hLdef] at h
        nlinarith [h]
      have hb2' : (3 / 16 : ℝ) * ((1 / 2 : ℝ) * L ^ 4 * Real.sqrt (D : ℝ)) ≤ (3 / 16 : ℝ) * ((1 / 2 : ℝ) * (10 * t)) := by
        have hsqrt : L ^ 4 * Real.sqrt (D : ℝ) ≤ 10 * t := by
          have h := hb2
          rw [show (1 / 10 : ℝ) * (ncpL D) ^ 4 * Real.sqrt (D : ℝ)
              = (1 / 10 : ℝ) * ((ncpL D) ^ 4 * Real.sqrt (D : ℝ)) by ring] at h
          rw [htdef, homdef]
          nlinarith [h]
        nlinarith [hsqrt]
      have hb3 : (3 / 16 : ℝ) * ((1 / 2 : ℝ) * (10 * t)) = (15 / 16 : ℝ) * t := by ring
      have h1 : 5 * (4608 * t * ((1 : ℝ) / 10000000)) = (1152 / 500000 : ℝ) * t := by ring
      nlinarith [hb1', hb2', hb3, h1, ht_nonneg]
    linarith [hterm, hbud2, hbud3]
  -- ===================== 9. the large-class event =====================
  set Big : Set (V → Fin k) := {f : V → Fin k | ∃ c : Fin k, J ≤ colourClassCount G f v c} with hBigdef
  have hBig_bound : (colSpace (V := V) k).prob Big ≤ Real.exp (-T) / 2 := by
    rw [hBigdef]
    have hsub : {f : V → Fin k | ∃ c : Fin k, J ≤ colourClassCount G f v c}
        ⊆ {f : V → Fin k | 1 ≤ occRaw (G.neighborFinset v) f J} := by
      intro f hf
      obtain ⟨c, hc⟩ := hf
      simp only [Set.mem_ofPred_eq]
      rw [occRaw, Nat.one_le_iff_ne_zero, Finset.card_ne_zero]
      refine ⟨c, ?_⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      refine le_trans hc (Finset.card_le_card ?_)
      intro x hx
      rw [Finset.mem_filter] at hx ⊢
      exact ⟨hx.1, hx.2.2⟩
    have hJpos : 0 < J := by omega
    have hK1 : (1 : ℕ) = 1 := rfl
    have htail := occRaw_tail (V := V) (k := k) (G.neighborFinset v) (j := J) (K := 1) hJpos (by norm_num)
    have hd := hdeg v
    have hd' : ((G.neighborFinset v).card : ℝ) = (G.degree v : ℝ) := by
      rw [SimpleGraph.card_neighborFinset_eq_degree]
    have hdD : ((G.neighborFinset v).card : ℝ) ≤ 2 * (k : ℝ) := by
      rw [hd']
      have h1 : (G.degree v : ℝ) ≤ (D : ℝ) := by exact_mod_cast hd
      have h2 : (D : ℝ) ≤ 2 * (k : ℝ) := by exact_mod_cast hDk
      linarith
    have hk2D : (k : ℝ) ≤ 2 * (D : ℝ) := hkD
    have hfac : (0 : ℝ) < (J.factorial : ℝ) := by positivity
    have h2J : (0 : ℝ) < (2 : ℝ) ^ J := by positivity
    have hkey : ((k : ℝ) * ((((G.neighborFinset v).card : ℝ) / (k : ℝ)) ^ J / (J.factorial : ℝ)))
        ≤ 2 * (D : ℝ) * ((2 : ℝ) ^ J / (J.factorial : ℝ)) := by
      have hbase2 : ((G.neighborFinset v).card : ℝ) / (k : ℝ) ≤ 2 := by
        rw [div_le_iff₀ hkR]; linarith [hdD]
      have h1 : (((G.neighborFinset v).card : ℝ) / (k : ℝ)) ^ J ≤ (2 : ℝ) ^ J :=
        pow_le_pow_left₀ (div_nonneg (Nat.cast_nonneg _) (le_of_lt hkR)) hbase2 J
      calc (k : ℝ) * ((((G.neighborFinset v).card : ℝ) / (k : ℝ)) ^ J / (J.factorial : ℝ))
          ≤ (k : ℝ) * ((2 : ℝ) ^ J / (J.factorial : ℝ)) :=
            mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right h1 hfac.le) (le_of_lt hkR)
        _ ≤ (2 * (D : ℝ)) * ((2 : ℝ) ^ J / (J.factorial : ℝ)) := by
            refine mul_le_mul_of_nonneg_right hkD (by positivity)
    have hlev := ncp_level_bound D (by rw [← hLdef]; exact hL44)
    have hlev' : 4 * (D : ℝ) * (2 : ℝ) ^ J / ((J.factorial : ℝ)) ≤ Real.exp (-T) := by
      rw [hJdef, hTdef]
      exact hlev
    calc (colSpace (V := V) k).prob {f : V → Fin k | ∃ c : Fin k, J ≤ colourClassCount G f v c}
        ≤ (colSpace (V := V) k).prob {f : V → Fin k | 1 ≤ occRaw (G.neighborFinset v) f J} :=
          FinSpace.prob_mono _ hsub
      _ ≤ ((k : ℝ) * ((((G.neighborFinset v).card : ℝ) / (k : ℝ)) ^ J / (J.factorial : ℝ))) ^ 1
            / (Nat.factorial 1 : ℝ) := htail
      _ = (k : ℝ) * ((((G.neighborFinset v).card : ℝ) / (k : ℝ)) ^ J / (J.factorial : ℝ)) := by
          rw [pow_one, Nat.factorial_one, Nat.cast_one, div_one]
      _ ≤ 2 * (D : ℝ) * ((2 : ℝ) ^ J / (J.factorial : ℝ)) := hkey
      _ = 4 * (D : ℝ) * (2 : ℝ) ^ J / ((J.factorial : ℝ)) / 2 := by ring
      _ ≤ Real.exp (-T) / 2 := by linarith [hlev']
  -- ===================== 10. the slice events =====================
  have hlog5 : (1 : ℝ) / 11 ≤ Real.log 5 - 1 := one_div_eleven_le_log_five_sub_one
  have hExponent : ∀ j : ℕ, Real.exp (-(T + Real.log (2 * (J : ℝ)) + 10)) ≤
      Real.exp (-(T + Real.log (2 * (J : ℝ)) + 10)) := fun _ => le_refl _
  have hslice_bound : ∀ j ∈ Finset.Icc 19 (J - 1),
      (colSpace (V := V) k).prob {f : V → Fin k | (Kf j : ℝ) ≤ (ncpN G f v j : ℝ)}
        ≤ Real.exp (-(T + Real.log (2 * (J : ℝ)) + 10)) := by
    intro j hj
    rw [Finset.mem_Icc] at hj
    have hj2 : 2 ≤ j := by omega
    have hprob := ncpN_tail (G := G) hk hDk hdeg v hj2 (hKf_pos j)
    have hev : {f : V → Fin k | (Kf j : ℝ) ≤ (ncpN G f v j : ℝ)}
        = {f : V → Fin k | Kf j ≤ ncpN G f v j} := by
      ext f
      simp only [Set.mem_ofPred_eq]
      exact Nat.cast_le
    rw [hev]
    refine le_trans hprob ?_
    -- `μ^K/K! ≤ (eμ/K)^K ≤ (5/e)^{-K} ≤ exp (-(T + log (2J) + 10))`
    have hKpos : 0 < Kf j := hKf_pos j
    have hμ0 : 0 ≤ ncpMuT G k v j := hmins j hj2
    have hfac_st : ((Kf j : ℝ) / Real.exp 1) ^ (Kf j) ≤ ((Kf j).factorial : ℝ) := by
      have h := Stirling.le_factorial_stirling (Kf j)
      have h1 : (1 : ℝ) ≤ Real.sqrt (2 * Real.pi * (Kf j : ℝ)) := by
        rw [Real.one_le_sqrt]
        have : (1 : ℝ) ≤ (Kf j : ℝ) := by exact_mod_cast hKpos
        nlinarith [Real.pi_gt_three, this]
      have h2 : ((Kf j : ℝ) / Real.exp 1) ^ (Kf j)
          ≤ Real.sqrt (2 * Real.pi * (Kf j : ℝ)) * ((Kf j : ℝ) / Real.exp 1) ^ (Kf j) :=
        le_mul_of_one_le_left
          (pow_nonneg (div_nonneg (Nat.cast_nonneg (Kf j)) (le_of_lt (Real.exp_pos 1))) _) h1
      linarith [h, h2]
    have hstep1 : (ncpMuT G k v j) ^ (Kf j) / ((Kf j).factorial : ℝ)
        ≤ (Real.exp 1 * ncpMuT G k v j / (Kf j : ℝ)) ^ (Kf j) := by
      have hK0 : (0 : ℝ) < (Kf j : ℝ) := by exact_mod_cast hKpos
      have hKfac : (0 : ℝ) < ((Kf j).factorial : ℝ) := by positivity
      have hpw : (0 : ℝ) < ((Kf j : ℝ) / Real.exp 1) ^ (Kf j) := by positivity
      have h1 : (ncpMuT G k v j) ^ (Kf j) / ((Kf j).factorial : ℝ)
          ≤ (ncpMuT G k v j) ^ (Kf j) / (((Kf j : ℝ) / Real.exp 1) ^ (Kf j)) := by
        rw [div_le_div_iff₀ hKfac hpw]
        exact mul_le_mul_of_nonneg_left hfac_st (by positivity)
      have h2 : (ncpMuT G k v j) ^ (Kf j) / (((Kf j : ℝ) / Real.exp 1) ^ (Kf j))
          = (Real.exp 1 * ncpMuT G k v j / (Kf j : ℝ)) ^ (Kf j) := by
        rw [div_eq_iff (pow_ne_zero _ (by positivity : ((Kf j : ℝ) / Real.exp 1) ≠ 0))]
        simp only [div_pow, mul_pow]
        field_simp
      rw [h2] at h1
      exact h1
    have hstep2 : (Real.exp 1 * ncpMuT G k v j / (Kf j : ℝ)) ^ (Kf j)
        ≤ ((5 : ℝ) / Real.exp 1) ^ (-(Kf j) : ℤ) := by
      have hmul : (Real.exp 1 * ncpMuT G k v j / (Kf j : ℝ)) ^ (Kf j)
          * ((5 : ℝ) / Real.exp 1) ^ (Kf j) ≤ 1 := by
        rw [← mul_pow]
        have hbase_eq : (Real.exp 1 * ncpMuT G k v j / (Kf j : ℝ)) * ((5 : ℝ) / Real.exp 1)
            = 5 * ncpMuT G k v j / (Kf j : ℝ) := by
          field_simp
        rw [hbase_eq]
        have h5μ : 5 * ncpMuT G k v j / (Kf j : ℝ) ≤ 1 := by
          rw [div_le_one (by positivity : (0 : ℝ) < (Kf j : ℝ))]
          exact hKf_ge_mu j
        have h0 : (0 : ℝ) ≤ 5 * ncpMuT G k v j / (Kf j : ℝ) := by
          have := hmins j hj2
          positivity
        exact pow_le_one₀ h0 h5μ
      rw [zpow_neg, inv_eq_one_div]
      exact (le_div_iff₀ (by positivity : (0 : ℝ) < ((5 : ℝ) / Real.exp 1) ^ (Kf j))).mpr hmul
    have harg : (0 : ℝ) ≤ T + Real.log (2 * (J : ℝ)) + 10 := by
      have hT2 : (0 : ℝ) < T := by rw [hTdef, ncpT]; positivity
      have hJ1 : (1 : ℕ) ≤ J := by omega
      have hJ1R : (1 : ℝ) ≤ (J : ℝ) := by exact_mod_cast hJ1
      have h1 : (0 : ℝ) < Real.log (2 * (J : ℝ)) := Real.log_pos (by linarith)
      linarith
    have hstep3 : ((5 : ℝ) / Real.exp 1) ^ (-(Kf j) : ℤ)
        ≤ Real.exp (-(T + Real.log (2 * (J : ℝ)) + 10)) := by
      have key : ((5 : ℝ) / Real.exp 1) ^ (Kf j)
          = Real.exp ((Kf j : ℝ) * Real.log ((5 : ℝ) / Real.exp 1)) := by
        rw [← Real.exp_log (by positivity : (0 : ℝ) < ((5 : ℝ) / Real.exp 1) ^ (Kf j)),
          Real.log_pow]
      have hRj : R ≤ (Kf j : ℝ) := hKf_ge_R j
      have hlog5e : (1 : ℝ) / 11 ≤ Real.log ((5 : ℝ) / Real.exp 1) := by
        rw [Real.log_div (by norm_num : (5 : ℝ) ≠ 0) (Real.exp_pos 1).ne', Real.log_exp]
        linarith [hlog5]
      have h6 : R = 11 * (T + Real.log (2 * (J : ℝ)) + 10) := by
        rw [hRdef, ncpRR, hTdef, ← hJdef]
      rw [h6] at hRj
      have hkey2 : Real.exp (T + Real.log (2 * (J : ℝ)) + 10)
          ≤ ((5 : ℝ) / Real.exp 1) ^ (Kf j) := by
        rw [key]
        refine Real.exp_le_exp.mpr ?_
        nlinarith [hRj, hlog5e, harg]
      rw [zpow_neg, inv_eq_one_div, Real.exp_neg, inv_eq_one_div]
      exact one_div_le_one_div_of_le (Real.exp_pos _) hkey2
    calc (ncpMuT G k v j) ^ (Kf j) / ((Kf j).factorial : ℝ)
        ≤ (Real.exp 1 * ncpMuT G k v j / (Kf j : ℝ)) ^ (Kf j) := hstep1
      _ ≤ ((5 : ℝ) / Real.exp 1) ^ (-(Kf j) : ℤ) := hstep2
      _ ≤ Real.exp (-(T + Real.log (2 * (J : ℝ)) + 10)) := hstep3
  -- ===================== 11. the union bound =====================
  set Slice : Set (V → Fin k) := ⋃ j ∈ Finset.Icc 19 (J - 1),
      {f : V → Fin k | (Kf j : ℝ) ≤ (ncpN G f v j : ℝ)} with hSlicedef
  have hcontain : {f : V → Fin k | t ≤ |Y f - (colSpace (V := V) k).expect Y|} ⊆ Big ∪ Slice := by
    intro f hf
    have hYge : t ≤ -Y f := hevent_sub hf
    rw [hBigdef]
    by_cases hB : ∃ c : Fin k, J ≤ colourClassCount G f v c
    · exact Or.inl hB
    · refine Or.inr ?_
      rw [hSlicedef]
      have hzero : ∀ j : ℕ, J ≤ j → ncpN G f v j = 0 := by
        intro j hj
        rw [ncpN, Finset.card_eq_zero]
        ext c
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
        intro hjc
        exact absurd (le_trans hj hjc) (fun h => hB ⟨c, h⟩)
      -- if no slice reaches its threshold, `-Y` is bounded by the budget
      by_contra hcon
      simp only [Set.mem_iUnion, Set.mem_setOf_eq, not_exists, not_and, not_le] at hcon
      have hstep1 : -Y f ≤ ∑ j ∈ Finset.Icc 19 (J - 1), (-(occW j)) * (ncpN G f v j : ℝ) := by
        rw [hYneg f]
        have hdrop : ∑ j ∈ Finset.Icc 19 D, (-(occW j)) * (ncpN G f v j : ℝ)
            = ∑ j ∈ (Finset.Icc 19 D).filter (fun j => j ≤ J - 1),
                (-(occW j)) * (ncpN G f v j : ℝ) := by
          rw [Finset.sum_filter]
          refine Finset.sum_congr rfl (fun j hj => ?_)
          rw [Finset.mem_Icc] at hj
          by_cases hle : j ≤ J - 1
          · rw [if_pos hle]
          · rw [if_neg hle, hzero j (by omega)]
            ring
        rw [hdrop]
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
        · intro j hj
          rw [Finset.mem_filter, Finset.mem_Icc] at hj
          rw [Finset.mem_Icc]
          exact ⟨hj.1.1, hj.2⟩
        · intro j hj _
          rw [Finset.mem_Icc] at hj
          exact mul_nonneg (by linarith [occW_neg_of_nineteen hj.1]) (Nat.cast_nonneg _)
      have hstep2 : ∑ j ∈ Finset.Icc 19 (J - 1), (-(occW j)) * (ncpN G f v j : ℝ)
          ≤ ∑ j ∈ Finset.Icc 19 (J - 1), (-(occW j)) * ((Kf j : ℝ) - 1) := by
        refine Finset.sum_le_sum (fun j hj => ?_)
        have hlt : ncpN G f v j < Kf j := by exact_mod_cast (hcon j hj)
        rw [Finset.mem_Icc] at hj
        have hle : ncpN G f v j ≤ Kf j - 1 := by omega
        have hcast : ((ncpN G f v j : ℕ) : ℝ) ≤ ((Kf j : ℕ) : ℝ) - 1 := by
          rw [← Nat.cast_one, ← Nat.cast_sub (by omega : 1 ≤ Kf j)]
          exact_mod_cast hle
        exact mul_le_mul_of_nonneg_left hcast (by linarith [occW_neg_of_nineteen hj.1])
      have hsumocc : (135 : ℝ) ≤ ∑ j ∈ Finset.Icc 19 (J - 1), (-(occW j)) := by
        have hmem : 19 ∈ Finset.Icc 19 (J - 1) := by
          rw [Finset.mem_Icc]
          refine ⟨le_refl _, ?_⟩
          have h20 : 20 ≤ J := by rw [hJdef, ncpJlev]; omega
          omega
        have hval : (-(occW 19)) = 135 := by norm_num [occW]
        rw [← hval]
        refine Finset.single_le_sum (f := fun j => -(occW j)) (fun j hj => ?_) hmem
        rw [Finset.mem_Icc] at hj
        linarith [occW_neg_of_nineteen hj.1]
      have hstrict : ∑ j ∈ Finset.Icc 19 (J - 1), (-(occW j)) * ((Kf j : ℝ) - 1)
          ≤ ∑ j ∈ Finset.Icc 19 (J - 1), (-(occW j)) * (Kf j : ℝ) - 135 := by
        have hsplit : ∑ j ∈ Finset.Icc 19 (J - 1), (-(occW j)) * ((Kf j : ℝ) - 1)
            = ∑ j ∈ Finset.Icc 19 (J - 1), (-(occW j)) * (Kf j : ℝ)
              - ∑ j ∈ Finset.Icc 19 (J - 1), (-(occW j)) := by
          rw [← Finset.sum_sub_distrib]
          exact Finset.sum_congr rfl (fun j _ => by ring)
        rw [hsplit]
        linarith
      linarith [hYge, hstep1, hstep2, hstrict, hbudget]
  -- ===================== 12. conclusion =====================
  have hslice_prob : (colSpace (V := V) k).prob Slice
      ≤ (J - 19 : ℕ) * Real.exp (-(T + Real.log (2 * (J : ℝ)) + 10)) := by
    rw [hSlicedef]
    refine le_trans (FinSpace.prob_biUnion_le_sum _ _ _) ?_
    calc ∑ j ∈ Finset.Icc 19 (J - 1),
          (colSpace (V := V) k).prob {f : V → Fin k | (Kf j : ℝ) ≤ (ncpN G f v j : ℝ)}
        ≤ ∑ _j ∈ Finset.Icc 19 (J - 1), Real.exp (-(T + Real.log (2 * (J : ℝ)) + 10)) :=
          Finset.sum_le_sum hslice_bound
      _ = ((Finset.Icc 19 (J - 1)).card : ℝ) * Real.exp (-(T + Real.log (2 * (J : ℝ)) + 10)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (J - 19 : ℕ) * Real.exp (-(T + Real.log (2 * (J : ℝ)) + 10)) := by
          have hcard : (Finset.Icc 19 (J - 1)).card ≤ J - 19 := by
            rw [Nat.card_Icc]; omega
          have hpos : (0 : ℝ) ≤ Real.exp (-(T + Real.log (2 * (J : ℝ)) + 10)) := (Real.exp_pos _).le
          exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hpos
  have hfinal : (colSpace (V := V) k).prob Slice ≤ Real.exp (-T) / 2 := by
    have hJ2 : (0 : ℝ) < 2 * (J : ℝ) := by
      have : (0 : ℝ) < (J : ℝ) := by
        have hJ19' : (0 : ℕ) < J := by omega
        exact_mod_cast hJ19'
      linarith
    have hexp_eq : Real.exp (-(T + Real.log (2 * (J : ℝ)) + 10))
        = Real.exp (-T) * (1 / (2 * (J : ℝ))) * Real.exp (-10) := by
      rw [show -(T + Real.log (2 * (J : ℝ)) + 10)
          = -T + (-Real.log (2 * (J : ℝ))) + (-10) by ring, Real.exp_add, Real.exp_add]
      simp only [Real.exp_neg, Real.exp_log hJ2, inv_eq_one_div]
    rw [hexp_eq] at hslice_prob
    have h3 : ((J - 19 : ℕ) : ℝ) * ((1 / (2 * (J : ℝ))) * Real.exp (-10)) ≤ 1 / 2 := by
      have hle : ((J - 19 : ℕ) : ℝ) ≤ (J : ℝ) := by exact_mod_cast Nat.sub_le J 19
      have hexp10 : Real.exp (-10) ≤ 1 := by
        rw [Real.exp_le_one_iff]; norm_num
      calc ((J - 19 : ℕ) : ℝ) * ((1 / (2 * (J : ℝ))) * Real.exp (-10))
          ≤ ((J - 19 : ℕ) : ℝ) * ((1 / (2 * (J : ℝ))) * 1) := by
            refine mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left hexp10 (by positivity)) (by positivity)
        _ = ((J - 19 : ℕ) : ℝ) / (2 * (J : ℝ)) := by ring
        _ ≤ (J : ℝ) / (2 * (J : ℝ)) :=
            div_le_div_of_nonneg_right hle (by positivity)
        _ = 1 / 2 := by field_simp
    calc (colSpace (V := V) k).prob Slice
        ≤ ((J - 19 : ℕ) : ℝ) * (Real.exp (-T) * (1 / (2 * (J : ℝ))) * Real.exp (-10)) :=
          hslice_prob
      _ = Real.exp (-T) * (((J - 19 : ℕ) : ℝ) * ((1 / (2 * (J : ℝ))) * Real.exp (-10))) := by
          ring
      _ ≤ Real.exp (-T) * (1 / 2) := mul_le_mul_of_nonneg_left h3 (Real.exp_pos _).le
      _ = Real.exp (-T) / 2 := by ring
  have hsum_prob : (colSpace (V := V) k).prob (Big ∪ Slice)
      ≤ Real.exp (-T) / 2 + Real.exp (-T) / 2 := by
    refine le_trans (prob_union_le _ _ _) ?_
    linarith [hBig_bound, hfinal]
  have hmain := FinSpace.prob_mono (colSpace (V := V) k) hcontain
  have hgoal : (colSpace (V := V) k).prob {f : V → Fin k | t ≤ |Y f - (colSpace (V := V) k).expect Y|}
      ≤ Real.exp (-T) := by
    linarith [hmain, hsum_prob]
  -- translate back to the statement
  have hexpT : Real.exp (-((Real.log ((D : ℝ) + 2)) ^ 4) / 5000 - 2) = Real.exp (-T) := by
    rw [hTdef, ncpT, ncpL]
    congr 1
    ring
  rw [hexpT]
  exact hgoal

end Work.Deep.Sparse
