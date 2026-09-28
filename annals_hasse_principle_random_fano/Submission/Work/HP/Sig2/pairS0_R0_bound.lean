import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.MDCommon
import Submission.Work.HP.MinkDefs
import Submission.Work.HP.lam_basic
import Submission.Work.HP.ball_count_small
import Submission.Work.HP.rk_le_card
import Submission.Work.HP.MDEstimates.ball_count_R0
import Submission.Work.HP.MDEstimates.ballCount_projScale_le
import Submission.Work.HP.MDEstimates.lam_projScale_le
import Submission.Work.HP.MDEstimates.rk_projScale
import Submission.Work.HP.Sig2.gam_rank_det
import Submission.Work.HP.Sig2.nu_indep
import Submission.Work.HP.Sig2.key_lemma_two_vectors
import Submission.Work.HP.MDBasic.mem_Gam_iff
import Submission.Work.HP.MDBasic.finite_sets
import Submission.Work.HP.FM.minkowski_lower
import Submission.Work.HP.six_le_NN

/-!
# The Lemma-R0 bound for `pairS0`

`pairS0 d n A p` is the number of *primitive* coefficient vectors `a` with `norm a <= A` that
vanish at both points of `p = (x,y)`, i.e. the number of primitive points of the lattice
`Gam d n x y` in the ball of radius `A`.  Lemma R0 of Browning--Le Boudec--Sawin
(*The Hasse principle for random Fano hypersurfaces*, Annals 197 (2023)) bounds such a lattice
point count by `A^{R-j} Y^j / det Γ + A^{R-1-j}` with `R = rk Γ = N_{d,n} - 2`, valid for
`j <= R - 1`, `1 <= A`, and any `Y` with `A <= Y` and `lam Γ R <= Y`.  Here we take
`Y := max C 1 * muXY n x y`: then `Y >= A` by the hypothesis `A <= muXY n x y`, and
`Y >= lam Γ (N-2)` by the paper's *Key lemma two vectors*
(`Work.HP.Sig2.key_lemma_two_vectors`).  The extra factor `max C 1` depends only on `d, n` and is
absorbed into the final constant using `j <= N_{d,n} - 3`.

The lattice point count is assembled from

* `ballCount_sum_bound`, Schmidt's upper bound in summation form, proved below by the classical
  induction that peels off a shortest vector and projects (`ballCount_projScale_le`,
  `lam_projScale_le`, `rk_projScale`), and
* `Work.HP.MDEstimates.sum_le_target`, the summation form of Lemma R0, which needs
  `det Γ <= λ_1 ⋯ λ_R` (`Work.HP.FM.minkowski_lower`, the easy half of Minkowski II),

while the lattice-theoretic hypotheses on `Γ` come from `Work.HP.Sig2.gam_rank_det`
(`rk Γ = N_{d,n} - 2` and `det Γ > 0` for pairs in `Ω`) and `Work.HP.six_le_NN` (`N_{d,n} >= 6`).
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

open Finset
open scoped BigOperators

namespace Work.HP.Sig2

open Work.HP.MDEstimates

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma eq_bot_of_rk_eq_zero {L : Submodule ℤ (ι → ℤ)} (h : rk L = 0) : L = ⊥ := by
  obtain ⟨n, b⟩ := Submodule.basisOfPid (Pi.basisFun ℤ ι) L
  have hn : n = 0 := by
    have h1 : Module.finrank ℤ L = n := by
      rw [Module.finrank_eq_card_basis b]; simp
    rw [← h1]; exact h
  subst hn
  rw [Submodule.eq_bot_iff]
  intro x hx
  have hzero : b.repr ⟨x, hx⟩ = 0 := Subsingleton.elim _ _
  have h2 : (⟨x, hx⟩ : L) = 0 := by
    have := congrArg b.repr.symm hzero
    simpa using this
  exact congrArg Subtype.val h2

lemma ballCount_bot (T : ℝ) (hT : 0 ≤ T) : ballCount (⊥ : Submodule ℤ (ι → ℤ)) T = 1 := by
  rw [ballCount]
  have hset : {v : ι → ℤ | v ∈ (⊥ : Submodule ℤ (ι → ℤ)) ∧ eNorm v ≤ T} = {0} := by
    ext v
    constructor
    · rintro ⟨hv, -⟩
      simpa using hv
    · rintro rfl
      refine ⟨Submodule.zero_mem _, ?_⟩
      simpa [eNorm] using hT
  rw [hset, Set.ncard_singleton]

/-- Schmidt's upper bound in sum form, with a constant depending only on the rank bound. -/
theorem ballCount_sum_bound (N : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ (L : Submodule ℤ (ι → ℤ)), rk L ≤ N → ∀ T : ℝ, 1 ≤ T →
      (ballCount L T : ℝ) ≤ K * ∑ k ∈ Finset.range (rk L + 1),
        T ^ k / ∏ i ∈ Finset.range k, lam L (i + 1) := by
  induction N with
  | zero =>
    refine ⟨1, one_pos, ?_⟩
    intro L hL T hT
    have hL0 : rk L = 0 := Nat.le_zero.mp hL
    have hbot : L = ⊥ := eq_bot_of_rk_eq_zero hL0
    subst hbot
    rw [ballCount_bot T (by linarith), hL0]
    norm_num
  | succ n ih =>
    obtain ⟨K, hKpos, hK⟩ := ih
    set d : ℝ := 2 / Real.sqrt 3 with hd
    have hsqpos : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
    have hdc : d * (Real.sqrt 3 / 2) = 1 := by rw [hd]; field_simp
    have hd1 : 1 ≤ d := by
      rw [hd, le_div_iff₀ hsqpos]
      have h2 : Real.sqrt 3 < 2 := by
        rw [show (2:ℝ) = Real.sqrt 4 by
          rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
        exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
      linarith
    have hdpos : 0 < d := lt_of_lt_of_le one_pos hd1
    refine ⟨K * (3 * d ^ n), by positivity, ?_⟩
    intro L hL T hT
    have hTpos : 0 < T := lt_of_lt_of_le one_pos hT
    by_cases hle : rk L ≤ n
    · have h1 := hK L hle T hT
      have hSnn : 0 ≤ ∑ k ∈ Finset.range (rk L + 1),
          T ^ k / ∏ i ∈ Finset.range k, lam L (i + 1) :=
        Finset.sum_nonneg fun k _ => div_nonneg (pow_nonneg (by linarith) k)
          (Finset.prod_nonneg fun i _ => lam_nonneg L (i + 1))
      refine le_trans h1 (mul_le_mul_of_nonneg_right ?_ hSnn)
      refine le_mul_of_one_le_right hKpos.le ?_
      have : (1:ℝ) ≤ d ^ n := one_le_pow₀ hd1
      nlinarith
    · have hrk : rk L = n + 1 := by omega
      have hne : L ≠ ⊥ := by
        intro h
        have h0 : rk (⊥ : Submodule ℤ (ι → ℤ)) = 0 := by rw [rk]; simp
        rw [h, h0] at hrk
        omega
      obtain ⟨u, huL, hu0, hulam, hshort⟩ := exists_short_vec L hne
      set lam1 : ℝ := eNorm u with hlam1
      have hlam1pos : 0 < lam1 := by rw [hlam1]; exact eNorm_pos_of_ne_zero hu0
      have hlam1eq : lam1 = lam L 1 := by rw [hlam1]; exact hulam
      have hlam1ge : 1 ≤ lam1 := by rw [hlam1eq]; exact one_le_lam L le_rfl (by omega)
      set L2 : Submodule ℤ (ι → ℤ) := Submodule.map (projScale u) L with hL2
      have hrk2 : rk L2 = n := by
        rw [hL2, rk_projScale L u huL hu0 hshort, hrk]; omega
      have hcnt := ballCount_projScale_le L u huL hu0 hshort T (by linarith)
      have hT2 : 1 ≤ lam1 ^ 2 * T := by nlinarith
      have hIH := hK L2 (by omega) (lam1 ^ 2 * T) hT2
      set t : ℕ → ℝ := fun k => T ^ k / ∏ i ∈ Finset.range k, lam L (i + 1) with ht
      set gg : ℕ → ℝ := fun k => T ^ k / ∏ i ∈ Finset.range k, lam L (i + 2) with hgg
      set g : ℕ → ℝ := fun k => (lam1 ^ 2 * T) ^ k / ∏ i ∈ Finset.range k, lam L2 (i + 1) with hgd
      set S : ℝ := ∑ k ∈ Finset.range (n + 2), t k with hS
      have htnn : ∀ k, 0 ≤ t k := fun k => div_nonneg (pow_nonneg (by linarith) k)
        (Finset.prod_nonneg fun i _ => lam_nonneg L (i + 1))
      have hSnn : 0 ≤ S := by
        rw [hS]; exact Finset.sum_nonneg fun k _ => htnn k
      have hg1 : ∀ k, k ≤ n → g k ≤ d ^ k * gg k := by
        intro k hk
        have hrel : ∀ i ∈ Finset.range k,
            Real.sqrt 3 / 2 * lam1 ^ 2 * lam L (i + 2) ≤ lam L2 (i + 1) := by
          intro i hi
          have hi' : i < k := Finset.mem_range.mp hi
          have hidx : i + 1 ≤ rk L - 1 := by
            have h1 : i + 1 ≤ k := by omega
            have h2 : k ≤ rk L - 1 := by omega
            exact le_trans h1 h2
          have h := lam_projScale_le L u huL hu0 hshort (i + 1) (by omega) hidx
          rw [← hlam1] at h
          exact h
        have hP2 : (Real.sqrt 3 / 2) ^ k * lam1 ^ (2 * k) *
              ∏ i ∈ Finset.range k, lam L (i + 2)
            ≤ ∏ i ∈ Finset.range k, lam L2 (i + 1) := by
          have hprod : ∏ i ∈ Finset.range k, (Real.sqrt 3 / 2 * lam1 ^ 2 * lam L (i + 2))
              ≤ ∏ i ∈ Finset.range k, lam L2 (i + 1) := by
            refine Finset.prod_le_prod₀ (fun i hi => ?_) (fun i hi => hrel i hi)
            exact mul_nonneg (mul_nonneg (by positivity) (by positivity))
              (lam_nonneg L (i + 2))
          have heq : ∏ i ∈ Finset.range k, (Real.sqrt 3 / 2 * lam1 ^ 2 * lam L (i + 2))
              = (Real.sqrt 3 / 2) ^ k * lam1 ^ (2 * k)
                * ∏ i ∈ Finset.range k, lam L (i + 2) := by
            rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range, mul_pow, pow_mul]
          rw [← heq]; exact hprod
        have h3 : 0 < ∏ i ∈ Finset.range k, lam L (i + 2) := by
          refine Finset.prod_pos fun i hi => ?_
          have hi' : i < k := Finset.mem_range.mp hi
          exact lt_of_lt_of_le one_pos (one_le_lam L (by omega) (by omega))
        have hP2pos : 0 < ∏ i ∈ Finset.range k, lam L2 (i + 1) :=
          lt_of_lt_of_le (mul_pos (mul_pos (by positivity) (pow_pos hlam1pos _)) h3) hP2
        have hdck : d ^ k * (Real.sqrt 3 / 2) ^ k = 1 := by rw [← mul_pow, hdc, one_pow]
        have hcross : lam1 ^ (2 * k) * ∏ i ∈ Finset.range k, lam L (i + 2)
            ≤ d ^ k * ∏ i ∈ Finset.range k, lam L2 (i + 1) := by
          calc lam1 ^ (2 * k) * ∏ i ∈ Finset.range k, lam L (i + 2)
              = (d ^ k * (Real.sqrt 3 / 2) ^ k)
                  * (lam1 ^ (2 * k) * ∏ i ∈ Finset.range k, lam L (i + 2)) := by
                rw [hdck, one_mul]
            _ = d ^ k * ((Real.sqrt 3 / 2) ^ k * lam1 ^ (2 * k)
                  * ∏ i ∈ Finset.range k, lam L (i + 2)) := by ring
            _ ≤ d ^ k * ∏ i ∈ Finset.range k, lam L2 (i + 1) :=
                mul_le_mul_of_nonneg_left hP2 (pow_nonneg hdpos.le k)
        calc g k = lam1 ^ (2 * k) * T ^ k / ∏ i ∈ Finset.range k, lam L2 (i + 1) := by
              simp only [hgd]
              rw [mul_pow, pow_mul]
          _ ≤ d ^ k * T ^ k / ∏ i ∈ Finset.range k, lam L (i + 2) := by
              rw [div_le_div_iff₀ hP2pos h3]
              calc lam1 ^ (2 * k) * T ^ k * ∏ i ∈ Finset.range k, lam L (i + 2)
                  = T ^ k * (lam1 ^ (2 * k) * ∏ i ∈ Finset.range k, lam L (i + 2)) := by ring
                _ ≤ T ^ k * (d ^ k * ∏ i ∈ Finset.range k, lam L2 (i + 1)) :=
                    mul_le_mul_of_nonneg_left hcross (pow_nonneg hTpos.le k)
                _ = d ^ k * T ^ k * ∏ i ∈ Finset.range k, lam L2 (i + 1) := by ring
          _ = d ^ k * gg k := by simp only [hgg]; ring
      have hg2 : ∀ k, k ≤ n → gg k ≤ t k := by
        intro k hk
        have hle : ∏ i ∈ Finset.range k, lam L (i + 1) ≤ ∏ i ∈ Finset.range k, lam L (i + 2) := by
          refine Finset.prod_le_prod₀ (fun i _ => lam_nonneg L (i + 1)) fun i hi => ?_
          have hi' : i < k := Finset.mem_range.mp hi
          have hidx : i + 2 ≤ rk L := by omega
          exact lam_mono L (by omega) hidx
        have hp1 : 0 < ∏ i ∈ Finset.range k, lam L (i + 1) := by
          refine Finset.prod_pos fun i hi => ?_
          have hi' : i < k := Finset.mem_range.mp hi
          have hidx : i + 1 ≤ rk L := by omega
          exact lt_of_lt_of_le one_pos (one_le_lam L (by omega) hidx)
        have hp2 : 0 < ∏ i ∈ Finset.range k, lam L (i + 2) := by
          refine Finset.prod_pos fun i hi => ?_
          have hi' : i < k := Finset.mem_range.mp hi
          have hidx : i + 2 ≤ rk L := by omega
          exact lt_of_lt_of_le one_pos (one_le_lam L (by omega) hidx)
        simp only [hgg, ht]
        exact div_le_div_of_nonneg_left (pow_nonneg hTpos.le k) hp1 hle
      have hg3 : ∀ k, k ≤ n → T / lam1 * gg k = t (k + 1) := by
        intro k hk
        have h1 : lam L 1 ≠ 0 := by rw [← hlam1eq]; exact ne_of_gt hlam1pos
        have h2 : (∏ i ∈ Finset.range k, lam L (i + 2)) ≠ 0 := by
          refine Finset.prod_ne_zero_iff.mpr fun i hi => ?_
          have hi' : i < k := Finset.mem_range.mp hi
          have hidx : i + 2 ≤ rk L := by omega
          exact ne_of_gt (lt_of_lt_of_le one_pos (one_le_lam L (by omega) hidx))
        have h3 : T ≠ 0 := ne_of_gt hTpos
        simp only [hgg, ht, hlam1eq, Finset.prod_range_succ']
        field_simp
        ring
      have hggnn : ∀ k, 0 ≤ gg k := fun k => div_nonneg (pow_nonneg hTpos.le k)
        (Finset.prod_nonneg fun i _ => lam_nonneg L (i + 2))
      have hgs : ∑ k ∈ Finset.range (n + 1), g k ≤ d ^ n * S := by
        have h1 : ∑ k ∈ Finset.range (n + 1), g k
            ≤ ∑ k ∈ Finset.range (n + 1), d ^ n * gg k := by
          refine Finset.sum_le_sum fun k hk => ?_
          have hk' : k ≤ n := by have := Finset.mem_range.mp hk; omega
          refine le_trans (hg1 k hk') ?_
          exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hd1 hk') (hggnn k)
        have h2 : ∑ k ∈ Finset.range (n + 1), d ^ n * gg k
            ≤ ∑ k ∈ Finset.range (n + 1), d ^ n * t k := by
          refine Finset.sum_le_sum fun k hk => ?_
          have hk' : k ≤ n := by have := Finset.mem_range.mp hk; omega
          exact mul_le_mul_of_nonneg_left (hg2 k hk') (pow_nonneg hdpos.le n)
        have h3 : ∑ k ∈ Finset.range (n + 1), d ^ n * t k
            = d ^ n * ∑ k ∈ Finset.range (n + 1), t k := by rw [Finset.mul_sum]
        have h4 : ∑ k ∈ Finset.range (n + 1), t k ≤ S := by
          rw [hS]
          refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr (by omega)) ?_
          intro i _ _; exact htnn i
        calc ∑ k ∈ Finset.range (n + 1), g k ≤ ∑ k ∈ Finset.range (n + 1), d ^ n * gg k := h1
          _ ≤ ∑ k ∈ Finset.range (n + 1), d ^ n * t k := h2
          _ = d ^ n * ∑ k ∈ Finset.range (n + 1), t k := h3
          _ ≤ d ^ n * S := mul_le_mul_of_nonneg_left h4 (pow_nonneg hdpos.le n)
      have hgT : T / lam1 * (∑ k ∈ Finset.range (n + 1), g k) ≤ d ^ n * S := by
        have h1 : T / lam1 * (∑ k ∈ Finset.range (n + 1), g k)
            ≤ ∑ k ∈ Finset.range (n + 1), d ^ n * t (k + 1) := by
          rw [Finset.mul_sum]
          refine Finset.sum_le_sum fun k hk => ?_
          have hk' : k ≤ n := by have := Finset.mem_range.mp hk; omega
          calc T / lam1 * g k ≤ T / lam1 * (d ^ n * gg k) := by
                refine mul_le_mul_of_nonneg_left (le_trans (hg1 k hk') ?_) (div_nonneg hTpos.le hlam1pos.le)
                exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hd1 hk') (hggnn k)
            _ = d ^ n * (T / lam1 * gg k) := by ring
            _ = d ^ n * t (k + 1) := by rw [hg3 k hk']
        have h2 : ∑ k ∈ Finset.range (n + 1), d ^ n * t (k + 1) ≤ d ^ n * S := by
          have h5 : S = (∑ k ∈ Finset.range (n + 1), t (k + 1)) + t 0 := by
            rw [hS, Finset.sum_range_succ']
          rw [h5, ← Finset.mul_sum, mul_add]
          exact le_add_of_nonneg_right (mul_nonneg (pow_nonneg hdpos.le n) (htnn 0))
        exact le_trans h1 h2
      have hkey : (2 * T / lam1 + 1) * (∑ k ∈ Finset.range (n + 1), g k) ≤ 3 * d ^ n * S := by
        have e : (2 * T / lam1 + 1) * (∑ k ∈ Finset.range (n + 1), g k)
            = 2 * (T / lam1 * (∑ k ∈ Finset.range (n + 1), g k))
              + (∑ k ∈ Finset.range (n + 1), g k) := by ring
        rw [e]
        linarith [hgT, hgs]
      have hfinal : (ballCount L T : ℝ)
          ≤ K * (3 * d ^ n) * ∑ k ∈ Finset.range (rk L + 1),
              T ^ k / ∏ i ∈ Finset.range k, lam L (i + 1) := by
        calc (ballCount L T : ℝ) ≤ (2 * T / lam1 + 1) * (ballCount L2 (lam1 ^ 2 * T) : ℝ) := hcnt
          _ ≤ (2 * T / lam1 + 1) * (K * ∑ k ∈ Finset.range (rk L2 + 1), g k) := by
                refine mul_le_mul_of_nonneg_left hIH ?_
                positivity
          _ = K * ((2 * T / lam1 + 1) * ∑ k ∈ Finset.range (n + 1), g k) := by
                rw [hrk2]; ring
          _ ≤ K * (3 * d ^ n * S) := mul_le_mul_of_nonneg_left hkey hKpos.le
          _ = K * (3 * d ^ n) * ∑ k ∈ Finset.range (rk L + 1),
                T ^ k / ∏ i ∈ Finset.range k, lam L (i + 1) := by
                rw [hS, ht, hrk]; ring
      exact hfinal

/-- Schmidt's upper bound in summation form, with the constant depending only on the index type. -/
theorem ballCount_sum_le (ι : Type*) [Fintype ι] [DecidableEq ι] :
    ∃ K : ℝ, 0 < K ∧ ∀ (L : Submodule ℤ (ι → ℤ)) (T : ℝ), 1 ≤ T →
      (ballCount L T : ℝ) ≤ K * (Finset.range (rk L + 1)).sum
        (fun k => T ^ k / (Finset.range k).prod (fun i => lam L (i + 1))) := by
  obtain ⟨K, hKpos, hK⟩ := ballCount_sum_bound (ι := ι) (Fintype.card ι)
  exact ⟨K, hKpos, fun L T hT => hK L (Work.HP.rk_le_card L) T hT⟩

/-- `pairS0` is a set of lattice points of `Gam d n x y` in the ball of radius `A`, hence is at
most the corresponding `ballCount`. -/
lemma pairS0_le_ballCount (d n : ℕ) (A : ℝ) (p : (Fin (n + 1) → ℤ) × (Fin (n + 1) → ℤ)) :
    pairS0 d n A p ≤ (ballCount (Gam d n p.1 p.2) A : ℝ) := by
  have hsub : {a ∈ primSet d n A (fun _ => True) |
      formEval d n a p.1 = 0 ∧ formEval d n a p.2 = 0} ⊆
      {v : Mon d n → ℤ | v ∈ Gam d n p.1 p.2 ∧ eNorm v ≤ A} := by
    rintro a ⟨⟨-, hnorm, -⟩, h1, h2⟩
    exact ⟨(Work.HP.MDBasic.mem_Gam_iff d n p.1 p.2 a).mpr ⟨h1, h2⟩, hnorm⟩
  have hfin : ({v : Mon d n → ℤ | v ∈ Gam d n p.1 p.2 ∧ eNorm v ≤ A}).Finite :=
    (Work.HP.MDBasic.finite_eNorm_le A).subset (fun v hv => hv.2)
  have h := Set.ncard_le_ncard hsub hfin
  simp only [pairS0, ballCount]
  exact_mod_cast h

theorem pairS0_R0_bound (d n : ℕ) (hd : 2 ≤ d) (hdn : d ≤ n) :
    ∃ K : ℝ, 0 < K ∧ ∀ (A B : ℝ) (p : (Fin (n + 1) → ℤ) × (Fin (n + 1) → ℤ)) (j : ℕ),
      p ∈ Omega d n B → 1 ≤ A → A ≤ muXY n p.1 p.2 → j ≤ NN d n - 3 →
      pairS0 d n A p ≤ K * (A ^ (NN d n - 2 - j) * (muXY n p.1 p.2) ^ j
        / detL (Gam d n p.1 p.2) + A ^ (NN d n - 3 - j)) := by
  obtain ⟨C, hCpos, hC⟩ := key_lemma_two_vectors d n hd hdn
  obtain ⟨K1, hK1pos, hK1⟩ := ballCount_sum_le (Mon d n)
  obtain ⟨K2, hK2pos, hK2⟩ := Work.HP.MDEstimates.sum_le_target (ι := Mon d n)
  have hN6 : 6 ≤ NN d n := six_le_NN d n hd hdn
  refine ⟨K1 * K2 * (max C 1) ^ (NN d n - 2), by positivity, ?_⟩
  intro A B p j hp hA hAmu hj
  have hx : IsPrim p.1 := hp.1.1
  have hy : IsPrim p.2 := hp.2.1.1
  have hxy : p.1 ≠ p.2 := hp.2.2.1
  have hxy' : p.1 ≠ -p.2 := hp.2.2.2
  have hli := nu_indep d n hd p.1 p.2 hx hy hxy hxy'
  obtain ⟨hrk, hdetpos⟩ := gam_rank_det d n p.1 p.2 hli
  have hmu_pos : 0 < muXY n p.1 p.2 := lt_of_lt_of_le (by linarith) hAmu
  have hdetle : detL (Gam d n p.1 p.2) ≤
      ∏ i ∈ Finset.range (rk (Gam d n p.1 p.2)), lam (Gam d n p.1 p.2) (i + 1) :=
    Work.HP.FM.minkowski_lower (Gam d n p.1 p.2)
  rw [hrk] at hdetle
  have hY1 : (1:ℝ) ≤ max C 1 := le_max_right C 1
  have hAmu' : A ≤ max C 1 * muXY n p.1 p.2 := by
    calc A ≤ muXY n p.1 p.2 := hAmu
      _ = 1 * muXY n p.1 p.2 := by ring
      _ ≤ max C 1 * muXY n p.1 p.2 := mul_le_mul_of_nonneg_right hY1 hmu_pos.le
  have hlamR : lam (Gam d n p.1 p.2) (NN d n - 2) ≤ max C 1 * muXY n p.1 p.2 := by
    calc lam (Gam d n p.1 p.2) (NN d n - 2) ≤ C * muXY n p.1 p.2 := hC p.1 p.2 hx hy hxy hxy'
      _ ≤ max C 1 * muXY n p.1 p.2 := mul_le_mul_of_nonneg_right (le_max_left C 1) hmu_pos.le
  have h2 := hK2 (Gam d n p.1 p.2) (NN d n - 2) j (max C 1 * muXY n p.1 p.2) A hrk
    (by omega) (by omega) hA hAmu' hlamR hdetpos hdetle
  have h1 := hK1 (Gam d n p.1 p.2) A hA
  rw [hrk] at h1
  have hS0 := pairS0_le_ballCount d n A p
  have hmain : (ballCount (Gam d n p.1 p.2) A : ℝ) ≤ K1 * (K2 *
      (A ^ (NN d n - 2 - j) * (max C 1 * muXY n p.1 p.2) ^ j / detL (Gam d n p.1 p.2)
        + A ^ (NN d n - 2 - 1 - j))) := by
    calc (ballCount (Gam d n p.1 p.2) A : ℝ)
        ≤ K1 * (Finset.range (NN d n - 2 + 1)).sum
            (fun k => A ^ k / (Finset.range k).prod (fun i => lam (Gam d n p.1 p.2) (i + 1))) := h1
      _ ≤ K1 * (K2 * (A ^ (NN d n - 2 - j) * (max C 1 * muXY n p.1 p.2) ^ j
            / detL (Gam d n p.1 p.2) + A ^ (NN d n - 2 - 1 - j))) :=
          mul_le_mul_of_nonneg_left h2 hK1pos.le
  have hMj : (max C 1) ^ j ≤ (max C 1) ^ (NN d n - 2) :=
    pow_le_pow_right₀ hY1 (by omega)
  have hMR1 : (1:ℝ) ≤ (max C 1) ^ (NN d n - 2) := one_le_pow₀ hY1
  have hX : A ^ (NN d n - 2 - j) * (max C 1 * muXY n p.1 p.2) ^ j / detL (Gam d n p.1 p.2)
      = (max C 1) ^ j * (A ^ (NN d n - 2 - j) * (muXY n p.1 p.2) ^ j
          / detL (Gam d n p.1 p.2)) := by
    rw [mul_pow]; ring
  have hXle : A ^ (NN d n - 2 - j) * (max C 1 * muXY n p.1 p.2) ^ j / detL (Gam d n p.1 p.2)
      ≤ (max C 1) ^ (NN d n - 2) * (A ^ (NN d n - 2 - j) * (muXY n p.1 p.2) ^ j
          / detL (Gam d n p.1 p.2)) := by
    rw [hX]
    exact mul_le_mul_of_nonneg_right hMj (by positivity)
  have hYle : A ^ (NN d n - 3 - j) ≤ (max C 1) ^ (NN d n - 2) * A ^ (NN d n - 3 - j) := by
    nlinarith [hMR1, pow_nonneg (by linarith : (0:ℝ) ≤ A) (NN d n - 3 - j)]
  have hexp : NN d n - 2 - 1 - j = NN d n - 3 - j := by omega
  calc pairS0 d n A p ≤ (ballCount (Gam d n p.1 p.2) A : ℝ) := hS0
    _ ≤ K1 * (K2 * (A ^ (NN d n - 2 - j) * (max C 1 * muXY n p.1 p.2) ^ j
          / detL (Gam d n p.1 p.2) + A ^ (NN d n - 2 - 1 - j))) := hmain
    _ = K1 * K2 * (A ^ (NN d n - 2 - j) * (max C 1 * muXY n p.1 p.2) ^ j
          / detL (Gam d n p.1 p.2) + A ^ (NN d n - 3 - j)) := by
        rw [hexp]; ring
    _ ≤ K1 * K2 * ((max C 1) ^ (NN d n - 2) *
          (A ^ (NN d n - 2 - j) * (muXY n p.1 p.2) ^ j / detL (Gam d n p.1 p.2))
        + (max C 1) ^ (NN d n - 2) * A ^ (NN d n - 3 - j)) := by
        refine mul_le_mul_of_nonneg_left (add_le_add hXle hYle) (by positivity)
    _ = K1 * K2 * (max C 1) ^ (NN d n - 2) *
          (A ^ (NN d n - 2 - j) * (muXY n p.1 p.2) ^ j / detL (Gam d n p.1 p.2)
            + A ^ (NN d n - 3 - j)) := by ring

end Work.HP.Sig2
