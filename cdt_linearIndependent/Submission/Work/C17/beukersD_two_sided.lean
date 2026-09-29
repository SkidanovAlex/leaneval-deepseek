import Mathlib
import Submission.Work.CRad.deps
import Submission.Work.CRad.d_decay_cuspDisc
import Submission.Work.C17.beukersUR_two_sided
import Submission.Work.C17.summable_shift_pow

/-!
# Two-sided bound for the Beukers companion sequence `dₙ(a) = vₙ(a) − η_a·uₙ(a)`

For `a ≥ 3` with `α := a + √(a²−1)`, `ρ := a − √(a²−1) = 1/α`:

`dₙ(a) < 0` for all `n`, and `c·ρⁿ/(n+1)⁴ ≤ |dₙ| ≤ C·(n+1)²·ρⁿ`.

Route, all on top of the already-proved Apéry limit `beukers_apéry_limit`
and of the sharp Legendre bounds `beukersUR_two_sided`
(`αⁿ/(n+1) ≤ uₙ ≤ αⁿ`):

* the Casorati/Wronskian identity `vₙuₙ₋₁ − vₙ₋₁uₙ = 1/n`
  (`beukersVR_ratio_diff`) gives, with `t_k := 1/(k·u_k·u_{k−1})`, the ratio
  difference `rₙ − rₙ₋₁ = tₙ`, where `rₙ = vₙ/uₙ`;
* telescoping gives `r_N = Σ_{k<N+1} t_k`, so the partial sums of `t`
  converge to `lim r_N = η_a` (`beukers_apéry_limit`), i.e. `Σ'_k t_k = η_a`;
* hence the exact tail formula `d_N = −u_N·Σ'_j t_{N+1+j}`, from which:
  - `d_N < 0` since every `t_k > 0`;
  - `|d_N| ≥ u_N·t_{N+1} = 1/((N+1)u_{N+1}) ≥ α^{−1}/((N+1)α^N)`;
  - `t_k ≤ (k+1)ρ^{2k−1}` (sharp growth of `u`), so
    `|d_N| ≤ α^N·Σ_{j}(N+2+j)ρ^{2N+1+2j} ≤ (N+2)ρ^{N+1}/(1−ρ²)²`.
-/

namespace Work.C17

open Submission.CDT
open scoped BigOperators

/-- the Apéry tail summand `t_k = 1/(k·u_k(a)·u_{k−1}(a))` (with `t_0 = 0`). -/
noncomputable def bdT (a : ℝ) (k : ℕ) : ℝ :=
  1 / ((k : ℝ) * beukersUR a k * beukersUR a (k - 1))

@[simp] lemma bdT_zero (a : ℝ) : bdT a 0 = 0 := by simp [bdT]

lemma bdT_nonneg (a : ℝ) (ha : 1 ≤ a) (k : ℕ) : 0 ≤ bdT a k := by
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk; simp
  · have h1 : 0 < beukersUR a k := beukersUR_pos a ha k
    have h2 : 0 < beukersUR a (k - 1) := beukersUR_pos a ha (k - 1)
    have hk' : 0 < (k : ℝ) := by exact_mod_cast hk
    exact le_of_lt (one_div_pos.mpr (by positivity))

lemma bdT_pos (a : ℝ) (ha : 1 ≤ a) {k : ℕ} (hk : 1 ≤ k) : 0 < bdT a k := by
  have h1 : 0 < beukersUR a k := beukersUR_pos a ha k
  have h2 : 0 < beukersUR a (k - 1) := beukersUR_pos a ha (k - 1)
  have hk' : 0 < (k : ℝ) := by exact_mod_cast hk
  exact one_div_pos.mpr (by positivity)

/-- `ρ_a·(a + √(a²−1)) = 1`. -/
lemma beukersRho_mul_alpha (a : ℝ) (ha : 3 ≤ a) :
    beukersRho a * (a + Real.sqrt (a ^ 2 - 1)) = 1 := by
  have hsq : (Real.sqrt (a ^ 2 - 1)) ^ 2 = a ^ 2 - 1 := by
    rw [Real.sq_sqrt]; nlinarith [sq_nonneg a]
  dsimp [beukersRho]
  nlinarith

lemma beukersRho_eq_inv_alpha (a : ℝ) (ha : 3 ≤ a) :
    beukersRho a = (a + Real.sqrt (a ^ 2 - 1))⁻¹ := by
  have h := beukersRho_mul_alpha a ha
  field_simp
  exact h

/-- the pointwise domination of the Apéry tail summand by the geometric
`(k+1)·ρ_a^{2k−1}` (uses the sharp lower bound `u_k ≥ α^k/(k+1)`). -/
lemma bdT_le_geom (a : ℝ) (ha : 3 ≤ a) {k : ℕ} (hk : 1 ≤ k) :
    bdT a k ≤ ((k : ℝ) + 1) / (a + Real.sqrt (a ^ 2 - 1)) ^ (2 * k - 1) := by
  have ha1 : 1 ≤ a := by linarith
  have hαpos : 0 < a + Real.sqrt (a ^ 2 - 1) := by
    have := Real.sqrt_nonneg (a ^ 2 - 1); linarith
  have hk0 : 0 < (k : ℝ) := by exact_mod_cast hk
  have h1 : 1 / beukersUR a k ≤ ((k : ℝ) + 1) / (a + Real.sqrt (a ^ 2 - 1)) ^ k := by
    have h := (beukersUR_two_sided a ha k).1
    have h' : 1 / beukersUR a k
        ≤ 1 / ((a + Real.sqrt (a ^ 2 - 1)) ^ k / ((k : ℝ) + 1)) :=
      one_div_le_one_div_of_le (by positivity) h
    have he : 1 / ((a + Real.sqrt (a ^ 2 - 1)) ^ k / ((k : ℝ) + 1))
        = ((k : ℝ) + 1) / (a + Real.sqrt (a ^ 2 - 1)) ^ k := by
      field_simp
    rwa [he] at h'
  have h2 : 1 / beukersUR a (k - 1) ≤ (k : ℝ) / (a + Real.sqrt (a ^ 2 - 1)) ^ (k - 1) := by
    have hk1 : (k - 1) + 1 = k := Nat.succ_pred_eq_of_pos hk
    have h := (beukersUR_two_sided a ha (k - 1)).1
    have hc : (((k - 1 : ℕ) : ℝ) + 1) = (k : ℝ) := by
      have h1 : (((k - 1 : ℕ) : ℝ) + 1) = (((k - 1) + 1 : ℕ) : ℝ) := by push_cast; ring
      rw [h1, hk1]
    rw [hc] at h
    have h' : 1 / beukersUR a (k - 1)
        ≤ 1 / ((a + Real.sqrt (a ^ 2 - 1)) ^ (k - 1) / (k : ℝ)) :=
      one_div_le_one_div_of_le (by positivity) h
    have he : 1 / ((a + Real.sqrt (a ^ 2 - 1)) ^ (k - 1) / (k : ℝ))
        = (k : ℝ) / (a + Real.sqrt (a ^ 2 - 1)) ^ (k - 1) := by
      field_simp
    rwa [he] at h'
  have hfac : bdT a k
      = (1 / (k : ℝ)) * (1 / beukersUR a k) * (1 / beukersUR a (k - 1)) := by
    rw [bdT]
    field_simp
  have hstep : (1 / (k : ℝ)) * (1 / beukersUR a k) * (1 / beukersUR a (k - 1))
      ≤ (1 / (k : ℝ)) * (((k : ℝ) + 1) / (a + Real.sqrt (a ^ 2 - 1)) ^ k)
        * ((k : ℝ) / (a + Real.sqrt (a ^ 2 - 1)) ^ (k - 1)) := by
    have hA : (1 / (k : ℝ)) * (1 / beukersUR a k)
        ≤ (1 / (k : ℝ)) * (((k : ℝ) + 1) / (a + Real.sqrt (a ^ 2 - 1)) ^ k) :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    have hB : 0 ≤ 1 / beukersUR a (k - 1) := by
      exact div_nonneg zero_le_one (le_of_lt (beukersUR_pos a ha1 (k - 1)))
    have hC : 0 ≤ (1 / (k : ℝ)) * (((k : ℝ) + 1) / (a + Real.sqrt (a ^ 2 - 1)) ^ k) := by
      positivity
    exact mul_le_mul hA h2 hB hC
  have hexp : k + (k - 1) = 2 * k - 1 := by omega
  have harith : (1 / (k : ℝ)) * (((k : ℝ) + 1) / (a + Real.sqrt (a ^ 2 - 1)) ^ k)
        * ((k : ℝ) / (a + Real.sqrt (a ^ 2 - 1)) ^ (k - 1))
      = ((k : ℝ) + 1) / (a + Real.sqrt (a ^ 2 - 1)) ^ (2 * k - 1) := by
    rw [← hexp, pow_add]
    field_simp
  calc bdT a k
      = (1 / (k : ℝ)) * (1 / beukersUR a k) * (1 / beukersUR a (k - 1)) := hfac
    _ ≤ (1 / (k : ℝ)) * (((k : ℝ) + 1) / (a + Real.sqrt (a ^ 2 - 1)) ^ k)
        * ((k : ℝ) / (a + Real.sqrt (a ^ 2 - 1)) ^ (k - 1)) := hstep
    _ = ((k : ℝ) + 1) / (a + Real.sqrt (a ^ 2 - 1)) ^ (2 * k - 1) := harith

/-- the closed form of the polynomial-geometric series. -/
lemma tsum_shift_mul_geom (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) (c : ℝ) :
    (∑' j : ℕ, (c + (j : ℝ)) * r ^ j) = c * (1 - r)⁻¹ + r / (1 - r) ^ 2 := by
  have hnorm : ‖r‖ < 1 := by rw [Real.norm_eq_abs, abs_of_pos hr0]; exact hr1
  have hsm1 : Summable (fun j : ℕ => r ^ j) := summable_geometric_of_norm_lt_one hnorm
  have hsm2 : Summable (fun j : ℕ => (j : ℝ) * r ^ j) := by
    simpa using summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1 (r := r) hnorm
  calc (∑' j : ℕ, (c + (j : ℝ)) * r ^ j)
      = ∑' j : ℕ, (c * r ^ j + (j : ℝ) * r ^ j) := tsum_congr (fun j => by ring)
    _ = (∑' j : ℕ, c * r ^ j) + ∑' j : ℕ, (j : ℝ) * r ^ j :=
        Summable.tsum_add (hsm1.mul_left c) hsm2
    _ = c * (1 - r)⁻¹ + r / (1 - r) ^ 2 := by
        rw [tsum_mul_left, tsum_geometric_of_norm_lt_one hnorm,
          tsum_coe_mul_geometric_of_norm_lt_one hnorm]

/-- the sharp geometric bound for the polynomial-geometric tail. -/
lemma tsum_shift_pow_sharp (ρ : ℝ) (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (N : ℕ) :
    (∑' j : ℕ, ((N : ℝ) + 2 + j) * ρ ^ (2 * (N + 1 + j) - 1))
      ≤ ((N : ℝ) + 2) * ρ ^ (2 * N + 1) / (1 - ρ ^ 2) ^ 2 := by
  have hρ2_0 : 0 < ρ ^ 2 := by positivity
  have hρ2_1 : ρ ^ 2 < 1 := by nlinarith
  have hden : 0 < 1 - ρ ^ 2 := by linarith
  have he : ∀ j : ℕ, ρ ^ (2 * (N + 1 + j) - 1) = ρ ^ (2 * N + 1) * (ρ ^ 2) ^ j := by
    intro j
    have h1 : 2 * (N + 1 + j) - 1 = 2 * N + 1 + 2 * j := by omega
    rw [h1, pow_add, pow_mul]
  have hval : (∑' j : ℕ, ((N : ℝ) + 2 + j) * ρ ^ (2 * (N + 1 + j) - 1))
      = ρ ^ (2 * N + 1)
          * (((N : ℝ) + 2) * (1 - ρ ^ 2)⁻¹ + ρ ^ 2 / (1 - ρ ^ 2) ^ 2) := by
    calc (∑' j : ℕ, ((N : ℝ) + 2 + j) * ρ ^ (2 * (N + 1 + j) - 1))
        = ∑' j : ℕ, ρ ^ (2 * N + 1) * (((N : ℝ) + 2 + j) * (ρ ^ 2) ^ j) := by
          apply tsum_congr; intro j; rw [he j]; ring
      _ = ρ ^ (2 * N + 1) * ∑' j : ℕ, (((N : ℝ) + 2 + j) * (ρ ^ 2) ^ j) := tsum_mul_left
      _ = ρ ^ (2 * N + 1)
            * (((N : ℝ) + 2) * (1 - ρ ^ 2)⁻¹ + ρ ^ 2 / (1 - ρ ^ 2) ^ 2) := by
          rw [tsum_shift_mul_geom (ρ ^ 2) hρ2_0 hρ2_1 ((N : ℝ) + 2)]
  rw [hval]
  have hinner : (((N : ℝ) + 2) * (1 - ρ ^ 2)⁻¹ + ρ ^ 2 / (1 - ρ ^ 2) ^ 2)
      = (((N : ℝ) + 2) * (1 - ρ ^ 2) + ρ ^ 2) / (1 - ρ ^ 2) ^ 2 := by
    field_simp
  rw [hinner]
  have hnum : ((N : ℝ) + 2) * (1 - ρ ^ 2) + ρ ^ 2 ≤ ((N : ℝ) + 2) := by
    nlinarith [hρ2_0, (show (0 : ℝ) ≤ N from Nat.cast_nonneg N)]
  calc ρ ^ (2 * N + 1) * ((((N : ℝ) + 2) * (1 - ρ ^ 2) + ρ ^ 2) / (1 - ρ ^ 2) ^ 2)
      ≤ ρ ^ (2 * N + 1) * (((N : ℝ) + 2) / (1 - ρ ^ 2) ^ 2) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact div_le_div_of_nonneg_right hnum (by positivity)
    _ = ((N : ℝ) + 2) * ρ ^ (2 * N + 1) / (1 - ρ ^ 2) ^ 2 := by ring


/-! ## The Casorati identity over `ℝ` (transfer from `ℚ` by continuity + density)

`beukersU`, `beukersV` are the rational coefficient sequences; the Casorati
identity `n·(uₙvₙ₋₁ − uₙ₋₁vₙ) = −1` is proved over `ℚ`
(`beukersUV_casoratian_value`).  Both sides of the identity, as functions of
`a`, are continuous on `ℝ` (they only involve the continuous coefficient
sequences `a ↦ uₙ(a)`, `a ↦ vₙ(a)`), and they agree on the dense set
`[3,∞) ∩ ℚ`, hence agree on `[3,∞)`.  -/

lemma continuous_beukersUR : ∀ n : ℕ, Continuous (fun a : ℝ => beukersUR a n)
  | 0 => by
      have h : (fun a : ℝ => beukersUR a 0) = fun _ : ℝ => (1 : ℝ) := by
        funext a; rfl
      rw [h]; exact continuous_const
  | 1 => by
      have h : (fun a : ℝ => beukersUR a 1) = fun a : ℝ => a := by
        funext a; rfl
      rw [h]; exact continuous_id
  | n + 2 => by
      have hfun : (fun a : ℝ => beukersUR a (n + 2)) = fun a : ℝ =>
          (((2 * (n : ℝ)) + 3) * a * beukersUR a (n + 1)
            - ((n : ℝ) + 1) * beukersUR a n) / ((n : ℝ) + 2) := by
        funext a
        simp [beukersUR]
      rw [hfun]
      exact (((continuous_const.mul continuous_id).mul
        (continuous_beukersUR (n + 1))).sub
        (continuous_const.mul (continuous_beukersUR n))).div_const _

lemma continuous_beukersVR (n : ℕ) : Continuous (fun a : ℝ => beukersVR a n) := by
  have hfun : (fun a : ℝ => beukersVR a n) = fun a : ℝ =>
      ∑ j ∈ Finset.Icc 1 n, beukersUR a (n - j) * (beukersUR a (j - 1) / (j : ℝ)) := by
    funext a
    rfl
  rw [hfun]
  refine Finset.induction_on (Finset.Icc 1 n) ?_ ?_
  · simpa using (continuous_const : Continuous fun _ : ℝ => (0 : ℝ))
  · intro m t hmt ih
    have hstep : (fun a : ℝ => ∑ j ∈ insert m t,
          beukersUR a (n - j) * (beukersUR a (j - 1) / (j : ℝ)))
        = fun a : ℝ => beukersUR a (n - m) * (beukersUR a (m - 1) / (m : ℝ))
            + ∑ j ∈ t, beukersUR a (n - j) * (beukersUR a (j - 1) / (j : ℝ)) := by
      funext a
      rw [Finset.sum_insert hmt]
    rw [hstep]
    exact ((continuous_beukersUR (n - m)).mul
      ((continuous_beukersUR (m - 1)).div_const _)).add ih

/-- the Casorati identity over `ℝ`, for `a ≥ 3`. -/
lemma beukersUV_casoratian_real (a : ℝ) (ha : 3 ≤ a) {n : ℕ} (hn : 1 ≤ n) :
    (n : ℝ) * (beukersUR a n * beukersVR a (n - 1) - beukersUR a (n - 1) * beukersVR a n)
      = -1 := by
  set F : ℝ → ℝ := fun a => (n : ℝ) * (beukersUR a n * beukersVR a (n - 1)
      - beukersUR a (n - 1) * beukersVR a n) + 1 with hFdef
  have hFcont : Continuous F := by
    rw [hFdef]
    exact (continuous_const.mul (((continuous_beukersUR n).mul
      (continuous_beukersVR (n - 1))).sub
      ((continuous_beukersUR (n - 1)).mul (continuous_beukersVR n)))).add continuous_const
  have hrat : ∀ q : ℚ, (3 : ℝ) ≤ (q : ℝ) → F (q : ℝ) = 0 := by
    intro q hq
    have hcas := beukersUV_casoratian_value q hn
    have hcast : (n : ℝ) * (beukersUR (q : ℝ) n * beukersVR (q : ℝ) (n - 1)
        - beukersUR (q : ℝ) (n - 1) * beukersVR (q : ℝ) n) = -1 := by
      have h := congrArg (fun t : ℚ => (t : ℝ)) hcas
      push_cast at h
      rw [beukersUR_eq_cast q n, beukersVR_eq_cast q (n - 1),
        beukersUR_eq_cast q (n - 1), beukersVR_eq_cast q n]
      simpa using h
    rw [hFdef]
    simp only
    rw [hcast]
    norm_num
  have hclosed : IsClosed {a : ℝ | F a = 0} := isClosed_eq hFcont continuous_const
  have hsub : Set.Ici (3 : ℝ) ⊆ closure {a : ℝ | F a = 0} := by
    intro b hb
    have hb3 : (3 : ℝ) ≤ b := hb
    rw [Metric.mem_closure_iff]
    intro ε hε
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show max (3 : ℝ) (b - ε) < b + ε by
      have h1 : (3 : ℝ) < b + ε := by linarith
      have h2 : b - ε < b + ε := by linarith
      exact max_lt h1 h2)
    have hqε : b - ε < (q : ℝ) := lt_of_le_of_lt (le_max_right _ _) hq1
    refine ⟨(q : ℝ), ?_, ?_⟩
    · have hq3 : (3 : ℝ) ≤ (q : ℝ) := le_of_lt (lt_of_le_of_lt (le_max_left _ _) hq1)
      exact hrat q hq3
    · rw [Real.dist_eq, abs_lt]
      constructor <;> linarith
  have hA : F a = 0 := hclosed.closure_subset (hsub ha)
  rw [hFdef] at hA
  simp only at hA
  linarith

/-- the ratio difference of the Apéry pair (real parameter). -/
lemma bdT_ratio_diff (a : ℝ) (ha : 3 ≤ a) {n : ℕ} (hn : 1 ≤ n) :
    beukersVR a n / beukersUR a n - beukersVR a (n - 1) / beukersUR a (n - 1)
      = 1 / ((n : ℝ) * beukersUR a n * beukersUR a (n - 1)) := by
  have ha1 : 1 ≤ a := by linarith
  have hcas := beukersUV_casoratian_real a ha hn
  have hu_n : beukersUR a n ≠ 0 := ne_of_gt (beukersUR_pos a ha1 n)
  have hu_n1 : beukersUR a (n - 1) ≠ 0 := ne_of_gt (beukersUR_pos a ha1 (n - 1))
  have hn0 : (n : ℝ) ≠ 0 := by
    have : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have h2 : beukersVR a n * beukersUR a (n - 1) - beukersVR a (n - 1) * beukersUR a n
      = 1 / (n : ℝ) := by
    have h3 : beukersUR a n * beukersVR a (n - 1) - beukersUR a (n - 1) * beukersVR a n
        = -(1 / (n : ℝ)) := by
      field_simp
      linarith [hcas]
    calc beukersVR a n * beukersUR a (n - 1) - beukersVR a (n - 1) * beukersUR a n
        = -(beukersUR a n * beukersVR a (n - 1) - beukersUR a (n - 1) * beukersVR a n) := by
          ring
      _ = -(-(1 / (n : ℝ))) := by rw [h3]
      _ = 1 / (n : ℝ) := by ring
  have h1 : beukersVR a n / beukersUR a n - beukersVR a (n - 1) / beukersUR a (n - 1)
      = (beukersVR a n * beukersUR a (n - 1) - beukersVR a (n - 1) * beukersUR a n)
        / (beukersUR a n * beukersUR a (n - 1)) := by
    field_simp
  rw [h1, h2]
  field_simp

/-- the partial sums of `t` telescope to the Apéry ratio. -/
lemma bdT_partial (a : ℝ) (ha : 3 ≤ a) (N : ℕ) :
    ∑ k ∈ Finset.range N, bdT a k = beukersVR a (N - 1) / beukersUR a (N - 1) := by
  induction N with
  | zero => simp [bdT, beukersVR]
  | succ N ih =>
      rw [Finset.sum_range_succ, ih]
      rcases Nat.eq_zero_or_pos N with hN | hN
      · subst hN
        simp [bdT, beukersVR]
      · have hrd := bdT_ratio_diff a ha hN
        have hrd' : beukersVR a N / beukersUR a N
            - beukersVR a (N - 1) / beukersUR a (N - 1) = bdT a N := by
          simpa only [bdT] using hrd
        have hidx : N + 1 - 1 = N := by omega
        rw [hidx]
        linarith [hrd']

/-- the partial sums of `t` at the shifted index. -/
lemma bdT_partial' (a : ℝ) (ha : 3 ≤ a) (N : ℕ) :
    ∑ k ∈ Finset.range (N + 1), bdT a k = beukersVR a N / beukersUR a N := by
  rw [bdT_partial a ha (N + 1)]
  norm_num

/-- `Σ'_k t_k = η_a`, the Apéry limit in tail form. -/
lemma bdT_hasSum (a : ℝ) (ha : 3 ≤ a) : HasSum (bdT a) (beukersEta a) := by
  have ha1 : 1 ≤ a := by linarith
  rw [hasSum_iff_tendsto_nat_of_nonneg (fun k => bdT_nonneg a ha1 k) (beukersEta a)]
  have hpr : Filter.Tendsto (fun N : ℕ => N - 1) Filter.atTop Filter.atTop := by
    rw [Filter.tendsto_atTop_atTop]
    intro b
    exact ⟨b + 1, fun N hN => by omega⟩
  have hlim : Filter.Tendsto (fun N : ℕ => beukersVR a (N - 1) / beukersUR a (N - 1))
      Filter.atTop (nhds (beukersEta a)) :=
    (beukers_apéry_limit a ha).comp hpr
  refine Filter.Tendsto.congr (fun N => ?_) hlim
  exact (bdT_partial a ha N).symm

/-- the sharp tail bound for the Apéry tail. -/
lemma bdT_tail_sharp (a : ℝ) (ha : 3 ≤ a) (n : ℕ) :
    ∑' j : ℕ, bdT a (j + (n + 1))
      ≤ ((n : ℝ) + 2) * beukersRho a ^ (2 * n + 1) / (1 - beukersRho a ^ 2) ^ 2 := by
  have ha1 : 1 ≤ a := by linarith
  have hρ0 : 0 < beukersRho a := beukers_rho_pos a ha
  have hρ1 : beukersRho a < 1 := beukers_rho_lt_one a ha
  have hpt : ∀ j : ℕ,
      bdT a (j + (n + 1)) ≤ ((n : ℝ) + 2 + j) * beukersRho a ^ (2 * (n + 1 + j) - 1) := by
    intro j
    have h := bdT_le_geom a ha (k := j + (n + 1)) (by omega)
    have hc : (((j + (n + 1) : ℕ) : ℝ) + 1) = (n : ℝ) + 2 + j := by push_cast; ring
    have he : 2 * (j + (n + 1)) - 1 = 2 * (n + 1 + j) - 1 := by omega
    have hρ : beukersRho a ^ (2 * (n + 1 + j) - 1)
        = ((a + Real.sqrt (a ^ 2 - 1)) ^ (2 * (n + 1 + j) - 1))⁻¹ := by
      rw [beukersRho_eq_inv_alpha a ha, inv_pow]
    simpa only [hc, he, hρ, div_eq_mul_inv] using h
  have hsm1 : Summable (fun j : ℕ => ((n : ℝ) + 2 + j) * beukersRho a ^ (2 * (n + 1 + j) - 1)) :=
    summable_shift_pow (beukersRho a) hρ0 hρ1 n
  have hsm2 : Summable (fun j : ℕ => bdT a (j + (n + 1))) :=
    (summable_nat_add_iff (n + 1)).mpr (bdT_hasSum a ha).summable
  exact le_trans (Summable.tsum_le_tsum hpt hsm2 hsm1)
    (tsum_shift_pow_sharp (beukersRho a) hρ0 hρ1 n)

/-- the exact tail formula for `d_N`. -/
lemma beukersD_eq_tail (a : ℝ) (ha : 3 ≤ a) (N : ℕ) :
    beukersD a N = -beukersUR a N * ∑' j : ℕ, bdT a (j + (N + 1)) := by
  have ha1 : 1 ≤ a := by linarith
  have hspl := Summable.sum_add_tsum_nat_add (f := bdT a) (N + 1) (bdT_hasSum a ha).summable
  rw [bdT_partial' a ha N, (bdT_hasSum a ha).tsum_eq] at hspl
  have huN : beukersUR a N ≠ 0 := ne_of_gt (beukersUR_pos a ha1 N)
  rw [beukersD]
  have htail : (∑' j : ℕ, bdT a (j + (N + 1)))
      = beukersEta a - beukersVR a N / beukersUR a N := by linarith
  rw [htail]
  field_simp
  ring

theorem beukersD_two_sided (a : ℝ) (ha : 3 ≤ a) :
    ∃ c C : ℝ, 0 < c ∧ ∀ n : ℕ, Submission.CDT.beukersD a n < 0 ∧
      c / (((n : ℝ) + 1) ^ 4 * (a + Real.sqrt (a ^ 2 - 1)) ^ n) ≤ |Submission.CDT.beukersD a n| ∧
      |Submission.CDT.beukersD a n| ≤ C * ((n : ℝ) + 1) ^ 2 / (a + Real.sqrt (a ^ 2 - 1)) ^ n := by
  classical
  have ha1 : 1 ≤ a := by linarith
  set α : ℝ := a + Real.sqrt (a ^ 2 - 1) with hαdef
  have hαpos : 0 < α := by
    rw [hαdef]
    have := Real.sqrt_nonneg (a ^ 2 - 1); linarith
  have hρpos : 0 < beukersRho a := beukers_rho_pos a ha
  have hρ1 : beukersRho a < 1 := beukers_rho_lt_one a ha
  have hρα : beukersRho a = α⁻¹ := by rw [hαdef]; exact beukersRho_eq_inv_alpha a ha
  have hu_pos : ∀ m : ℕ, 0 < beukersUR a m := fun m => beukersUR_pos a ha1 m
  have hu_le : ∀ m : ℕ, beukersUR a m ≤ α ^ m := by
    intro m
    have h := (beukersUR_two_sided a ha m).2
    rwa [← hαdef] at h
  have hmul_pow : ∀ m : ℕ, α ^ m * beukersRho a ^ m = 1 := by
    intro m
    rw [← mul_pow, hρα, mul_inv_cancel₀ (ne_of_gt hαpos), one_pow]
  have hrpow : ∀ m : ℕ, beukersRho a ^ m = (α ^ m)⁻¹ := by
    intro m
    rw [← inv_pow, ← hρα]
  refine ⟨α⁻¹, 2 / (1 - beukersRho a ^ 2) ^ 2, by positivity, ?_⟩
  intro n
  have htail := beukersD_eq_tail a ha n
  have hsm : Summable (fun j : ℕ => bdT a (j + (n + 1))) :=
    (summable_nat_add_iff (n + 1)).mpr (bdT_hasSum a ha).summable
  have hTpos : 0 < ∑' j : ℕ, bdT a (j + (n + 1)) := by
    have hle : bdT a (n + 1) ≤ ∑' j : ℕ, bdT a (j + (n + 1)) := by
      have h := Summable.le_tsum hsm (0 : ℕ) (fun j _ => bdT_nonneg a ha1 _)
      simpa only [Nat.zero_add] using h
    have hpos : 0 < bdT a (n + 1) := bdT_pos a ha1 (by omega)
    linarith
  have hneg : beukersD a n < 0 := by
    rw [htail]
    have := hu_pos n
    nlinarith
  have habs : |beukersD a n| = beukersUR a n * ∑' j : ℕ, bdT a (j + (n + 1)) := by
    rw [abs_of_neg hneg, htail]
    ring
  refine ⟨hneg, ?_, ?_⟩
  · -- lower bound
    rw [habs]
    have h1 : bdT a (n + 1) ≤ ∑' j : ℕ, bdT a (j + (n + 1)) := by
      have h := Summable.le_tsum hsm (0 : ℕ) (fun j _ => bdT_nonneg a ha1 _)
      simpa only [Nat.zero_add] using h
    have h1' := mul_le_mul_of_nonneg_left h1 (le_of_lt (hu_pos n))
    have hval : beukersUR a n * bdT a (n + 1)
        = 1 / (((n : ℝ) + 1) * beukersUR a (n + 1)) := by
      have hune : beukersUR a n ≠ 0 := ne_of_gt (hu_pos n)
      have hun1 : beukersUR a (n + 1) ≠ 0 := ne_of_gt (hu_pos (n + 1))
      have hn1 : ((n : ℝ) + 1) ≠ 0 := by positivity
      rw [bdT, show n + 1 - 1 = n from by omega]
      field_simp
      push_cast
      ring
    have h2 : 1 / (((n : ℝ) + 1) * α ^ (n + 1))
        ≤ 1 / (((n : ℝ) + 1) * beukersUR a (n + 1)) := by
      have hpos : 0 < ((n : ℝ) + 1) * beukersUR a (n + 1) := by
        have := hu_pos (n + 1); positivity
      have hle : ((n : ℝ) + 1) * beukersUR a (n + 1) ≤ ((n : ℝ) + 1) * α ^ (n + 1) := by
        have := hu_le (n + 1); nlinarith [(show (0 : ℝ) ≤ n from Nat.cast_nonneg n)]
      exact one_div_le_one_div_of_le hpos hle
    have h3 : α⁻¹ / (((n : ℝ) + 1) * α ^ n)
        = 1 / (((n : ℝ) + 1) * α ^ (n + 1)) := by
      rw [pow_succ]
      field_simp
    have h4 : α⁻¹ / (((n : ℝ) + 1) ^ 4 * α ^ n)
        ≤ α⁻¹ / (((n : ℝ) + 1) * α ^ n) := by
      have hpow : ((n : ℝ) + 1) ≤ ((n : ℝ) + 1) ^ 4 := by
        have ht1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith [(show (0 : ℝ) ≤ n from Nat.cast_nonneg n)]
        have h3 : (1 : ℝ) ≤ ((n : ℝ) + 1) ^ 3 := one_le_pow₀ ht1
        calc ((n : ℝ) + 1) = ((n : ℝ) + 1) * 1 := by ring
          _ ≤ ((n : ℝ) + 1) * ((n : ℝ) + 1) ^ 3 :=
              mul_le_mul_of_nonneg_left h3 (by positivity)
          _ = ((n : ℝ) + 1) ^ 4 := by ring
      have hA : 1 / (((n : ℝ) + 1) ^ 4 * α ^ n) ≤ 1 / (((n : ℝ) + 1) * α ^ n) := by
        have hpos : 0 < ((n : ℝ) + 1) * α ^ n := by positivity
        have hle : ((n : ℝ) + 1) * α ^ n ≤ ((n : ℝ) + 1) ^ 4 * α ^ n := by
          have := pow_pos hαpos n
          nlinarith [(show (0 : ℝ) ≤ n from Nat.cast_nonneg n)]
        exact one_div_le_one_div_of_le hpos hle
      have := mul_le_mul_of_nonneg_left hA (le_of_lt (inv_pos.mpr hαpos))
      simpa only [div_eq_mul_inv, one_mul] using this
    calc α⁻¹ / (((n : ℝ) + 1) ^ 4 * α ^ n)
        ≤ α⁻¹ / (((n : ℝ) + 1) * α ^ n) := h4
      _ = 1 / (((n : ℝ) + 1) * α ^ (n + 1)) := h3
      _ ≤ 1 / (((n : ℝ) + 1) * beukersUR a (n + 1)) := h2
      _ = beukersUR a n * bdT a (n + 1) := hval.symm
      _ ≤ beukersUR a n * ∑' j : ℕ, bdT a (j + (n + 1)) := h1'
  · -- upper bound
    rw [habs]
    have hT := bdT_tail_sharp a ha n
    have hTnn : 0 ≤ ∑' j : ℕ, bdT a (j + (n + 1)) := by
      have hle : bdT a (n + 1) ≤ ∑' j : ℕ, bdT a (j + (n + 1)) := by
        have h := Summable.le_tsum hsm (0 : ℕ) (fun j _ => bdT_nonneg a ha1 _)
        simpa only [Nat.zero_add] using h
      have h0 : 0 ≤ bdT a (n + 1) := bdT_nonneg a ha1 _
      linarith
    have hstep := mul_le_mul (hu_le n) hT hTnn (by positivity : (0:ℝ) ≤ α ^ n)
    have hL : α ^ n * (((n : ℝ) + 2) * beukersRho a ^ (2 * n + 1) / (1 - beukersRho a ^ 2) ^ 2)
        = ((n : ℝ) + 2) * beukersRho a ^ (n + 1) / (1 - beukersRho a ^ 2) ^ 2 := by
      have hmain : α ^ n * beukersRho a ^ (2 * n + 1) = beukersRho a ^ (n + 1) := by
        have hpow : beukersRho a ^ (2 * n + 1)
            = beukersRho a ^ n * beukersRho a ^ (n + 1) := by
          rw [← pow_add]; congr 1; omega
        rw [hpow, ← mul_assoc, hmul_pow n, one_mul]
      calc α ^ n * (((n : ℝ) + 2) * beukersRho a ^ (2 * n + 1) / (1 - beukersRho a ^ 2) ^ 2)
          = ((n : ℝ) + 2) * (α ^ n * beukersRho a ^ (2 * n + 1))
              / (1 - beukersRho a ^ 2) ^ 2 := by ring
        _ = ((n : ℝ) + 2) * beukersRho a ^ (n + 1) / (1 - beukersRho a ^ 2) ^ 2 := by
              rw [hmain]
    have hcmp : ((n : ℝ) + 2) * beukersRho a ^ (n + 1)
        ≤ 2 * ((n : ℝ) + 1) ^ 2 * beukersRho a ^ n := by
      have h1 : ((n : ℝ) + 2) * beukersRho a ≤ 2 * ((n : ℝ) + 1) ^ 2 := by
        nlinarith [hρpos, hρ1, sq_nonneg ((n : ℝ) + 1), (show (0 : ℝ) ≤ n from Nat.cast_nonneg n)]
      rw [pow_succ]
      nlinarith [mul_le_mul_of_nonneg_right h1 (pow_nonneg (le_of_lt hρpos) n),
        pow_pos hρpos n]
    have hR : (2 / (1 - beukersRho a ^ 2) ^ 2) * ((n : ℝ) + 1) ^ 2 / α ^ n
        = 2 * ((n : ℝ) + 1) ^ 2 * beukersRho a ^ n / (1 - beukersRho a ^ 2) ^ 2 := by
      rw [hrpow n]
      ring
    calc beukersUR a n * ∑' j : ℕ, bdT a (j + (n + 1))
        ≤ α ^ n * (((n : ℝ) + 2) * beukersRho a ^ (2 * n + 1) / (1 - beukersRho a ^ 2) ^ 2) :=
          hstep
      _ = ((n : ℝ) + 2) * beukersRho a ^ (n + 1) / (1 - beukersRho a ^ 2) ^ 2 := hL
      _ ≤ 2 * ((n : ℝ) + 1) ^ 2 * beukersRho a ^ n / (1 - beukersRho a ^ 2) ^ 2 :=
          div_le_div_of_nonneg_right hcmp (by positivity)
      _ = (2 / (1 - beukersRho a ^ 2) ^ 2) * ((n : ℝ) + 1) ^ 2 / α ^ n := hR.symm

end Work.C17
