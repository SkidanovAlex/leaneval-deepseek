import Mathlib
import Submission.Work.BourgainPlan.Assembly.Defs

/-!
# The squeeze step for Bourgain's polynomial ergodic theorem

This file proves `Work.BourgainPlan.Assembly.ae_tendsto_of_lacunary_monotone`: a nonnegative
sequence `u : ℕ → X → ℝ` whose partial mass `N ↦ N * u N x` is nondecreasing (for a.e. `x`), which
is a.e. bounded, and whose lacunary subsequences `i ↦ u ⌊ρ_m^i⌋ x` converge a.e. for a family
`ρ_m ↓ 1` of reals `> 1`, converges a.e. as `N → ∞`.

The pointwise content is the classical squeeze: for `n` in the block
`⌊ρ^i⌋ ≤ n < ⌊ρ^{i+1}⌋`, monotonicity of the mass gives

  `v n ≤ (⌊ρ^{i+1}⌋ / ⌊ρ^i⌋) * v ⌊ρ^{i+1}⌋`,   `v n ≥ (⌊ρ^i⌋ / ⌊ρ^{i+1}⌋) * v ⌊ρ^i⌋`,

and the ratios tend to `ρ` and `ρ⁻¹`.  Hence `liminf v ≥ L_ρ / ρ` and `limsup v ≤ ρ L_ρ` where
`L_ρ = lim_i v ⌊ρ^i⌋`; eliminating `L_ρ` and letting `ρ ↓ 1` gives `limsup v ≤ liminf v`.
-/

open Filter Function MeasureTheory
open scoped Topology ENNReal BigOperators

set_option autoImplicit false

namespace Work.BourgainPlan.Assembly

/-! ## Elementary facts about `lac ρ i = ⌊ρ ^ i⌋₊` -/

section Lac

variable {ρ : ℝ}

lemma lac_mono (hρ : 1 ≤ ρ) : Monotone (lac ρ) :=
  fun _ _ hij => Nat.floor_mono (pow_le_pow_right₀ hρ hij)

lemma one_le_lac (hρ : 1 ≤ ρ) (i : ℕ) : 1 ≤ lac ρ i :=
  Nat.le_floor (a := ρ ^ i) (by simpa using one_le_pow₀ hρ (n := i))

lemma lac_unbounded (hρ : 1 < ρ) : ∀ n : ℕ, ∃ i : ℕ, n < lac ρ i := by
  intro n
  have h : ∀ᶠ i in atTop, ((n : ℝ) + 1) ≤ ρ ^ i :=
    (tendsto_pow_atTop_atTop_of_one_lt hρ).eventually_ge_atTop _
  rw [eventually_atTop] at h
  obtain ⟨i, hi⟩ := h
  refine ⟨i, lt_of_lt_of_le (Nat.lt_succ_self n) (Nat.le_floor (a := ρ ^ i) ?_)⟩
  simpa using hi i le_rfl

/-- The ratio of consecutive lacunary indices tends to `ρ`. -/
lemma lac_succ_ratio (hρ : 1 < ρ) :
    Tendsto (fun i : ℕ => ((lac ρ (i + 1) : ℝ) / (lac ρ i : ℝ))) atTop (nhds ρ) := by
  have hρ1 : (1 : ℝ) ≤ ρ := le_of_lt hρ
  have hρ0 : (0 : ℝ) < ρ := lt_trans zero_lt_one hρ
  have honeN : ∀ i, 1 ≤ lac ρ i := fun i =>
    Nat.le_floor (a := ρ ^ i) (by simpa using one_le_pow₀ hρ1 (n := i))
  have hNpos : ∀ i, (0 : ℝ) < (lac ρ i : ℝ) := fun i =>
    Nat.cast_pos.mpr (lt_of_lt_of_le Nat.zero_lt_one (honeN i))
  have hNle : ∀ i, (lac ρ i : ℝ) ≤ ρ ^ i := fun i => Nat.floor_le (by positivity)
  have hNlt : ∀ i, ρ ^ i < (lac ρ i : ℝ) + 1 := fun i => Nat.lt_floor_add_one _
  have hlow : Tendsto (fun i : ℕ => ρ - (1 / ρ) ^ i) atTop (nhds ρ) := by
    have h : Tendsto (fun i : ℕ => (1 / ρ) ^ i) atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) (by rw [div_lt_one hρ0]; exact hρ)
    simpa using (tendsto_const_nhds.sub h :
      Tendsto (fun i : ℕ => ρ - (1 / ρ) ^ i) atTop (nhds (ρ - 0)))
  have hup : Tendsto (fun i : ℕ => ρ + ρ / (ρ ^ i - 1)) atTop (nhds ρ) := by
    have hden : Tendsto (fun i : ℕ => ρ ^ i - 1) atTop atTop := by
      have h := tendsto_atTop_add_const_right atTop (-1) (tendsto_pow_atTop_atTop_of_one_lt hρ)
      simpa [sub_eq_add_neg] using h
    have h0 : Tendsto (fun i : ℕ => ρ / (ρ ^ i - 1)) atTop (nhds 0) :=
      Filter.Tendsto.div_atTop tendsto_const_nhds hden
    simpa using (tendsto_const_nhds.add h0 :
      Tendsto (fun i : ℕ => ρ + ρ / (ρ ^ i - 1)) atTop (nhds (ρ + 0)))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le hlow hup ?_ ?_
  · intro i
    show ρ - (1 / ρ) ^ i ≤ (lac ρ (i + 1) : ℝ) / (lac ρ i : ℝ)
    have hkey : ρ - (1 / ρ) ^ i = (ρ ^ (i + 1) - 1) / ρ ^ i := by
      rw [one_div_pow, sub_div, pow_succ', mul_div_assoc,
        div_self (pow_ne_zero i (ne_of_gt hρ0)), mul_one]
    rw [hkey]
    exact div_le_div₀ (Nat.cast_nonneg _)
      (by have h := Nat.lt_floor_add_one (ρ ^ (i + 1)); simp only [lac]; linarith)
      (hNpos i) (hNle i)
  · intro i
    show (lac ρ (i + 1) : ℝ) / (lac ρ i : ℝ) ≤ ρ + ρ / (ρ ^ i - 1)
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · simp only [lac, Nat.zero_add, pow_one, pow_zero, Nat.floor_one, Nat.cast_one, div_one,
        sub_self, div_zero, add_zero]
      exact Nat.floor_le (le_of_lt hρ0)
    · have hi1 : (0 : ℝ) < ρ ^ i - 1 := by
        have : (1 : ℝ) < ρ ^ i := one_lt_pow₀ hρ (by omega)
        linarith
      have hstep : (lac ρ (i + 1) : ℝ) / (lac ρ i : ℝ) ≤ ρ ^ (i + 1) / (ρ ^ i - 1) :=
        div_le_div₀ (by positivity) (hNle (i + 1)) hi1 (by linarith [hNlt i])
      refine hstep.trans_eq ?_
      have hX : ρ ^ i - 1 ≠ 0 := ne_of_gt hi1
      field_simp
      ring

end Lac

/-! ## Block decomposition of `ℕ` by a monotone unbounded sequence -/

/-- Every `n ≥ N 0` lies in a block `[N i, N (i+1))`, and the block index is maximal. -/
lemma exists_block {N : ℕ → ℕ} (hNmono : Monotone N) (hNunb : ∀ n : ℕ, ∃ i, n < N i)
    {n : ℕ} (hn : N 0 ≤ n) :
    ∃ i, N i ≤ n ∧ n < N (i + 1) ∧ ∀ j, N j ≤ n → j ≤ i := by
  obtain ⟨i₁, hi₁⟩ := hNunb n
  have key : ∀ j, N j ≤ n → j < i₁ := by
    intro j hj
    by_contra h
    rw [not_lt] at h
    have : N i₁ ≤ N j := hNmono h
    omega
  refine ⟨Nat.findGreatest (fun j => N j ≤ n) i₁, ?_, ?_, ?_⟩
  · exact Nat.findGreatest_spec (P := fun j => N j ≤ n) (Nat.zero_le i₁) hn
  · by_contra h
    rw [not_lt] at h
    have hle : Nat.findGreatest (fun j => N j ≤ n) i₁ + 1 < i₁ :=
      key (Nat.findGreatest (fun j => N j ≤ n) i₁ + 1) h
    have h2 : Nat.findGreatest (fun j => N j ≤ n) i₁ + 1 ≤
        Nat.findGreatest (fun j => N j ≤ n) i₁ :=
      Nat.le_findGreatest (le_of_lt hle) h
    omega
  · intro j hj
    exact Nat.le_findGreatest (le_of_lt (key j hj)) hj

/-- Block comparison for `limsup`: if `v n ≤ w i` on each block `i`, then
`limsup v ≤ limsup w`. -/
lemma limsup_le_limsup_of_block {v w : ℕ → ℝ} {N : ℕ → ℕ} (hNmono : Monotone N)
    (hNunb : ∀ n : ℕ, ∃ i, n < N i)
    (hblock : ∀ i n, N i ≤ n → n < N (i + 1) → v n ≤ w i)
    (hvcobdd : ∃ a, ∀ n, a ≤ v n) (hwbd : ∃ a, ∀ᶠ i in atTop, w i ≤ a) :
    limsup v atTop ≤ limsup w atTop := by
  refine Filter.le_limsup_of_le (u := w) hwbd ?_
  intro b hb
  refine Filter.limsup_le_of_le (u := v) ?_ ?_
  · obtain ⟨a, ha⟩ := hvcobdd
    exact Filter.isCoboundedUnder_le_of_le atTop ha
  · rw [eventually_atTop] at hb ⊢
    obtain ⟨i₀, hi₀⟩ := hb
    refine ⟨max (N 0) (N i₀), fun n hn => ?_⟩
    obtain ⟨i, hi1, hi2, himax⟩ := exists_block hNmono hNunb (le_trans (le_max_left _ _) hn)
    exact le_trans (hblock i n hi1 hi2) (hi₀ i (himax i₀ (le_trans (le_max_right _ _) hn)))

/-- Block comparison for `liminf`: if `w i ≤ v n` on each block `i`, then
`liminf w ≤ liminf v`. -/
lemma liminf_le_liminf_of_block {v w : ℕ → ℝ} {N : ℕ → ℕ} (hNmono : Monotone N)
    (hNunb : ∀ n : ℕ, ∃ i, n < N i)
    (hblock : ∀ i n, N i ≤ n → n < N (i + 1) → w i ≤ v n)
    (hwcobdd : ∃ a, ∀ᶠ i in atTop, a ≤ w i) (hvbd : ∃ a, ∀ᶠ n in atTop, v n ≤ a) :
    liminf w atTop ≤ liminf v atTop := by
  refine Filter.liminf_le_of_le (u := w) ?_ ?_
  · obtain ⟨a, ha⟩ := hwcobdd
    exact Filter.isBoundedUnder_of_eventually_ge ha
  · intro b hb
    refine Filter.le_liminf_of_le (u := v) ?_ ?_
    · obtain ⟨a, ha⟩ := hvbd
      exact Filter.isCoboundedUnder_ge_of_eventually_le atTop ha
    · rw [eventually_atTop] at hb ⊢
      obtain ⟨i₀, hi₀⟩ := hb
      refine ⟨max (N 0) (N i₀), fun n hn => ?_⟩
      obtain ⟨i, hi1, hi2, himax⟩ := exists_block hNmono hNunb (le_trans (le_max_left _ _) hn)
      exact le_trans (hi₀ i (himax i₀ (le_trans (le_max_right _ _) hn))) (hblock i n hi1 hi2)

/-- Upper comparison on a block. -/
lemma block_upper {v : ℕ → ℝ} {N : ℕ → ℕ} {i n : ℕ}
    (hvnn : ∀ n, 0 ≤ v n)
    (hmono : ∀ a b : ℕ, a ≤ b → (a : ℝ) * v a ≤ (b : ℝ) * v b)
    (h1 : N i ≤ n) (h2 : n ≤ N (i + 1)) (hNi : 0 < N i) :
    v n ≤ ((N (i + 1) : ℝ) / (N i : ℝ)) * v (N (i + 1)) := by
  have hNi' : (0 : ℝ) < (N i : ℝ) := by exact_mod_cast hNi
  have h1' : (N i : ℝ) ≤ (n : ℝ) := by exact_mod_cast h1
  have hni : (0 : ℝ) < (n : ℝ) := lt_of_lt_of_le hNi' h1'
  have hkey : (n : ℝ) * v n ≤ (N (i + 1) : ℝ) * v (N (i + 1)) := hmono n (N (i + 1)) h2
  have h2' : v n ≤ ((N (i + 1) : ℝ) / (n : ℝ)) * v (N (i + 1)) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hni]
    linarith [hkey]
  have h3 : ((N (i + 1) : ℝ) / (n : ℝ)) ≤ ((N (i + 1) : ℝ) / (N i : ℝ)) :=
    div_le_div_of_nonneg_left (by positivity) hNi' h1'
  calc v n ≤ ((N (i + 1) : ℝ) / (n : ℝ)) * v (N (i + 1)) := h2'
    _ ≤ ((N (i + 1) : ℝ) / (N i : ℝ)) * v (N (i + 1)) :=
        mul_le_mul_of_nonneg_right h3 (hvnn _)

/-- Lower comparison on a block. -/
lemma block_lower {v : ℕ → ℝ} {N : ℕ → ℕ} {i n : ℕ}
    (hvnn : ∀ n, 0 ≤ v n)
    (hmono : ∀ a b : ℕ, a ≤ b → (a : ℝ) * v a ≤ (b : ℝ) * v b)
    (h1 : N i ≤ n) (h2 : n ≤ N (i + 1)) (hNi : 0 < N i) :
    ((N i : ℝ) / (N (i + 1) : ℝ)) * v (N i) ≤ v n := by
  have hNi' : (0 : ℝ) < (N i : ℝ) := by exact_mod_cast hNi
  have h1' : (N i : ℝ) ≤ (n : ℝ) := by exact_mod_cast h1
  have h2' : (n : ℝ) ≤ (N (i + 1) : ℝ) := by exact_mod_cast h2
  have hni : (0 : ℝ) < (n : ℝ) := lt_of_lt_of_le hNi' h1'
  have hkey : (N i : ℝ) * v (N i) ≤ (n : ℝ) * v n := hmono (N i) n h1
  have h4 : ((N i : ℝ) / (n : ℝ)) * v (N i) ≤ v n := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hni]
    linarith [hkey]
  have h3 : ((N i : ℝ) / (N (i + 1) : ℝ)) ≤ ((N i : ℝ) / (n : ℝ)) :=
    div_le_div_of_nonneg_left (by positivity) hni h2'
  calc ((N i : ℝ) / (N (i + 1) : ℝ)) * v (N i)
      ≤ ((N i : ℝ) / (n : ℝ)) * v (N i) := mul_le_mul_of_nonneg_right h3 (hvnn _)
    _ ≤ v n := h4

/-! ## The two lacunary bounds -/

/-- Upper bound for the `limsup` along the lacunary subsequence
`⌊ρ ^ i⌋`: `limsup v ≤ ρ * lim v ⌊ρ^i⌋`. -/
lemma limsup_le_mul_of_lac {v : ℕ → ℝ} {ρ F : ℝ} (hρ : 1 < ρ)
    (hvnn : ∀ n, 0 ≤ v n)
    (hmono : ∀ a b : ℕ, a ≤ b → (a : ℝ) * v a ≤ (b : ℝ) * v b)
    (hF : Tendsto (fun i => v (lac ρ i)) atTop (nhds F)) :
    limsup v atTop ≤ ρ * F := by
  have hNmono : Monotone (lac ρ) := lac_mono (le_of_lt hρ)
  have hNunb : ∀ n : ℕ, ∃ i, n < lac ρ i := lac_unbounded hρ
  have hN1 : ∀ i, 0 < lac ρ i :=
    fun i => lt_of_lt_of_le Nat.zero_lt_one (one_le_lac (le_of_lt hρ) i)
  have hshift : Tendsto (fun i : ℕ => v (lac ρ (i + 1))) atTop (nhds F) :=
    hF.comp (tendsto_add_atTop_nat 1)
  have hw : Tendsto
      (fun i : ℕ => ((lac ρ (i + 1) : ℝ) / (lac ρ i : ℝ)) * v (lac ρ (i + 1)))
      atTop (nhds (ρ * F)) :=
    (lac_succ_ratio hρ).mul hshift
  rw [← hw.limsup_eq]
  refine limsup_le_limsup_of_block hNmono hNunb ?_ ⟨0, hvnn⟩ hw.isBoundedUnder_le
  intro i n h1 h2
  exact block_upper hvnn hmono h1 h2.le (hN1 i)

/-- Lower bound for the `liminf` along the lacunary subsequence
`⌊ρ ^ i⌋`: `lim v ⌊ρ^i⌋ / ρ ≤ liminf v`. -/
lemma inv_mul_le_liminf_of_lac {v : ℕ → ℝ} {ρ F : ℝ} (hρ : 1 < ρ)
    (hvnn : ∀ n, 0 ≤ v n)
    (hmono : ∀ a b : ℕ, a ≤ b → (a : ℝ) * v a ≤ (b : ℝ) * v b)
    (hbdd : ∃ B : ℝ, ∀ n, ‖v n‖ ≤ B)
    (hF : Tendsto (fun i => v (lac ρ i)) atTop (nhds F)) :
    ρ⁻¹ * F ≤ liminf v atTop := by
  have hρ0 : (0 : ℝ) < ρ := lt_trans zero_lt_one hρ
  have hNmono : Monotone (lac ρ) := lac_mono (le_of_lt hρ)
  have hNunb : ∀ n : ℕ, ∃ i, n < lac ρ i := lac_unbounded hρ
  have hN1 : ∀ i, 0 < lac ρ i :=
    fun i => lt_of_lt_of_le Nat.zero_lt_one (one_le_lac (le_of_lt hρ) i)
  have hratio : Tendsto
      (fun i : ℕ => ((lac ρ (i + 1) : ℝ) / (lac ρ i : ℝ))⁻¹) atTop (nhds ρ⁻¹) :=
    (lac_succ_ratio hρ).inv₀ (ne_of_gt hρ0)
  have hw : Tendsto
      (fun i : ℕ => ((lac ρ (i + 1) : ℝ) / (lac ρ i : ℝ))⁻¹ * v (lac ρ i))
      atTop (nhds (ρ⁻¹ * F)) :=
    hratio.mul hF
  rw [← hw.liminf_eq]
  refine liminf_le_liminf_of_block hNmono hNunb ?_ ?_ ?_
  · intro i n h1 h2
    have : ((lac ρ (i + 1) : ℝ) / (lac ρ i : ℝ))⁻¹ = (lac ρ i : ℝ) / (lac ρ (i + 1) : ℝ) :=
      inv_div _ _
    rw [this]
    exact block_lower hvnn hmono h1 h2.le (hN1 i)
  · refine ⟨0, Eventually.of_forall fun i => ?_⟩
    exact mul_nonneg (by positivity) (hvnn _)
  · obtain ⟨B, hB⟩ := hbdd
    exact ⟨B, Eventually.of_forall fun n =>
      le_trans (by rw [Real.norm_eq_abs]; exact le_abs_self _) (hB n)⟩

/-! ## The pointwise squeeze -/

/-- Pointwise form of the squeeze: a nonnegative sequence with nondecreasing mass, bounded, whose
lacunary subsequences `⌊ρ_m^i⌋` all converge for a family `ρ_m ↓ 1`, converges to its own `limsup`. -/
lemma lacunary_pointwise_aux {v : ℕ → ℝ} {ρ : ℕ → ℝ}
    (hρ : ∀ m : ℕ, 1 < ρ m) (hρ1 : Tendsto ρ atTop (nhds (1 : ℝ)))
    (hvnn : ∀ n : ℕ, 0 ≤ v n)
    (hmono : ∀ a b : ℕ, a ≤ b → (a : ℝ) * v a ≤ (b : ℝ) * v b)
    (hbdd : ∃ B : ℝ, ∀ n : ℕ, ‖v n‖ ≤ B)
    (hlac : ∀ m : ℕ, ∃ L : ℝ, Tendsto (fun i : ℕ => v (lac (ρ m) i)) atTop (nhds L)) :
    Tendsto v atTop (nhds (limsup v atTop)) := by
  choose L hL using hlac
  have hub : ∀ m, limsup v atTop ≤ ρ m * L m :=
    fun m => limsup_le_mul_of_lac (hρ m) hvnn hmono (hL m)
  have hlb : ∀ m, (ρ m)⁻¹ * L m ≤ liminf v atTop :=
    fun m => inv_mul_le_liminf_of_lac (hρ m) hvnn hmono hbdd (hL m)
  have hstep : ∀ m, limsup v atTop ≤ (ρ m) ^ 2 * liminf v atTop := by
    intro m
    have hm1 : (0 : ℝ) < ρ m := lt_trans zero_lt_one (hρ m)
    have hLm : L m ≤ ρ m * liminf v atTop := by
      have h := mul_le_mul_of_nonneg_left (hlb m) (le_of_lt hm1)
      rwa [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hm1), one_mul] at h
    calc limsup v atTop ≤ ρ m * L m := hub m
      _ ≤ ρ m * (ρ m * liminf v atTop) := mul_le_mul_of_nonneg_left hLm (le_of_lt hm1)
      _ = (ρ m) ^ 2 * liminf v atTop := by ring
  have hle : limsup v atTop ≤ liminf v atTop := by
    have h : Tendsto (fun m : ℕ => (ρ m) ^ 2 * liminf v atTop) atTop
        (nhds ((1 : ℝ) ^ 2 * liminf v atTop)) :=
      (hρ1.pow 2).mul_const (liminf v atTop)
    have := ge_of_tendsto (a := (1 : ℝ) ^ 2 * liminf v atTop) h
      (Eventually.of_forall hstep)
    simpa using this
  have hb : IsBoundedUnder (· ≤ ·) atTop v := by
    obtain ⟨B, hB⟩ := hbdd
    exact isBoundedUnder_of_eventually_le (Eventually.of_forall fun n =>
      le_trans (by rw [Real.norm_eq_abs]; exact le_abs_self _) (hB n))
  have hb' : IsBoundedUnder (· ≥ ·) atTop v :=
    isBoundedUnder_of_eventually_ge (Eventually.of_forall fun n => hvnn n)
  exact tendsto_of_le_liminf_of_limsup_le hle le_rfl hb hb'

/-! ## The a.e. statement -/

/-- Squeeze step.  A nonnegative sequence whose partial "mass" `N ↦ N · u N` is nondecreasing
and which is a.e. bounded above, and whose lacunary subsequences `⌊ρ^i⌋` converge a.e. for a
family `ρ` decreasing to `1`, converges a.e. -/
theorem ae_tendsto_of_lacunary_monotone {X : Type*} [MeasurableSpace X]
    {μ : MeasureTheory.Measure X}
    {u : ℕ → X → ℝ} {ρ : ℕ → ℝ} (hρ : ∀ m, 1 < ρ m)
    (hρ1 : Filter.Tendsto ρ Filter.atTop (nhds (1 : ℝ)))
    (hnn : ∀ N x, 0 ≤ u N x)
    (hmono : ∀ x, Monotone (fun N : ℕ => (N : ℝ) * u N x))
    (hbdd : Filter.Eventually (fun x => ∃ B : ℝ, ∀ N, ‖u N x‖ ≤ B) (MeasureTheory.ae μ))
    (hlac : ∀ m : ℕ, ∃ F : X → ℝ, Filter.Eventually
      (fun x => Filter.Tendsto (fun i => u (lac (ρ m) i) x) Filter.atTop (nhds (F x)))
      (MeasureTheory.ae μ)) :
    LacConv μ u := by
  choose F hF using hlac
  have h2 : ∀ᵐ x ∂μ, ∀ m : ℕ, ∃ L : ℝ,
      Filter.Tendsto (fun i : ℕ => u (lac (ρ m) i) x) Filter.atTop (nhds L) :=
    MeasureTheory.ae_all_iff.2 fun m => (hF m).mono fun x hx => ⟨F m x, hx⟩
  refine ⟨fun x => limsup (fun n : ℕ => u n x) atTop, ?_⟩
  filter_upwards [hbdd, h2] with x hxb hxl
  exact lacunary_pointwise_aux hρ hρ1 (fun n => hnn n x)
    (fun a b hab => hmono x hab) hxb hxl

end Work.BourgainPlan.Assembly
