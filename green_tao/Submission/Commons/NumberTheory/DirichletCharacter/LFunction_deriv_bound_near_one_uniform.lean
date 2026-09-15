import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.NumberTheory.Harmonic.Bounds
import Submission.Commons.NumberTheory.DirichletCharacter.LSeries_partial_sums_tendsto
import Submission.Commons.NumberTheory.DirichletCharacter.partial_sum_bound

open Complex Filter
open scoped Real BigOperators Topology

set_option autoImplicit false

namespace Commons.NumberTheory.DirichletCharacter

noncomputable section

/-- `exp (5/4) ≤ 4`. -/
lemma exp_five_fourths_le_four : Real.exp (5 / 4 : ℝ) ≤ 4 := by
  have h4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  have hle : (5 : ℝ) / 4 ≤ Real.log 4 := by
    rw [h4]
    have := Real.log_two_gt_d9
    linarith
  calc Real.exp (5 / 4) ≤ Real.exp (Real.log 4) := Real.exp_le_exp.mpr hle
    _ = 4 := Real.exp_log (by norm_num)

/-- The function `t ↦ t^{-(σ+1)}` is antitone on intervals contained in `[1,∞)` for `σ ≥ -1`. -/
lemma antitoneOn_rpow_neg_add_one {σ : ℝ} (hσ : -1 ≤ σ) {a b : ℕ} (ha : 1 ≤ a) :
    AntitoneOn (fun t : ℝ => t ^ (-(σ + 1))) (Set.Icc (a : ℝ) (b : ℝ)) := by
  intro x hx y hy hxy
  have ha1 : (1 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
  have hx1 : (1 : ℝ) ≤ x := le_trans ha1 hx.1
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx1
  have hy0 : 0 < y := lt_of_lt_of_le hx0 hxy
  have hexp : -(σ + 1) ≤ 0 := by linarith
  exact Real.rpow_le_rpow_of_nonpos hx0 hxy hexp

/-- Summation bound: for `σ > 0` and `a ≥ 1`, `∑_{a < i < b} i^{-(σ+1)} ≤ a^{-σ}/σ`. -/
lemma sum_Ico_rpow_neg_add_one_le {σ : ℝ} (hσ : 0 < σ) {a b : ℕ} (ha : 1 ≤ a) :
    ∑ i ∈ Finset.Ico (a + 1) b, (i : ℝ) ^ (-(σ + 1)) ≤ (a : ℝ) ^ (-σ) / σ := by
  rcases Nat.lt_or_ge b (a + 1) with hb | hb
  · rw [Finset.Ico_eq_empty_of_le (by omega : b ≤ a + 1), Finset.sum_empty]
    have h1 : (0 : ℝ) < (a : ℝ) := by exact_mod_cast (by omega : 0 < a)
    positivity
  · have hb1 : 1 ≤ b := by omega
    have habe : a ≤ b - 1 := by omega
    have hanti : AntitoneOn (fun t : ℝ => t ^ (-(σ + 1))) (Set.Icc (a : ℝ) ((b - 1 : ℕ) : ℝ)) :=
      antitoneOn_rpow_neg_add_one (by linarith) ha
    have hIco := AntitoneOn.sum_le_integral_Ico (a := a) (b := b - 1) habe hanti
    -- reindex the sum
    have hshift : (∑ i ∈ Finset.Ico (a + 1) b, (i : ℝ) ^ (-(σ + 1)))
        = ∑ x ∈ Finset.Ico a (b - 1), ((x + 1 : ℕ) : ℝ) ^ (-(σ + 1)) := by
      rw [Finset.sum_Ico_eq_sum_range, Finset.sum_Ico_eq_sum_range]
      refine Finset.sum_congr ?_ (fun k _ => ?_)
      · rw [show (b - 1) - a = b - (a + 1) by omega]
      · rw [show a + k + 1 = a + 1 + k by omega]
    rw [hshift]
    have hint : (∫ x in (a : ℝ)..((b - 1 : ℕ) : ℝ), x ^ (-(σ + 1)))
        = ((a : ℝ) ^ (-σ) - ((b - 1 : ℕ) : ℝ) ^ (-σ)) / σ := by
      have hc : ((-(σ + 1) : ℝ) ≠ -1) := by linarith
      have hnotmem : (0 : ℝ) ∉ Set.uIcc (a : ℝ) ((b - 1 : ℕ) : ℝ) := by
        rw [Set.uIcc_of_le (by exact_mod_cast habe)]
        intro hcon
        have h1 : (1 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
        simp only [Set.mem_Icc] at hcon
        linarith [hcon.2]
      have hcond : (-1 : ℝ) < -(σ + 1) ∨ (-(σ + 1) : ℝ) ≠ -1 ∧
          (0 : ℝ) ∉ Set.uIcc (a : ℝ) ((b - 1 : ℕ) : ℝ) := Or.inr ⟨hc, hnotmem⟩
      rw [integral_rpow hcond]
      have hexp : (-(σ + 1) : ℝ) + 1 = -σ := by ring
      rw [hexp]
      rw [div_neg, ← neg_div, neg_sub]
    calc ∑ x ∈ Finset.Ico a (b - 1), ((x + 1 : ℕ) : ℝ) ^ (-(σ + 1))
        ≤ ∫ x in (a : ℝ)..((b - 1 : ℕ) : ℝ), x ^ (-(σ + 1)) := hIco
      _ = ((a : ℝ) ^ (-σ) - ((b - 1 : ℕ) : ℝ) ^ (-σ)) / σ := hint
      _ ≤ (a : ℝ) ^ (-σ) / σ := by
          have h2 : 0 ≤ ((b - 1 : ℕ) : ℝ) ^ (-σ) := Real.rpow_nonneg (Nat.cast_nonneg _) _
          have h3 : 0 ≤ ((b - 1 : ℕ) : ℝ) ^ (-σ) / σ := div_nonneg h2 hσ.le
          rw [sub_div]
          linarith

/-- Abel summation bound for a tail of the Dirichlet series of a non-trivial character:
for `Re s > 0` and `1 ≤ M`,
`‖∑_{M < n ≤ K} χ(n) n^{-s}‖ ≤ N · M^{-Re s} · (2 + ‖s‖ / Re s)`. -/
lemma abel_tail_bound {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
    {s : ℂ} (hs : 0 < s.re) {M K : ℕ} (hM : 1 ≤ M) :
    ‖∑ n ∈ Finset.Icc (M + 1) K, (χ (n : ZMod N) : ℂ) * (n : ℂ) ^ (-s)‖
      ≤ (N : ℝ) * (M : ℝ) ^ (-s.re) * (2 + ‖s‖ / s.re) := by
  have hSb : ∀ j : ℕ, ‖∑ i ∈ Finset.range j, (χ (i : ZMod N) : ℂ)‖ ≤ (N : ℝ) :=
    fun j => partial_sum_bound χ hχ j
  have hMpos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast (by omega : 0 < M)
  rcases Nat.lt_or_ge K (M + 1) with hKM | hKM
  · rw [Finset.Icc_eq_empty (by omega), Finset.sum_empty, norm_zero]
    have h1 : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
    have h2 : (0 : ℝ) ≤ (M : ℝ) ^ (-s.re) := Real.rpow_nonneg (Nat.cast_nonneg M) _
    have h3 : (0 : ℝ) ≤ 2 + ‖s‖ / s.re := by
      have := norm_nonneg s
      positivity
    exact mul_nonneg (mul_nonneg h1 h2) h3
  · have hMK : M < K := by omega
    have hK1 : 1 ≤ K := by omega
    have hIcc : Finset.Icc (M + 1) K = Finset.Ico (M + 1) (K + 1) := by
      ext n; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
    have hpart := Finset.sum_Ico_by_parts (f := fun i : ℕ => (i : ℂ) ^ (-s))
      (g := fun i : ℕ => (χ (i : ZMod N) : ℂ)) (m := M + 1) (n := K + 1) (by omega)
    have hswap : (∑ n ∈ Finset.Icc (M + 1) K, (χ (n : ZMod N) : ℂ) * (n : ℂ) ^ (-s))
        = ∑ n ∈ Finset.Icc (M + 1) K, (n : ℂ) ^ (-s) * (χ (n : ZMod N) : ℂ) :=
      Finset.sum_congr rfl (fun n _ => mul_comm _ _)
    simp only [smul_eq_mul] at hpart
    rw [hswap, hIcc, hpart]
    have hfM : (0 : ℝ) < (M : ℝ) ^ s.re := Real.rpow_pos_of_pos hMpos _
    have hKle : (M : ℝ) ≤ (K : ℝ) := by exact_mod_cast (le_of_lt hMK)
    have h1 : ‖(K : ℂ) ^ (-s) * (∑ i ∈ Finset.range (K + 1), (χ (i : ZMod N) : ℂ))‖
        ≤ (N : ℝ) * (M : ℝ) ^ (-s.re) := by
      rw [norm_mul, Complex.norm_natCast_cpow_of_pos (by omega : 0 < K) (-s)]
      have hle : (K : ℝ) ^ (-s.re) ≤ (M : ℝ) ^ (-s.re) :=
        Real.rpow_le_rpow_of_nonpos hMpos hKle (by simp; linarith [hs])
      calc (K : ℝ) ^ (-s.re) * ‖∑ i ∈ Finset.range (K + 1), (χ (i : ZMod N) : ℂ)‖
          ≤ (K : ℝ) ^ (-s.re) * (N : ℝ) :=
            mul_le_mul_of_nonneg_left (hSb (K + 1)) (Real.rpow_nonneg (Nat.cast_nonneg K) _)
        _ ≤ (M : ℝ) ^ (-s.re) * (N : ℝ) := mul_le_mul_of_nonneg_right hle (Nat.cast_nonneg N)
        _ = (N : ℝ) * (M : ℝ) ^ (-s.re) := by ring
    have h2 : ‖((M + 1 : ℕ) : ℂ) ^ (-s) * (∑ i ∈ Finset.range (M + 1), (χ (i : ZMod N) : ℂ))‖
        ≤ (N : ℝ) * (M : ℝ) ^ (-s.re) := by
      rw [norm_mul, Complex.norm_natCast_cpow_of_pos (by omega : 0 < M + 1) (-s)]
      have hle : ((M + 1 : ℕ) : ℝ) ^ (-s.re) ≤ (M : ℝ) ^ (-s.re) :=
        Real.rpow_le_rpow_of_nonpos hMpos (by exact_mod_cast (Nat.le_succ M))
          (by simp; linarith [hs])
      calc ((M + 1 : ℕ) : ℝ) ^ (-s.re) * ‖∑ i ∈ Finset.range (M + 1), (χ (i : ZMod N) : ℂ)‖
          ≤ ((M + 1 : ℕ) : ℝ) ^ (-s.re) * (N : ℝ) :=
            mul_le_mul_of_nonneg_left (hSb (M + 1)) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
        _ ≤ (M : ℝ) ^ (-s.re) * (N : ℝ) := mul_le_mul_of_nonneg_right hle (Nat.cast_nonneg N)
        _ = (N : ℝ) * (M : ℝ) ^ (-s.re) := by ring
    have h3 : ‖∑ i ∈ Finset.Ico (M + 1) K,
          (((i + 1 : ℕ) : ℂ) ^ (-s) - ((i : ℕ) : ℂ) ^ (-s))
            * (∑ j ∈ Finset.range (i + 1), (χ (j : ZMod N) : ℂ))‖
        ≤ (N : ℝ) * (‖s‖ / s.re) * (M : ℝ) ^ (-s.re) := by
      calc ‖∑ i ∈ Finset.Ico (M + 1) K,
            (((i + 1 : ℕ) : ℂ) ^ (-s) - ((i : ℕ) : ℂ) ^ (-s))
              * (∑ j ∈ Finset.range (i + 1), (χ (j : ZMod N) : ℂ))‖
          ≤ ∑ i ∈ Finset.Ico (M + 1) K,
              ‖(((i + 1 : ℕ) : ℂ) ^ (-s) - ((i : ℕ) : ℂ) ^ (-s))
                * (∑ j ∈ Finset.range (i + 1), (χ (j : ZMod N) : ℂ))‖ := norm_sum_le _ _
        _ ≤ ∑ i ∈ Finset.Ico (M + 1) K, (N : ℝ) * (‖s‖ * (i : ℝ) ^ (-(s.re + 1))) := by
            refine Finset.sum_le_sum (fun i hi => ?_)
            rw [Finset.mem_Ico] at hi
            have hi1 : 1 ≤ i := by omega
            rw [norm_mul, norm_sub_rev]
            have hd := norm_cpow_nat_sub_succ_cpow_le s hs hi1
            calc ‖(i : ℂ) ^ (-s) - ((i + 1 : ℕ) : ℂ) ^ (-s)‖
                  * ‖∑ j ∈ Finset.range (i + 1), (χ (j : ZMod N) : ℂ)‖
                ≤ (‖s‖ * (i : ℝ) ^ (-(s.re + 1))) * (N : ℝ) :=
                  mul_le_mul hd (hSb (i + 1)) (norm_nonneg _) (by positivity)
              _ = (N : ℝ) * (‖s‖ * (i : ℝ) ^ (-(s.re + 1))) := by ring
        _ = (N : ℝ) * ‖s‖ * ∑ i ∈ Finset.Ico (M + 1) K, (i : ℝ) ^ (-(s.re + 1)) := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl (fun i _ => by ring)
        _ ≤ (N : ℝ) * ‖s‖ * ((M : ℝ) ^ (-s.re) / s.re) := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            exact sum_Ico_rpow_neg_add_one_le hs hM
        _ = (N : ℝ) * (‖s‖ / s.re) * (M : ℝ) ^ (-s.re) := by ring
    have htri : ‖(K : ℂ) ^ (-s) * (∑ i ∈ Finset.range (K + 1), (χ (i : ZMod N) : ℂ))
          - ((M + 1 : ℕ) : ℂ) ^ (-s) * (∑ i ∈ Finset.range (M + 1), (χ (i : ZMod N) : ℂ))
          - ∑ i ∈ Finset.Ico (M + 1) K,
              (((i + 1 : ℕ) : ℂ) ^ (-s) - ((i : ℕ) : ℂ) ^ (-s))
                * (∑ j ∈ Finset.range (i + 1), (χ (j : ZMod N) : ℂ))‖
        ≤ ‖(K : ℂ) ^ (-s) * (∑ i ∈ Finset.range (K + 1), (χ (i : ZMod N) : ℂ))‖
          + ‖((M + 1 : ℕ) : ℂ) ^ (-s) * (∑ i ∈ Finset.range (M + 1), (χ (i : ZMod N) : ℂ))‖
          + ‖∑ i ∈ Finset.Ico (M + 1) K,
              (((i + 1 : ℕ) : ℂ) ^ (-s) - ((i : ℕ) : ℂ) ^ (-s))
                * (∑ j ∈ Finset.range (i + 1), (χ (j : ZMod N) : ℂ))‖ := by
      calc _ ≤ ‖(K : ℂ) ^ (-s) * (∑ i ∈ Finset.range (K + 1), (χ (i : ZMod N) : ℂ))
              - ((M + 1 : ℕ) : ℂ) ^ (-s) * (∑ i ∈ Finset.range (M + 1), (χ (i : ZMod N) : ℂ))‖
            + ‖∑ i ∈ Finset.Ico (M + 1) K,
              (((i + 1 : ℕ) : ℂ) ^ (-s) - ((i : ℕ) : ℂ) ^ (-s))
                * (∑ j ∈ Finset.range (i + 1), (χ (j : ZMod N) : ℂ))‖ := norm_sub_le _ _
        _ ≤ _ := by
            have := norm_sub_le ((K : ℂ) ^ (-s) * (∑ i ∈ Finset.range (K + 1), (χ (i : ZMod N) : ℂ)))
              (((M + 1 : ℕ) : ℂ) ^ (-s) * (∑ i ∈ Finset.range (M + 1), (χ (i : ZMod N) : ℂ)))
            linarith
    calc _ ≤ ‖(K : ℂ) ^ (-s) * (∑ i ∈ Finset.range (K + 1), (χ (i : ZMod N) : ℂ))‖
          + ‖((M + 1 : ℕ) : ℂ) ^ (-s) * (∑ i ∈ Finset.range (M + 1), (χ (i : ZMod N) : ℂ))‖
          + ‖∑ i ∈ Finset.Ico (M + 1) K,
              (((i + 1 : ℕ) : ℂ) ^ (-s) - ((i : ℕ) : ℂ) ^ (-s))
                * (∑ j ∈ Finset.range (i + 1), (χ (j : ZMod N) : ℂ))‖ := htri
      _ ≤ (N : ℝ) * (M : ℝ) ^ (-s.re) + (N : ℝ) * (M : ℝ) ^ (-s.re)
          + (N : ℝ) * (‖s‖ / s.re) * (M : ℝ) ^ (-s.re) := by linarith [h1, h2, h3]
      _ = (N : ℝ) * (M : ℝ) ^ (-s.re) * (2 + ‖s‖ / s.re) := by ring

/-- Conversion `Icc a b = Ico a (b+1)` for natural numbers. -/
lemma Icc_eq_Ico_succ (a b : ℕ) : Finset.Icc a b = Finset.Ico a (b + 1) := by
  ext n; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega

/-- Bound for the `L`-function of a non-trivial character in the half plane `Re s > 0`,
obtained by splitting the Dirichlet series at `n = N` and using that the partial sums of
`χ` are bounded by the modulus. -/
theorem LFunction_norm_le_abel {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
    {z : ℂ} (hz : 0 < z.re) :
    ‖χ.LFunction z‖ ≤ (∑ n ∈ Finset.Icc 1 N, (n : ℝ) ^ (-z.re))
        + (N : ℝ) * (N : ℝ) ^ (-z.re) * (2 + ‖z‖ / z.re) := by
  have hN2 : 2 ≤ N := by
    rcases Nat.lt_or_ge N 2 with h | h
    · have hN0 : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
      have hN1 : N = 1 := by omega
      subst hN1
      exact absurd (Subsingleton.elim χ 1) hχ
    · exact h
  have hN1 : 1 ≤ N := by omega
  set F : ℕ → ℂ := fun K => ∑ n ∈ Finset.Icc 1 K, (χ (n : ZMod N) : ℂ) * (n : ℂ) ^ (-z) with hF
  have hlim : Tendsto F atTop (nhds (χ.LFunction z)) :=
    LSeries_partial_sums_tendsto χ hχ hz
  set H : ℂ := ∑ n ∈ Finset.Icc 1 N, (χ (n : ZMod N) : ℂ) * (n : ℂ) ^ (-z) with hH
  have hev : ∀ᶠ K : ℕ in atTop, F K - H = ∑ n ∈ Finset.Icc (N + 1) K, (χ (n : ZMod N) : ℂ) * (n : ℂ) ^ (-z) := by
    filter_upwards [eventually_ge_atTop N] with K hK
    have hconsec := Finset.sum_Ico_consecutive
      (f := fun n : ℕ => (χ (n : ZMod N) : ℂ) * (n : ℂ) ^ (-z))
      (by omega : 1 ≤ N + 1) (by omega : N + 1 ≤ K + 1)
    simp only [hF, hH]
    rw [Icc_eq_Ico_succ 1 K, Icc_eq_Ico_succ 1 N, Icc_eq_Ico_succ (N + 1) K, ← hconsec]
    ring
  have htail : Tendsto (fun K : ℕ => F K - H) atTop (nhds (χ.LFunction z - H)) :=
    hlim.sub tendsto_const_nhds
  have htail' : Tendsto (fun K : ℕ => ∑ n ∈ Finset.Icc (N + 1) K, (χ (n : ZMod N) : ℂ) * (n : ℂ) ^ (-z))
      atTop (nhds (χ.LFunction z - H)) := htail.congr' hev
  have hbd : ∀ K : ℕ, ‖∑ n ∈ Finset.Icc (N + 1) K, (χ (n : ZMod N) : ℂ) * (n : ℂ) ^ (-z)‖
      ≤ (N : ℝ) * (N : ℝ) ^ (-z.re) * (2 + ‖z‖ / z.re) :=
    fun K => abel_tail_bound χ hχ hz hN1
  have hkey : ‖χ.LFunction z - H‖ ≤ (N : ℝ) * (N : ℝ) ^ (-z.re) * (2 + ‖z‖ / z.re) :=
    le_of_tendsto' htail'.norm hbd
  have hHbound : ‖H‖ ≤ ∑ n ∈ Finset.Icc 1 N, (n : ℝ) ^ (-z.re) := by
    rw [hH]
    calc ‖∑ n ∈ Finset.Icc 1 N, (χ (n : ZMod N) : ℂ) * (n : ℂ) ^ (-z)‖
        ≤ ∑ n ∈ Finset.Icc 1 N, ‖(χ (n : ZMod N) : ℂ) * (n : ℂ) ^ (-z)‖ := norm_sum_le _ _
      _ ≤ ∑ n ∈ Finset.Icc 1 N, (n : ℝ) ^ (-z.re) := by
          refine Finset.sum_le_sum (fun n hn => ?_)
          rw [Finset.mem_Icc] at hn
          rw [norm_mul, Complex.norm_natCast_cpow_of_pos (by omega : 0 < n) (-z), Complex.neg_re]
          have hc : ‖(χ (n : ZMod N) : ℂ)‖ ≤ 1 := by
            simpa using χ.norm_le_one (n : ZMod N)
          have hp : 0 ≤ (n : ℝ) ^ (-z.re) := Real.rpow_nonneg (Nat.cast_nonneg n) _
          calc ‖(χ (n : ZMod N) : ℂ)‖ * (n : ℝ) ^ (-z.re) ≤ 1 * (n : ℝ) ^ (-z.re) :=
                mul_le_mul_of_nonneg_right hc hp
            _ = (n : ℝ) ^ (-z.re) := one_mul _
  calc ‖χ.LFunction z‖ = ‖(χ.LFunction z - H) + H‖ := by ring_nf
    _ ≤ ‖χ.LFunction z - H‖ + ‖H‖ := norm_add_le _ _
    _ ≤ (N : ℝ) * (N : ℝ) ^ (-z.re) * (2 + ‖z‖ / z.re) + ∑ n ∈ Finset.Icc 1 N, (n : ℝ) ^ (-z.re) :=
        add_le_add hkey hHbound
    _ = (∑ n ∈ Finset.Icc 1 N, (n : ℝ) ^ (-z.re))
          + (N : ℝ) * (N : ℝ) ^ (-z.re) * (2 + ‖z‖ / z.re) := by ring

/-- A non-trivial Dirichlet character has modulus at least `2`. -/
lemma two_le_of_ne_one {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) : 2 ≤ N := by
  rcases Nat.lt_or_ge N 2 with h | h
  · have hN0 : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
    have hN1 : N = 1 := by omega
    subst hN1
    exact absurd (Subsingleton.elim χ 1) hχ
  · exact h

/-- `∑_{n = 1}^{N} 1/n ≤ 1 + log N`. -/
lemma sum_Icc_one_div_le (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, (1 : ℝ) / (n : ℝ)) ≤ 1 + Real.log (N : ℝ) := by
  have hcast : (∑ n ∈ Finset.Icc 1 N, (1 : ℝ) / (n : ℝ)) = ((harmonic N : ℚ) : ℝ) := by
    rw [harmonic_eq_sum_Icc]
    push_cast
    simp [one_div]
  rw [hcast]
  exact harmonic_le_one_add_log N

/-- Uniform bound near `s = 1` for the `L`-function of a non-trivial character:
`‖L(χ, z)‖ ≤ 144 log(2N)` whenever `Re z ≥ 1 - 5/(4 log(2N))` and `‖z‖ ≤ 2`. -/
theorem LFunction_norm_le_log_near_one {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) {z : ℂ} (hlo : 1 - 5 / (4 * Real.log (2 * (N : ℝ))) ≤ z.re)
    (hnz : ‖z‖ ≤ 2) :
    ‖χ.LFunction z‖ ≤ 144 * Real.log (2 * (N : ℝ)) := by
  have hN2 : 2 ≤ N := two_le_of_ne_one χ hχ
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (NeZero.pos N)
  set ℓ : ℝ := Real.log (2 * (N : ℝ)) with hℓ
  have h2N4 : (4 : ℝ) ≤ 2 * (N : ℝ) := by
    have : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN2
    linarith
  have hlog4 : Real.log 4 ≤ ℓ := by
    rw [hℓ]
    exact Real.log_le_log (by norm_num) h2N4
  have hlog4_eq : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  have hℓ_gt : (5 : ℝ) / 4 < ℓ := by
    rw [hlog4_eq] at hlog4
    have := Real.log_two_gt_d9
    linarith
  have hℓpos : 0 < ℓ := by linarith
  have h5div : 5 / (4 * ℓ) < 1 := by
    rw [div_lt_one (by positivity)]
    linarith
  have hzpos : 0 < z.re := by linarith
  have hℓ43 : (4 : ℝ) / 3 ≤ ℓ := by
    rw [hlog4_eq] at hlog4
    have := Real.log_two_gt_d9
    linarith
  have hz16 : (1 : ℝ) / 16 ≤ z.re := by
    have h1 : 5 / (4 * ℓ) ≤ 15 / 16 := by
      rw [div_le_iff₀ (by positivity)]
      linarith
    linarith
  have hlogN_le : Real.log (N : ℝ) ≤ ℓ := by
    rw [hℓ]
    exact Real.log_le_log hNpos (by linarith)
  have hlogN_nn : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast (NeZero.pos N) : (1:ℝ) ≤ (N:ℝ))
  have hNpow : (N : ℝ) ^ (1 - z.re) ≤ 4 := by
    have h1 : 1 - z.re ≤ 5 / (4 * ℓ) := by linarith
    have h2 : (1 - z.re) * Real.log (N : ℝ) ≤ 5 / 4 := by
      calc (1 - z.re) * Real.log (N : ℝ) ≤ (5 / (4 * ℓ)) * Real.log (N : ℝ) :=
            mul_le_mul_of_nonneg_right h1 hlogN_nn
        _ ≤ (5 / (4 * ℓ)) * ℓ := mul_le_mul_of_nonneg_left hlogN_le (by positivity)
        _ = 5 / 4 := by field_simp
    calc (N : ℝ) ^ (1 - z.re) = Real.exp (Real.log (N : ℝ) * (1 - z.re)) :=
          Real.rpow_def_of_pos hNpos _
      _ = Real.exp ((1 - z.re) * Real.log (N : ℝ)) := by rw [mul_comm]
      _ ≤ Real.exp (5 / 4) := Real.exp_le_exp.mpr h2
      _ ≤ 4 := exp_five_fourths_le_four
  have hhead : (∑ n ∈ Finset.Icc 1 N, (n : ℝ) ^ (-z.re)) ≤ 8 * ℓ := by
    have hpt : ∀ n ∈ Finset.Icc 1 N, (n : ℝ) ^ (-z.re) ≤ 4 * ((n : ℝ)⁻¹) := by
      intro n hn
      rw [Finset.mem_Icc] at hn
      have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn.1
      have hn0 : (0 : ℝ) < (n : ℝ) := lt_of_lt_of_le zero_lt_one hn1
      have hnN : (n : ℝ) ≤ (N : ℝ) := by exact_mod_cast hn.2
      have hsplit : (n : ℝ) ^ (-z.re) = (n : ℝ) ^ (1 - z.re) * (n : ℝ) ^ (-1 : ℝ) := by
        rw [← Real.rpow_add hn0]
        congr 1
        ring
      rw [hsplit]
      have hle4 : (n : ℝ) ^ (1 - z.re) ≤ 4 := by
        rcases lt_or_ge (1 - z.re) 0 with hneg | hnonneg
        · have hone : (n : ℝ) ^ (1 - z.re) ≤ 1 :=
            Real.rpow_le_one_of_one_le_of_nonpos hn1 hneg.le
          linarith
        · calc (n : ℝ) ^ (1 - z.re) ≤ (N : ℝ) ^ (1 - z.re) :=
              Real.rpow_le_rpow (by positivity) hnN hnonneg
            _ ≤ 4 := hNpow
      calc (n : ℝ) ^ (1 - z.re) * (n : ℝ) ^ (-1 : ℝ) ≤ 4 * (n : ℝ) ^ (-1 : ℝ) :=
            mul_le_mul_of_nonneg_right hle4 (Real.rpow_nonneg (Nat.cast_nonneg n) _)
        _ = 4 * (n : ℝ)⁻¹ := by rw [Real.rpow_neg_one]
    calc (∑ n ∈ Finset.Icc 1 N, (n : ℝ) ^ (-z.re)) ≤ ∑ n ∈ Finset.Icc 1 N, 4 * ((n : ℝ)⁻¹) :=
          Finset.sum_le_sum hpt
      _ = 4 * ∑ n ∈ Finset.Icc 1 N, ((n : ℝ)⁻¹) := by rw [Finset.mul_sum]
      _ ≤ 4 * (1 + Real.log (N : ℝ)) := by
          refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
          have h := sum_Icc_one_div_le N
          simpa [one_div] using h
      _ ≤ 8 * ℓ := by linarith
  have htail : (N : ℝ) * (N : ℝ) ^ (-z.re) * (2 + ‖z‖ / z.re) ≤ 136 := by
    have h1 : (N : ℝ) * (N : ℝ) ^ (-z.re) ≤ 4 := by
      have h2 : (N : ℝ) * (N : ℝ) ^ (-z.re) = (N : ℝ) ^ (1 - z.re) := by
        conv_rhs => rw [show (1 : ℝ) - z.re = 1 + (-z.re) by ring]
        rw [Real.rpow_add hNpos, Real.rpow_one]
      rw [h2]
      exact hNpow
    have h3 : 2 + ‖z‖ / z.re ≤ 34 := by
      have h4 : ‖z‖ / z.re ≤ 32 := by
        rw [div_le_iff₀ hzpos]
        nlinarith [hnz, hz16]
      linarith
    calc (N : ℝ) * (N : ℝ) ^ (-z.re) * (2 + ‖z‖ / z.re) ≤ 4 * 34 :=
          mul_le_mul h1 h3 (by positivity) (by norm_num)
      _ = 136 := by norm_num
  have hmaster := LFunction_norm_le_abel χ hχ hzpos
  linarith [hmaster, hhead, htail]

/-- Cauchy's estimate applied to the uniform near-one bound: the derivative of `L(χ, ·)`
on the segment `1 - 1/log(2N) ≤ σ ≤ 1` is `O((log(2N))²)`, uniformly in `N` and `χ`. -/
theorem LFunction_deriv_bound_near_one_uniform :
    ∃ C : ℝ, 0 < C ∧ ∀ {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N), χ ≠ 1 → χ.IsPrimitive →
      ∀ σ : ℝ, 1 - 1 / Real.log (2 * (N : ℝ)) ≤ σ → σ ≤ 1 →
      ‖deriv (DirichletCharacter.LFunction χ) (σ : ℂ)‖ ≤ C * (Real.log (2 * (N : ℝ))) ^ 2 := by
  refine ⟨576, by norm_num, ?_⟩
  intro N _inst χ hχ _hprim σ hσlo hσhi
  have hN2 : 2 ≤ N := two_le_of_ne_one χ hχ
  set ℓ : ℝ := Real.log (2 * (N : ℝ)) with hℓ
  have h2N4 : (4 : ℝ) ≤ 2 * (N : ℝ) := by
    have : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN2
    linarith
  have hlog4 : Real.log 4 ≤ ℓ := by
    rw [hℓ]
    exact Real.log_le_log (by norm_num) h2N4
  have hlog4_eq : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  have hℓ43 : (4 : ℝ) / 3 ≤ ℓ := by
    rw [hlog4_eq] at hlog4
    have := Real.log_two_gt_d9
    linarith
  have hℓpos : 0 < ℓ := by linarith
  set r : ℝ := 1 / (4 * ℓ) with hr
  have hrpos : 0 < r := by rw [hr]; positivity
  have hr_le : r ≤ 1 / 4 := by
    rw [hr, div_le_iff₀ (by positivity)]
    linarith
  have hd : DiffContOnCl ℂ (DirichletCharacter.LFunction χ) (Metric.ball (σ : ℂ) r) :=
    (DirichletCharacter.differentiable_LFunction hχ).diffContOnCl
  have hbound : ∀ z ∈ Metric.sphere (σ : ℂ) r, ‖DirichletCharacter.LFunction χ z‖ ≤ 144 * ℓ := by
    intro z hz
    rw [Metric.mem_sphere, dist_eq_norm] at hz
    have hzre_abs : |z.re - σ| ≤ r := by
      have h := Complex.abs_re_le_norm (z - (σ : ℂ))
      rw [Complex.sub_re, Complex.ofReal_re] at h
      rwa [hz] at h
    have hzim_abs : |z.im| ≤ r := by
      have h := Complex.abs_im_le_norm (z - (σ : ℂ))
      rw [Complex.sub_im, Complex.ofReal_im, sub_zero] at h
      rwa [hz] at h
    have hzlo : 1 - 5 / (4 * Real.log (2 * (N : ℝ))) ≤ z.re := by
      have h1 : σ - r ≤ z.re := by linarith [(abs_le.mp hzre_abs).1]
      have h2 : 1 - 1 / ℓ ≤ σ := by
        have h := hσlo
        rwa [hℓ] at h
      have h3 : 1 - 5 / (4 * ℓ) = 1 - 1 / ℓ - 1 / (4 * ℓ) := by field_simp; ring
      have h4 : r = 1 / (4 * ℓ) := hr
      rw [← hℓ]
      linarith
    have hnz : ‖z‖ ≤ 2 := by
      have hzre_le : z.re ≤ 5 / 4 := by
        have h1 : z.re ≤ σ + r := by linarith [(abs_le.mp hzre_abs).2]
        linarith [hσhi, hr_le]
      have hzre_ge : (1 : ℝ) / 16 ≤ z.re := by
        have hlo' : 1 - 5 / (4 * ℓ) ≤ z.re := by rw [← hℓ] at hzlo; exact hzlo
        have h5 : 5 / (4 * ℓ) ≤ 15 / 16 := by
          rw [div_le_iff₀ (by positivity)]
          linarith
        linarith
      have h2 : ‖z‖ ^ 2 ≤ 4 := by
        rw [Complex.sq_norm, Complex.normSq_apply]
        have him := abs_le.mp hzim_abs
        nlinarith [hzre_le, hzre_ge, him.1, him.2, hr_le, sq_nonneg z.im]
      nlinarith [norm_nonneg z]
    exact LFunction_norm_le_log_near_one χ hχ hzlo hnz
  have hcauchy := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (f := DirichletCharacter.LFunction χ)
    (c := (σ : ℂ)) (R := r) (C := 144 * ℓ) hrpos hd hbound
  have hrval : (144 * ℓ) / r = 576 * ℓ ^ 2 := by
    rw [hr]
    field_simp
    ring
  calc ‖deriv (DirichletCharacter.LFunction χ) (σ : ℂ)‖ ≤ (144 * ℓ) / r := hcauchy
    _ = 576 * ℓ ^ 2 := hrval
    _ = 576 * (Real.log (2 * (N : ℝ))) ^ 2 := by rw [hℓ]

end

end Commons.NumberTheory.DirichletCharacter