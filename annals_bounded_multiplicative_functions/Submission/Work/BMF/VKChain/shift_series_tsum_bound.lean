import Mathlib
import Submission.Work.BMF.VKGrowth
import Submission.Work.BMF.VKGrowthDefs
import Submission.Work.BMF.HurwitzShift
import Submission.Work.BMF.VKChain.block_sum_uniform
import Submission.Work.BMF.VKChain.shift_head_bound
import Submission.Work.BMF.VKChain.shift_vk_range_bound
import Submission.Work.BMF.VKChain.kl_tail_block_bound
import Submission.Work.BMF.VKChain.shiftTerm_kl_range_le
import Submission.Work.BMF.VKChain.kl_prod_le_one
import Submission.Work.BMF.VKChain.tail_piece_le_one
import Submission.Work.BMF.VKChain.head_absorb
import Submission.Work.BMF.VKChain.gate_kappa_le
import Submission.Work.BMF.VKChain.sigma_range_facts

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.VKChain

open Finset
open scoped BigOperators

noncomputable section

/-! ## Elementary splitting/reindexing helpers -/

/-- `Ioc a b` reindexed as a range shifted by `a+1`. -/
lemma sum_Ioc_eq_sum_range_add {f : ℕ → ℂ} {a b : ℕ} (hab : a ≤ b) :
    (∑ i ∈ Finset.Ioc a b, f i) = ∑ k ∈ Finset.range (b - a), f (k + (a + 1)) := by
  have hIoc : Finset.Ioc a b = Finset.Ico (a + 1) (b + 1) := by
    ext x; simp only [Finset.mem_Ioc, Finset.mem_Ico]; omega
  rw [hIoc, Finset.sum_Ico_eq_sum_range]
  have h1 : b + 1 - (a + 1) = b - a := by omega
  rw [h1]
  exact Finset.sum_congr rfl (fun k _ => congrArg f (by omega))

/-- Splitting a shifted tail of a summable series. -/
lemma tsum_shifted_tail_split {f : ℕ → ℂ} (M k : ℕ)
    (hsum : Summable (fun m : ℕ => f (m + M))) :
    (∑' m : ℕ, f (m + M)) = (∑ m ∈ Finset.range k, f (m + M)) + ∑' m : ℕ, f ((M + k) + m) := by
  have h := hsum.sum_add_tsum_nat_add k
  rw [← h]
  congr 1
  exact tsum_congr (fun i => congrArg f (by omega))

/-- **Four-term decomposition of the shift-difference series.** -/
lemma shiftTerm_four_split {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) {s : ℂ} (hs : 0 < s.re)
    {K₀ Nt M : ℕ} (hK₀Nt : K₀ ≤ Nt) (hNtM : Nt ≤ M) :
    (∑' m : ℕ, Work.BMF.shiftTerm a m s) =
      ((∑ m ∈ Finset.range (K₀ + 1), Work.BMF.shiftTerm a m s)
        + (∑ m ∈ Finset.Ioc K₀ Nt, Work.BMF.shiftTerm a m s)
        + (∑ m ∈ Finset.Ioc Nt M, Work.BMF.shiftTerm a m s))
      + ∑' m : ℕ, Work.BMF.shiftTerm a ((M + 1) + m) s := by
  have hsum : Summable (fun m : ℕ => Work.BMF.shiftTerm a m s) := by
    have h := Work.BMF.summable_norm_shiftTerm (a := a) ha ha1 (s := s) hs 0
    simpa using h.of_norm
  have hsumM : ∀ M' : ℕ, Summable (fun m : ℕ => Work.BMF.shiftTerm a (m + M') s) :=
    fun M' => (summable_nat_add_iff M').mpr hsum
  have h1 : (∑' m : ℕ, Work.BMF.shiftTerm a m s) =
      (∑ m ∈ Finset.range (K₀ + 1), Work.BMF.shiftTerm a m s)
        + (∑' m : ℕ, Work.BMF.shiftTerm a (m + (K₀ + 1)) s) :=
    (hsum.sum_add_tsum_nat_add (K₀ + 1)).symm
  have h2 : (∑' m : ℕ, Work.BMF.shiftTerm a (m + (K₀ + 1)) s) =
      (∑ m ∈ Finset.range (Nt - K₀), Work.BMF.shiftTerm a (m + (K₀ + 1)) s)
        + (∑' m : ℕ, Work.BMF.shiftTerm a ((Nt + 1) + m) s) := by
    rw [tsum_shifted_tail_split (f := fun m => Work.BMF.shiftTerm a m s) (K₀ + 1) (Nt - K₀)
      (hsumM (K₀ + 1))]
    congr 1
    exact tsum_congr (fun i => congrArg (fun j => Work.BMF.shiftTerm a j s) (by omega))
  have h3 : (∑' m : ℕ, Work.BMF.shiftTerm a ((Nt + 1) + m) s) =
      (∑ m ∈ Finset.range (M - Nt), Work.BMF.shiftTerm a (m + (Nt + 1)) s)
        + (∑' m : ℕ, Work.BMF.shiftTerm a ((M + 1) + m) s) := by
    have hsym : (∑' m : ℕ, Work.BMF.shiftTerm a ((Nt + 1) + m) s)
        = (∑' m : ℕ, Work.BMF.shiftTerm a (m + (Nt + 1)) s) :=
      tsum_congr (fun m => congrArg (fun j => Work.BMF.shiftTerm a j s) (by omega))
    rw [hsym, tsum_shifted_tail_split (f := fun m => Work.BMF.shiftTerm a m s) (Nt + 1) (M - Nt)
      (hsumM (Nt + 1))]
    congr 1
    exact tsum_congr (fun i => congrArg (fun j => Work.BMF.shiftTerm a j s) (by omega))
  have hQ1 : (∑ m ∈ Finset.range (Nt - K₀), Work.BMF.shiftTerm a (m + (K₀ + 1)) s)
      = ∑ m ∈ Finset.Ioc K₀ Nt, Work.BMF.shiftTerm a m s :=
    (sum_Ioc_eq_sum_range_add (f := fun m => Work.BMF.shiftTerm a m s) hK₀Nt).symm
  have hQ2 : (∑ m ∈ Finset.range (M - Nt), Work.BMF.shiftTerm a (m + (Nt + 1)) s)
      = ∑ m ∈ Finset.Ioc Nt M, Work.BMF.shiftTerm a m s :=
    (sum_Ioc_eq_sum_range_add (f := fun m => Work.BMF.shiftTerm a m s) hNtM).symm
  rw [h1, h2, h3, hQ1, hQ2]
  ring

/-- Elementary absorption of the constant pieces. -/
lemma absorb_constants {X Y S : ℝ} (hS : 1 ≤ S) (hY : 0 ≤ Y) :
    (1 + X) * S + 2 + Y + 1 + 1 ≤ (5 + X + Y) * S := by
  have h4 : (0 : ℝ) ≤ 4 + Y := by linarith
  have h5 : (0 : ℝ) ≤ S - 1 := by linarith
  nlinarith [mul_nonneg h4 h5]

/-- A single shift-difference term with `m ≥ 1` has norm at most `2`. -/
lemma norm_shiftTerm_le_two {a σ t : ℝ} (ha : 0 < a) (hσ0 : 0 ≤ σ) {m : ℕ} (hm : 1 ≤ m) :
    ‖Work.BMF.shiftTerm a m ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ 2 := by
  set s : ℂ := (σ : ℂ) + (t : ℂ) * Complex.I with hs
  have hsre : s.re = σ := by rw [hs]; simp
  have h1 : 0 < (m : ℝ) + a := by positivity
  have h2 : 0 < (((m + 1 : ℕ) : ℝ)) := by positivity
  have hm1 : (1 : ℝ) ≤ (m : ℝ) + a := by
    have h : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    linarith
  have hm2 : (1 : ℝ) ≤ (((m + 1 : ℕ) : ℝ)) := by
    exact_mod_cast (by omega : 1 ≤ m + 1)
  have e1 : ‖((((m : ℝ) + a : ℝ)) : ℂ) ^ (-s)‖ = ((m : ℝ) + a) ^ (-σ) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos h1, Complex.neg_re, hsre]
  have e2 : ‖(((((m + 1 : ℕ) : ℝ))) : ℂ) ^ (-s)‖ = (((m + 1 : ℕ) : ℝ)) ^ (-σ) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos h2, Complex.neg_re, hsre]
  have b1 : ((m : ℝ) + a) ^ (-σ) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hm1 (by linarith)
  have b2 : ((((m + 1 : ℕ) : ℝ))) ^ (-σ) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hm2 (by linarith)
  have hgoal : ‖Work.BMF.shiftTerm a m s‖ ≤ 2 := by
    unfold Work.BMF.shiftTerm
    calc ‖((((m : ℝ) + a : ℝ)) : ℂ) ^ (-s) - ((((m + 1 : ℕ) : ℝ)) : ℂ) ^ (-s)‖
        ≤ ‖((((m : ℝ) + a : ℝ)) : ℂ) ^ (-s)‖ + ‖(((((m + 1 : ℕ) : ℝ)) : ℂ) ^ (-s))‖ :=
          norm_sub_le _ _
      _ = ((m : ℝ) + a) ^ (-σ) + (((m + 1 : ℕ) : ℝ)) ^ (-σ) := by rw [e1, e2]
      _ ≤ 1 + 1 := add_le_add b1 b2
      _ = 2 := by norm_num
  rw [hs] at hgoal
  exact hgoal

/-- **The shift-difference series in the Vinogradov–Korobov strip.**

`∑_{m≥0} ((m+a)^{-s} - (m+1)^{-s})` with `s = σ + i t` is `O(a^{-σ} + (log(|t|+3))^{6/7})`
uniformly for `0 < a ≤ 1`, `|t| ≥ 3` and `1 - (cvk/4)(log(|t|+3))^{-6/7} ≤ σ ≤ 2`.

Route (all inputs already proved here). Write `L = log(|t|+3)`, `κ = (L/cvk)^{6/7}`,
`K₀ = ⌈exp κ⌉₊ + 1`, `Nt = ⌈|t|⌉₊`, `M = ⌈|t|²⌉₊ + 1`. The gate `exp(1000/cvk^6) ≤ |t|` gives
`L ≥ 1000/cvk^6`, hence `κ ≤ L/2` and `exp κ + 2 ≤ |t|`, so `K₀ ≤ Nt` and `K₀ ∈ [exp κ, exp κ+2]`.
Split `∑' m, shiftTerm a m s = ∑_{m ∈ range K₀} shiftTerm a m s + ∑' m, shiftTerm a (K₀+m) s`
(`Work.BMF.shiftTerm_split`), then apply `Summable.sum_add_tsum_nat_add` twice to the tails, with
`k = Nt - K₀` and `k = M - Nt`, and reindex the finite tails so that they read
`∑_{m ∈ Ioc K₀ Nt} shiftTerm a m s` and `∑_{m ∈ Ioc Nt M} shiftTerm a m s`. Then:
* head `m < K₀`: `Work.BMF.VKChain.shift_head_bound` (its `hσκ` is `(1-σ)κ ≤ cvk^{1/7}/4 ≤ 1`),
  giving `a^{-σ} + 2·(5 e⁴)(2+κ) ≤ (1 + 10 e⁴(2+cvk^{-6/7}))(a^{-σ} + L^{6/7})`;
* VK range `Ioc K₀ Nt`: `Work.BMF.VKChain.shift_vk_range_bound`, its `hAb` input supplied by
  `Work.BMF.VKChain.block_sum_uniform` (literally the same expression, `L ≥ 1`), giving the
  constant `2 Cvk e^{1/2} Ab`;
* KL range `Ioc Nt M`: `Work.BMF.VKChain.shiftTerm_kl_range_le` with the block input
  `Work.BMF.VKChain.kl_tail_block_bound`, giving `(log M/log 2 + 2)·24π M^{1/3}/|t| ≤ 1`;
* far tail `m > M`: `Work.BMF.shiftTerm_tail_le`, giving `(‖s‖/σ) M^{-σ} ≤ 3|t|^{-1/2} ≤ 1`
  because `σ ≥ 3/4` and `M ≥ |t|²`.
`As` may depend on `Cvk, cvk`. -/
theorem shift_series_tsum_bound {Cvk cvk : ℝ} (hVK : Work.BMF.VKExpInput Cvk cvk)
    (hcvk0 : 0 < cvk) (hcvk1 : cvk ≤ 1) (hCvk : 0 < Cvk) :
    ∃ As : ℝ, 0 < As ∧ ∀ (a σ t : ℝ), 0 < a → a ≤ 1 → 3 ≤ |t| →
      Real.exp (1000 / cvk ^ 6) ≤ |t| →
      1 - (cvk / 4) * Real.log (|t| + 3) ^ (-(6 / 7 : ℝ)) ≤ σ → σ ≤ 2 →
      ‖∑' m : ℕ, Work.BMF.shiftTerm a m ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤
        As * (a ^ (-σ) + Real.log (|t| + 3) ^ (6 / 7 : ℝ)) := by
  obtain ⟨A, hApos, hAbA⟩ := block_sum_uniform cvk hcvk0 hcvk1
  refine ⟨5 + 10 * Real.exp 4 * (2 + cvk ^ (-(6 / 7) : ℝ)) + (2 * Cvk * Real.exp (1 / 2)) * A,
    ?_, ?_⟩
  · have hX : 0 ≤ 10 * Real.exp 4 * (2 + cvk ^ (-(6 / 7) : ℝ)) :=
      mul_nonneg (mul_nonneg (by norm_num) (Real.exp_pos 4).le)
        (by have h := Real.rpow_pos_of_pos hcvk0 (-(6 / 7 : ℝ)); linarith)
    have hY : 0 ≤ (2 * Cvk * Real.exp (1 / 2)) * A :=
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hCvk.le) (Real.exp_pos (1 / 2)).le)
        hApos.le
    linarith
  · intro a σ t ha ha1 ht3 hgate hσlow hσ2
    obtain ⟨hκhalf, hexpκ2, hL1⟩ := gate_kappa_le hcvk0 hcvk1 ht3 hgate
    set L : ℝ := Real.log (|t| + 3) with hL
    have hL1' : 1 ≤ L := by rw [hL]; exact hL1
    set κ : ℝ := (L / cvk) ^ (6 / 7 : ℝ) with hκ
    have hexpκ2' : Real.exp κ + 2 ≤ |t| := by rw [hκ, hL]; exact hexpκ2
    have hσlow' : 1 - cvk / 4 * L ^ (-(6 / 7 : ℝ)) ≤ σ := by rw [hL]; exact hσlow
    obtain ⟨hσκ', hσδ, hσ34⟩ := sigma_range_facts hcvk0 hcvk1 hL1' hσlow'
    have hσ0 : 0 < σ := by linarith
    have hσκ : (1 - σ) * κ ≤ 1 := by rw [hκ]; exact hσκ'
    have hσδ' : 1 - σ ≤ cvk ^ (6 / 7 : ℝ) / 2 * Real.log (|t| + 3) ^ (-(6 / 7 : ℝ)) := by
      rw [hL] at hσδ; exact hσδ
    set K₀ : ℕ := Nat.ceil (Real.exp κ) with hK₀
    set Nt : ℕ := Nat.ceil |t| with hNt
    set M : ℕ := Nat.ceil (|t| ^ 2) with hM
    have hκpos : 0 < κ := by rw [hκ]; exact Real.rpow_pos_of_pos (by positivity) _
    have hκ0 : 0 ≤ κ := hκpos.le
    have hexpκ1 : (1 : ℝ) < Real.exp κ := by
      rw [← Real.exp_zero]; exact Real.exp_lt_exp.mpr hκpos
    have hK₀2 : 2 ≤ K₀ := by
      rw [hK₀]
      have h : ¬ (Nat.ceil (Real.exp κ) ≤ 1) := by
        intro hle
        have h2 : Real.exp κ ≤ (1 : ℝ) := by simpa using (Nat.ceil_le).mp hle
        linarith
      omega
    have hK₀1 : 1 ≤ K₀ := by omega
    have hK₀le : (K₀ : ℝ) ≤ Real.exp κ + 2 := by
      rw [hK₀]
      have h := Nat.ceil_lt_add_one (Real.exp_nonneg κ)
      linarith
    have hK₀Nt : K₀ ≤ Nt := by
      have hreal : (K₀ : ℝ) ≤ (Nt : ℝ) := by
        rw [hK₀, hNt]
        have h1 := Nat.ceil_lt_add_one (Real.exp_nonneg κ)
        have h2 : Real.exp κ + 1 ≤ |t| := by linarith
        have h3 : |t| ≤ (Nat.ceil |t| : ℝ) := Nat.le_ceil |t|
        linarith
      exact_mod_cast hreal
    have hlogK₀ : (Real.log (|t| + 3) / cvk) ^ (6 / 7 : ℝ) ≤ Real.log (K₀ : ℝ) := by
      have hge : Real.exp κ ≤ (K₀ : ℝ) := by rw [hK₀]; exact Nat.le_ceil _
      have h1 : κ ≤ Real.log (K₀ : ℝ) := by
        have h := Real.log_le_log (Real.exp_pos κ) hge
        rwa [Real.log_exp] at h
      have hκL : κ = (Real.log (|t| + 3) / cvk) ^ (6 / 7 : ℝ) := by rw [hκ, hL]
      rwa [hκL] at h1
    have hNt2 : |t| ≤ (Nt : ℝ) := by rw [hNt]; exact Nat.le_ceil |t|
    have hNt1 : (Nt : ℝ) ≤ |t| + 1 := by
      rw [hNt]
      have h := Nat.ceil_lt_add_one (abs_nonneg t)
      linarith
    have hNt3 : 1 ≤ Nt := by
      have h : (3 : ℝ) ≤ (Nt : ℝ) := le_trans ht3 hNt2
      exact_mod_cast (show (1 : ℝ) ≤ (Nt : ℝ) by linarith)
    have hMge : |t| ^ 2 ≤ (M : ℝ) := by rw [hM]; exact Nat.le_ceil _
    have hMle : (M : ℝ) ≤ |t| ^ 2 + 2 := by
      rw [hM]
      have h := Nat.ceil_lt_add_one (by positivity : (0 : ℝ) ≤ |t| ^ 2)
      linarith
    have hM1 : 1 ≤ (M : ℝ) := by
      have h : (1 : ℝ) ≤ |t| ^ 2 := by nlinarith [abs_nonneg t, ht3]
      linarith
    have hNtM : Nt ≤ M := by
      have hmono : |t| ≤ |t| ^ 2 := by nlinarith [abs_nonneg t, ht3]
      have h := Nat.ceil_mono hmono
      rwa [← hNt, ← hM] at h
    have hgate1000 : Real.exp 1000 ≤ Real.exp (1000 / cvk ^ 6) := by
      apply Real.exp_le_exp.mpr
      rw [le_div_iff₀ (by positivity : (0 : ℝ) < cvk ^ 6)]
      have h4 : cvk ^ 6 ≤ 1 := pow_le_one₀ hcvk0.le hcvk1
      nlinarith
    have h1000 : Real.exp 1000 ≤ |t| := le_trans hgate1000 hgate
    have h16 : 16 ≤ |t| := by
      have h := Real.add_one_le_exp 1000
      linarith
    -- the four-term decomposition
    have hkey := shiftTerm_four_split (a := a) (s := (σ : ℂ) + (t : ℂ) * Complex.I)
      ha ha1 (by simpa using hσ0) hK₀Nt hNtM
    rw [hkey]
    set A1 : ℂ := ∑ m ∈ Finset.range (K₀ + 1),
      Work.BMF.shiftTerm a m ((σ : ℂ) + (t : ℂ) * Complex.I) with hA1
    set B1 : ℂ := ∑ m ∈ Finset.Ioc K₀ Nt,
      Work.BMF.shiftTerm a m ((σ : ℂ) + (t : ℂ) * Complex.I) with hB1
    set C1 : ℂ := ∑ m ∈ Finset.Ioc Nt M,
      Work.BMF.shiftTerm a m ((σ : ℂ) + (t : ℂ) * Complex.I) with hC1
    set D1 : ℂ := ∑' m : ℕ, Work.BMF.shiftTerm a ((M + 1) + m)
      ((σ : ℂ) + (t : ℂ) * Complex.I) with hD1
    -- head
    have hP1 : ‖A1‖ ≤ (1 + 10 * Real.exp 4 * (2 + cvk ^ (-(6 / 7) : ℝ)))
        * (a ^ (-σ) + L ^ (6 / 7 : ℝ)) + 2 := by
      rw [hA1]
      have hsplit : (∑ m ∈ Finset.range (K₀ + 1),
            Work.BMF.shiftTerm a m ((σ : ℂ) + (t : ℂ) * Complex.I))
          = (∑ m ∈ Finset.range K₀, Work.BMF.shiftTerm a m ((σ : ℂ) + (t : ℂ) * Complex.I))
            + Work.BMF.shiftTerm a K₀ ((σ : ℂ) + (t : ℂ) * Complex.I) :=
        Finset.sum_range_succ _ _
      rw [hsplit]
      have hhead := shift_head_bound (K₀ := K₀) (a := a) (σ := σ) (t := t) (κ := κ)
        ha hσ0 hσ2 hκ0 hσκ hK₀le
      have hsingle := norm_shiftTerm_le_two (a := a) (σ := σ) (t := t) ha hσ0.le hK₀1
      have habs := head_absorb (cvk := cvk) (L := L) (a := a) (σ := σ)
        hcvk0 hcvk1 ha ha1 hσ0 hL1'
      rw [← hκ] at habs
      calc ‖(∑ m ∈ Finset.range K₀, Work.BMF.shiftTerm a m ((σ : ℂ) + (t : ℂ) * Complex.I))
              + Work.BMF.shiftTerm a K₀ ((σ : ℂ) + (t : ℂ) * Complex.I)‖
          ≤ ‖∑ m ∈ Finset.range K₀, Work.BMF.shiftTerm a m ((σ : ℂ) + (t : ℂ) * Complex.I)‖
            + ‖Work.BMF.shiftTerm a K₀ ((σ : ℂ) + (t : ℂ) * Complex.I)‖ := norm_add_le _ _
        _ ≤ (a ^ (-σ) + 2 * (Real.exp 4 * 5 * (2 + κ))) + 2 := add_le_add hhead hsingle
        _ ≤ ((1 + 10 * Real.exp 4 * (2 + cvk ^ (-(6 / 7) : ℝ)))
              * (a ^ (-σ) + L ^ (6 / 7 : ℝ))) + 2 := by linarith
    -- VK range
    have hQ1 : ‖B1‖ ≤ (2 * Cvk * Real.exp (1 / 2)) * A := by
      rw [hB1]
      have hq := shift_vk_range_bound (Cvk := Cvk) (cvk := cvk) (Ab := A) (a := a) (σ := σ)
        (t := t) hVK hcvk0 hcvk1 ha ha1 ht3 hσ0 hσ2 hσδ' hK₀2 hNt1 hK₀Nt hlogK₀
        (hAbA (Real.log (|t| + 3)) hL1)
      calc ‖∑ m ∈ Finset.Ioc K₀ Nt, Work.BMF.shiftTerm a m ((σ : ℂ) + (t : ℂ) * Complex.I)‖
          ≤ 2 * Cvk * Real.exp (1 / 2) * A := hq
        _ = (2 * Cvk * Real.exp (1 / 2)) * A := by ring
    -- KL range
    have hQ2 : ‖C1‖ ≤ 1 := by
      rw [hC1]
      have hkl : ∀ {u σ' t' : ℝ}, 0 < u → u ≤ 1 → 0 < σ' → 3 ≤ t' → ∀ {K R : ℕ}, K < R →
          (R : ℝ) ≤ 2 * K → t' ≤ (K : ℝ) →
          ‖∑ n ∈ Finset.Ioc K R,
              ((((n : ℝ) + u : ℝ)) : ℂ) ^ (-((σ' : ℂ) + (t' : ℂ) * Complex.I))‖ ≤
            12 * Real.pi * (K : ℝ) ^ (1 - σ') / t' :=
        fun {u σ' t'} hu hu1 hσ' ht' {K R} hRK hR2K htK =>
          kl_tail_block_bound hu hu1 hσ' ht' hRK hR2K htK
      have hq := shiftTerm_kl_range_le hkl ha ha1 hσ0 ht3 (by linarith : 2 / 3 ≤ σ)
        hNt2 hNt3 hNtM
      have hprod := kl_prod_le_one (t := t) (M := (M : ℝ)) hM1 hMle h1000
      calc ‖∑ m ∈ Finset.Ioc Nt M, Work.BMF.shiftTerm a m ((σ : ℂ) + (t : ℂ) * Complex.I)‖
          ≤ (Real.log (M : ℝ) / Real.log 2 + 2)
              * (24 * Real.pi * (M : ℝ) ^ (1 / 3 : ℝ) / |t|) := hq
        _ ≤ 1 := hprod
    -- far tail
    have hT : ‖D1‖ ≤ 1 := by
      rw [hD1]
      have htail := Work.BMF.shiftTerm_tail_le (a := a) (σ := σ) (t := t) ha ha1 hσ0 (M + 1)
      have hMge' : |t| ^ 2 ≤ ((M + 1 : ℕ) : ℝ) := by
        have h : (M : ℝ) ≤ ((M + 1 : ℕ) : ℝ) := by push_cast; linarith
        linarith
      have htp := tail_piece_le_one (σ := σ) (t := t) (M := ((M + 1 : ℕ) : ℝ)) (a := a)
        ha hσ34 hσ2 hMge' h16
      exact le_trans htail htp
    -- assembly
    have hYnn : 0 ≤ (2 * Cvk * Real.exp (1 / 2)) * A :=
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hCvk.le) (Real.exp_pos (1 / 2)).le)
        hApos.le
    have hS : 1 ≤ a ^ (-σ) + L ^ (6 / 7 : ℝ) := by
      have haσ : a ^ σ ≤ 1 := Real.rpow_le_one ha.le ha1 hσ0.le
      have hinv : 1 ≤ (a ^ σ)⁻¹ := (one_le_inv₀ (Real.rpow_pos_of_pos ha σ)).mpr haσ
      have h1 : 1 ≤ a ^ (-σ) := by
        rw [Real.rpow_neg ha.le]
        exact hinv
      have h2 : 0 ≤ L ^ (6 / 7 : ℝ) := Real.rpow_nonneg (by linarith) _
      linarith
    have htri : ‖(((A1 + B1) + C1) + D1)‖ ≤ ‖A1‖ + ‖B1‖ + ‖C1‖ + ‖D1‖ := by
      have h1 := norm_add_le ((A1 + B1) + C1) D1
      have h2 := norm_add_le (A1 + B1) C1
      have h3 := norm_add_le A1 B1
      linarith
    calc ‖(((A1 + B1) + C1) + D1)‖
        ≤ ‖A1‖ + ‖B1‖ + ‖C1‖ + ‖D1‖ := htri
      _ ≤ ((1 + 10 * Real.exp 4 * (2 + cvk ^ (-(6 / 7) : ℝ)))
              * (a ^ (-σ) + L ^ (6 / 7 : ℝ)) + 2) + (2 * Cvk * Real.exp (1 / 2)) * A + 1 + 1 :=
            by linarith
      _ ≤ (5 + 10 * Real.exp 4 * (2 + cvk ^ (-(6 / 7) : ℝ))
              + (2 * Cvk * Real.exp (1 / 2)) * A) * (a ^ (-σ) + L ^ (6 / 7 : ℝ)) :=
          absorb_constants hS hYnn

end

end Work.BMF.VKChain
