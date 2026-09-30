import Mathlib
import Submission.Work.BMF.VKGrowth

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The KL range bound for the shift-difference series

Given the Karatsuba–Landau (van der Corput first-derivative) bound for a *single* dyadic block
of a shifted sum,

`‖∑_{K < n ≤ R} (n+u)^{-(σ+it)}‖ ≤ 12 π K^{1-σ}/t`  (`K < R`, `R ≤ 2K`, `t ≤ K`),

we deduce the bound for the shift-difference series over a long range `Nt < m ≤ M` with
`|t| ≤ Nt ≤ M` and `σ ≥ 2/3`:

`‖∑_{Nt < m ≤ M} ((m+a)^{-s} - (m+1)^{-s})‖ ≤ (log M / log 2 + 2) · 24 π M^{1/3}/|t|`,  `s = σ + it`.

The sum of shift-differences is the difference of the two shifted sums over the *same* range
`(Nt, M]`, each of which is estimated dyadically.  On a block with left endpoint `K ≤ M` we have
`K^{1-σ} ≤ K^{1/3} ≤ M^{1/3}` (as `σ ≥ 2/3`, `K ≥ 1`), so every block costs at most
`24 π M^{1/3}/|t|`, and the number of blocks is at most `log M / log 2 + 1`.
-/

namespace Work.BMF.VKChain

open Finset

/-! ## Splitting a range at a point -/

private lemma sum_Ioc_split {α : Type*} [AddCommMonoid α] (f : ℕ → α) {a b c : ℕ}
    (hab : a ≤ b) (hbc : b ≤ c) :
    ∑ n ∈ Finset.Ioc a c, f n = (∑ n ∈ Finset.Ioc a b, f n) + ∑ n ∈ Finset.Ioc b c, f n := by
  have hdisj : Disjoint (Finset.Ioc a b) (Finset.Ioc b c) := by
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    simp only [Finset.mem_Ioc] at hx1 hx2
    omega
  rw [← Finset.Ioc_union_Ioc_eq_Ioc hab hbc, Finset.sum_union hdisj]

/-! ## Dyadic decomposition

If every block `(K,R]` with left endpoint `K ∈ [K₀, K₀ 2^J]` and `R ≤ 2K` is bounded by `B`,
then `(K₀, M]` is bounded by `(J+1)B` whenever `K₀ 2^J ≤ M ≤ K₀ 2^{J+1}`. -/

private lemma dyadic_sum_le (F : ℕ → ℂ) (K₀ : ℕ) (hK₀ : 1 ≤ K₀) {B : ℝ} (hB : 0 ≤ B) :
    ∀ J : ℕ,
      (∀ K R : ℕ, K₀ ≤ K → K ≤ K₀ * 2 ^ J → K < R → R ≤ 2 * K →
        ‖∑ n ∈ Finset.Ioc K R, F n‖ ≤ B) →
      ∀ M : ℕ, K₀ * 2 ^ J ≤ M → M ≤ K₀ * 2 ^ (J + 1) →
        ‖∑ n ∈ Finset.Ioc K₀ M, F n‖ ≤ ((J : ℝ) + 1) * B := by
  intro J
  induction J with
  | zero =>
    intro hblock M hM hM'
    have hM₀ : K₀ ≤ M := by simpa using hM
    have hM₀' : M ≤ 2 * K₀ := by
      have h := hM'
      rw [zero_add, pow_one] at h
      omega
    by_cases hlt : K₀ < M
    · have h := hblock K₀ M le_rfl (le_of_eq (mul_one K₀).symm) hlt hM₀'
      simpa using h
    · have hEq : M = K₀ := le_antisymm (not_lt.mp hlt) hM₀
      rw [hEq, Finset.Ioc_self, Finset.sum_empty, norm_zero]
      push_cast
      linarith
  | succ J ih =>
    intro hblock M hM hM'
    set K₁ : ℕ := K₀ * 2 ^ (J + 1) with hK₁def
    have hmid : K₀ * 2 ^ J ≤ K₁ := by
      rw [hK₁def]
      exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) (by omega))
    have hK₀mid : K₀ ≤ K₀ * 2 ^ J := by
      calc K₀ = K₀ * 1 := (mul_one K₀).symm
        _ ≤ K₀ * 2 ^ J := Nat.mul_le_mul_left _ Nat.one_le_two_pow
    have hK₀K₁ : K₀ ≤ K₁ := le_trans hK₀mid hmid
    have hK₁M : K₁ ≤ M := by rw [hK₁def]; exact hM
    have h1 : ‖∑ n ∈ Finset.Ioc K₀ K₁, F n‖ ≤ ((J : ℝ) + 1) * B :=
      ih (fun K R hK hKJ hKR hR2K => hblock K R hK (le_trans hKJ hmid) hKR hR2K)
        K₁ hmid (le_of_eq hK₁def)
    have h2 : ‖∑ n ∈ Finset.Ioc K₁ M, F n‖ ≤ B := by
      by_cases hlt : K₁ < M
      · refine hblock K₁ M hK₀K₁ ?_ hlt ?_
        · rw [hK₁def]
        · calc M ≤ K₀ * 2 ^ (J + 1 + 1) := hM'
            _ = 2 * (K₀ * 2 ^ (J + 1)) := by ring
      · have hEq : M = K₁ := le_antisymm (not_lt.mp hlt) hK₁M
        rw [hEq, Finset.Ioc_self, Finset.sum_empty, norm_zero]
        exact hB
    rw [sum_Ioc_split F hK₀K₁ hK₁M]
    calc ‖(∑ n ∈ Finset.Ioc K₀ K₁, F n) + ∑ n ∈ Finset.Ioc K₁ M, F n‖
        ≤ ‖∑ n ∈ Finset.Ioc K₀ K₁, F n‖ + ‖∑ n ∈ Finset.Ioc K₁ M, F n‖ := norm_add_le _ _
      _ ≤ ((J : ℝ) + 1) * B + B := add_le_add h1 h2
      _ = ((↑(J + 1) : ℝ) + 1) * B := by push_cast; ring

/-! ## The per-block KL bound for either sign of `t` -/

private lemma block_bound
    (hkl : ∀ {u σ t : ℝ}, 0 < u → u ≤ 1 → 0 < σ → 3 ≤ t → ∀ {K R : ℕ}, K < R →
      (R : ℝ) ≤ 2 * K → t ≤ (K : ℝ) →
      ‖∑ n ∈ Finset.Ioc K R, ((((n : ℝ) + u : ℝ)) : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I))‖ ≤
        12 * Real.pi * (K : ℝ) ^ (1 - σ) / t)
    {u σ t : ℝ} (hu : 0 < u) (hu1 : u ≤ 1) (hσ : 0 < σ) (ht : 3 ≤ |t|)
    {K R : ℕ} (hKR : K < R) (hR2K : (R : ℝ) ≤ 2 * K) (htK : |t| ≤ (K : ℝ)) :
    ‖∑ n ∈ Finset.Ioc K R, ((((n : ℝ) + u : ℝ)) : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I))‖ ≤
      12 * Real.pi * (K : ℝ) ^ (1 - σ) / |t| := by
  by_cases ht0 : 0 ≤ t
  · rw [abs_of_nonneg ht0]
    exact hkl hu hu1 hσ (by rw [abs_of_nonneg ht0] at ht; exact ht) hKR hR2K
      (by rw [← abs_of_nonneg ht0]; exact htK)
  · have htneg : t < 0 := lt_of_not_ge ht0
    have ht' : 3 ≤ -t := by
      rw [abs_of_neg htneg] at ht; linarith
    have htK' : -t ≤ (K : ℝ) := by
      rw [abs_of_neg htneg] at htK; linarith
    have key := hkl hu hu1 hσ ht' hKR hR2K htK'
    rw [abs_of_neg htneg]
    have hterm : ∀ n ∈ Finset.Ioc K R,
        ((((n : ℝ) + u : ℝ)) : ℂ) ^ (-((σ : ℂ) + ((-t : ℝ) : ℂ) * Complex.I))
          = (starRingEnd ℂ) (((((n : ℝ) + u : ℝ)) : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I))) := by
      intro n _
      have hy : (0 : ℝ) ≤ (n : ℝ) + u := by positivity
      rw [Commons.Analysis.Complex.conj_cpow_ofReal_of_nonneg hy]
      congr 1
      simp only [map_neg, map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]
      push_cast
      ring
    have hsum : (∑ n ∈ Finset.Ioc K R,
          ((((n : ℝ) + u : ℝ)) : ℂ) ^ (-((σ : ℂ) + ((-t : ℝ) : ℂ) * Complex.I)))
        = (starRingEnd ℂ) (∑ n ∈ Finset.Ioc K R,
          ((((n : ℝ) + u : ℝ)) : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I))) := by
      rw [map_sum]
      exact Finset.sum_congr rfl hterm
    have hnormeq : ‖∑ n ∈ Finset.Ioc K R,
          ((((n : ℝ) + u : ℝ)) : ℂ) ^ (-((σ : ℂ) + ((-t : ℝ) : ℂ) * Complex.I))‖
        = ‖∑ n ∈ Finset.Ioc K R,
          ((((n : ℝ) + u : ℝ)) : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I))‖ := by
      rw [hsum, Complex.norm_conj]
    rw [← hnormeq]
    exact key

/-! ## The main theorem -/

theorem shiftTerm_kl_range_le
    (hkl : ∀ {u σ t : ℝ}, 0 < u → u ≤ 1 → 0 < σ → 3 ≤ t → ∀ {K R : ℕ}, K < R →
      (R : ℝ) ≤ 2 * K → t ≤ (K : ℝ) →
      ‖∑ n ∈ Finset.Ioc K R, ((((n : ℝ) + u : ℝ)) : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I))‖ ≤
        12 * Real.pi * (K : ℝ) ^ (1 - σ) / t)
    {a σ t : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) (hσ : 0 < σ) (ht : 3 ≤ |t|) (hσ23 : 2 / 3 ≤ σ)
    {Nt M : ℕ} (hNt : |t| ≤ (Nt : ℝ)) (hNt3 : 1 ≤ Nt) (hNtM : Nt ≤ M) :
    ‖∑ m ∈ Finset.Ioc Nt M, Work.BMF.shiftTerm a m ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤
      (Real.log (M : ℝ) / Real.log 2 + 2) * (24 * Real.pi * (M : ℝ) ^ (1 / 3 : ℝ) / |t|) := by
  set s : ℂ := (σ : ℂ) + (t : ℂ) * Complex.I with hs
  set B : ℝ := 24 * Real.pi * (M : ℝ) ^ (1 / 3 : ℝ) / |t| with hBdef
  have htpos : (0 : ℝ) < |t| := by linarith
  have hBnn : 0 ≤ B := by
    rw [hBdef]
    exact div_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) Real.pi_nonneg)
        (Real.rpow_nonneg (by positivity) _)) htpos.le
  rcases eq_or_lt_of_le hNtM with hEq | hlt
  · -- `M = Nt`: the range is empty
    rw [← hEq, Finset.Ioc_self]
    have hNt1 : (1 : ℝ) ≤ (Nt : ℝ) := by exact_mod_cast hNt3
    have hlog : 0 ≤ Real.log (Nt : ℝ) := Real.log_nonneg hNt1
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have h1 : 0 ≤ Real.log (Nt : ℝ) / Real.log 2 + 2 :=
      add_nonneg (div_nonneg hlog hlog2.le) (by norm_num)
    simp only [Finset.sum_empty, norm_zero]
    exact mul_nonneg h1 hBnn
  · -- `Nt < M`
    obtain ⟨J, hJlow, hJhigh⟩ : ∃ J : ℕ, Nt * 2 ^ J ≤ M ∧ M ≤ Nt * 2 ^ (J + 1) := by
      have hex : ∃ J : ℕ, M ≤ Nt * 2 ^ J := ⟨M, by
        have h1 : M < 2 ^ M := Nat.lt_two_pow_self
        have h2 : 2 ^ M ≤ Nt * 2 ^ M := Nat.le_mul_of_pos_left _ (by omega)
        omega⟩
      have hJspec : M ≤ Nt * 2 ^ Nat.find hex := Nat.find_spec hex
      have hJpos : 0 < Nat.find hex := by
        by_contra hcon
        have h0 : Nat.find hex = 0 := Nat.eq_zero_of_not_pos hcon
        rw [h0, pow_zero, mul_one] at hJspec
        omega
      refine ⟨Nat.find hex - 1, ?_, ?_⟩
      · have hmin := Nat.find_min hex (m := Nat.find hex - 1) (by omega)
        omega
      · have hpred : Nat.find hex - 1 + 1 = Nat.find hex := Nat.succ_pred_eq_of_pos hJpos
        rw [hpred]
        exact hJspec
    have hblock : ∀ K R : ℕ, Nt ≤ K → K ≤ Nt * 2 ^ J → K < R → R ≤ 2 * K →
        ‖∑ n ∈ Finset.Ioc K R, Work.BMF.shiftTerm a n s‖ ≤ B := by
      intro K R hNK hKJ hKR hR2K
      have hKM : K ≤ M := le_trans hKJ hJlow
      have hK1 : 1 ≤ K := le_trans hNt3 hNK
      have hKt : |t| ≤ (K : ℝ) := le_trans hNt (by exact_mod_cast hNK)
      have hKr : (1 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK1
      have hKσ : (K : ℝ) ^ (1 - σ) ≤ (K : ℝ) ^ (1 / 3 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hKr (by linarith)
      have hK3M : (K : ℝ) ^ (1 / 3 : ℝ) ≤ (M : ℝ) ^ (1 / 3 : ℝ) :=
        Real.rpow_le_rpow (by positivity) (by exact_mod_cast hKM) (by norm_num)
      have hR2K' : (R : ℝ) ≤ 2 * (K : ℝ) := by exact_mod_cast hR2K
      have hsplit : (∑ n ∈ Finset.Ioc K R, Work.BMF.shiftTerm a n s)
          = (∑ n ∈ Finset.Ioc K R, ((((n : ℝ) + a : ℝ)) : ℂ) ^ (-s))
            - ∑ n ∈ Finset.Ioc K R, (((n + 1 : ℕ) : ℝ) : ℂ) ^ (-s) := by
        simp only [Work.BMF.shiftTerm]
        rw [Finset.sum_sub_distrib]
      have hA : ‖∑ n ∈ Finset.Ioc K R, ((((n : ℝ) + a : ℝ)) : ℂ) ^ (-s)‖ ≤
          12 * Real.pi * (K : ℝ) ^ (1 - σ) / |t| := by
        have h := block_bound hkl ha ha1 hσ ht hKR hR2K' hKt
        rwa [← hs] at h
      have hB' : ‖∑ n ∈ Finset.Ioc K R, (((n + 1 : ℕ) : ℝ) : ℂ) ^ (-s)‖ ≤
          12 * Real.pi * (K : ℝ) ^ (1 - σ) / |t| := by
        have h := block_bound (u := 1) (σ := σ) (t := t) hkl one_pos le_rfl hσ ht hKR hR2K' hKt
        rw [← hs] at h
        have heq : (∑ n ∈ Finset.Ioc K R, (((n + 1 : ℕ) : ℝ) : ℂ) ^ (-s))
            = ∑ n ∈ Finset.Ioc K R, ((((n : ℝ) + 1 : ℝ)) : ℂ) ^ (-s) := by
          refine Finset.sum_congr rfl (fun n _ => ?_)
          push_cast
          ring
        rw [heq]
        exact h
      calc ‖∑ n ∈ Finset.Ioc K R, Work.BMF.shiftTerm a n s‖
          = ‖(∑ n ∈ Finset.Ioc K R, ((((n : ℝ) + a : ℝ)) : ℂ) ^ (-s))
              - ∑ n ∈ Finset.Ioc K R, (((n + 1 : ℕ) : ℝ) : ℂ) ^ (-s)‖ := by rw [hsplit]
        _ ≤ ‖∑ n ∈ Finset.Ioc K R, ((((n : ℝ) + a : ℝ)) : ℂ) ^ (-s)‖
              + ‖∑ n ∈ Finset.Ioc K R, (((n + 1 : ℕ) : ℝ) : ℂ) ^ (-s)‖ := norm_sub_le _ _
        _ ≤ 12 * Real.pi * (K : ℝ) ^ (1 - σ) / |t| + 12 * Real.pi * (K : ℝ) ^ (1 - σ) / |t| :=
              add_le_add hA hB'
        _ = 24 * Real.pi * (K : ℝ) ^ (1 - σ) / |t| := by ring
        _ ≤ B := by
          rw [hBdef]
          have h3 : (K : ℝ) ^ (1 - σ) ≤ (M : ℝ) ^ (1 / 3 : ℝ) := le_trans hKσ hK3M
          have h4 : (K : ℝ) ^ (1 - σ) / |t| ≤ (M : ℝ) ^ (1 / 3 : ℝ) / |t| :=
            div_le_div_of_nonneg_right h3 htpos.le
          calc 24 * Real.pi * (K : ℝ) ^ (1 - σ) / |t|
              = 24 * Real.pi * ((K : ℝ) ^ (1 - σ) / |t|) := by ring
            _ ≤ 24 * Real.pi * ((M : ℝ) ^ (1 / 3 : ℝ) / |t|) :=
                mul_le_mul_of_nonneg_left h4 (by positivity)
            _ = 24 * Real.pi * (M : ℝ) ^ (1 / 3 : ℝ) / |t| := by ring
    have hdyad : ‖∑ n ∈ Finset.Ioc Nt M, Work.BMF.shiftTerm a n s‖ ≤ ((J : ℝ) + 1) * B :=
      dyadic_sum_le (fun n => Work.BMF.shiftTerm a n s) Nt hNt3 hBnn J hblock M hJlow hJhigh
    have hcount : ((J : ℝ) + 1) ≤ Real.log (M : ℝ) / Real.log 2 + 2 := by
      have h2pow : (2 : ℝ) ^ J ≤ (M : ℝ) := by
        have h1 : (1 : ℝ) ≤ (Nt : ℝ) := by exact_mod_cast hNt3
        have h2 : (1 : ℝ) * 2 ^ J ≤ (Nt : ℝ) * 2 ^ J :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
        have h3 : (Nt : ℝ) * 2 ^ J ≤ (M : ℝ) := by exact_mod_cast hJlow
        calc (2 : ℝ) ^ J = 1 * 2 ^ J := by ring
          _ ≤ (Nt : ℝ) * 2 ^ J := h2
          _ ≤ (M : ℝ) := h3
      have hlog : (J : ℝ) * Real.log 2 ≤ Real.log (M : ℝ) := by
        have h := Real.log_le_log (by positivity : (0 : ℝ) < (2 : ℝ) ^ J) h2pow
        rwa [Real.log_pow] at h
      have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
      have hJle : (J : ℝ) ≤ Real.log (M : ℝ) / Real.log 2 := (le_div_iff₀ hlog2).mpr hlog
      linarith
    calc ‖∑ m ∈ Finset.Ioc Nt M, Work.BMF.shiftTerm a m s‖
        ≤ ((J : ℝ) + 1) * B := hdyad
      _ ≤ (Real.log (M : ℝ) / Real.log 2 + 2) * B := mul_le_mul_of_nonneg_right hcount hBnn

end Work.BMF.VKChain
