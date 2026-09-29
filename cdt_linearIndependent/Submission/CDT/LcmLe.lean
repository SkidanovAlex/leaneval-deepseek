import Mathlib
import Submission.CDT.LcmUniform

open Finset Filter
open Submission.CDT.LcmUniform
open scoped BigOperators Topology

/-
# Lemma `lcm lemma` (2) of Calegari–Dimitrov–Tang: the uniform upper bound for the window `lcm`

The paper's `lcm lemma` (2): for every `ε > 0` there is `N` such that for all `n ≥ N` and all
`0 ≤ k ≤ n`, with `γ = k/n`, the window `lcm` `L_{n,k} = lcm(n-k, …, n)` satisfies

`log L_{n,k} ≤ k·Σ_{h ≤ ⌊1/γ⌋−1} 1/h + n/⌊1/γ⌋ + εn`;

in particular `k = o(n)` forces `L_{n,k} = exp(o(n))`.  Since `⌊1/γ⌋ = ⌊n/k⌋` for `γ = k/n`, this is
`log L_{n,k} ≤ (Σ_{h ≤ n/k − 1} 1/h)·k + n/(n/k) + εn` (and for `k = 0` the right-hand side is
`εn`, which bounds `log L_{n,0} = log n`).

The proof splits at the small scale `δ = 1/j`:

* if `k < ⌊n/j⌋`, then `L_{n,k} ≤ L_{n,⌊n/j⌋}` (the window is contained in the larger window) and the
  uniform asymptotic `Submission.CDT.LcmUniform.log_lcm_window_uniform`, evaluated at `γ = 1/j`,
  gives `log L_{n,k}/n ≤ H_{j−1}/j + 1/j + ε/4 ≤ ε`;
* if `k ≥ ⌊n/j⌋`, then `γ = k/n ≥ 1/(2j)` and the same asymptotic at `γ` gives the claimed bound
  verbatim.
-/

namespace Submission.CDT.LcmLe

theorem tendsto_harm_div (c : ℝ) (hc : 0 < c) :
    ∀ᶠ j : ℕ in Filter.atTop,
      (∑ m ∈ Finset.Icc 1 j, ((m : ℝ))⁻¹) / (j : ℝ) < c := by
  obtain ⟨N, hN⟩ : ∃ N : ℕ, 1 / ((N : ℝ) + 1) < c / 2 := by
    rcases exists_nat_gt (2 / c) with ⟨N, hN⟩
    refine ⟨N, ?_⟩
    rw [div_lt_iff₀ (by positivity : (0 : ℝ) < (N : ℝ) + 1)]
    have h1 : 2 / c < (N : ℝ) + 1 := by linarith
    have h2 : (c / 2) * (2 / c) = 1 := by field_simp
    have h3 : (c / 2) * (2 / c) < (c / 2) * ((N : ℝ) + 1) :=
      mul_lt_mul_of_pos_left h1 (by linarith : (0 : ℝ) < c / 2)
    linarith [h3, h2]
  set HN : ℝ := ∑ m ∈ Finset.Icc 1 N, ((m : ℝ))⁻¹ with hHN
  have hHNnn : 0 ≤ HN := by rw [hHN]; exact Finset.sum_nonneg (fun m _ => by positivity)
  obtain ⟨J, hJ1, hJ⟩ : ∃ J : ℕ, 1 ≤ J ∧ HN / (J : ℝ) < c / 2 := by
    rcases exists_nat_gt (HN / (c / 2)) with ⟨J₀, hJ₀⟩
    refine ⟨max J₀ 1, le_max_right J₀ 1, ?_⟩
    have h1 : HN / (c / 2) < (((max J₀ 1 : ℕ)) : ℝ) :=
      lt_of_lt_of_le hJ₀ (by exact_mod_cast le_max_left J₀ 1)
    rw [div_lt_iff₀ (by linarith : (0 : ℝ) < c / 2)] at h1
    rw [div_lt_iff₀ (by positivity : (0 : ℝ) < (((max J₀ 1 : ℕ)) : ℝ))]
    linarith
  filter_upwards [Filter.eventually_ge_atTop (max N (J + 1))] with j hj
  have hjN : N ≤ j := le_trans (le_max_left _ _) hj
  have hjJ : J ≤ j := by
    have h : J + 1 ≤ j := le_trans (le_max_right _ _) hj
    omega
  have hjpos : (0 : ℝ) < (j : ℝ) := by
    have : 0 < j := by omega
    exact_mod_cast this
  have hJpos : (0 : ℝ) < (J : ℝ) := by
    have h : (0 : ℕ) < J := by omega
    exact_mod_cast h
  have hHJ : HN / (j : ℝ) < c / 2 := by
    have h1 : HN / (j : ℝ) ≤ HN / (J : ℝ) :=
      div_le_div_of_nonneg_left hHNnn hJpos (by exact_mod_cast hjJ)
    linarith
  have hunion : Finset.Icc 1 j = Finset.Icc 1 N ∪ Finset.Icc (N + 1) j := by
    ext m; simp only [Finset.mem_Icc, Finset.mem_union]; omega
  have hdisj : Disjoint (Finset.Icc 1 N) (Finset.Icc (N + 1) j) := by
    rw [Finset.disjoint_left]; intro m hm hm'
    rw [Finset.mem_Icc] at hm hm'; omega
  have hsplit : (∑ m ∈ Finset.Icc 1 j, ((m : ℝ))⁻¹)
      = HN + ∑ m ∈ Finset.Icc (N + 1) j, ((m : ℝ))⁻¹ := by
    rw [hunion, Finset.sum_union hdisj, hHN]
  have htail : (∑ m ∈ Finset.Icc (N + 1) j, ((m : ℝ))⁻¹)
      ≤ ((j - N : ℕ) : ℝ) * (1 / ((N : ℝ) + 1)) := by
    calc (∑ m ∈ Finset.Icc (N + 1) j, ((m : ℝ))⁻¹)
        ≤ ∑ _m ∈ Finset.Icc (N + 1) j, (1 / ((N : ℝ) + 1)) := by
          refine Finset.sum_le_sum (fun m hm => ?_)
          rw [Finset.mem_Icc] at hm
          have h1 : (0 : ℝ) < (N : ℝ) + 1 := by positivity
          have h2 : ((N : ℝ) + 1) ≤ (m : ℝ) := by
            have h3 : N + 1 ≤ m := hm.1
            exact_mod_cast h3
          simpa [one_div] using one_div_le_one_div_of_le h1 h2
      _ = ((Finset.Icc (N + 1) j).card : ℝ) * (1 / ((N : ℝ) + 1)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ = ((j - N : ℕ) : ℝ) * (1 / ((N : ℝ) + 1)) := by
          rw [Nat.card_Icc]
          have h1 : j + 1 - (N + 1) = j - N := by omega
          rw [h1]
  have hbound : (∑ m ∈ Finset.Icc 1 j, ((m : ℝ))⁻¹) / (j : ℝ)
      ≤ HN / (j : ℝ) + 1 / ((N : ℝ) + 1) := by
    rw [hsplit, add_div]
    have hstep : (∑ m ∈ Finset.Icc (N + 1) j, ((m : ℝ))⁻¹) / (j : ℝ) ≤ 1 / ((N : ℝ) + 1) := by
      refine le_trans (div_le_div_of_nonneg_right htail hjpos.le) ?_
      have h1 : ((j - N : ℕ) : ℝ) * (1 / ((N : ℝ) + 1))
          ≤ (j : ℝ) * (1 / ((N : ℝ) + 1)) := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        exact_mod_cast Nat.sub_le j N
      calc (((j - N : ℕ) : ℝ) * (1 / ((N : ℝ) + 1))) / (j : ℝ)
          ≤ ((j : ℝ) * (1 / ((N : ℝ) + 1))) / (j : ℝ) :=
            div_le_div_of_nonneg_right h1 hjpos.le
        _ = 1 / ((N : ℝ) + 1) := by
            field_simp
    linarith [hstep]
  linarith [hbound, hHJ, hN]

theorem log_lcm_window_le_uniform (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in Filter.atTop, ∀ k : ℕ, k ≤ n →
      Real.log ((((Finset.Icc (n - k) n).erase 0).lcm (fun m => m) : ℕ) : ℝ)
        ≤ (∑ h ∈ Finset.Icc 1 (n / k - 1), ((h : ℝ))⁻¹) * (k : ℝ)
            + (n : ℝ) / ((n / k : ℕ) : ℝ) + ε * (n : ℝ) := by
  classical
  have hε2 : (0 : ℝ) < ε / 2 := by linarith
  obtain ⟨j, hj1, hjH⟩ : ∃ j : ℕ, 1 ≤ j ∧
      (∑ m ∈ Finset.Icc 1 j, ((m : ℝ))⁻¹) / (j : ℝ) + 1 / (j : ℝ) < ε / 2 := by
    have h1 : ∀ᶠ j : ℕ in Filter.atTop,
        (∑ m ∈ Finset.Icc 1 j, ((m : ℝ))⁻¹) / (j : ℝ) < ε / 4 :=
      tendsto_harm_div (ε / 4) (by linarith)
    have h2 : ∀ᶠ j : ℕ in Filter.atTop, 1 / (j : ℝ) < ε / 4 := by
      have ht : Filter.Tendsto (fun j : ℕ => (1 : ℝ) / (j : ℝ)) Filter.atTop (nhds 0) := by
        simpa [Function.comp_def] using
          (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop)
      exact ht.eventually (eventually_lt_nhds (by linarith))
    obtain ⟨N1, hN1⟩ := Filter.eventually_atTop.mp h1
    obtain ⟨N2, hN2⟩ := Filter.eventually_atTop.mp h2
    refine ⟨max N1 N2 + 1, by omega, ?_⟩
    have e1 := hN1 _ (by omega : N1 ≤ max N1 N2 + 1)
    have e2 := hN2 _ (by omega : N2 ≤ max N1 N2 + 1)
    linarith
  have hjpos : (0 : ℝ) < (j : ℝ) := by
    have h : (0 : ℕ) < j := by omega
    exact_mod_cast h
  set γ₀ : ℝ := 1 / (2 * (j : ℝ)) with hγ₀def
  have hγ₀pos : 0 < γ₀ := by rw [hγ₀def]; positivity
  have hγ₀1 : γ₀ ≤ 1 := by
    rw [hγ₀def, div_le_one (by positivity)]
    have hj1R : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj1
    linarith
  have hε4 : (0 : ℝ) < ε / 4 := by linarith
  have hunif := log_lcm_window_uniform γ₀ (ε / 4) hγ₀pos hγ₀1 hε4
  have hlogR : ∀ᶠ x : ℝ in Filter.atTop, Real.log x ≤ ε * x := by
    have h := Real.isLittleO_log_id_atTop.bound hε
    filter_upwards [h, Filter.eventually_ge_atTop (1 : ℝ)] with x hx hx1
    have h1 : |Real.log x| ≤ ε * |x| := by simpa only [Real.norm_eq_abs, id] using hx
    rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ x)] at h1
    exact le_trans (le_abs_self (Real.log x)) h1
  have hlog : ∀ᶠ n : ℕ in Filter.atTop, Real.log (n : ℝ) ≤ ε * (n : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually hlogR
  filter_upwards [hunif, hlog, Filter.eventually_ge_atTop (2 * j + 1)] with n hnun hnlog hnbig
  intro k hkn
  have hnR : (0 : ℝ) < (n : ℝ) := by
    have h : (0 : ℕ) < n := by omega
    exact_mod_cast h
  have hn1 : 1 ≤ n := by omega
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    have hL : (((Finset.Icc (n - 0) n).erase 0).lcm (fun m => m) : ℕ) = n := by
      have hset : (Finset.Icc (n - 0) n).erase 0 = {n} := by
        ext m
        simp only [Finset.mem_erase, Finset.mem_Icc, Finset.mem_singleton]
        omega
      rw [hset]
      simp
    rw [hL, Nat.div_zero]
    have hsum0 : (∑ h ∈ (Finset.Icc 1 (0 - 1) : Finset ℕ), ((h : ℝ))⁻¹) = 0 := by
      norm_num
    rw [hsum0]
    norm_num
    exact hnlog
  · have hk1 : 1 ≤ k := hk
    set k₀ : ℕ := n / j with hk₀def
    by_cases hcase : k < k₀
    · -- small `k`
      have hmono : (Finset.Icc (n - k) n).erase 0 ⊆ (Finset.Icc (n - k₀) n).erase 0 := by
        intro m hm
        rw [Finset.mem_erase] at hm ⊢
        obtain ⟨hm0, hmIcc⟩ := hm
        refine ⟨hm0, ?_⟩
        rw [Finset.mem_Icc] at hmIcc ⊢
        omega
      have hdiv := Finset.lcm_mono (f := fun m => m) hmono
      have h1pos : (0 : ℕ) < ((Finset.Icc (n - k) n).erase 0).lcm (fun m => m) :=
        Nat.pos_of_ne_zero (Finset.lcm_ne_zero_iff.mpr (fun m hm => (Finset.mem_erase.mp hm).1))
      have h2pos : (0 : ℕ) < ((Finset.Icc (n - k₀) n).erase 0).lcm (fun m => m) :=
        Nat.pos_of_ne_zero (Finset.lcm_ne_zero_iff.mpr (fun m hm => (Finset.mem_erase.mp hm).1))
      have hlogle : Real.log ((((Finset.Icc (n - k) n).erase 0).lcm (fun m => m) : ℕ) : ℝ)
          ≤ Real.log ((((Finset.Icc (n - k₀) n).erase 0).lcm (fun m => m) : ℕ) : ℝ) :=
        Real.log_le_log (by exact_mod_cast h1pos)
          (by exact_mod_cast Nat.le_of_dvd h2pos hdiv)
      have hbound : Real.log ((((Finset.Icc (n - k₀) n).erase 0).lcm (fun m => m) : ℕ) : ℝ)
          ≤ ε * (n : ℝ) := by
        have hkj : γ₀ ≤ 1 / (j : ℝ) := by
          rw [hγ₀def]
          rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < 2 * (j : ℝ)) hjpos]
          linarith [hjpos]
        have hjle1 : 1 / (j : ℝ) ≤ 1 := by rw [div_le_one hjpos]; exact_mod_cast hj1
        have h := hnun (1 / (j : ℝ)) hkj hjle1
        have hfk : ⌊(1 / (j : ℝ)) * (n : ℝ)⌋₊ = k₀ := by
          rw [show (1 / (j : ℝ)) * (n : ℝ) = (n : ℝ) / (j : ℝ) by ring]
          rw [Nat.floor_div_natCast, Nat.floor_natCast, hk₀def]
        have hfinv : ⌊1 / (1 / (j : ℝ))⌋₊ = j := by
          rw [one_div_one_div]
          exact Nat.floor_natCast j
        rw [hfk, hfinv] at h
        have hV : (1 / (j : ℝ)) * (∑ h ∈ Finset.Icc 1 (j - 1), ((h : ℝ))⁻¹) + ((j : ℝ))⁻¹ < ε / 2 := by
          have hle : (∑ h ∈ Finset.Icc 1 (j - 1), ((h : ℝ))⁻¹)
              ≤ ∑ h ∈ Finset.Icc 1 j, ((h : ℝ))⁻¹ := by
            refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc_right ?_) ?_
            · omega
            · intro x hx _
              positivity
          have h1 : (1 / (j : ℝ)) * (∑ h ∈ Finset.Icc 1 (j - 1), ((h : ℝ))⁻¹)
              ≤ (1 / (j : ℝ)) * (∑ h ∈ Finset.Icc 1 j, ((h : ℝ))⁻¹) :=
            mul_le_mul_of_nonneg_left hle (by positivity)
          have h2 : (1 / (j : ℝ)) * (∑ h ∈ Finset.Icc 1 j, ((h : ℝ))⁻¹)
              = (∑ h ∈ Finset.Icc 1 j, ((h : ℝ))⁻¹) / (j : ℝ) := by ring
          have h3 : ((j : ℝ))⁻¹ = 1 / (j : ℝ) := by rw [one_div]
          linarith [h1, h2, h3, hjH]
        have h2 : Real.log ((((Finset.Icc (n - k₀) n).erase 0).lcm (fun m => m) : ℕ) : ℝ) / (n : ℝ)
            ≤ (1 / (j : ℝ)) * (∑ h ∈ Finset.Icc 1 (j - 1), ((h : ℝ))⁻¹) + ((j : ℝ))⁻¹ + ε / 4 := by
          have := (abs_le.mp h).2
          linarith
        have h3 : Real.log ((((Finset.Icc (n - k₀) n).erase 0).lcm (fun m => m) : ℕ) : ℝ)
            ≤ ((1 / (j : ℝ)) * (∑ h ∈ Finset.Icc 1 (j - 1), ((h : ℝ))⁻¹) + ((j : ℝ))⁻¹ + ε / 4)
              * (n : ℝ) := (div_le_iff₀ hnR).mp h2
        have h4 : ((1 / (j : ℝ)) * (∑ h ∈ Finset.Icc 1 (j - 1), ((h : ℝ))⁻¹) + ((j : ℝ))⁻¹ + ε / 4)
              * (n : ℝ) ≤ ε * (n : ℝ) := by
          have h5 : (1 / (j : ℝ)) * (∑ h ∈ Finset.Icc 1 (j - 1), ((h : ℝ))⁻¹) + ((j : ℝ))⁻¹ + ε / 4 ≤ ε := by
            linarith [hV, hε4]
          nlinarith [h5, hnR]
        linarith [h3, h4]
      have hRHSnn : 0 ≤ (∑ h ∈ Finset.Icc 1 (n / k - 1), ((h : ℝ))⁻¹) * (k : ℝ)
          + (n : ℝ) / ((n / k : ℕ) : ℝ) := by
        have h1 : 0 ≤ (∑ h ∈ Finset.Icc 1 (n / k - 1), ((h : ℝ))⁻¹) :=
          Finset.sum_nonneg (fun h _ => by positivity)
        have h2 : (0 : ℝ) ≤ (k : ℝ) := by positivity
        have h3 : 0 ≤ (n : ℝ) / ((n / k : ℕ) : ℝ) := by positivity
        linarith [mul_nonneg h1 h2, h3]
      linarith [hlogle, hbound, hRHSnn]
    · -- large `k`
      have hk₀le : k₀ ≤ k := le_of_not_gt hcase
      set γ : ℝ := (k : ℝ) / (n : ℝ) with hγdef
      have hγpos : 0 < γ := by rw [hγdef]; positivity
      have hγle1 : γ ≤ 1 := by
        rw [hγdef, div_le_one hnR]
        exact_mod_cast hkn
      have hγge : γ₀ ≤ γ := by
        rw [hγdef, hγ₀def]
        rw [div_le_div_iff₀ (by positivity) hnR]
        have hnk : n < (k + 1) * j := by
          have h1 : n / j < k + 1 := by omega
          exact (Nat.div_lt_iff_lt_mul (by omega : 0 < j)).mp h1
        have h2 : (k + 1) * j ≤ 2 * k * j := by
          have : k + 1 ≤ 2 * k := by omega
          exact Nat.mul_le_mul_right j this
        have h3 : (2 * k * j : ℕ) ≤ 2 * k * j := le_refl _
        have h4 : ((n : ℕ) : ℝ) ≤ 2 * (k : ℝ) * (j : ℝ) := by
          have h5 : (n : ℕ) ≤ 2 * k * j := le_trans hnk.le (le_trans h2 h3)
          exact_mod_cast h5
        nlinarith [h4]
      have h := hnun γ hγge hγle1
      have hfk : ⌊γ * (n : ℝ)⌋₊ = k := by
        rw [hγdef, show (k : ℝ) / (n : ℝ) * (n : ℝ) = (k : ℝ) by
          have hn0 : (n : ℝ) ≠ 0 := ne_of_gt hnR
          field_simp]
        exact Nat.floor_natCast k
      have hfinv : ⌊1 / γ⌋₊ = n / k := by
        rw [hγdef, show 1 / ((k : ℝ) / (n : ℝ)) = (n : ℝ) / (k : ℝ) by
          have hk0 : (k : ℝ) ≠ 0 := by positivity
          field_simp]
        rw [Nat.floor_div_natCast, Nat.floor_natCast]
      rw [hfk, hfinv] at h
      have hV : (n : ℝ) * (γ * (∑ h ∈ Finset.Icc 1 (n / k - 1), ((h : ℝ))⁻¹)
            + ((n / k : ℕ) : ℝ)⁻¹)
          = (∑ h ∈ Finset.Icc 1 (n / k - 1), ((h : ℝ))⁻¹) * (k : ℝ)
            + (n : ℝ) / ((n / k : ℕ) : ℝ) := by
        rw [hγdef]
        have hk0 : (k : ℝ) ≠ 0 := by positivity
        first | (field_simp; ring) | field_simp
      have h2 : Real.log ((((Finset.Icc (n - k) n).erase 0).lcm (fun m => m) : ℕ) : ℝ) / (n : ℝ)
          ≤ γ * (∑ h ∈ Finset.Icc 1 (n / k - 1), ((h : ℝ))⁻¹) + ((n / k : ℕ) : ℝ)⁻¹ + ε / 4 := by
        have := (abs_le.mp h).2
        linarith
      have h3 : Real.log ((((Finset.Icc (n - k) n).erase 0).lcm (fun m => m) : ℕ) : ℝ)
          ≤ (γ * (∑ h ∈ Finset.Icc 1 (n / k - 1), ((h : ℝ))⁻¹) + ((n / k : ℕ) : ℝ)⁻¹ + ε / 4)
            * (n : ℝ) := (div_le_iff₀ hnR).mp h2
      have h4 : (γ * (∑ h ∈ Finset.Icc 1 (n / k - 1), ((h : ℝ))⁻¹) + ((n / k : ℕ) : ℝ)⁻¹ + ε / 4)
            * (n : ℝ)
          = ((∑ h ∈ Finset.Icc 1 (n / k - 1), ((h : ℝ))⁻¹) * (k : ℝ)
              + (n : ℝ) / ((n / k : ℕ) : ℝ)) + ε / 4 * (n : ℝ) := by
        rw [← hV]; ring
      linarith [h3, h4, mul_nonneg (by linarith : (0:ℝ) ≤ ε/4) hnR.le]

/-- **The `k = o(n)` case of Lemma `lcm lemma` (2).**  If `k n = o(n)` (and `k n ≤ n`), then
`log L_{n,k n} = o(n)`, i.e. `L_{n,k n} = exp(o(n))`.  This is the qualitative form of
`log_lcm_window_le_uniform`; the proof is the small-`k` half of that proof: a fixed scale
`δ = 1/j` with `V(1/j) < ε/2` is chosen once, and eventual smallness of `k n/n` puts `k n` below
`⌊n/j⌋`, where the window `lcm` is monotone and the uniform asymptotic applies. -/
theorem tendsto_log_lcm_window_div (k : ℕ → ℕ) (hk : ∀ n, k n ≤ n)
    (hko : Filter.Tendsto (fun n : ℕ => (k n : ℝ) / (n : ℝ)) Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun n : ℕ => Real.log
        ((((Finset.Icc (n - k n) n).erase 0).lcm (fun m => m) : ℕ) : ℝ) / (n : ℝ))
      Filter.atTop (nhds 0) := by
  classical
  refine tendsto_order.mpr ⟨?_, ?_⟩
  · intro b hb
    filter_upwards [Filter.eventually_ge_atTop 1] with n hn
    have hnR : (0 : ℝ) < (n : ℝ) := by
      have h : (0 : ℕ) < n := by omega
      exact_mod_cast h
    have hdvd : n ∣ ((Finset.Icc (n - k n) n).erase 0).lcm (fun m => m) := by
      refine Finset.dvd_lcm (f := fun m => m) ?_
      rw [Finset.mem_erase, Finset.mem_Icc]
      refine ⟨by omega, ⟨?_, le_refl n⟩⟩
      omega
    have hL1 : (1 : ℝ) ≤ ((((Finset.Icc (n - k n) n).erase 0).lcm (fun m => m) : ℕ) : ℝ) := by
      have h1 : (1 : ℕ) ≤ ((Finset.Icc (n - k n) n).erase 0).lcm (fun m => m) :=
        Nat.one_le_iff_ne_zero.mpr (Finset.lcm_ne_zero_iff.mpr (fun m hm => (Finset.mem_erase.mp hm).1))
      exact_mod_cast h1
    have hlog : 0 ≤ Real.log ((((Finset.Icc (n - k n) n).erase 0).lcm (fun m => m) : ℕ) : ℝ) :=
      Real.log_nonneg hL1
    have h0 : 0 ≤ Real.log ((((Finset.Icc (n - k n) n).erase 0).lcm (fun m => m) : ℕ) : ℝ) / (n : ℝ) :=
      div_nonneg hlog hnR.le
    linarith
  · intro b hb
    have hb2 : (0 : ℝ) < b / 2 := by linarith
    obtain ⟨j, hj1, hjH⟩ : ∃ j : ℕ, 1 ≤ j ∧
        (∑ m ∈ Finset.Icc 1 j, ((m : ℝ))⁻¹) / (j : ℝ) + 1 / (j : ℝ) < b / 2 := by
      have h1 : ∀ᶠ j : ℕ in Filter.atTop,
          (∑ m ∈ Finset.Icc 1 j, ((m : ℝ))⁻¹) / (j : ℝ) < b / 4 :=
        tendsto_harm_div (b / 4) (by linarith)
      have h2 : ∀ᶠ j : ℕ in Filter.atTop, 1 / (j : ℝ) < b / 4 := by
        have ht : Filter.Tendsto (fun j : ℕ => (1 : ℝ) / (j : ℝ)) Filter.atTop (nhds 0) := by
          simpa [Function.comp_def] using
            (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop)
        exact ht.eventually (eventually_lt_nhds (by linarith))
      obtain ⟨N1, hN1⟩ := Filter.eventually_atTop.mp h1
      obtain ⟨N2, hN2⟩ := Filter.eventually_atTop.mp h2
      refine ⟨max N1 N2 + 1, by omega, ?_⟩
      have e1 := hN1 _ (by omega : N1 ≤ max N1 N2 + 1)
      have e2 := hN2 _ (by omega : N2 ≤ max N1 N2 + 1)
      linarith
    have hjpos : (0 : ℝ) < (j : ℝ) := by
      have h : (0 : ℕ) < j := by omega
      exact_mod_cast h
    set γ₀ : ℝ := 1 / (2 * (j : ℝ)) with hγ₀def
    have hγ₀pos : 0 < γ₀ := by rw [hγ₀def]; positivity
    have hγ₀1 : γ₀ ≤ 1 := by
      rw [hγ₀def, div_le_one (by positivity)]
      have hj1R : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj1
      linarith
    have hunif := log_lcm_window_uniform γ₀ (b / 2) hγ₀pos hγ₀1 hb2
    have hsmall : ∀ᶠ n : ℕ in Filter.atTop, (k n : ℝ) < (n : ℝ) / (j : ℝ) := by
      have h1 := hko.eventually (eventually_lt_nhds (by positivity : (0 : ℝ) < 1 / (j : ℝ)))
      filter_upwards [h1, Filter.eventually_ge_atTop 1] with n hn hn1
      have hnR : (0 : ℝ) < (n : ℝ) := by
        have h : (0 : ℕ) < n := by omega
        exact_mod_cast h
      have h2 : (k n : ℝ) < (1 / (j : ℝ)) * (n : ℝ) := by
        have := (div_lt_iff₀ hnR).mp hn
        linarith
      calc (k n : ℝ) < (1 / (j : ℝ)) * (n : ℝ) := h2
        _ = (n : ℝ) / (j : ℝ) := by ring
    have hjle1 : 1 / (j : ℝ) ≤ 1 := by rw [div_le_one hjpos]; exact_mod_cast hj1
    have hkj : γ₀ ≤ 1 / (j : ℝ) := by
      rw [hγ₀def]
      rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < 2 * (j : ℝ)) hjpos]
      linarith [hjpos]
    filter_upwards [hunif, hsmall, Filter.eventually_ge_atTop 1] with n hnun hnk hn1
    have hnR : (0 : ℝ) < (n : ℝ) := by
      have h : (0 : ℕ) < n := by omega
      exact_mod_cast h
    have hk0 : k n ≤ n := hk n
    have hkn' : k n ≤ n / j := by
      have h2 : ⌊(n : ℝ) / (j : ℝ)⌋₊ = n / j := by
        rw [Nat.floor_div_natCast, Nat.floor_natCast]
      have h : k n ≤ ⌊(n : ℝ) / (j : ℝ)⌋₊ := Nat.le_floor (le_of_lt hnk)
      rwa [h2] at h
    have hmono : (Finset.Icc (n - k n) n).erase 0 ⊆ (Finset.Icc (n - n / j) n).erase 0 := by
      intro m hm
      rw [Finset.mem_erase] at hm ⊢
      obtain ⟨hm0, hmIcc⟩ := hm
      refine ⟨hm0, ?_⟩
      rw [Finset.mem_Icc] at hmIcc ⊢
      omega
    have hdiv := Finset.lcm_mono (f := fun m => m) hmono
    have h1pos : (0 : ℕ) < ((Finset.Icc (n - k n) n).erase 0).lcm (fun m => m) :=
      Nat.pos_of_ne_zero (Finset.lcm_ne_zero_iff.mpr (fun m hm => (Finset.mem_erase.mp hm).1))
    have h2pos : (0 : ℕ) < ((Finset.Icc (n - n / j) n).erase 0).lcm (fun m => m) :=
      Nat.pos_of_ne_zero (Finset.lcm_ne_zero_iff.mpr (fun m hm => (Finset.mem_erase.mp hm).1))
    have hlogle : Real.log ((((Finset.Icc (n - k n) n).erase 0).lcm (fun m => m) : ℕ) : ℝ)
        ≤ Real.log ((((Finset.Icc (n - n / j) n).erase 0).lcm (fun m => m) : ℕ) : ℝ) :=
      Real.log_le_log (by exact_mod_cast h1pos)
        (by exact_mod_cast Nat.le_of_dvd h2pos hdiv)
    have h := hnun (1 / (j : ℝ)) hkj hjle1
    have hfk : ⌊(1 / (j : ℝ)) * (n : ℝ)⌋₊ = n / j := by
      rw [show (1 / (j : ℝ)) * (n : ℝ) = (n : ℝ) / (j : ℝ) by ring]
      rw [Nat.floor_div_natCast, Nat.floor_natCast]
    have hfinv : ⌊1 / (1 / (j : ℝ))⌋₊ = j := by
      rw [one_div_one_div]
      exact Nat.floor_natCast j
    rw [hfk, hfinv] at h
    have hV : (1 / (j : ℝ)) * (∑ h ∈ Finset.Icc 1 (j - 1), ((h : ℝ))⁻¹) + ((j : ℝ))⁻¹ < b / 2 := by
      have hle : (∑ h ∈ Finset.Icc 1 (j - 1), ((h : ℝ))⁻¹) ≤ ∑ h ∈ Finset.Icc 1 j, ((h : ℝ))⁻¹ := by
        refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc_right ?_) ?_
        · omega
        · intro x hx _
          positivity
      have h1 : (1 / (j : ℝ)) * (∑ h ∈ Finset.Icc 1 (j - 1), ((h : ℝ))⁻¹)
          ≤ (1 / (j : ℝ)) * (∑ h ∈ Finset.Icc 1 j, ((h : ℝ))⁻¹) :=
        mul_le_mul_of_nonneg_left hle (by positivity)
      have h2 : (1 / (j : ℝ)) * (∑ h ∈ Finset.Icc 1 j, ((h : ℝ))⁻¹)
          = (∑ h ∈ Finset.Icc 1 j, ((h : ℝ))⁻¹) / (j : ℝ) := by ring
      have h3 : ((j : ℝ))⁻¹ = 1 / (j : ℝ) := by rw [one_div]
      linarith [h1, h2, h3, hjH]
    have hbnd : Real.log ((((Finset.Icc (n - n / j) n).erase 0).lcm (fun m => m) : ℕ) : ℝ) / (n : ℝ)
        ≤ (1 / (j : ℝ)) * (∑ h ∈ Finset.Icc 1 (j - 1), ((h : ℝ))⁻¹) + ((j : ℝ))⁻¹ + b / 2 := by
      have := (abs_le.mp h).2
      linarith
    have hfin : Real.log ((((Finset.Icc (n - k n) n).erase 0).lcm (fun m => m) : ℕ) : ℝ) / (n : ℝ)
        < b := by
      have h4 : Real.log ((((Finset.Icc (n - k n) n).erase 0).lcm (fun m => m) : ℕ) : ℝ) / (n : ℝ)
          ≤ Real.log ((((Finset.Icc (n - n / j) n).erase 0).lcm (fun m => m) : ℕ) : ℝ) / (n : ℝ) :=
        div_le_div_of_nonneg_right hlogle hnR.le
      linarith [h4, hbnd, hV]
    exact hfin


end LcmLe
