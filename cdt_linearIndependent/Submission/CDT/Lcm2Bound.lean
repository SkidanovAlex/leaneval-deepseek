import Mathlib
import Submission.CDT.LcmGe
import Submission.CDT.LcmGeUniform
import Submission.CDT.LcmLe
import Submission.CDT.LcmUniform
import Submission.Commons.NumberTheory.Chebyshev.prod_primes_dvd
import Submission.Commons.Analysis.ExpLog.harmonic_le_one_add_log

open Finset Filter
open scoped BigOperators Topology

/-
# Lemma `lcm-2` (2) of Calegari–Dimitrov–Tang (arXiv:2408.15403): the uniform upper bound

The paper's Lemma `lcm-2` (2): for every `ε > 0` there is `N` such that for all `n ≥ N` and all
`0 ≤ k, l ≤ n` one has

`log L^{≥ l}_{n,k} ≤ k·Σ_{h ≤ h₀} 1/h + (n/⌊(n + (l-k)⁺)/max(k,l)⌋ - l)⁺ + εn`,

where `h₀ = ⌊(n-k)/max(k,l)⌋`, `L^{≥ l}_{n,k}` is the product of the primes `p > l` that have a
multiple in `[n-k, n]`, and `x⁺ = max(x,0)`.

The proof follows the paper, with the case analysis by the size of `k` and `l`:

* **`k` short** (`k·J ≤ n`): the window lcm is monotone in `k` and the uniform Lemma `lcm lemma`
  (1) at the fixed scale `γ = 1/J` bounds it by `exp((H(J-1)/J + 1/J + η)·n)`.
* **`l` large** (`(2J-1)·n ≤ 2J·l`): every prime `p > l` occurring divides `p` itself into the
  window, so `log L^{≥ l}_{n,k} ≤ θ(n) - θ(⌊(1-1/(2J))n⌋) ≤ (ε/4)·n` by the prime number theorem.
* **`l` short, `k` long**: `l ≤ k`, so `max(k,l) = k`, and Lemma `lcm lemma` (2) gives the bound
  verbatim.
* **middle range** (`k, l ≥ n/J` and `l < (1-1/(2J))n`): the uniform Lemma `lcm-2` (1) gives the
  exact model `(k+1)H_h + n/(h+1) - l + C` (`h = ⌊(n-k-1)/max(k,l)⌋`), and the elementary
  comparison **`comparison`** shows that this model is at most the paper's closed form plus the
  `O(log n)` term `H_h₀`, which is absorbed in `εn`.

The paper's middle-range bound is proved by a floor/harmonic comparison; the auxiliary lemmas here
(`comparison`, `hden_eq`, `H_le_log`) make that comparison explicit and elementary.
-/

namespace Submission.CDT.Lcm2Bound

open Submission.CDT.LcmGe (Lge Lge_cast log_Lge theta_sub_theta_eq)
open Submission.CDT.LcmGeUniform (lcm_ge_harmonic_uniform)
open Submission.CDT.LcmLe (log_lcm_window_le_uniform tendsto_harm_div)
open Submission.CDT.LcmUniform (log_lcm_window_uniform theta_rel_error)

noncomputable def H (m : ℕ) : ℝ := ∑ a ∈ Finset.Icc 1 m, ((a : ℝ))⁻¹

theorem add_div_eq (n k : ℕ) (hkn : k ≤ n) (hk : 0 < k) : n / k = (n - k) / k + 1 := by
  conv_lhs => rw [← Nat.sub_add_cancel hkn]
  rw [show (n - k) + k = (n - k) + k * 1 from by ring]
  rw [Nat.add_mul_div_left _ _ hk]

theorem hden_eq (n k l : ℕ) (hk : k ≤ n) (hl : l ≤ n) (hM : 0 < max k l) :
    (n + (l - k)) / max k l = (n - k) / max k l + 1 := by
  rcases le_total k l with hkl | hlk
  · have hmax : max k l = l := max_eq_right hkl
    have hpos : 0 < l := by rw [← hmax]; exact hM
    rw [hmax]
    have h1 : n + (l - k) = (n - k) + l := by omega
    rw [h1, show (n - k) + l = (n - k) + l * 1 from by ring]
    rw [Nat.add_mul_div_left _ _ hpos]
  · have hmax : max k l = k := max_eq_left hlk
    have hpos : 0 < k := by rw [← hmax]; exact hM
    rw [hmax, Nat.sub_eq_zero_of_le hlk, Nat.add_zero]
    exact add_div_eq n k hk hpos

theorem H_nonneg (m : ℕ) : 0 ≤ H m := Finset.sum_nonneg fun a _ => by positivity

theorem H_eq (m : ℕ) : H m = ∑ a ∈ Finset.Icc 1 m, (1:ℝ)/(a:ℝ) := by
  unfold H; exact Finset.sum_congr rfl fun a _ => by rw [one_div]

theorem H_succ (m : ℕ) : H (m+1) = H m + ((m:ℝ)+1)⁻¹ := by
  unfold H
  rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ m + 1)]
  norm_num

theorem H_le_log (m : ℕ) : H m ≤ 1 + Real.log (m:ℝ) := by
  rcases Nat.eq_zero_or_pos m with h | h
  · rw [h]; unfold H; simp
  · rw [H_eq]
    exact Commons.Analysis.ExpLog.harmonic_le_one_add_log m h

theorem add_max_sub (x l : ℝ) : l + max (x - l) 0 = max x l := by
  rcases le_total l x with h | h
  · have h1 : max (x - l) 0 = x - l := max_eq_left (by linarith : 0 ≤ x - l)
    have h2 : max x l = x := max_eq_left h
    rw [h1, h2]; ring
  · have h1 : max (x - l) 0 = 0 := max_eq_right (by linarith : x - l ≤ 0)
    have h2 : max x l = l := max_eq_right h
    rw [h1, h2]; ring

theorem add_max_neg (y : ℝ) : y + max (-y) 0 = max y 0 := by
  rcases le_total 0 y with h | h
  · have h1 : max (-y) 0 = 0 := max_eq_right (by linarith : -y ≤ 0)
    have h2 : max y 0 = y := max_eq_left h
    rw [h1, h2]; ring
  · have h1 : max (-y) 0 = -y := max_eq_left (by linarith : 0 ≤ -y)
    have h2 : max y 0 = 0 := max_eq_right h
    rw [h1, h2]; ring

theorem term_eq_zero (M l n k a : ℕ) (hMl : l ≤ M) (ha1 : a + 1 ≤ (n - k)/M) :
    max ((l:ℝ) - (n:ℝ)/((a:ℝ)+1)) 0 = 0 := by
  refine max_eq_right ?_
  have hna : M * (a + 1) ≤ n := by
    calc M * (a+1) ≤ M * ((n - k)/M) := Nat.mul_le_mul_left M ha1
      _ ≤ n - k := by rw [Nat.mul_comm]; exact Nat.div_mul_le_self (n-k) M
      _ ≤ n := Nat.sub_le _ _
  have hl1 : (l:ℝ) * ((a:ℝ)+1) ≤ (M:ℝ) * ((a:ℝ)+1) := by
    have h : (l:ℝ) ≤ (M:ℝ) := by exact_mod_cast hMl
    exact mul_le_mul_of_nonneg_right h (by positivity)
  have hM1 : (M:ℝ) * ((a:ℝ)+1) ≤ (n:ℝ) := by
    have h : ((M * (a+1) : ℕ) : ℝ) ≤ (n:ℝ) := by exact_mod_cast hna
    push_cast at h ⊢
    linarith
  have : (l:ℝ) ≤ (n:ℝ) / ((a:ℝ)+1) := by
    rw [le_div_iff₀ (by positivity : (0:ℝ) < (a:ℝ)+1)]
    linarith
  linarith

theorem comparison_eq (M k l n m : ℕ) (hm : m = (n - k)/M) (hMl : l ≤ M) :
    ((k:ℝ)+1) * H m + (n:ℝ)/((m:ℝ)+1) - (l:ℝ)
      + (∑ a ∈ Finset.Icc 1 m, max ((l:ℝ) - (n:ℝ)/((a:ℝ)+1)) 0)
    ≤ (k:ℝ) * H m + max ((n:ℝ)/((m:ℝ)+1) - (l:ℝ)) 0 + H m := by
  have hCle : (∑ a ∈ Finset.Icc 1 m, max ((l:ℝ) - (n:ℝ)/((a:ℝ)+1)) 0)
      ≤ max (-((n:ℝ)/((m:ℝ)+1) - (l:ℝ))) 0 := by
    rcases Nat.eq_zero_or_pos m with hm0 | hmpos
    · rw [hm0]; simp
    · have hEq : (∑ a ∈ Finset.Icc 1 m, max ((l:ℝ) - (n:ℝ)/((a:ℝ)+1)) 0)
          = max (-((n:ℝ)/((m:ℝ)+1) - (l:ℝ))) 0 := by
        rw [Finset.sum_eq_single m ?_ ?_]
        · congr 1; ring
        · intro a ha hne
          rw [Finset.mem_Icc] at ha
          exact term_eq_zero M l n k a hMl (by rw [← hm]; omega)
        · intro hnotin
          rw [Finset.mem_Icc] at hnotin
          omega
      rw [hEq]
  have hy := add_max_neg ((n:ℝ)/((m:ℝ)+1) - (l:ℝ))
  set hh := H m
  linarith [hCle, hy]

theorem h0_le_succ (N M : ℕ) : N / M ≤ (N - 1) / M + 1 := by
  rcases Nat.eq_zero_or_pos M with hM | hM
  · rw [hM]; simp
  · rcases Nat.eq_zero_or_pos N with hN | hN
    · simp [hN]
    · have hdm : M * ((N - 1) / M) + (N - 1) % M = N - 1 := Nat.div_add_mod (N - 1) M
      have hmod' : (N - 1) % M ≤ M - 1 := by
        have := Nat.mod_lt (N - 1) hM; omega
      have h4 : N - 1 ≤ M * ((N - 1) / M) + (M - 1) := by
        calc N - 1 = M * ((N - 1) / M) + (N - 1) % M := hdm.symm
          _ ≤ M * ((N - 1) / M) + (M - 1) := Nat.add_le_add_left hmod' _
      have hN' : N = (N - 1) + 1 := by omega
      have h5 : N ≤ M * ((N - 1) / M) + M := by omega
      have h6 : M * ((N - 1) / M) + M = M * ((N - 1) / M + 1) := by
        rw [Nat.mul_add, Nat.mul_one]
      exact Nat.div_le_of_le_mul (h5.trans h6.le)

theorem mul_div_eq_of_div_eq (N M : ℕ) (h : N / M = (N - 1) / M + 1) : M * (N / M) = N := by
  have hMpos : 0 < M := by
    rcases Nat.eq_zero_or_pos M with h0 | h0
    · rw [h0] at h; simp at h
    · exact h0
  have hdm : M * ((N - 1) / M) + (N - 1) % M = N - 1 := Nat.div_add_mod (N - 1) M
  have hmod : (N - 1) % M < M := Nat.mod_lt _ hMpos
  have h1 : M * (N / M) ≤ N := by rw [Nat.mul_comm]; exact Nat.div_mul_le_self N M
  have h2 : N ≤ M * (N / M) := by
    rw [h, Nat.mul_add, Nat.mul_one]
    omega
  omega

theorem comparison_succ (M k l n m : ℕ) (hmax : M = max k l) (hMpos : 0 < M)
    (hkn : k ≤ n) (hmul : M * (m+1) = n - k) :
    ((k:ℝ)+1) * H m + (n:ℝ)/((m:ℝ)+1) - (l:ℝ)
      + (∑ a ∈ Finset.Icc 1 m, max ((l:ℝ) - (n:ℝ)/((a:ℝ)+1)) 0)
    ≤ (k:ℝ) * H (m+1) + max ((n:ℝ)/((((m+1:ℕ):ℝ))+1) - (l:ℝ)) 0 + H (m+1) := by
  have hdiv : (n - k)/M = m + 1 := by
    rw [← hmul, Nat.mul_comm]
    exact Nat.mul_div_left (m+1) hMpos
  have hC : (∑ a ∈ Finset.Icc 1 m, max ((l:ℝ) - (n:ℝ)/((a:ℝ)+1)) 0) = 0 := by
    refine Finset.sum_eq_zero fun a ha => ?_
    rw [Finset.mem_Icc] at ha
    exact term_eq_zero M l n k a (by rw [hmax]; exact le_max_right _ _) (by rw [hdiv]; omega)
  rw [hC, H_succ m, add_zero]
  have hden : ((((m+1:ℕ):ℝ))+1) = (m:ℝ)+2 := by push_cast; ring
  rw [hden]
  have hnk_cast : ((n - k : ℕ) : ℝ) = (n:ℝ) - (k:ℝ) := Nat.cast_sub hkn
  have hcast : (M:ℝ) * ((m:ℝ)+1) = ((n - k : ℕ) : ℝ) := by
    have h : ((M * (m+1) : ℕ) : ℝ) = (M:ℝ) * ((m:ℝ)+1) := by push_cast; ring
    rw [← h, hmul]
  have hnk1 : (n:ℝ) - ((k:ℝ) + 1) ≤ (M:ℝ) * ((m:ℝ)+1) := by linarith [hnk_cast, hcast]
  have hMle : (M:ℝ) ≤ max ((n:ℝ)/((m:ℝ)+2)) (l:ℝ) := by
    rcases le_total l k with hlk | hkl
    · have hMk : M = k := by rw [hmax, max_eq_left hlk]
      have hn : n = k * (m + 2) := by
        have h1 : n - k = k * (m+1) := by rw [← hmul, hMk]
        rw [← Nat.sub_add_cancel hkn, h1]; ring
      have hx : (n:ℝ)/((m:ℝ)+2) = (k:ℝ) := by
        rw [hn]; push_cast; field_simp
      rw [hx, hMk]
      exact le_max_left _ _
    · have hMl : M = l := by rw [hmax, max_eq_right hkl]
      rw [hMl]
      exact le_max_right _ _
  have hkey : ((n:ℝ) - ((k:ℝ) + 1))/((m:ℝ)+1) ≤ max ((n:ℝ)/((m:ℝ)+2)) (l:ℝ) := by
    calc ((n:ℝ) - ((k:ℝ) + 1))/((m:ℝ)+1)
        ≤ ((M:ℝ) * ((m:ℝ)+1))/((m:ℝ)+1) :=
          div_le_div_of_nonneg_right hnk1 (by positivity)
      _ = (M:ℝ) := mul_div_cancel_right₀ _ (by positivity : ((m:ℝ)+1) ≠ 0)
      _ ≤ _ := hMle
  have hcore : (n:ℝ)/((m:ℝ)+1) - (l:ℝ)
      ≤ (k:ℝ) * ((m:ℝ)+1)⁻¹ + ((m:ℝ)+1)⁻¹ + max ((n:ℝ)/((m:ℝ)+2) - (l:ℝ)) 0 := by
    have h1 : ((n:ℝ) - ((k:ℝ)+1))/((m:ℝ)+1)
        = (n:ℝ)/((m:ℝ)+1) - ((k:ℝ)+1)/((m:ℝ)+1) := by rw [sub_div]
    have h2 : ((k:ℝ)+1)/((m:ℝ)+1) = (k:ℝ) * ((m:ℝ)+1)⁻¹ + ((m:ℝ)+1)⁻¹ := by
      rw [add_div]; ring_nf
    have h3 : max ((n:ℝ)/((m:ℝ)+2) - (l:ℝ)) 0 = max ((n:ℝ)/((m:ℝ)+2)) (l:ℝ) - (l:ℝ) := by
      linarith [add_max_sub ((n:ℝ)/((m:ℝ)+2)) (l:ℝ)]
    linarith [hkey, h1, h2, h3]
  have hH2 : (k:ℝ) * (H m + ((m:ℝ)+1)⁻¹) + max ((n:ℝ)/((m:ℝ)+2) - (l:ℝ)) 0
        + (H m + ((m:ℝ)+1)⁻¹)
      = (k:ℝ) * H m + ((k:ℝ) * ((m:ℝ)+1)⁻¹ + ((m:ℝ)+1)⁻¹)
        + max ((n:ℝ)/((m:ℝ)+2) - (l:ℝ)) 0 + H m := by ring
  rw [hH2]
  linarith [hcore]

theorem comparison (k l n : ℕ) (hk : k ≤ n) (_hl : l ≤ n) :
    ((k:ℝ)+1) * H ((n-k-1)/max k l) + (n:ℝ)/((((n-k-1)/max k l : ℕ) : ℝ)+1) - (l:ℝ)
      + (∑ a ∈ Finset.Icc 1 ((n-k-1)/max k l), max ((l:ℝ) - (n:ℝ)/((a:ℝ)+1)) 0)
    ≤ (k:ℝ) * H ((n-k)/max k l)
      + max ((n:ℝ)/((((n-k)/max k l : ℕ) : ℝ)+1) - (l:ℝ)) 0 + H ((n-k)/max k l) := by
  set M : ℕ := max k l with hM
  set m : ℕ := (n - k - 1)/M with hm
  set m₀ : ℕ := (n - k)/M with hm0
  have hle : m ≤ m₀ := by rw [hm, hm0]; exact Nat.div_le_div_right (Nat.sub_le _ _)
  have hsucc : m₀ ≤ m + 1 := by rw [hm, hm0]; exact h0_le_succ (n-k) M
  have hMl : l ≤ M := by rw [hM]; exact le_max_right _ _
  rcases eq_or_lt_of_le hle with heq | hlt
  · rw [← heq]
    exact comparison_eq M k l n m (by rw [heq, hm0]) hMl
  · have hm0eq : m₀ = m + 1 := by omega
    have h0eq : (n - k)/M = (n - k - 1)/M + 1 := by rw [← hm0, ← hm, hm0eq]
    have hmul : M * (m+1) = n - k := by
      have h1 : (n - k)/M = m + 1 := by rw [← hm0, hm0eq]
      rw [← h1]
      exact mul_div_eq_of_div_eq (n-k) M h0eq
    have hMpos : 0 < M := by
      rcases Nat.eq_zero_or_pos M with h0 | h0
      · exfalso
        have h0' : m₀ = 0 := by rw [hm0, h0, Nat.div_zero]
        have hcontra : m + 1 = 0 := by rw [← hm0eq, h0']
        exact Nat.succ_ne_zero m hcontra
      · exact h0
    rw [hm0eq]
    exact comparison_succ M k l n m hM hMpos hk hmul

theorem lcm_ne_zero (n k : ℕ) : (((Finset.Icc (n - k) n).erase 0).lcm (fun m => m)) ≠ 0 := by
  rw [Finset.lcm_ne_zero_iff]
  intro a ha
  rw [Finset.mem_erase] at ha
  exact ha.1

/-- Monotonicity of the window `lcm` in the window length. -/
theorem lcm_window_mono (n k k' : ℕ) (hk : k ≤ k') :
    (((Finset.Icc (n - k) n).erase 0).lcm (fun m => m))
      ≤ (((Finset.Icc (n - k') n).erase 0).lcm (fun m => m)) := by
  refine Nat.le_of_dvd (Nat.pos_of_ne_zero (lcm_ne_zero n k')) ?_
  have hsub : (Finset.Icc (n - k) n).erase 0 ⊆ (Finset.Icc (n - k') n).erase 0 := by
    intro m hm
    rw [Finset.mem_erase] at hm ⊢
    refine ⟨hm.1, ?_⟩
    rw [Finset.mem_Icc] at hm ⊢
    exact ⟨le_trans (Nat.sub_le_sub_left hk n) hm.2.1, hm.2.2⟩
  exact Finset.lcm_mono hsub (f := fun m => m)

theorem Lge_dvd_lcm (l n k : ℕ) :
    Lge l n k ∣ (((Finset.Icc (n - k) n).erase 0).lcm (fun m => m)) := by
  rw [Lge]
  refine Commons.NumberTheory.Chebyshev.prod_primes_dvd ?_ ?_
  · intro p hp
    rw [Finset.mem_filter] at hp
    exact hp.2.1
  · intro p hp
    rw [Finset.mem_filter] at hp
    obtain ⟨-, -, -, ⟨m, hm, hpm⟩⟩ := hp
    exact dvd_trans hpm (Finset.dvd_lcm hm)

theorem one_le_Lge (l n k : ℕ) : 1 ≤ Lge l n k := by
  rw [Lge]
  exact Finset.one_le_prod₀ (fun p hp => by
    rw [Finset.mem_filter] at hp
    exact le_of_lt hp.2.1.one_lt)

theorem log_Lge_le_log_lcm (l n k : ℕ) :
    Real.log ((Lge l n k : ℕ) : ℝ)
      ≤ Real.log (((((Finset.Icc (n - k) n).erase 0).lcm (fun m => m) : ℕ)) : ℝ) := by
  have hLpos : 0 < ((Finset.Icc (n - k) n).erase 0).lcm (fun m => m) :=
    Nat.pos_of_ne_zero (lcm_ne_zero n k)
  have hle : Lge l n k ≤ _ := Nat.le_of_dvd hLpos (Lge_dvd_lcm l n k)
  refine Real.log_le_log (by exact_mod_cast one_le_Lge l n k) ?_
  exact_mod_cast hle

/-- The uniform window-lcm asymptotic evaluated at the fixed scale `γ = 1/J`. -/
theorem log_lcm_window_uniform_at (J : ℕ) (hJ : 1 ≤ J) (η : ℝ) (hη : 0 < η) :
    ∀ᶠ n : ℕ in Filter.atTop,
      Real.log ((((Finset.Icc (n - n/J) n).erase 0).lcm (fun m => m) : ℕ) : ℝ) / (n:ℝ)
        ≤ H (J-1)/(J:ℝ) + 1/(J:ℝ) + η := by
  have hJpos : (0:ℝ) < (J:ℝ) := by exact_mod_cast hJ
  have hγpos : (0:ℝ) < (1:ℝ)/J := by positivity
  have hγ1 : (1:ℝ)/J ≤ 1 := by
    rw [div_le_iff₀ hJpos]
    simpa using (by exact_mod_cast hJ : (1:ℝ) ≤ (J:ℝ))
  filter_upwards [log_lcm_window_uniform ((1:ℝ)/J) η hγpos hγ1 hη] with n hn
  have h := hn ((1:ℝ)/J) (le_refl _) hγ1
  have hf : ⌊((1:ℝ)/J) * (n:ℝ)⌋₊ = n / J := by
    rw [one_div_mul_eq_div, Nat.floor_div_natCast, Nat.floor_natCast]
  have hf2 : (⌊1 / ((1:ℝ)/J)⌋₊ : ℕ) = J := by
    rw [one_div_one_div, Nat.floor_natCast]
  rw [hf, hf2] at h
  have hval : ((1:ℝ)/J) * (∑ h ∈ Finset.Icc 1 (J - 1), ((h : ℝ))⁻¹) + ((J:ℝ))⁻¹
      = H (J-1)/(J:ℝ) + 1/(J:ℝ) := by
    rw [H, one_div]; ring
  rw [hval] at h
  have h2 := (abs_le.mp h).2
  linarith

/-- Case 1: `k J ≤ n` (the very short window). -/
theorem log_lcm_window_le_small (J : ℕ) (hJ : 1 ≤ J) (η : ℝ) (hη : 0 < η) :
    ∀ᶠ n : ℕ in Filter.atTop, ∀ k : ℕ, k * J ≤ n →
      Real.log ((((Finset.Icc (n - k) n).erase 0).lcm (fun m => m) : ℕ) : ℝ)
        ≤ (H (J-1)/(J:ℝ) + 1/(J:ℝ) + η) * (n:ℝ) := by
  have hJpos : (0:ℝ) < (J:ℝ) := by exact_mod_cast hJ
  filter_upwards [log_lcm_window_uniform_at J hJ η hη] with n hn k hk
  rcases Nat.eq_zero_or_pos n with hn0 | hnpos
  · subst hn0
    have hk0 : k = 0 := by
      have h : k * J = 0 := Nat.le_zero.mp hk
      rcases Nat.mul_eq_zero.mp h with h' | h'
      · exact h'
      · omega
    subst hk0
    simp
  · have hkJ : k ≤ n / J := by
      have hcast : (k:ℝ) * (J:ℝ) ≤ (n:ℝ) := by exact_mod_cast hk
      have h1 : (k:ℝ) ≤ (n:ℝ)/(J:ℝ) := by
        rw [le_div_iff₀ hJpos]; linarith
      have h3 : k ≤ ⌊(n:ℝ)/(J:ℝ)⌋₊ := Nat.le_floor h1
      rwa [Nat.floor_div_natCast, Nat.floor_natCast] at h3
    have hmono : Real.log ((((Finset.Icc (n - k) n).erase 0).lcm (fun m => m) : ℕ) : ℝ)
        ≤ Real.log ((((Finset.Icc (n - n/J) n).erase 0).lcm (fun m => m) : ℕ) : ℝ) :=
      Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero (lcm_ne_zero n k))
        (by exact_mod_cast lcm_window_mono n k (n/J) hkJ)
    have hnpos' : (0:ℝ) < (n:ℝ) := by exact_mod_cast hnpos
    have h4 := mul_le_mul_of_nonneg_right hn hnpos'.le
    rw [show (Real.log ((((Finset.Icc (n - n/J) n).erase 0).lcm (fun m => m) : ℕ) : ℝ) / (n:ℝ))
        * (n:ℝ)
        = Real.log ((((Finset.Icc (n - n/J) n).erase 0).lcm (fun m => m) : ℕ) : ℝ)
        from by field_simp] at h4
    linarith [hmono, h4]

/-- **Lemma `lcm-2` (2) of Calagari–Dimitrov–Tang.**  Uniformly in `0 ≤ k, l ≤ n`:
`log L^{≥ l}_{n,k} ≤ k·H_{h₀} + (n/(h₀+1) - l)^+ + εn`, `h₀ = ⌊(n-k)/max(k,l)⌋`. -/
theorem log_Lge_le_uniform (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in Filter.atTop, ∀ k l : ℕ, k ≤ n → l ≤ n →
      Real.log ((Lge l n k : ℕ) : ℝ)
        ≤ (k : ℝ) * H ((n - k) / max k l)
          + max ((n : ℝ) / ((((n + (l - k)) / max k l : ℕ)) : ℝ) - (l : ℝ)) 0
          + ε * (n : ℝ) := by
  obtain ⟨J, hJ1, hJH⟩ : ∃ J : ℕ, 1 ≤ J ∧ H J / (J:ℝ) + 1 / (J:ℝ) < ε / 8 := by
    have h1 : ∀ᶠ j : ℕ in Filter.atTop, H j / (j:ℝ) < ε / 16 := by
      filter_upwards [tendsto_harm_div (ε/16) (by linarith)] with j hj
      simpa [H] using hj
    have h2 : ∀ᶠ j : ℕ in Filter.atTop, 1 / (j:ℝ) < ε / 16 := by
      have ht : Filter.Tendsto (fun j : ℕ => (1:ℝ)/j) Filter.atTop (nhds 0) := by
        simpa [Function.comp_def] using tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
      exact ht.eventually (eventually_lt_nhds (by linarith))
    obtain ⟨N1, hN1⟩ := Filter.eventually_atTop.mp h1
    obtain ⟨N2, hN2⟩ := Filter.eventually_atTop.mp h2
    refine ⟨max (max N1 N2) 1, by omega, ?_⟩
    have e1 := hN1 _ (by omega : N1 ≤ max (max N1 N2) 1)
    have e2 := hN2 _ (by omega : N2 ≤ max (max N1 N2) 1)
    linarith
  have hJpos : (0:ℝ) < (J:ℝ) := by exact_mod_cast hJ1
  have hγ1 : (1:ℝ)/J ≤ 1 := by
    rw [div_le_iff₀ hJpos]
    simpa using (by exact_mod_cast hJ1 : (1:ℝ) ≤ (J:ℝ))
  have hJinv : (1:ℝ)/(J:ℝ) ≤ ε/8 := by
    have h : 0 ≤ H J / (J:ℝ) := div_nonneg (H_nonneg J) hJpos.le
    linarith
  have hHJ : H (J-1)/(J:ℝ) + 1/(J:ℝ) ≤ ε/8 := by
    have h1 : H (J-1) ≤ H J := by
      unfold H
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun a _ _ => by positivity)
      exact Finset.Icc_subset_Icc_right (by omega : J - 1 ≤ J)
    have h2 : H (J-1)/(J:ℝ) ≤ H J/(J:ℝ) := div_le_div_of_nonneg_right h1 hJpos.le
    linarith
  have hsmall := log_lcm_window_le_small J hJ1 (ε/8) (by linarith)
  have hhar := lcm_ge_harmonic_uniform ((1:ℝ)/J) (by positivity) hγ1 (ε/4) (by linarith)
  have hle2 := log_lcm_window_le_uniform (ε/2) (by linarith)
  have hhle := H_le_log
  have hlog : ∀ᶠ n : ℕ in Filter.atTop, 1 + Real.log (n:ℝ) ≤ (ε/8) * (n:ℝ) := by
    have h := Real.isLittleO_log_id_atTop.bound (c := ε/16) (by linarith)
    have h2 : ∀ᶠ x : ℝ in Filter.atTop, (1:ℝ) + Real.log x ≤ (ε/8) * x := by
      filter_upwards [h, Filter.eventually_ge_atTop (max 1 (16/ε))] with x hx hx1
      have hx1' : (1:ℝ) ≤ x := le_trans (le_max_left _ _) hx1
      have hxpos : (0:ℝ) < x := lt_of_lt_of_le one_pos hx1'
      have hlognn : 0 ≤ Real.log x := Real.log_nonneg hx1'
      have h1 : Real.log x ≤ (ε/16) * x := by
        have hh := hx
        simp only [id_eq, Real.norm_eq_abs, abs_of_nonneg hlognn,
          abs_of_nonneg hxpos.le] at hh
        linarith
      have h4 : (16/ε) ≤ x := le_trans (le_max_right _ _) hx1
      have h3 : 1 ≤ (ε/16) * x := by
        have h5 : (ε/16) * (16/ε) ≤ (ε/16) * x :=
          mul_le_mul_of_nonneg_left h4 (by linarith)
        have h6 : (ε/16) * (16/ε) = 1 := by field_simp
        linarith
      linarith
    exact tendsto_natCast_atTop_atTop.eventually h2
  have hHb : ∀ᶠ n : ℕ in Filter.atTop, ∀ m : ℕ, m ≤ n → H m ≤ (ε/4) * (n:ℝ) := by
    filter_upwards [hlog] with n hn
    intro m hm
    rcases Nat.eq_zero_or_pos m with hm0 | hmpos
    · rw [hm0]; have : H 0 = 0 := rfl; rw [this]; positivity
    · have h1 : H m ≤ 1 + Real.log (m:ℝ) := H_le_log m
      have h2 : Real.log (m:ℝ) ≤ Real.log (n:ℝ) :=
        Real.log_le_log (by exact_mod_cast hmpos) (by exact_mod_cast hm)
      have h3 : (ε/8) * (n:ℝ) ≤ (ε/4) * (n:ℝ) := by
        have : (ε/8:ℝ) ≤ ε/4 := by linarith
        exact mul_le_mul_of_nonneg_right this (by positivity)
      linarith
  obtain ⟨Y₀, hY₀⟩ := theta_rel_error (ε/16) (by linarith)
  have hbig : ∀ᶠ n : ℕ in Filter.atTop,
      (4:ℝ) ≤ (n:ℝ) ∧ 16/ε ≤ (n:ℝ) ∧ 4 * max Y₀ 0 ≤ (n:ℝ) := by
    have h1 : ∀ᶠ n : ℕ in Filter.atTop,
        max 4 (max (16/ε) (4 * max Y₀ 0)) ≤ (n:ℝ) :=
      tendsto_natCast_atTop_atTop.eventually (Filter.eventually_ge_atTop _)
    filter_upwards [h1] with n hn
    exact ⟨le_trans (le_max_left _ _) hn,
      le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hn,
      le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hn⟩
  filter_upwards [hsmall, hhar, hle2, hHb, hbig] with
    n hsmall_n hhar_n hle2_n hHb_n hnbig
  obtain ⟨h4n, h16n, hY4n⟩ := hnbig
  have hmaxY : max Y₀ 0 ≤ (n:ℝ) := by
    have h1 : max Y₀ 0 ≤ 4 * max Y₀ 0 := by
      have h := mul_le_mul_of_nonneg_right (show (1:ℝ) ≤ 4 by norm_num) (le_max_right Y₀ 0)
      simpa using h
    linarith
  have hYn : Y₀ ≤ (n:ℝ) := le_trans (le_max_left Y₀ 0) hmaxY
  have hnpos : (0:ℝ) < (n:ℝ) := lt_of_lt_of_le (by norm_num) h4n
  intro k l hkn hln
  by_cases h1 : k * J ≤ n
  · -- Case 1: very short window
    have hlg := log_Lge_le_log_lcm l n k
    have hs := hsmall_n k h1
    have hε4 : H (J-1)/(J:ℝ) + 1/(J:ℝ) + ε/8 ≤ ε/4 := by linarith
    have hs' : Real.log ((((Finset.Icc (n - k) n).erase 0).lcm (fun m => m) : ℕ) : ℝ)
        ≤ (ε/4) * (n:ℝ) := le_trans hs (mul_le_mul_of_nonneg_right hε4 (by positivity))
    have hnn : (0:ℝ) ≤ (k:ℝ) * H ((n - k) / max k l)
        + max ((n : ℝ) / ((((n + (l - k)) / max k l : ℕ)) : ℝ) - (l : ℝ)) 0 := by
      have ha : 0 ≤ (k:ℝ) * H ((n - k) / max k l) :=
        mul_nonneg (by positivity) (H_nonneg _)
      have hb : 0 ≤ max ((n : ℝ) / ((((n + (l - k)) / max k l : ℕ)) : ℝ) - (l : ℝ)) 0 :=
        le_max_right _ _
      linarith
    have hεn : (ε/4) * (n:ℝ) ≤ ε * (n:ℝ) := by
      have : (ε/4:ℝ) ≤ ε := by linarith
      exact mul_le_mul_of_nonneg_right this (by positivity)
    linarith
  · by_cases h2 : (2*J - 1) * n ≤ (2*J) * l
    · -- Case 2: l large
      have hJ2pos : (0:ℝ) < (2:ℝ)*(J:ℝ) := by
        have hJ2 : (1:ℝ) ≤ (J:ℝ) := by exact_mod_cast hJ1
        linarith
      have h2Jc : ((2*J : ℕ) : ℝ) = (2:ℝ)*(J:ℝ) := by push_cast; ring
      set X : ℝ := (((2*J - 1 : ℕ) : ℝ) * (n:ℝ)) / ((2:ℝ)*(J:ℝ)) with hX
      have hXnn : 0 ≤ X := by rw [hX]; positivity
      set m : ℕ := ⌊X⌋₊ with hmdef
      have hm_low : X - 1 ≤ (m:ℝ) := by
        have h := Nat.lt_floor_add_one X
        rw [← hmdef] at h
        linarith
      have hmle : (m:ℝ) ≤ X := by
        rw [hmdef]; exact Nat.floor_le hXnn
      have hlge : X ≤ (l:ℝ) := by
        have h2R : (((2*J - 1) * n : ℕ) : ℝ) ≤ ((2*J : ℕ) : ℝ) * (l:ℝ) := by
          exact_mod_cast h2
        have h1 : (((2*J - 1) * n : ℕ) : ℝ) = ((2*J - 1 : ℕ) : ℝ) * (n:ℝ) := by
          push_cast; ring
        rw [h1, h2Jc] at h2R
        rw [hX, div_le_iff₀ hJ2pos]
        linarith
      have hmn : m ≤ n := by
        have h1 : X ≤ (n:ℝ) := by
          rw [hX, div_le_iff₀ hJ2pos]
          have h3 : ((2*J - 1 : ℕ) : ℝ) ≤ (2:ℝ)*(J:ℝ) := by
            have : (2*J - 1 : ℕ) ≤ 2*J := by omega
            exact_mod_cast this
          nlinarith [hnpos.le, h3]
        exact_mod_cast (le_trans hmle h1)
      have hmY : Y₀ ≤ (m:ℝ) := by
        have hx : (n:ℝ)/2 ≤ X := by
          rw [hX, le_div_iff₀ hJ2pos]
          have h1 : ((2*J - 1 : ℕ) : ℝ) = (2:ℝ)*(J:ℝ) - 1 := by
            rw [Nat.cast_sub (by omega : 1 ≤ 2*J)]
            push_cast; ring
          have hJ2 : (1:ℝ) ≤ (J:ℝ) := by exact_mod_cast hJ1
          rw [h1]
          nlinarith [hnpos.le]
        linarith [hmaxY, h4n, hm_low, hx, hY4n, le_max_left Y₀ 0]
      -- the sum over the primes is bounded by `θ n - θ m`
      have hFILT1 : (Finset.Icc 1 n).filter
          (fun p => p.Prime ∧ l < p ∧ (∃ m ∈ (Finset.Icc (n - k) n).erase 0, p ∣ m))
          ⊆ (Finset.Icc 1 n).filter (fun p => p.Prime ∧ m < p) := by
        intro p hp
        rw [Finset.mem_filter] at hp ⊢
        obtain ⟨hp1, hp2, hp3, hp4⟩ := hp
        refine ⟨hp1, hp2, ?_⟩
        have hpl : (l:ℝ) < (p:ℝ) := by exact_mod_cast hp3
        have : (m:ℝ) < (p:ℝ) := lt_of_le_of_lt (le_trans hmle hlge) hpl
        exact_mod_cast this
      have hsum_le : (∑ p ∈ (Finset.Icc 1 n).filter
            (fun p => p.Prime ∧ l < p ∧ (∃ m ∈ (Finset.Icc (n - k) n).erase 0, p ∣ m)),
            Real.log (p:ℝ))
          ≤ ∑ p ∈ (Finset.Icc 1 n).filter (fun p => p.Prime ∧ m < p), Real.log (p:ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg hFILT1 (fun p hp _ => by
          rw [Finset.mem_filter] at hp
          exact Real.log_nonneg (by exact_mod_cast (Finset.mem_Icc.mp hp.1).1))
      have htheta_le : Chebyshev.theta (n:ℝ) - Chebyshev.theta (m:ℝ) ≤ (ε/4) * (n:ℝ) := by
        have h1 : Chebyshev.theta (n:ℝ) - (n:ℝ) ≤ (ε/16)*(n:ℝ) :=
          (abs_le.mp (hY₀ n hYn)).2
        have h2 : -((ε/16)*(m:ℝ)) ≤ Chebyshev.theta (m:ℝ) - (m:ℝ) :=
          (abs_le.mp (hY₀ m hmY)).1
        have hx3 : (n:ℝ) - X = (n:ℝ)/((2:ℝ)*(J:ℝ)) := by
          rw [hX]
          have h1 : ((2*J - 1 : ℕ) : ℝ) = (2:ℝ)*(J:ℝ) - 1 := by
            rw [Nat.cast_sub (by omega : 1 ≤ 2*J)]
            push_cast; ring
          rw [h1]
          field_simp
          ring
        have hx1 : (n:ℝ) - (m:ℝ) ≤ (n:ℝ)/((2:ℝ)*(J:ℝ)) + 1 := by linarith [hm_low, hx3]
        have hx4 : (n:ℝ)/((2:ℝ)*(J:ℝ)) ≤ (ε/16) * (n:ℝ) := by
          rw [div_le_iff₀ hJ2pos]
          have h2 : (1:ℝ) ≤ (ε/8) * (J:ℝ) := by
            have h := mul_le_mul_of_nonneg_right hJinv hJpos.le
            rwa [one_div_mul_eq_div, div_self (ne_of_gt hJpos)] at h
          nlinarith [h2, hnpos.le]
        have h4 : 1 ≤ (ε/16) * (n:ℝ) := by
          have h := mul_le_mul_of_nonneg_left h16n (by linarith : (0:ℝ) ≤ ε/16)
          have h6 : (ε/16) * (16/ε) = 1 := by field_simp
          linarith
        have hmle_n : (m:ℝ) ≤ (n:ℝ) := by exact_mod_cast hmn
        have h5 : (ε/16) * (m:ℝ) ≤ (ε/16) * (n:ℝ) :=
          mul_le_mul_of_nonneg_left hmle_n (by positivity)
        have h6 : (n:ℝ)/((2:ℝ)*(J:ℝ)) + 1 ≤ (ε/16)*(n:ℝ) + (ε/16)*(n:ℝ) := by
          linarith [hx4, h4]
        linarith [h1, h2, hx1, h5, h6]
      have hfin : Real.log ((Lge l n k : ℕ) : ℝ) ≤ (ε/4) * (n:ℝ) := by
        rw [Lge_cast, Real.log_prod (fun p hp => by
          rw [Finset.mem_filter] at hp
          exact_mod_cast hp.2.1.pos.ne')]
        have htheta : (∑ p ∈ (Finset.Icc 1 n).filter (fun p => p.Prime ∧ m < p), Real.log (p:ℝ))
            = Chebyshev.theta (n:ℝ) - Chebyshev.theta (m:ℝ) :=
          (theta_sub_theta_eq m n hmn).symm
        linarith [hsum_le, htheta, htheta_le]
      have hRHSnn : (0:ℝ) ≤ (k:ℝ) * H ((n - k) / max k l)
          + max ((n : ℝ) / ((((n + (l - k)) / max k l : ℕ)) : ℝ) - (l : ℝ)) 0 := by
        have ha : 0 ≤ (k:ℝ) * H ((n - k) / max k l) :=
          mul_nonneg (by positivity) (H_nonneg _)
        have hb : 0 ≤ max ((n : ℝ) / ((((n + (l - k)) / max k l : ℕ)) : ℝ) - (l : ℝ)) 0 :=
          le_max_right _ _
        linarith
      have hεn : (ε/4) * (n:ℝ) ≤ ε * (n:ℝ) := by
        have h : (ε/4:ℝ) ≤ ε := by linarith
        exact mul_le_mul_of_nonneg_right h hnpos.le
      linarith
    · by_cases h3 : l * J ≤ n
      · -- Case 3: l short, k long
        have hkgt : n < k * J := lt_of_not_ge h1
        have hJmul : l * J < k * J := lt_of_le_of_lt h3 hkgt
        have hlk : l ≤ k := le_of_lt (Nat.lt_of_mul_lt_mul_right hJmul)
        have hmax : max k l = k := max_eq_left hlk
        have hkpos : 0 < k := by
          rcases Nat.eq_zero_or_pos k with hk0 | hkpos
          · rw [hk0, Nat.zero_mul] at hkgt; omega
          · exact hkpos
        have hdiv : (n - k) / k = n / k - 1 := by
          have h := add_div_eq n k hkn hkpos
          rw [h, Nat.add_sub_cancel]
        have hsum : (∑ h ∈ Finset.Icc 1 (n / k - 1), ((h : ℝ))⁻¹) = H ((n - k) / max k l) := by
          rw [hmax, hdiv]; rfl
        have hlg := log_Lge_le_log_lcm l n k
        have hle2n := hle2_n k hkn
        rw [hsum] at hle2n
        have hl2 : (l:ℝ) ≤ (ε/2) * (n:ℝ) := by
          have h1' : (l:ℝ) * (J:ℝ) ≤ (n:ℝ) := by exact_mod_cast h3
          have h2' : (l:ℝ) ≤ (n:ℝ)/(J:ℝ) := by
            rw [le_div_iff₀ hJpos]; linarith
          have h3' : (n:ℝ)/(J:ℝ) ≤ (ε/8) * (n:ℝ) := by
            have h := mul_le_mul_of_nonneg_right hJinv hnpos.le
            rwa [one_div_mul_eq_div] at h
          have h4' : (ε/8) * (n:ℝ) ≤ (ε/2) * (n:ℝ) := by
            have : (ε/8:ℝ) ≤ ε/2 := by linarith
            exact mul_le_mul_of_nonneg_right this hnpos.le
          linarith
        have hmaxle : (n:ℝ)/((n/k : ℕ) : ℝ)
            ≤ max ((n:ℝ)/((n/k : ℕ) : ℝ) - (l:ℝ)) 0 + (ε/2) * (n:ℝ) := by
          have h := le_max_left ((n:ℝ)/((n/k : ℕ) : ℝ) - (l:ℝ)) (0:ℝ)
          linarith
        have hstep : H ((n - k) / max k l) * (k:ℝ)
              + (n:ℝ)/((n/k : ℕ) : ℝ) + (ε/2) * (n:ℝ)
            ≤ (k:ℝ) * H ((n - k) / max k l)
              + max ((n : ℝ) / ((((n + (l - k)) / max k l : ℕ)) : ℝ) - (l : ℝ)) 0
              + ε * (n:ℝ) := by
          rw [mul_comm (H ((n - k) / max k l)) (k:ℝ), hmax,
            Nat.sub_eq_zero_of_le hlk, Nat.add_zero]
          linarith
        calc Real.log ((Lge l n k : ℕ) : ℝ)
            ≤ Real.log ((((Finset.Icc (n - k) n).erase 0).lcm (fun m => m) : ℕ) : ℝ) := hlg
          _ ≤ H ((n - k) / max k l) * (k:ℝ) + (n:ℝ)/((n/k : ℕ) : ℝ) + (ε/2) * (n:ℝ) :=
              hle2n
          _ ≤ _ := hstep
      · -- Case 4: middle range
        have hkgt : n < k * J := lt_of_not_ge h1
        have hlgt : n < l * J := lt_of_not_ge h3
        have hkpos : 0 < k := by
          rcases Nat.eq_zero_or_pos k with hk0 | hkpos
          · rw [hk0, Nat.zero_mul] at hkgt; omega
          · exact hkpos
        have hMpos : 0 < max k l := lt_of_lt_of_le hkpos (le_max_left _ _)
        have hgk : (1:ℝ)/J * (n:ℝ) ≤ (k:ℝ) := by
          have hcast : (n:ℝ) ≤ (k:ℝ)*(J:ℝ) := by exact_mod_cast (le_of_lt hkgt)
          rw [one_div_mul_eq_div, div_le_iff₀ hJpos]
          linarith
        have hgl : (1:ℝ)/J * (n:ℝ) ≤ (l:ℝ) := by
          have hcast : (n:ℝ) ≤ (l:ℝ)*(J:ℝ) := by exact_mod_cast (le_of_lt hlgt)
          rw [one_div_mul_eq_div, div_le_iff₀ hJpos]
          linarith
        have huni := hhar_n k l hgk hkn hgl hln
        have hmodel : ((k:ℝ)+1) * (∑ a ∈ Finset.Icc 1 ((n - k - 1) / max k l), (1:ℝ)/(a:ℝ))
            = ((k:ℝ)+1) * H ((n - k - 1) / max k l) := by rw [H_eq]
        have hup : Real.log ((Lge l n k : ℕ) : ℝ)
            ≤ ((k:ℝ)+1) * H ((n - k - 1) / max k l)
              + (n:ℝ) / ((((n - k - 1) / max k l : ℕ) : ℝ) + 1) - (l:ℝ)
              + (∑ a ∈ Finset.Icc 1 ((n - k - 1) / max k l),
                  max ((l:ℝ) - (n:ℝ)/((a:ℝ)+1)) 0) + (ε/4) * (n:ℝ) := by
          have h := (abs_le.mp huni).2
          linarith [hmodel]
        have hcomp := comparison k l n hkn hln
        have hden : ((n + (l - k)) / max k l : ℕ) = ((n - k) / max k l) + 1 :=
          hden_eq n k l hkn hln hMpos
        have h0le : (n - k) / max k l ≤ n :=
          le_trans (Nat.div_le_self _ _) (Nat.sub_le _ _)
        have hHb0 : H ((n - k) / max k l) ≤ (ε/4) * (n:ℝ) := hHb_n _ h0le
        have hRHSeq : (k:ℝ) * H ((n - k) / max k l)
              + max ((n:ℝ)/((((n - k) / max k l : ℕ) : ℝ)+1) - (l:ℝ)) 0
              + H ((n - k) / max k l)
            ≤ (k:ℝ) * H ((n - k) / max k l)
              + max ((n:ℝ)/((((n + (l - k)) / max k l : ℕ)) : ℝ) - (l:ℝ)) 0
              + (ε/2) * (n:ℝ) := by
          rw [hden]
          push_cast
          have h1 : H ((n - k) / max k l) ≤ (ε/2) * (n:ℝ) := by
            have h2 : (ε/4)*(n:ℝ) ≤ (ε/2)*(n:ℝ) :=
              mul_le_mul_of_nonneg_right (by linarith) hnpos.le
            linarith [hHb0, h2]
          linarith [h1]
        have htot : (ε/4)*(n:ℝ) + (ε/2)*(n:ℝ) ≤ ε*(n:ℝ) := by
          have h : ((3:ℝ)/4)*ε ≤ ε := by linarith
          have h2 : (ε/4)*(n:ℝ) + (ε/2)*(n:ℝ) = ((3:ℝ)/4)*ε*(n:ℝ) := by ring
          rw [h2]
          exact mul_le_mul_of_nonneg_right h hnpos.le
        linarith [hup, hcomp, hRHSeq, htot]

end Submission.CDT.Lcm2Bound
