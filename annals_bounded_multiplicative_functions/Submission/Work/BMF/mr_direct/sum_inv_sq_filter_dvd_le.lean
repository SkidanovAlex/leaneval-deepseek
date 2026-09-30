import Mathlib
import Submission.Work.BMF.mr_direct_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

namespace Work.BMF.mr_direct

open Finset

/-- Telescoping tail bound: for `1 ≤ m` and every `N`,
`∑_{k=m}^{N} 1/k² ≤ 2/m`.  (Indeed `1/k² ≤ 2(1/k - 1/(k+1))` and the right-hand side
telescopes.) -/
private lemma tail_inv_sq_Icc_le (m N : ℕ) (hm : 1 ≤ m) :
    ∑ k ∈ Finset.Icc m N, (1:ℝ)/(k:ℝ)^2 ≤ 2/(m:ℝ) := by
  have hsub : Finset.Icc m N ⊆ Finset.Ioo (m-1) (N+1) := by
    intro k hk
    simp only [Finset.mem_Icc] at hk
    simp only [Finset.mem_Ioo]
    omega
  calc ∑ k ∈ Finset.Icc m N, (1:ℝ)/(k:ℝ)^2
      ≤ ∑ k ∈ Finset.Ioo (m-1) (N+1), (1:ℝ)/(k:ℝ)^2 :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (by intro k _ _; positivity)
    _ = ∑ k ∈ Finset.Ioo (m-1) (N+1), ((k:ℝ)^2)⁻¹ := by
        apply Finset.sum_congr rfl; intro k _; rw [one_div]
    _ ≤ 2 / (((m-1:ℕ):ℝ) + 1) := sum_Ioo_inv_sq_le (m-1) (N+1)
    _ = 2/(m:ℝ) := by
        have hcast : ((m-1:ℕ):ℝ) = (m:ℝ) - 1 := by
          rw [Nat.cast_sub hm]; norm_num
        rw [hcast]; ring

/-- Sum over an arbitrary finite set of multiples of `p` whose quotients by `p` are all at
least `m`: `∑_{t ∈ s} 1/t² ≤ 2/(p·c)` whenever `c ≤ p·m`.  The set `s` is mapped to its
quotients `t/p`, which are all `≥ m`, and the tail bound `tail_inv_sq_Icc_le` is applied. -/
private lemma sum_multiples_inv_sq_le (s : Finset ℕ) (p c m : ℕ) (hp : 1 ≤ p) (hc : 1 ≤ c)
    (hdiv : ∀ t ∈ s, p ∣ t) (hmle : ∀ t ∈ s, m ≤ t / p) (hpm : c ≤ p * m) :
    ∑ t ∈ s, (1:ℝ)/(t:ℝ)^2 ≤ 2/((p:ℝ)*(c:ℝ)) := by
  have hm1 : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · subst h; simp at hpm; omega
    · exact h
  set N : ℕ := s.sup id with hN
  have hdiv' : ∀ t ∈ s, t = p * (t / p) := by
    intro t ht
    rw [mul_comm]
    exact (Nat.div_mul_cancel (hdiv t ht)).symm
  have hinj : Set.InjOn (fun t => t / p) (↑s : Set ℕ) := by
    intro t1 ht1 t2 ht2 heq
    have heq' : t1 / p = t2 / p := heq
    rw [hdiv' t1 ht1, hdiv' t2 ht2, heq']
  have hstep : ∑ t ∈ s, (1:ℝ)/(t:ℝ)^2
      = ∑ k ∈ s.image (fun t => t / p), (1:ℝ)/((p:ℝ)*(k:ℝ))^2 := by
    have hA : ∑ t ∈ s, (1:ℝ)/(t:ℝ)^2
        = ∑ t ∈ s, (fun k : ℕ => (1:ℝ)/((p:ℝ)*(k:ℝ))^2) (t / p) := by
      apply Finset.sum_congr rfl
      intro t ht
      have hcast : (t:ℝ) = (p:ℝ) * ((t/p:ℕ):ℝ) := by
        have hpt : p * (t/p) = t := by rw [mul_comm]; exact Nat.div_mul_cancel (hdiv t ht)
        calc (t:ℝ) = ((p * (t/p) : ℕ) : ℝ) := by rw [hpt]
          _ = (p:ℝ) * ((t/p:ℕ):ℝ) := by push_cast; ring
      rw [hcast]
    rw [hA]
    exact (Finset.sum_image (s := s) (g := fun t => t / p)
        (f := fun k : ℕ => (1:ℝ)/((p:ℝ)*(k:ℝ))^2) hinj).symm
  rw [hstep]
  have hsub : s.image (fun t => t / p) ⊆ Finset.Icc m N := by
    intro k hk
    rw [Finset.mem_image] at hk
    obtain ⟨t, ht, rfl⟩ := hk
    rw [Finset.mem_Icc]
    refine ⟨hmle t ht, ?_⟩
    have hle : t ≤ N := by rw [hN]; exact Finset.le_sup (f := id) ht
    exact le_trans (Nat.div_le_self t p) hle
  have hfac : ∑ k ∈ Finset.Icc m N, (1:ℝ)/((p:ℝ)*(k:ℝ))^2
      = (1/(p:ℝ)^2) * ∑ k ∈ Finset.Icc m N, (1:ℝ)/(k:ℝ)^2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    simp only [one_div, mul_pow, mul_inv]
  calc ∑ k ∈ s.image (fun t => t / p), (1:ℝ)/((p:ℝ)*(k:ℝ))^2
      ≤ ∑ k ∈ Finset.Icc m N, (1:ℝ)/((p:ℝ)*(k:ℝ))^2 :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (by intro k _ _; positivity)
    _ = (1/(p:ℝ)^2) * ∑ k ∈ Finset.Icc m N, (1:ℝ)/(k:ℝ)^2 := hfac
    _ ≤ (1/(p:ℝ)^2) * (2/(m:ℝ)) := by
        apply mul_le_mul_of_nonneg_left (tail_inv_sq_Icc_le m N hm1) (by positivity)
    _ ≤ 2/((p:ℝ)*(c:ℝ)) := by
        have hpR : (0:ℝ) < (p:ℝ) := by exact_mod_cast hp
        have hcR : (0:ℝ) < (c:ℝ) := by exact_mod_cast hc
        have hmR : (0:ℝ) < (m:ℝ) := by exact_mod_cast hm1
        have hpmR : (c:ℝ) ≤ (p:ℝ)*(m:ℝ) := by exact_mod_cast hpm
        have hden : (0:ℝ) < (p:ℝ)*(c:ℝ) := mul_pos hpR hcR
        have hle : (p:ℝ)*(c:ℝ) ≤ (p:ℝ)^2*(m:ℝ) := by nlinarith [hpmR, hpR, hcR]
        have h1 : 1/((p:ℝ)^2*(m:ℝ)) ≤ 1/((p:ℝ)*(c:ℝ)) :=
          one_div_le_one_div_of_le hden hle
        have hkey : (1/(p:ℝ)^2) * (2/(m:ℝ)) = 2*(1/((p:ℝ)^2*(m:ℝ))) := by
          simp only [one_div, mul_inv]
          ring
        rw [hkey]
        calc 2*(1/((p:ℝ)^2*(m:ℝ))) ≤ 2*(1/((p:ℝ)*(c:ℝ))) :=
              mul_le_mul_of_nonneg_left h1 (by norm_num)
          _ = 2/((p:ℝ)*(c:ℝ)) := by ring

theorem sum_inv_sq_filter_dvd_le (M U : ℝ) (p : ℕ) (hM : 0 < M) (hp : 1 ≤ p) :
    ∑ t ∈ (Work.BMF.natIcc M U).filter (fun t => p ∣ t), (1 : ℝ) / (t : ℝ) ^ 2
      ≤ 2 / ((p : ℝ) * M) := by
  change ∑ t ∈ (Finset.Icc ⌈M⌉₊ ⌊U⌋₊).filter (fun t => p ∣ t), (1:ℝ)/(t:ℝ)^2
      ≤ 2/((p:ℝ)*M)
  set c : ℕ := ⌈M⌉₊ with hc
  have hc1 : 1 ≤ c := by
    have : 0 < c := by rw [hc]; exact Nat.ceil_pos.mpr hM
    omega
  have hMle : M ≤ (c:ℝ) := by rw [hc]; exact Nat.le_ceil M
  set m : ℕ := ⌈(c:ℝ)/(p:ℝ)⌉₊ with hm
  have hpR : (0:ℝ) < (p:ℝ) := by exact_mod_cast hp
  have hmain : ∑ t ∈ (Finset.Icc c ⌊U⌋₊).filter (fun t => p ∣ t), (1:ℝ)/(t:ℝ)^2
      ≤ 2/((p:ℝ)*(c:ℝ)) := by
    apply sum_multiples_inv_sq_le _ p c m hp hc1
    · intro t ht; exact (Finset.mem_filter.mp ht).2
    · intro t ht
      rw [hm, Nat.ceil_le]
      have hct : c ≤ t := (Finset.mem_Icc.mp (Finset.mem_filter.mp ht).1).1
      have hpt : p * (t/p) = t := by
        rw [mul_comm]; exact Nat.div_mul_cancel (Finset.mem_filter.mp ht).2
      rw [div_le_iff₀ hpR]
      have hle : (c:ℝ) ≤ (p:ℝ) * ((t/p:ℕ):ℝ) := by
        calc (c:ℝ) ≤ (t:ℝ) := by exact_mod_cast hct
          _ = ((p*(t/p):ℕ):ℝ) := by rw [hpt]
          _ = (p:ℝ)*((t/p:ℕ):ℝ) := by push_cast; ring
      nlinarith [hle]
    · rw [hm]
      have hceil : (c:ℝ)/(p:ℝ) ≤ ((⌈(c:ℝ)/(p:ℝ)⌉₊ : ℕ):ℝ) := Nat.le_ceil _
      have hreal : (c:ℝ) ≤ ((p * ⌈(c:ℝ)/(p:ℝ)⌉₊ : ℕ) : ℝ) := by
        rw [div_le_iff₀ hpR] at hceil
        push_cast
        nlinarith [hceil]
      exact_mod_cast hreal
  calc ∑ t ∈ (Finset.Icc c ⌊U⌋₊).filter (fun t => p ∣ t), (1:ℝ)/(t:ℝ)^2
      ≤ 2/((p:ℝ)*(c:ℝ)) := hmain
    _ ≤ 2/((p:ℝ)*M) := by
        have hdenM : (0:ℝ) < (p:ℝ)*M := mul_pos hpR hM
        have hle : (p:ℝ)*M ≤ (p:ℝ)*(c:ℝ) := mul_le_mul_of_nonneg_left hMle hpR.le
        have h1 : 1/((p:ℝ)*(c:ℝ)) ≤ 1/((p:ℝ)*M) := one_div_le_one_div_of_le hdenM hle
        calc 2/((p:ℝ)*(c:ℝ)) = 2*(1/((p:ℝ)*(c:ℝ))) := by ring
          _ ≤ 2*(1/((p:ℝ)*M)) := mul_le_mul_of_nonneg_left h1 (by norm_num)
          _ = 2/((p:ℝ)*M) := by ring

end Work.BMF.mr_direct
