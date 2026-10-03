import Mathlib
import Submission.Work.Peluse.Basic

set_option linter.unusedVariables false

namespace Work.Peluse.Track

/-- All elements of the arithmetic progression `c[L] = {c, 2c, …, Lc}` with
`L = ⌊γ' M⌋` lie in `[-N, N]`, provided `|c i * y| ≤ N` for every `1 ≤ y ≤ M`.

This is the version for *every* index `j : Fin (m+1)` (the lemma
`Work.Peluse.PET.arithIcc_abs_le` covers only the indices `i.succ`, `i : Fin m`).
Since `|c i| ≤ N/M` and `L ≤ γ' M ≤ γ M / (1000 (m+1)) ≤ M/2000`, the difference
`c_m - c_j` satisfies `|c_m - c_j| L ≤ 2N γ' M ≤ N`. -/
theorem arithIcc_abs_le_any {m : ℕ} (hm : 0 < m) {N M : ℕ} (hN : 0 < N) (hM : 0 < M)
    (c : Fin (m + 1) → ℤ) {γ γ' : ℝ} (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hγ' : 0 < γ')
    (hγ'le : γ' ≤ γ / (1000 * ((m : ℝ) + 1)))
    (hc : ∀ y ∈ Finset.Icc 1 M, ∀ i : Fin (m + 1), |c i * (y : ℤ)| ≤ (N : ℤ)) :
    ∀ j : Fin (m + 1), ∀ a ∈ Work.Peluse.arithIcc (c ⟨m, Nat.lt_succ_self m⟩ - c j)
        (⌊γ' * (M : ℝ)⌋).toNat, |a| ≤ (N : ℤ) := by
  intro j a ha
  simp only [Work.Peluse.arithIcc, Finset.mem_image] at ha
  obtain ⟨n, hn, rfl⟩ := ha
  simp only [Finset.mem_Icc] at hn
  obtain ⟨_hn1, hnL⟩ := hn
  set d : ℤ := c ⟨m, Nat.lt_succ_self m⟩ - c j with hd
  have hMmem : M ∈ Finset.Icc 1 M := by simp only [Finset.mem_Icc]; exact ⟨hM, le_rfl⟩
  have hcm : |c ⟨m, Nat.lt_succ_self m⟩ * (M:ℤ)| ≤ (N:ℤ) := hc M hMmem _
  have hci : |c j * (M:ℤ)| ≤ (N:ℤ) := hc M hMmem j
  -- integer bound: `|d| M ≤ 2N`
  have hdM : |d| * (M:ℤ) ≤ 2*(N:ℤ) := by
    have h1 : |d * (M:ℤ)| ≤ 2*(N:ℤ) := by
      have heq : d * (M:ℤ) = c ⟨m, Nat.lt_succ_self m⟩ * (M:ℤ) - c j * (M:ℤ) := by
        simp only [hd]; ring
      rw [heq]
      calc |c ⟨m, Nat.lt_succ_self m⟩ * (M:ℤ) - c j * (M:ℤ)|
          ≤ |c ⟨m, Nat.lt_succ_self m⟩ * (M:ℤ)| + |c j * (M:ℤ)| := abs_sub _ _
        _ ≤ (N:ℤ) + (N:ℤ) := add_le_add hcm hci
        _ = 2*(N:ℤ) := by ring
    rwa [abs_mul, abs_of_nonneg (by positivity : (0:ℤ) ≤ (M:ℤ))] at h1
  have hdMℝ : |(d:ℝ)| * (M:ℝ) ≤ 2*(N:ℝ) := by
    have h2 : ((|d| : ℤ) : ℝ) * ((M:ℤ):ℝ) ≤ ((2*(N:ℤ) : ℤ) : ℝ) := by exact_mod_cast hdM
    rw [Int.cast_abs] at h2
    push_cast at h2
    exact h2
  -- real bound: `n ≤ ⌊γ' M⌋ ≤ γ' M`
  have hpos : (0:ℝ) < γ' * (M:ℝ) := mul_pos hγ' (by exact_mod_cast hM)
  have hLle : ((⌊γ' * (M:ℝ)⌋.toNat : ℕ) : ℝ) ≤ γ' * (M:ℝ) := by
    rw [Int.floor_toNat]
    exact Nat.floor_le (le_of_lt hpos)
  have hnℝ : (n:ℝ) ≤ γ' * (M:ℝ) := le_trans (by exact_mod_cast hnL) hLle
  -- the numerical gain `2 N γ' ≤ N`
  have hγ'2000 : γ' ≤ 1/2000 := by
    have hden : (0:ℝ) < 1000 * ((m:ℝ) + 1) := by
      have : (1:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm
      nlinarith
    calc γ' ≤ γ / (1000 * ((m:ℝ) + 1)) := hγ'le
      _ ≤ 1 / (1000 * ((m:ℝ) + 1)) := div_le_div_of_nonneg_right hγ1 (le_of_lt hden)
      _ ≤ 1 / (1000 * 2) := by
            refine div_le_div_of_nonneg_left (by norm_num) (by norm_num) ?_
            have : (1:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm
            nlinarith
      _ = 1/2000 := by norm_num
  have key : 2 * (N:ℝ) * γ' ≤ (N:ℝ) := by
    have h : 2 * (N:ℝ) * γ' ≤ 2 * (N:ℝ) * (1/2000) :=
      mul_le_mul_of_nonneg_left hγ'2000 (by positivity)
    nlinarith [h]
  have hmain0 : |(d:ℝ)| * (n:ℝ) ≤ (N:ℝ) := by
    calc |(d:ℝ)| * (n:ℝ) ≤ |(d:ℝ)| * (γ' * (M:ℝ)) :=
          mul_le_mul_of_nonneg_left hnℝ (abs_nonneg _)
      _ = (|(d:ℝ)| * (M:ℝ)) * γ' := by ring
      _ ≤ (2*(N:ℝ)) * γ' := mul_le_mul_of_nonneg_right hdMℝ (le_of_lt hγ')
      _ = 2 * (N:ℝ) * γ' := by ring
      _ ≤ (N:ℝ) := key
  have hmain : |(d:ℝ) * (n:ℝ)| ≤ (N:ℝ) := by
    have hnabs : |(n:ℝ)| = (n:ℝ) := abs_of_nonneg (Nat.cast_nonneg n)
    rw [abs_mul, hnabs]
    exact hmain0
  have hcast : (((|d * (n:ℤ)| : ℤ)) : ℝ) ≤ (N:ℝ) := by
    rw [Int.cast_abs]
    push_cast
    exact hmain
  exact_mod_cast hcast

end Work.Peluse.Track
