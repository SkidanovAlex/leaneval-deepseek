import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace Commons.Analysis.Sum

/-- Telescoping identity for a step sum over `Icc m N`, valid when `m ≤ N`. -/
private lemma sum_Icc_sub_step (ψ : ℕ → ℝ) {m N : ℕ} (h : m ≤ N) :
    ∑ k ∈ Finset.Icc m N, (ψ k - ψ (k + 1)) = ψ m - ψ (N + 1) := by
  have hmain : ∑ k ∈ Finset.Icc m N, (ψ (k + 1) - ψ k) = ψ (N + 1) - ψ m :=
    Finset.sum_Icc_sub h ψ
  have hneg : ∑ k ∈ Finset.Icc m N, (ψ k - ψ (k + 1))
      = -∑ k ∈ Finset.Icc m N, (ψ (k + 1) - ψ k) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl (fun k _ => by ring)
  rw [hneg, hmain]; ring

/-- Telescoping identity for a step sum over `Icc m N`, valid when `m ≤ N + 1`
(the case `m = N + 1` gives the empty sum). -/
private lemma sum_Icc_sub_step' (ψ : ℕ → ℝ) {m N : ℕ} (h : m ≤ N + 1) :
    ∑ k ∈ Finset.Icc m N, (ψ k - ψ (k + 1)) = ψ m - ψ (N + 1) := by
  rcases eq_or_lt_of_le h with h' | h'
  · subst h'
    rw [Finset.Icc_eq_empty (by omega), Finset.sum_empty, sub_self]
  · exact sum_Icc_sub_step ψ (by omega)

theorem sum_antitone_rank_le {ι : Type*} [Fintype ι] (g : ι → ℕ) (ψ : ℕ → ℝ)
    (hψ : ∀ a b : ℕ, 1 ≤ a → a ≤ b → ψ b ≤ ψ a) :
    (∑ i : ι, ψ ((Finset.univ.filter (fun j => g j ≤ g i)).card)) ≤
      ∑ j ∈ Finset.Icc 1 (Fintype.card ι), ψ j := by
  let n : ℕ := Fintype.card ι
  let r : ι → ℕ := fun i => (Finset.univ.filter (fun j => g j ≤ g i)).card
  let T : Finset ℕ := Finset.Icc 1 (n - 1)
  let d : ℕ → ℝ := fun k => ψ k - ψ (k + 1)
  let P : ℕ → ℕ := fun k => (Finset.univ.filter (fun i => r i ≤ k)).card
  change (∑ i : ι, ψ (r i)) ≤ ∑ j ∈ Finset.Icc 1 n, ψ j
  -- Basic properties of the rank function `r`.
  have hr_pos : ∀ i, 1 ≤ r i := by
    intro i
    change 1 ≤ (Finset.univ.filter (fun j => g j ≤ g i)).card
    exact Finset.card_pos.mpr ⟨i, by simp⟩
  have hr_le : ∀ i, r i ≤ n := by
    intro i
    change (Finset.univ.filter (fun j => g j ≤ g i)).card ≤ Fintype.card ι
    calc (Finset.univ.filter (fun j => g j ≤ g i)).card
        ≤ (Finset.univ : Finset ι).card :=
          Finset.card_le_card (Finset.filter_subset (fun j => g j ≤ g i) Finset.univ)
      _ = Fintype.card ι := Finset.card_univ
  have hr_mono : ∀ {i j : ι}, g j ≤ g i → r j ≤ r i := by
    intro i j h
    change (Finset.univ.filter (fun k => g k ≤ g j)).card
        ≤ (Finset.univ.filter (fun k => g k ≤ g i)).card
    apply Finset.card_le_card
    intro k hk
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
    exact le_trans hk h
  -- Key counting bound: at most `k` indices have rank `≤ k`.
  have hP : ∀ k, P k ≤ k := by
    intro k
    change (Finset.univ.filter (fun i => r i ≤ k)).card ≤ k
    rcases Finset.eq_empty_or_nonempty (Finset.univ.filter (fun i => r i ≤ k)) with h | ⟨i₀, hi₀⟩
    · rw [h]; simp
    · obtain ⟨i₁, hi₁, hmax⟩ :=
        Finset.exists_max_image (Finset.univ.filter (fun i => r i ≤ k)) g ⟨i₀, hi₀⟩
      have hi₁' : r i₁ ≤ k := by simpa using hi₁
      have hA : Finset.univ.filter (fun i => r i ≤ k)
          = Finset.univ.filter (fun j => g j ≤ g i₁) := by
        ext j
        rw [Finset.mem_filter, Finset.mem_filter]
        simp only [Finset.mem_univ, true_and]
        constructor
        · intro hj
          exact hmax j (Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩)
        · intro hj
          have := hr_mono hj
          omega
      rw [hA]
      exact hi₁'
  -- Per-element decomposition of `ψ m` into a telescoping sum with indicator.
  have hkey : ∀ m, 1 ≤ m → m ≤ n →
      ψ m = ψ n + ∑ k ∈ T, (if m ≤ k then d k else 0) := by
    intro m hm1 hm2
    have hn1 : 1 ≤ n := le_trans hm1 hm2
    have hTf : T.filter (fun k => m ≤ k) = Finset.Icc m (n - 1) := by
      change (Finset.Icc 1 (n - 1)).filter (fun k => m ≤ k) = Finset.Icc m (n - 1)
      ext k
      simp only [Finset.mem_filter, Finset.mem_Icc]
      constructor
      · rintro ⟨⟨h1, h2⟩, hmk⟩; exact ⟨hmk, h2⟩
      · rintro ⟨hmk, h2⟩; exact ⟨⟨le_trans hm1 hmk, h2⟩, hmk⟩
    have hsum : ∑ k ∈ T, (if m ≤ k then d k else 0) = ψ m - ψ n := by
      change (∑ k ∈ T, (if m ≤ k then (ψ k - ψ (k + 1)) else 0)) = ψ m - ψ n
      rw [← Finset.sum_filter, hTf]
      have key := sum_Icc_sub_step' ψ (m := m) (N := n - 1)
        (by rw [Nat.sub_add_cancel hn1]; exact hm2)
      rw [Nat.sub_add_cancel hn1] at key
      exact key
    rw [hsum]; ring
  -- Inner sum over `i` for fixed `k`.
  have hinner1 : ∀ k, (∑ i : ι, (if r i ≤ k then d k else 0)) = (P k : ℝ) * d k := by
    intro k
    change (∑ i : ι, (if r i ≤ k then d k else 0))
        = ((Finset.univ.filter (fun i => r i ≤ k)).card : ℝ) * d k
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  -- Inner sum over `j ∈ Icc 1 n` for fixed `k`.
  have hinner2 : ∀ k ∈ T,
      (∑ j ∈ Finset.Icc 1 n, (if j ≤ k then d k else 0)) = (k : ℝ) * d k := by
    intro k hk
    have hk' : k ∈ Finset.Icc 1 (n - 1) := hk
    have hk_le : k ≤ n := by
      have := (Finset.mem_Icc.mp hk').2; omega
    have hfil : (Finset.Icc 1 n).filter (fun j => j ≤ k) = Finset.Icc 1 k := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_Icc]
      constructor
      · rintro ⟨⟨hj1, _⟩, hjk⟩; exact ⟨hj1, hjk⟩
      · rintro ⟨hj1, hjk⟩; exact ⟨⟨hj1, le_trans hjk hk_le⟩, hjk⟩
    rw [← Finset.sum_filter, hfil, Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel,
      nsmul_eq_mul]
  -- Left-hand side expressed as `n * ψ n + ∑_k P k * d k`.
  have hLHS : (∑ i : ι, ψ (r i)) = n * ψ n + ∑ k ∈ T, (P k : ℝ) * d k := by
    have h1 : ∑ i : ι, ψ (r i)
        = ∑ i : ι, (ψ n + ∑ k ∈ T, (if r i ≤ k then d k else 0)) :=
      Finset.sum_congr rfl (fun i _ => hkey (r i) (hr_pos i) (hr_le i))
    rw [h1, Finset.sum_add_distrib]
    have hc : (∑ _i : ι, ψ n) = n * ψ n := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [hc, Finset.sum_comm]
    congr 1
    exact Finset.sum_congr rfl (fun k _ => hinner1 k)
  -- Right-hand side expressed as `n * ψ n + ∑_k k * d k`.
  have hRHS : (∑ j ∈ Finset.Icc 1 n, ψ j) = n * ψ n + ∑ k ∈ T, (k : ℝ) * d k := by
    have h1 : ∑ j ∈ Finset.Icc 1 n, ψ j
        = ∑ j ∈ Finset.Icc 1 n, (ψ n + ∑ k ∈ T, (if j ≤ k then d k else 0)) := by
      apply Finset.sum_congr rfl
      intro j hj
      exact hkey j (Finset.mem_Icc.mp hj).1 (Finset.mem_Icc.mp hj).2
    rw [h1, Finset.sum_add_distrib]
    rw [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
    rw [Finset.sum_comm]
    congr 1
    exact Finset.sum_congr rfl (fun k hk => hinner2 k hk)
  -- Term-by-term comparison.
  have hineq : ∑ k ∈ T, (P k : ℝ) * d k ≤ ∑ k ∈ T, (k : ℝ) * d k := by
    apply Finset.sum_le_sum
    intro k hk
    have hk' : k ∈ Finset.Icc 1 (n - 1) := hk
    have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk').1
    have hdk : 0 ≤ d k := by
      change 0 ≤ ψ k - ψ (k + 1)
      exact sub_nonneg.mpr (hψ k (k + 1) hk1 (Nat.le_succ k))
    have hPk : (P k : ℝ) ≤ (k : ℝ) := by exact_mod_cast hP k
    exact mul_le_mul_of_nonneg_right hPk hdk
  rw [hLHS, hRHS]
  exact add_le_add le_rfl hineq

end Commons.Analysis.Sum