import Mathlib.NumberTheory.Divisors
import Submission.Commons.NumberTheory.ArithmeticFunction.sum_Icc_divisors_filter_swap

namespace Commons.NumberTheory.ArithmeticFunction

lemma sum_divisors_filter_eq_antidiag_filter {M : Type*} [AddCommMonoid M] (n T : ℕ)
    (g : ℕ → ℕ → M) :
    (∑ m ∈ n.divisors.filter (fun m => T < m ∧ T < n / m), g m (n / m))
      = ∑ p ∈ n.divisorsAntidiagonal.filter (fun p => T < p.1 ∧ T < p.2), g p.1 p.2 := by
  rw [Finset.sum_filter, Finset.sum_filter]
  exact (Nat.sum_divisorsAntidiagonal
    (n := n) (f := fun a b => if T < a ∧ T < b then g a b else 0)).symm

theorem sum_Icc_divisors_filter_swap_gt {M : Type*} [AddCommMonoid M] (y T : ℕ)
    (g : ℕ → ℕ → M) :
    (∑ n ∈ Finset.Icc 1 y,
        ∑ m ∈ n.divisors.filter (fun m => T < m ∧ T < n / m), g m (n / m))
      = ∑ m ∈ Finset.Icc (T + 1) y,
          ∑ k ∈ Finset.Icc (T + 1) (y / m), g m k := by
  let s : Finset (Σ _ : ℕ, ℕ × ℕ) :=
    (Finset.Icc 1 y).sigma (fun n => n.divisorsAntidiagonal.filter (fun p => T < p.1 ∧ T < p.2))
  let t : Finset (Σ _ : ℕ, ℕ) :=
    (Finset.Icc (T + 1) y).sigma (fun m => Finset.Icc (T + 1) (y / m))
  let F : (Σ _ : ℕ, ℕ × ℕ) → M := fun x => g x.2.1 x.2.2
  let G : (Σ _ : ℕ, ℕ) → M := fun x => g x.1 x.2
  have hL : (∑ n ∈ Finset.Icc 1 y,
        ∑ m ∈ n.divisors.filter (fun m => T < m ∧ T < n / m), g m (n / m)) = ∑ x ∈ s, F x := by
    dsimp only [s, F]
    rw [Finset.sum_sigma]
    apply Finset.sum_congr rfl
    intro n hn
    exact sum_divisors_filter_eq_antidiag_filter n T g
  have hR : (∑ m ∈ Finset.Icc (T + 1) y,
        ∑ k ∈ Finset.Icc (T + 1) (y / m), g m k) = ∑ x ∈ t, G x := by
    dsimp only [t, G]
    rw [Finset.sum_sigma]
  rw [hL, hR]
  refine Finset.sum_nbij' (fun x => (⟨x.2.1, x.2.2⟩ : Σ _ : ℕ, ℕ))
    (fun x => (⟨x.1 * x.2, (x.1, x.2)⟩ : Σ _ : ℕ, ℕ × ℕ)) ?_ ?_ ?_ ?_ ?_
  · -- hi : i x ∈ t
    intro x hx
    dsimp only [s] at hx
    rw [Finset.mem_sigma] at hx
    obtain ⟨hxs, hxanti⟩ := hx
    rw [Finset.mem_Icc] at hxs
    obtain ⟨hx1lo, hx1hi⟩ := hxs
    rw [Finset.mem_filter] at hxanti
    obtain ⟨hxantimem, hxanticond⟩ := hxanti
    rw [Nat.mem_divisorsAntidiagonal] at hxantimem
    obtain ⟨hmul, hne⟩ := hxantimem
    obtain ⟨ht1, ht2⟩ := hxanticond
    dsimp only [t]
    simp only [Finset.mem_sigma, Finset.mem_Icc]
    refine ⟨⟨by omega, ?_⟩, by omega, ?_⟩
    · calc x.2.1 ≤ x.2.1 * x.2.2 := Nat.le_mul_of_pos_right _ (by omega)
        _ = x.1 := hmul
        _ ≤ y := hx1hi
    · rw [Nat.le_div_iff_mul_le (by omega : 0 < x.2.1)]
      calc x.2.2 * x.2.1 = x.2.1 * x.2.2 := Nat.mul_comm _ _
        _ = x.1 := hmul
        _ ≤ y := hx1hi
  · -- hj : j x ∈ s
    intro x hx
    dsimp only [t] at hx
    rw [Finset.mem_sigma] at hx
    obtain ⟨hxt, hxk⟩ := hx
    rw [Finset.mem_Icc] at hxt hxk
    obtain ⟨hxt1lo, hxt1hi⟩ := hxt
    obtain ⟨hxk1lo, hxk1hi⟩ := hxk
    dsimp only [s]
    simp only [Finset.mem_sigma, Finset.mem_Icc, Finset.mem_filter, Nat.mem_divisorsAntidiagonal]
    rw [Nat.le_div_iff_mul_le (by omega : 0 < x.1)] at hxk1hi
    refine ⟨⟨Nat.mul_pos (by omega) (by omega), ?_⟩,
      ⟨⟨trivial, Nat.mul_ne_zero (by omega) (by omega)⟩, by omega, by omega⟩⟩
    calc x.1 * x.2 = x.2 * x.1 := Nat.mul_comm _ _
      _ ≤ y := hxk1hi
  · -- left_inv
    intro x hx
    obtain ⟨n, a, b⟩ := x
    dsimp only [s] at hx
    rw [Finset.mem_sigma] at hx
    obtain ⟨-, hxanti⟩ := hx
    rw [Finset.mem_filter] at hxanti
    obtain ⟨hxantimem, -⟩ := hxanti
    rw [Nat.mem_divisorsAntidiagonal] at hxantimem
    obtain ⟨hmul, -⟩ := hxantimem
    dsimp only []
    rw [hmul]
  · -- right_inv
    intro x hx
    obtain ⟨m, k⟩ := x
    rfl
  · -- h
    intro x hx
    rfl

end Commons.NumberTheory.ArithmeticFunction