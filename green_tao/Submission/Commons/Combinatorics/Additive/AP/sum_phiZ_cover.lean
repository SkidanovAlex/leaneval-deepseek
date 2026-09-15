import Mathlib
import Submission.Commons.Combinatorics.Additive.AP.sum_of_two_linear_forms

namespace Commons.Combinatorics.Additive.AP

open Finset

/-- Sum of a function updated at one point, over a finite type. -/
lemma sum_update {α M : Type*} [Fintype α] [DecidableEq α] [AddCommGroup M]
    (f : α → M) (a : α) (b : M) :
    ∑ i, Function.update f a b i = ∑ i, f i + (b - f a) := by
  have h : ∀ i, Function.update f a b i = f i + (if i = a then b - f a else 0) := by
    intro i
    by_cases hi : i = a
    · subst hi
      rw [Function.update_self, if_pos rfl]
      abel
    · rw [Function.update_of_ne hi, if_neg hi]
      abel
  rw [Finset.sum_congr rfl (fun i _ => h i), Finset.sum_add_distrib]
  congr 1
  rw [Finset.sum_ite_eq']
  simp

/-- Weighted version of `sum_update`. -/
lemma sum_mul_update {α M : Type*} [Fintype α] [DecidableEq α] [CommRing M]
    (c f : α → M) (a : α) (b : M) :
    ∑ i, c i * Function.update f a b i = (∑ i, c i * f i) + c a * (b - f a) := by
  have h : ∀ i, c i * Function.update f a b i
      = c i * f i + (if i = a then c i * (b - f a) else 0) := by
    intro i
    by_cases hi : i = a
    · subst hi
      rw [Function.update_self, if_pos rfl]
      ring
    · rw [Function.update_of_ne hi, if_neg hi]
      ring
  rw [Finset.sum_congr rfl (fun i _ => h i), Finset.sum_add_distrib]
  congr 1
  rw [Finset.sum_ite_eq']
  simp

/-- Sum of a function, updated at two distinct points, which vanishes off those points. -/
lemma sum_update₂ {α M : Type*} [Fintype α] [DecidableEq α] [AddCommGroup M]
    {a₁ a₂ : α} (h : a₁ ≠ a₂) (b₁ b₂ : M) :
    ∑ i, Function.update (Function.update (0 : α → M) a₁ b₁) a₂ b₂ i = b₁ + b₂ := by
  rw [sum_update (Function.update (0 : α → M) a₁ b₁) a₂ b₂,
      Function.update_of_ne h.symm, sum_update (0 : α → M) a₁ b₁]
  simp

/-- Weighted version of `sum_update₂`. -/
lemma sum_mul_update₂ {α M : Type*} [Fintype α] [DecidableEq α] [CommRing M]
    {a₁ a₂ : α} (h : a₁ ≠ a₂) (b₁ b₂ : M) (c : α → M) :
    ∑ i, c i * Function.update (Function.update (0 : α → M) a₁ b₁) a₂ b₂ i
      = c a₁ * b₁ + c a₂ * b₂ := by
  rw [sum_mul_update c (Function.update (0 : α → M) a₁ b₁) a₂ b₂,
      Function.update_of_ne h.symm, sum_mul_update c (0 : α → M) a₁ b₁,
      Finset.sum_eq_zero (fun i _ => by simp)]
  simp

/-- Surjectivity of `y ↦ (∑ y i, ∑ y i * ((i:ZMod p)+1)⁻¹)` for `n ≥ 2`, `p ≥ 3`. -/
lemma surj_phiZ {p : ℕ} [Fact p.Prime] {n : ℕ} (hn : 2 ≤ n) (hp : 3 ≤ p) :
    Function.Surjective (fun y : Fin n → ZMod p =>
      (∑ i : Fin n, (1 : ZMod p) * y i, ∑ i : Fin n, ((i : ZMod p) + 1)⁻¹ * y i)) := by
  intro q
  obtain ⟨a, b⟩ := q
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h
    have hd : p ∣ 2 := (CharP.cast_eq_zero_iff (ZMod p) p 2).mp h
    have hp2 : p ≤ 2 := Nat.le_of_dvd (by norm_num) hd
    omega
  have hn0 : 0 < n := by omega
  have hn1 : 1 < n := by omega
  let i0 : Fin n := ⟨0, hn0⟩
  let i1 : Fin n := ⟨1, hn1⟩
  have hi01 : i0 ≠ i1 := by
    intro h
    have hh := congrArg Fin.val h
    simp only [i0, i1] at hh
    omega
  set Y : Fin n → ZMod p :=
    Function.update (Function.update (0 : Fin n → ZMod p) i0 (2*b - a)) i1 (2*(a-b)) with hY
  refine ⟨Y, ?_⟩
  rw [hY, Prod.mk.injEq]
  have hc0 : ((i0 : ZMod p) + 1)⁻¹ = 1 := by
    have : (i0 : ZMod p) = 0 := by simp [i0]
    rw [this]; norm_num
  have hc1 : ((i1 : ZMod p) + 1)⁻¹ = (2 : ZMod p)⁻¹ := by
    have : (i1 : ZMod p) = 1 := by simp [i1]
    rw [this]; norm_num
  constructor
  · simp only [one_mul]
    rw [sum_update₂ hi01 (2*b - a) (2*(a-b))]
    ring
  · rw [sum_mul_update₂ hi01 (2*b - a) (2*(a-b)) (fun i => ((i : ZMod p) + 1)⁻¹)]
    simp only [hc0, hc1]
    have hmm : (2 : ZMod p)⁻¹ * (2 * (a - b)) = a - b := by
      rw [← mul_assoc, inv_mul_cancel₀ h2, one_mul]
    rw [one_mul, hmm]
    ring

theorem sum_phiZ_cover {p : ℕ} [Fact p.Prime] {k : ℕ} (hk : 3 ≤ k) (hkp : k ≤ p)
    (G : ZMod p → ZMod p → ℝ) :
    (∑ u : Fin (k-1) → ZMod p, G (∑ t, u t) (∑ t, u t / ((t : ZMod p) + 1)))
      = (p : ℝ)^(k-3) * ∑ q : ZMod p × ZMod p, G q.1 q.2 := by
  have hn : 2 ≤ k - 1 := by omega
  have hp : 3 ≤ p := by omega
  have hsub : k - 1 - 2 = k - 3 := by omega
  have key := sum_of_two_linear_forms (p := p) (n := k - 1) hn
      (fun _ : Fin (k-1) => (1 : ZMod p)) (fun i : Fin (k-1) => ((i : ZMod p) + 1)⁻¹)
      (surj_phiZ hn hp) (fun z : ZMod p × ZMod p => G z.1 z.2)
  trans (∑ y : Fin (k-1) → ZMod p,
      G (∑ i : Fin (k-1), (1 : ZMod p) * y i)
        (∑ i : Fin (k-1), ((i : ZMod p) + 1)⁻¹ * y i))
  · apply Finset.sum_congr rfl
    intro y _
    rw [show (∑ i : Fin (k-1), (1 : ZMod p) * y i) = ∑ i, y i from
          Finset.sum_congr rfl (fun i _ => one_mul (y i)),
        show (∑ i : Fin (k-1), ((i : ZMod p) + 1)⁻¹ * y i) = ∑ i, y i / ((i : ZMod p) + 1) from
          Finset.sum_congr rfl (fun i _ => by rw [div_eq_mul_inv, mul_comm])]
  · rw [← hsub]; exact key

end Commons.Combinatorics.Additive.AP
