import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Ring.BooleanRing

namespace Commons.Combinatorics.Transference

open Finset

/-- Auxiliary general bound: for a finite index set `S`, a family of points `u ω h` (indexed by
`ω ∈ S` and `h : H`, with `H` a finite type of cardinality `N`) and functions `ν F` with
`|F x| ≤ ν x + 1`, if the "local Fourier condition" `|N⁻¹ ∑ h, ∏_{ω ∈ A} ν (u ω h) - 1| ≤ ε`
holds for every nonempty subset `A ⊆ S`, then
`|N⁻¹ ∑ h, ∏_{ω ∈ S} F (u ω h)| ≤ 2^{|S|} (1 + ε)`. -/
theorem dualFunc_bound_gen {α H X : Type*} [Fintype H] [DecidableEq α]
    (S : Finset α) (u : α → H → X) (ν F : X → ℝ)
    (hF : ∀ x, |F x| ≤ ν x + 1) {ε : ℝ} (hε : 0 ≤ ε)
    (hNpos : 0 < ((Fintype.card H : ℝ)))
    (hLFC : ∀ A : Finset α, A ⊆ S → A.Nonempty →
      |((Fintype.card H : ℝ))⁻¹ * (∑ h : H, ∏ ω ∈ A, ν (u ω h)) - 1| ≤ ε) :
    |((Fintype.card H : ℝ))⁻¹ *
      (∑ h : H, ∏ ω ∈ S, F (u ω h))| ≤ (2:ℝ)^(S.card) * (1+ε) := by
  have hNne : ((Fintype.card H : ℝ)) ≠ 0 := ne_of_gt hNpos
  have hNinv_nonneg : 0 ≤ ((Fintype.card H : ℝ))⁻¹ := inv_nonneg.mpr (le_of_lt hNpos)
  have hFle : ∀ x, |F x| ≤ 1 + ν x := by intro x; have := hF x; linarith
  have step1 : |∑ h : H, ∏ ω ∈ S, F (u ω h)|
      ≤ ∑ A ∈ S.powerset, ∑ h : H, ∏ ω ∈ A, ν (u ω h) := by
    calc |∑ h : H, ∏ ω ∈ S, F (u ω h)|
        ≤ ∑ h : H, |∏ ω ∈ S, F (u ω h)| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ h : H, ∏ ω ∈ S, |F (u ω h)| := by simp_rw [Finset.abs_prod]
      _ ≤ ∑ h : H, ∏ ω ∈ S, (1 + ν (u ω h)) := by
            apply Finset.sum_le_sum; intro h _
            apply Finset.prod_le_prod
            · intro ω _; exact abs_nonneg _
            · intro ω _; exact hFle _
      _ = ∑ h : H, ∑ A ∈ S.powerset, ∏ ω ∈ A, ν (u ω h) := by
            simp_rw [Finset.prod_one_add]
      _ = ∑ A ∈ S.powerset, ∑ h : H, ∏ ω ∈ A, ν (u ω h) := Finset.sum_comm
  have hterm : ∀ A ∈ S.powerset,
      |((Fintype.card H : ℝ))⁻¹ * (∑ h : H, ∏ ω ∈ A, ν (u ω h))| ≤ 1 + ε := by
    intro A hA
    rw [Finset.mem_powerset] at hA
    by_cases hne : A.Nonempty
    · have h := hLFC A hA hne
      rw [abs_le] at h ⊢
      exact ⟨by linarith [h.1], by linarith [h.2]⟩
    · rw [Finset.not_nonempty_iff_eq_empty] at hne
      subst hne
      simp only [Finset.prod_empty, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
        inv_mul_cancel₀ hNne, abs_one]
      linarith
  calc |((Fintype.card H : ℝ))⁻¹ * (∑ h : H, ∏ ω ∈ S, F (u ω h))|
      ≤ ∑ A ∈ S.powerset, |((Fintype.card H : ℝ))⁻¹ * (∑ h : H, ∏ ω ∈ A, ν (u ω h))| := by
        rw [abs_mul, abs_of_nonneg hNinv_nonneg]
        calc (Fintype.card H : ℝ)⁻¹ * |∑ h : H, ∏ ω ∈ S, F (u ω h)|
            ≤ (Fintype.card H : ℝ)⁻¹ * ∑ A ∈ S.powerset, ∑ h : H, ∏ ω ∈ A, ν (u ω h) :=
              mul_le_mul_of_nonneg_left step1 hNinv_nonneg
          _ = ∑ A ∈ S.powerset, (Fintype.card H : ℝ)⁻¹ * (∑ h : H, ∏ ω ∈ A, ν (u ω h)) := by
              rw [Finset.mul_sum]
          _ ≤ ∑ A ∈ S.powerset, |(Fintype.card H : ℝ)⁻¹ * (∑ h : H, ∏ ω ∈ A, ν (u ω h))| := by
              apply Finset.sum_le_sum; intro A _; exact le_abs_self _
    _ ≤ ∑ A ∈ S.powerset, (1 + ε) := by
        apply Finset.sum_le_sum; intro A hA; exact hterm A hA
    _ = (2:ℝ)^(S.card) * (1+ε) := by
        rw [Finset.sum_const, nsmul_eq_mul, Finset.card_powerset]
        push_cast; ring

theorem dualFunc_bound {p : ℕ} [Fact p.Prime] {d : ℕ} (hd : 1 ≤ d) (ν : ZMod p → ℝ)
    (F : ZMod p → ℝ) (hF : ∀ x, |F x| ≤ ν x + 1) {ε : ℝ} (hε : 0 ≤ ε)
    (hLFC : ∀ A : Finset (Fin d → Bool), A ⊆ Finset.univ.erase (0 : Fin d → Bool) →
      A.Nonempty → ∀ b : ZMod p,
      |((Fintype.card (Fin d → ZMod p) : ℝ))⁻¹ *
        (∑ h : Fin d → ZMod p,
          ∏ ω ∈ A, ν (b + ∑ j : Fin d, (if ω j then (1 : ZMod p) else 0) * h j)) - 1|
        ≤ ε) (b : ZMod p) :
    |((Fintype.card (Fin d → ZMod p) : ℝ))⁻¹ *
      (∑ h : Fin d → ZMod p,
        ∏ ω ∈ Finset.univ.erase (0 : Fin d → Bool),
          F (b + ∑ j : Fin d, (if ω j then (1 : ZMod p) else 0) * h j))|
      ≤ ((2 : ℝ) ^ (2 ^ d - 1)) * (1 + ε) := by
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hpd : 2 ≤ p ^ d := by
    calc 2 ≤ p := hp2
      _ = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ d := Nat.pow_le_pow_right (by omega) hd
  have hNpos : 0 < ((Fintype.card (Fin d → ZMod p) : ℝ)) := by
    have hcard : Fintype.card (Fin d → ZMod p) = p ^ d := by
      rw [Fintype.card_fun, ZMod.card, Fintype.card_fin]
    rw [hcard]
    have : (2:ℝ) ≤ ((p ^ d : ℕ) : ℝ) := by exact_mod_cast hpd
    linarith
  have hScard : (Finset.univ.erase (0 : Fin d → Bool)).card = 2 ^ d - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fun,
      Fintype.card_bool, Fintype.card_fin]
  let u : (Fin d → Bool) → (Fin d → ZMod p) → ZMod p :=
    fun ω h => b + ∑ j : Fin d, (if ω j then (1 : ZMod p) else 0) * h j
  have key := dualFunc_bound_gen (S := Finset.univ.erase (0 : Fin d → Bool))
      (u := u) (ν := ν) (F := F) hF hε hNpos
      (fun A hA hAne => hLFC A hA hAne b)
  rw [hScard] at key
  exact key

end Commons.Combinatorics.Transference