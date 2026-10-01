import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Complex.Basic
import Mathlib.Order.Interval.Finset.Nat

open Finset

namespace Commons.NumberTheory.DirichletCharacter

/-- Decomposition of the sum `∑_{n ∈ Icc 1 N} f n` into residue classes modulo `q`:
each `n` is written uniquely as `a + m * q` with `1 ≤ a ≤ min q N` and `m ∈ Icc 0 ((N - a)/q)`. -/
theorem residue_block_sum_decomp (q N : ℕ) (hq : 1 ≤ q) (f : ℕ → ℂ) :
    ∑ n ∈ Finset.Icc 1 N, f n
      = ∑ a ∈ Finset.Icc 1 (min q N),
          ∑ m ∈ Finset.Icc 0 ((N - a) / q), f (a + m * q) := by
  have hqpos : 0 < q := hq
  rw [Finset.sum_sigma' (Finset.Icc 1 (min q N))
        (fun a => Finset.Icc 0 ((N - a) / q)) (fun a m => f (a + m * q))]
  symm
  apply Finset.sum_bij (fun x (_ : x ∈ (Finset.Icc 1 (min q N)).sigma
        (fun a => Finset.Icc 0 ((N - a) / q))) => x.1 + x.2 * q)
  · -- the map sends the sigma-type index set into `Icc 1 N`
    intro x hx
    rw [Finset.mem_sigma] at hx
    obtain ⟨hx1, hx2⟩ := hx
    rw [Finset.mem_Icc] at hx1 hx2 ⊢
    obtain ⟨ha1, ha2⟩ := hx1
    obtain ⟨_, hmq⟩ := hx2
    have hx1N : x.1 ≤ N := le_trans ha2 (min_le_right q N)
    have hmul : x.2 * q ≤ N - x.1 := (Nat.le_div_iff_mul_le hqpos).mp hmq
    exact ⟨le_trans ha1 (Nat.le_add_right _ _),
      (calc x.1 + x.2 * q ≤ x.1 + (N - x.1) := Nat.add_le_add_left hmul _
        _ = N := Nat.add_sub_cancel' hx1N)⟩
  · -- the map is injective
    intro x hx y hy hxy
    rw [Finset.mem_sigma] at hx hy
    obtain ⟨hx1, hx2⟩ := hx
    obtain ⟨hy1, hy2⟩ := hy
    rw [Finset.mem_Icc] at hx1 hy1
    have hxq : x.1 ≤ q := le_trans hx1.2 (min_le_left q N)
    have hyq : y.1 ≤ q := le_trans hy1.2 (min_le_left q N)
    have hb : x.1 - 1 < q := by omega
    have hc : y.1 - 1 < q := by omega
    have key : x.1 - 1 + x.2 * q = y.1 - 1 + y.2 * q := by omega
    have hmod : (x.1 - 1 + x.2 * q) % q = (y.1 - 1 + y.2 * q) % q := by rw [key]
    rw [Nat.add_mul_mod_self_right, Nat.add_mul_mod_self_right,
        Nat.mod_eq_of_lt hb, Nat.mod_eq_of_lt hc] at hmod
    have h1 : x.1 = y.1 := by omega
    have h2 : x.2 = y.2 := by
      have hxy' : x.2 * q = y.2 * q := by omega
      exact Nat.mul_right_cancel hqpos hxy'
    exact Sigma.ext h1 (heq_of_eq h2)
  · -- the map is surjective
    intro b hb
    rw [Finset.mem_Icc] at hb
    obtain ⟨hb1, hbN⟩ := hb
    refine ⟨⟨(b - 1) % q + 1, (b - 1) / q⟩, ?_, ?_⟩
    · rw [Finset.mem_sigma]
      dsimp only
      have hmodlt : (b - 1) % q < q := Nat.mod_lt _ hqpos
      have hmodle : (b - 1) % q ≤ b - 1 := Nat.mod_le _ _
      have hsub1 : b - 1 + 1 = b := Nat.sub_add_cancel hb1
      have hdm : (b - 1) / q * q + (b - 1) % q = b - 1 := by
        have h := Nat.div_add_mod (b - 1) q
        rwa [Nat.mul_comm q ((b - 1) / q)] at h
      constructor
      · rw [Finset.mem_Icc]
        exact ⟨by omega, le_min (by omega) (by omega)⟩
      · rw [Finset.mem_Icc]
        refine ⟨Nat.zero_le _, ?_⟩
        rw [Nat.le_div_iff_mul_le hqpos]
        omega
    · dsimp only
      have hsub1 : b - 1 + 1 = b := Nat.sub_add_cancel hb1
      have hdm : (b - 1) / q * q + (b - 1) % q = b - 1 := by
        have h := Nat.div_add_mod (b - 1) q
        rwa [Nat.mul_comm q ((b - 1) / q)] at h
      omega
  · intro x hx
    rfl

end Commons.NumberTheory.DirichletCharacter