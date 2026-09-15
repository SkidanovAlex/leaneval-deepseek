import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Ring.IsFormallyReal
import Submission.Commons.Combinatorics.Additive.AP.sum_of_linear_forms

open Finset

namespace Commons.Combinatorics.Transference

theorem avg_tau_dot {p : ℕ} [Fact p.Prime] {d : ℕ} (c : Fin d → ZMod p) (hc : ∃ j, c j ≠ 0)
    (τ : ZMod p → ℝ) (K : ℕ) {A : ℝ}
    (hτ : (Fintype.card (ZMod p) : ℝ)⁻¹ * ∑ x, (τ x) ^ K ≤ A) :
    (Fintype.card (Fin d → ZMod p) : ℝ)⁻¹ *
      (∑ h : Fin d → ZMod p, (τ (∑ j, c j * h j)) ^ K) ≤ A := by
  classical
  obtain ⟨j0, hj0⟩ := hc
  have hd : 1 ≤ d := by
    have := j0.isLt
    omega
  let c' : Fin 1 → Fin d → ZMod p := fun _ => c
  have hsurj : Function.Surjective
      (fun y : Fin d → ZMod p => fun m : Fin 1 => ∑ i, c' m i * y i) := by
    intro z
    refine ⟨Pi.single j0 (z 0 * (c j0)⁻¹), ?_⟩
    funext m
    have hm : m = 0 := Subsingleton.elim m 0
    rw [hm]
    show (∑ i : Fin d, c i * (Pi.single j0 (z 0 * (c j0)⁻¹) : Fin d → ZMod p) i) = z 0
    rw [Finset.sum_eq_single j0]
    · rw [Pi.single_eq_same]
      have hh : c j0 * (z 0 * (c j0)⁻¹) = z 0 * (c j0 * (c j0)⁻¹) := by ring
      rw [hh, mul_inv_cancel₀ hj0, mul_one]
    · intro b _ hb
      rw [Pi.single_eq_of_ne hb, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ j0) h
  have h1 : (∑ z : Fin 1 → ZMod p, (τ (z 0)) ^ K) = ∑ x : ZMod p, (τ x) ^ K := by
    let e : (Fin 1 → ZMod p) ≃ ZMod p :=
      { toFun := fun z => z 0
        invFun := fun x => fun _ => x
        left_inv := by intro z; funext m; fin_cases m; rfl
        right_inv := by intro x; rfl }
    exact Fintype.sum_equiv e (fun z : Fin 1 → ZMod p => (τ (z 0)) ^ K)
      (fun x : ZMod p => (τ x) ^ K) (fun z => rfl)
  have key := Commons.Combinatorics.Additive.AP.sum_of_linear_forms (p := p) (n := d) (r := 1)
    hd c' hsurj (fun z : Fin 1 → ZMod p => (τ (z 0)) ^ K)
  have hsum : (∑ y : Fin d → ZMod p, (τ (∑ i, c i * y i)) ^ K)
      = (p : ℝ) ^ (d - 1) * (∑ x : ZMod p, (τ x) ^ K) := by
    rw [← h1]
    simpa [c'] using key
  have hcardV : (Fintype.card (Fin d → ZMod p) : ℝ) = (p : ℝ) ^ d := by
    have h : Fintype.card (Fin d → ZMod p) = p ^ d := by
      rw [Fintype.card_fun, Fintype.card_fin, ZMod.card]
    rw [h, Nat.cast_pow]
  have hp0 : (p : ℝ) ≠ 0 := by
    exact_mod_cast (Fact.out : p.Prime).ne_zero
  rw [hsum, hcardV]
  have hmain : ((p : ℝ) ^ d)⁻¹ * ((p : ℝ) ^ (d - 1) * (∑ x : ZMod p, (τ x) ^ K))
      = (p : ℝ)⁻¹ * (∑ x : ZMod p, (τ x) ^ K) := by
    have hPd : (p : ℝ) ^ d = (p : ℝ) ^ (d - 1) * (p : ℝ) := by
      rw [← pow_succ, Nat.sub_add_cancel hd]
    rw [hPd, mul_inv_rev, mul_assoc,
      ← mul_assoc ((p : ℝ) ^ (d - 1))⁻¹ ((p : ℝ) ^ (d - 1)) (∑ x : ZMod p, (τ x) ^ K),
      inv_mul_cancel₀ (pow_ne_zero _ hp0), one_mul]
  rw [hmain]
  simpa [ZMod.card] using hτ

end Commons.Combinatorics.Transference