import Mathlib
import Submission.Work.GYMajorant
import Submission.Work.RelSzem3
import Submission.Work.Extract2
import Submission.Commons.Combinatorics.Additive.Szemeredi.dense_szemeredi_function

/-!
# The Green–Tao majorant assembly (workstream C, final step)

This file isolates the *exact* remaining gap of the Green–Tao development in a single hypothesis
`hP`: the Green–Tao Proposition 9.5 statement that the Goldston–Yıldırım measurement
`ν = nuGT` (Green–Tao Definition 8.1) is `k`-pseudorandom with arbitrarily small error, has
positive density and dominates the W-tricked von Mangoldt `fGT = Λ̃`.

Everything on the transference side is unconditional and `p`-uniform
(`GTTrans.relative_szemeredi_uniform_final`), so the passage from `hP` to the theorem is a short
composition.
-/

open Finset
open scoped BigOperators

set_option linter.style.haveILetI false

namespace GYMaj

open Commons.NumberTheory.Sieve

/-- The Green–Tao constant `k · 2^{k+5}` of Lemma `mu-majorises`. -/
noncomputable def Cmaj (k : ℕ) : ℝ := (k : ℝ) * (2 : ℝ) ^ (k + 5)

/-- **The Green–Tao majorant interface** (Green–Tao Proposition 9.5). -/
theorem green_tao_of_majorant {εw : ℝ} (hεw : 0 < εw) (hεw4 : 4 * εw < 1)
    (hP : ∀ (k : ℕ), 3 ≤ k → ∃ (δ : ℝ) (CmB : ℕ → ℕ → ℝ), 0 < δ ∧
      ∀ (cd : ℝ), 0 < cd → ∀ (ε : ℝ), 0 < ε →
      ∃ (P : ℕ), 0 < P ∧
      ∀ (p : ℕ) [Fact p.Prime], P ≤ p →
        ∃ (R W : ℕ) (B : ℝ), 1 < R ∧ 1 ≤ W ∧ 0 < B ∧
          KPseudorandom p k (nuGT R W p εw) CmB ε ∧
          δ * (p : ℝ) ≤ ∑ x : ZMod p, (Cmaj k)⁻¹ * fGT W p εw x ∧
          (∀ x : ZMod p, (Cmaj k)⁻¹ * fGT W p εw x ≤ nuGT R W p εw x) ∧
          (∀ x : ZMod p, (Cmaj k)⁻¹ * fGT W p εw x ≤ B) ∧
          B ^ (k - 1) * (∑ x : ZMod p, (Cmaj k)⁻¹ * fGT W p εw x) < cd * (p : ℝ) ^ 2 ∧
          (∀ x : ZMod p, fGT W p εw x ≠ 0 →
            εw * (p : ℝ) ≤ (x.val : ℝ) ∧ (x.val : ℝ) ≤ 2 * εw * (p : ℝ) ∧
              Nat.Prime (W * x.val + 1))) :
    LeanEval.NumberTheory.ContainsArbitraryAPs {p : ℕ | Nat.Prime p} := by
  classical
  refine GTTrans.contains_arith_prog_of_data_var (εw := εw) hεw hεw4 ?_
  intro k hk
  obtain ⟨δ, CmB, hδ, hrest⟩ := hP k hk
  -- the dense Szemerédi engine, at density `δ/12`
  set δd : ℝ := δ / 12 with hδddef
  have hδd : 0 < δd := by rw [hδddef]; linarith
  have hδδd : 4 * δd * 3 ≤ δ := le_of_eq (by rw [hδddef]; ring)
  obtain ⟨cd, hcd, P₀, hDense⟩ :=
    Commons.Combinatorics.Additive.Szemeredi.dense_szemeredi_function (k := k) (by omega)
      (δ := δd) hδd
  -- the Gowers-uniformity parameter
  set T : ℝ := GTTrans.relSzemBudget k cd with hTdef
  have h2k : (0 : ℝ) < (2 : ℝ) ^ k - 1 := by
    have h := one_lt_pow₀ (by norm_num : (1:ℝ) < 2) (by omega : k ≠ 0)
    linarith
  have h3k : (0 : ℝ) < (3 : ℝ) ^ k - 1 := by
    have h := one_lt_pow₀ (by norm_num : (1:ℝ) < 3) (by omega : k ≠ 0)
    linarith
  have hTpos : 0 < T := by
    rw [hTdef, GTTrans.relSzemBudget]
    exact div_pos (mul_pos h3k hcd) (mul_pos h2k (by positivity))
  set s : ℝ := 3 * T / (2 * 16 * (2 : ℝ) ^ k) with hsdef
  have hs0 : 0 < s := by rw [hsdef]; positivity
  set gr : ℝ := s ^ (2 ^ (k - 1)) with hgrdef
  have hgr : 0 < gr := by rw [hgrdef]; exact pow_pos hs0 _
  have h16k : (0 : ℝ) < 16 * (2 : ℝ) ^ k := by positivity
  have hgrT : (16 * (2 : ℝ) ^ k) * (gr ^ (((2 ^ (k - 1) : ℕ) : ℝ))⁻¹ / 3)
      ≤ GTTrans.relSzemBudget k cd / 2 := by
    have hgrn : (0 : ℝ) < ((2 ^ (k - 1) : ℕ) : ℝ) := by positivity
    have hpow : gr ^ (((2 ^ (k - 1) : ℕ) : ℝ))⁻¹ = s := by
      rw [hgrdef, ← Real.rpow_natCast s (2 ^ (k - 1)), ← Real.rpow_mul (le_of_lt hs0)]
      rw [mul_inv_cancel₀ (by positivity : (((2 ^ (k - 1) : ℕ)) : ℝ) ≠ 0), Real.rpow_one]
    have hval : (16 * (2 : ℝ) ^ k) * (s / 3) = T / 2 := by rw [hsdef]; field_simp
    rw [hpow, hval, hTdef]
  -- the uniform relative Szemerédi theorem
  obtain ⟨N₀, εp₀, hεp₀0, hεp₀1, hmain⟩ :=
    GTTrans.relative_szemeredi_uniform_final (k := k) hk (C := 5) (by norm_num)
      (C₀ := CmB) (δ := δ) (δd := δd) (cd := cd) hgr hδ hδd hcd hDense hδδd hgrT
  -- the majorant at error `εp₀`
  obtain ⟨Ph, hPh0, hdata⟩ := hrest cd hcd εp₀ hεp₀0
  refine ⟨cd, max Ph (max N₀ (max P₀ k)), hcd, ?_⟩
  intro p hpprime hpP
  haveI : Fact p.Prime := hpprime
  have hpPh : Ph ≤ p := le_trans (le_max_left _ _) hpP
  have hpN₀ : N₀ ≤ p := le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hpP)
  have hpP₀ : P₀ ≤ p := le_trans (le_max_left _ _) (le_trans (le_max_right _ _)
    (le_trans (le_max_right _ _) hpP))
  have hpk : k ≤ p := le_trans (le_max_right _ _)
    (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hpP))
  obtain ⟨R, W, B, hR1, hW1, hB0, hKp, hdens, hmaj, hBfd, hBnum, hsupp⟩ := hdata p hpPh
  set f : ZMod p → ℝ := fun x => (Cmaj k)⁻¹ * fGT W p εw x with hfdef
  have hf0 : ∀ x, 0 ≤ f x := fun x => mul_nonneg
    (inv_nonneg.mpr (mul_nonneg (Nat.cast_nonneg k) (by positivity))) (fGT_nonneg W p εw x)
  have hsupp' : ∀ x : ZMod p, f x ≠ 0 →
      εw * (p : ℝ) ≤ (x.val : ℝ) ∧ (x.val : ℝ) ≤ 2 * εw * (p : ℝ) ∧
        Nat.Prime (W * x.val + 1) := by
    intro x hx
    exact hsupp x (fun h => hx (by rw [hfdef]; simp only [h, mul_zero]))
  refine ⟨W, f, B, hW1, hf0, hBfd, hBnum, ?_, hsupp'⟩
  -- the sharp AP count
  have hsh := hmain p hpk hpN₀ hpP₀ (nuGT R W p εw) f εp₀
    (fun x => nuGT_nonneg hR1 x) hf0 hmaj hKp hεp₀0.le hdens le_rfl
  exact hsh

end GYMaj
