import Mathlib
import Submission.Szemeredi.Removal.FullRegularity

/-!
# A manifestly monotone complexity ladder

`ladderM` is a variant of `ladder` whose per-step increment is *monotone* in the
complexity parameter `m`, which is needed to construct the a priori complexity
bounds (`Mbdd`) used in the corrected full regularity lemma.
-/

open scoped BigOperators
open Finset
open Szemeredi.Removal.SigAlg

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Szemeredi.Removal

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The manifestly monotone per-step complexity increment, dominating `dichBound`
whenever `ε ≤ 1`. -/
noncomputable def stepBound (H : Finset (Finset ι)) (m : ℕ) (G : ℕ → ℕ) (M : ℕ) : ℕ :=
  (H.card + 1) * 2 ^ (2 ^ m) * (G M + 1) ^ 2 + 2

/-- The monotone complexity ladder: starts at `G m` and at each step adds
`stepBound`, evaluated at the current value. -/
noncomputable def ladderM (H : Finset (Finset ι)) (m : ℕ) (G : ℕ → ℕ) : ℕ → ℕ :=
  Nat.rec (G m) (fun _ M => M + stepBound H m G M)

@[simp] theorem ladderM_zero (H : Finset (Finset ι)) (m : ℕ) (G : ℕ → ℕ) :
    ladderM H m G 0 = G m := rfl

@[simp] theorem ladderM_succ (H : Finset (Finset ι)) (m : ℕ) (G : ℕ → ℕ) (k : ℕ) :
    ladderM H m G (k + 1) = ladderM H m G k + stepBound H m G (ladderM H m G k) := rfl

theorem ladderM_mono_K (H : Finset (Finset ι)) (m : ℕ) (G : ℕ → ℕ) :
    Monotone (ladderM H m G) := by
  apply monotone_nat_of_le_succ
  intro k
  rw [ladderM_succ]
  exact Nat.le_add_right _ _

theorem stepBound_mono {H : Finset (Finset ι)} {G : ℕ → ℕ} (hG : Monotone G) {m1 m2 M1 M2 : ℕ}
    (hm : m1 ≤ m2) (hM : M1 ≤ M2) : stepBound H m1 G M1 ≤ stepBound H m2 G M2 := by
  unfold stepBound
  have h1 : 2 ^ (2 ^ m1) ≤ 2 ^ (2 ^ m2) := Nat.pow_le_pow_right (by norm_num)
    (Nat.pow_le_pow_right (by norm_num) hm)
  have h2 : (G M1 + 1) ^ 2 ≤ (G M2 + 1) ^ 2 :=
    Nat.pow_le_pow_left (Nat.add_le_add_right (hG hM) 1) 2
  have h3 : (H.card + 1) * 2 ^ (2 ^ m1) * (G M1 + 1) ^ 2
      ≤ (H.card + 1) * 2 ^ (2 ^ m2) * (G M2 + 1) ^ 2 :=
    Nat.mul_le_mul (Nat.mul_le_mul_left _ h1) h2
  omega

theorem ladderM_mono_m {H : Finset (Finset ι)} {G : ℕ → ℕ} (hG : Monotone G) {m1 m2 : ℕ}
    (h : m1 ≤ m2) (K : ℕ) : ladderM H m1 G K ≤ ladderM H m2 G K := by
  induction K with
  | zero => simpa using hG h
  | succ k ih =>
      rw [ladderM_succ, ladderM_succ]
      exact Nat.add_le_add ih (stepBound_mono hG h ih)

theorem ladderM_mono {H : Finset (Finset ι)} {G : ℕ → ℕ} (hG : Monotone G) {m1 m2 K1 K2 : ℕ}
    (hm : m1 ≤ m2) (hK : K1 ≤ K2) : ladderM H m1 G K1 ≤ ladderM H m2 G K2 :=
  le_trans (ladderM_mono_m hG hm K1) (ladderM_mono_K H m2 G hK)

/-- A crude step count dominating `prelimK H m (1/(F m))`. -/
noncomputable def stepCnt (H : Finset (Finset ι)) (m : ℕ) (F : ℕ → ℕ) : ℕ :=
  Nat.ceil ((H.card : ℝ) * (2 : ℝ) ^ (2 ^ m) * (F m : ℝ) ^ 2) + 1

theorem prelimK_one_div_le_stepCnt (H : Finset (Finset ι)) (m : ℕ) (F : ℕ → ℕ)
    (hFpos : 0 < F m) : prelimK H m (1 / (F m : ℝ)) ≤ stepCnt H m F := by
  unfold prelimK stepCnt
  have hFm : (F m : ℝ) ≠ 0 := by positivity
  have h : (H.card : ℝ) * (2 : ℝ) ^ (2 ^ m) / (1 / (F m : ℝ)) ^ 2
      = (H.card : ℝ) * (2 : ℝ) ^ (2 ^ m) * (F m : ℝ) ^ 2 := by
    rw [one_div, inv_pow, div_inv_eq_mul]
  rw [h]

theorem stepCnt_mono (H : Finset (Finset ι)) (F : ℕ → ℕ) (hF : Monotone F) :
    Monotone (fun m => stepCnt H m F) := by
  intro m1 m2 hm
  unfold stepCnt
  apply Nat.add_le_add_right
  apply Nat.ceil_mono
  have h1 : (2 : ℝ) ^ (2 ^ m1) ≤ (2 : ℝ) ^ (2 ^ m2) :=
    pow_le_pow_right₀ (by norm_num) (Nat.pow_le_pow_right (by norm_num) hm)
  have h2 : (F m1 : ℝ) ≤ (F m2 : ℝ) := by exact_mod_cast hF hm
  gcongr

/-- `ladder` is bounded by `ladderM` when `ε ≤ 1`. -/
theorem ladder_le_ladderM {H : Finset (Finset ι)} {m : ℕ} {ε : ℝ} {G : ℕ → ℕ}
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hG1 : ∀ n, 1 ≤ G n) (hGmono : Monotone G) (k : ℕ) :
    ladder H m ε G k ≤ ladderM H m G k := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [ladder_succ, ladderM_succ]
      have hGM : G (ladder H m ε G k) ≤ G (ladderM H m G k) := hGmono ih
      have hGC : (G (ladder H m ε G k) : ℝ) ≤ (G (ladderM H m G k) : ℝ) + 1 := by
        exact_mod_cast le_trans hGM (Nat.le_succ _)
      have hd : dichBound H m ε (1 / (G (ladder H m ε G k) : ℝ))
          ≤ stepBound H m G (ladderM H m G k) := by
        unfold dichBound stepBound
        have hsq : ε ^ 2 ≤ 1 := by nlinarith
        have hC2 : (G (ladder H m ε G k) : ℝ) ^ 2
            ≤ ((G (ladderM H m G k) : ℝ) + 1) ^ 2 :=
          pow_le_pow_left₀ (by positivity) hGC 2
        have hval : (H.card : ℝ) * (2 : ℝ) ^ (2 ^ m) * ε ^ 2
              / (1 / (G (ladder H m ε G k) : ℝ)) ^ 2
            ≤ ((H.card + 1) * 2 ^ (2 ^ m) * (G (ladderM H m G k) + 1) ^ 2 : ℕ) := by
          have heq : (H.card : ℝ) * (2 : ℝ) ^ (2 ^ m) * ε ^ 2
                / (1 / (G (ladder H m ε G k) : ℝ)) ^ 2
              = (H.card : ℝ) * (2 : ℝ) ^ (2 ^ m)
                * (ε ^ 2 * (G (ladder H m ε G k) : ℝ) ^ 2) := by
            rw [one_div, inv_pow, div_inv_eq_mul]; ring
          rw [heq]
          have hA : (H.card : ℝ) ≤ (H.card : ℝ) + 1 := by linarith
          have hL : (H.card : ℝ) * (2 : ℝ) ^ (2 ^ m)
              ≤ ((H.card : ℝ) + 1) * (2 : ℝ) ^ (2 ^ m) :=
            mul_le_mul_of_nonneg_right hA (by positivity)
          have hR : ε ^ 2 * (G (ladder H m ε G k) : ℝ) ^ 2
              ≤ 1 * ((G (ladderM H m G k) : ℝ) + 1) ^ 2 :=
            mul_le_mul hsq hC2 (by positivity) (by norm_num)
          calc (H.card : ℝ) * (2 : ℝ) ^ (2 ^ m)
                * (ε ^ 2 * (G (ladder H m ε G k) : ℝ) ^ 2)
              = ((H.card : ℝ) * (2 : ℝ) ^ (2 ^ m))
                * (ε ^ 2 * (G (ladder H m ε G k) : ℝ) ^ 2) := by ring
            _ ≤ (((H.card : ℝ) + 1) * (2 : ℝ) ^ (2 ^ m))
                * (1 * ((G (ladderM H m G k) : ℝ) + 1) ^ 2) :=
                mul_le_mul hL hR (by positivity) (by positivity)
            _ = ((H.card + 1) * 2 ^ (2 ^ m) * (G (ladderM H m G k) + 1) ^ 2 : ℕ) := by
                push_cast; ring
        have h1 : Nat.ceil ((H.card : ℝ) * (2 : ℝ) ^ (2 ^ m) * ε ^ 2
              / (1 / (G (ladder H m ε G k) : ℝ)) ^ 2)
            ≤ (H.card + 1) * 2 ^ (2 ^ m) * (G (ladderM H m G k) + 1) ^ 2 :=
          Nat.ceil_le.mpr hval
        omega
      omega

end Szemeredi.Removal
