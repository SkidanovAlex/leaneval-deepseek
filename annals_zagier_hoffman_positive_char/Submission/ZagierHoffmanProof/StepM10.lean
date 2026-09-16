import Submission.ZagierHoffmanProof.StepM9
import Submission.ZagierHoffmanProof.StepL199
import Submission.ZagierHoffmanProof.StepB5
import Submission.ZagierHoffmanProof.Block
import Submission.ZagierHoffmanProof.StepD
import Submission.ZagierHoffmanProof.StepL1

set_option autoImplicit false
set_option maxHeartbeats 16000000

open Polynomial RatFunc
open scoped BigOperators WithZero
open WithZero
open Commons.Data.Nat

/-!
# Step M10: Thakur's theorem "multizeta values do not vanish" over `F₂`

Using the exact degree of every power sum over `F₂` (`val_P_iter`, Step M7) we compute the
degree of every multizeta block `S_d(𝔰)`:

  `v (S_d 𝔰) = exp (−(sExp d 𝔰₀ + sExp (d−1) 𝔰₁ + ⋯ + sExp (d−r+1) 𝔰_{r−1}))`,

the exponent is strictly increasing in `d` (`sSeq_strictMono`), so the block `d = r-1` strictly
dominates the others in the sum `ζ_A(𝔰) = Σ_d S_d(𝔰)`, whence `ζ_A(𝔰) ≠ 0` for **every**
tuple `𝔰` — Thakur's Theorem 4 at `q = 2`.
-/

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

section Seq

/-- The exponent of the depth-`r` block `S_d(𝔰)`: the (unique) dominating degree configuration
is `(d, r-2, r-3, …, 0)`, so the exponent is
`sExp d (𝔰 0) + sSeq (r-1) (tail 𝔰) (r-2)`. -/
noncomputable def sSeq : (r : ℕ) → (Fin r → ℕ+) → ℕ → ℤ
  | 0, _, _ => 0
  | 1, 𝔰, d => sExp d (𝔰 0)
  | (r + 2), 𝔰, d => sExp d (𝔰 0) + sSeq (r + 1) (expTail 𝔰) r

lemma sSeq_one (𝔰 : Fin 1 → ℕ+) (d : ℕ) : sSeq 1 𝔰 d = sExp d (𝔰 0) := by
  rw [sSeq]

lemma sSeq_succ (r : ℕ) (𝔰 : Fin (r + 2) → ℕ+) (d : ℕ) :
    sSeq (r + 2) 𝔰 d = sExp d (𝔰 0) + sSeq (r + 1) (expTail 𝔰) r := by
  rw [sSeq]

/-- `sSeq r 𝔰` is strictly increasing in the level `d`. -/
lemma sSeq_strictMono : ∀ (r : ℕ) (hr : 0 < r) (𝔰 : Fin r → ℕ+),
    StrictMono (fun d => sSeq r 𝔰 d) := by
  intro r
  induction r with
  | zero => intro hr; exact absurd hr (by omega)
  | succ r ih =>
      intro hr 𝔰
      rcases Nat.eq_zero_or_pos r with hr0 | hr0
      · subst hr0
        intro a b hab
        show sSeq 1 𝔰 a < sSeq 1 𝔰 b
        rw [sSeq_one, sSeq_one]
        exact sExp_strictMono (𝔰 0) hab
      · obtain ⟨k, rfl⟩ : ∃ k, r = k + 1 := ⟨r - 1, by omega⟩
        intro a b hab
        show sSeq (k + 2) 𝔰 a < sSeq (k + 2) 𝔰 b
        rw [sSeq_succ k 𝔰 a, sSeq_succ k 𝔰 b]
        have h1 : sExp a (𝔰 0) < sExp b (𝔰 0) := sExp_strictMono (𝔰 0) hab
        linarith

end Seq

section Blocks

/-- ★★ The exact valuation of every multizeta block over `F₂`. -/
theorem val_S_sSeq (h2 : Nat.card F = 2) :
    ∀ (r : ℕ) (hr : 0 < r) (𝔰 : Fin r → ℕ+) (d : ℕ),
      r - 1 ≤ d → Valued.v (S F r hr 𝔰 d) = exp (-(sSeq r 𝔰 d)) := by
  intro r
  induction r with
  | zero => intro hr; exact absurd hr (by omega)
  | succ r ih =>
      intro hr 𝔰 d hd
      rcases Nat.eq_zero_or_pos r with hr0 | hr0
      · subst hr0
        rw [S_one_eq_P F d (by norm_num) 𝔰, sSeq_one]
        exact val_P_iter F h2 d (𝔰 0)
      · obtain ⟨k, rfl⟩ : ∃ k, r = k + 1 := ⟨r - 1, by omega⟩
        have hT : 0 < k + 1 := by omega
        have hrec : S F (k + 2) hr 𝔰 d
            = P F d (𝔰 0) * S_lt F (k + 1) hT (expTail 𝔰) d := by
          rw [S_d_recursion F (k + 2) (by omega) (by omega) (by omega) 𝔰 d]
          congr 2
        rw [hrec, S_lt_eq_sum_levels F (k + 1) hT (expTail 𝔰) d]
        have hkd : k < d := by omega
        have hIHk : Valued.v (S F (k + 1) hT (expTail 𝔰) k)
            = exp (-(sSeq (k + 1) (expTail 𝔰) k)) :=
          ih hT (expTail 𝔰) k (by omega)
        have hdom : Valued.v (∑ i ∈ Finset.range d, S F (k + 1) hT (expTail 𝔰) i)
            = exp (-(sSeq (k + 1) (expTail 𝔰) k)) := by
          refine (Valuation.map_sum_eq_of_lt (v := Valued.v) (j := k)
            (Finset.mem_range.mpr hkd) ?_).trans hIHk
          intro i hi
          rw [Finset.mem_sdiff, Finset.mem_singleton] at hi
          obtain ⟨hir, hik⟩ := hi
          have hid : i < d := Finset.mem_range.mp hir
          rcases lt_trichotomy i k with h | h | h
          · have hzero : S F (k + 1) hT (expTail 𝔰) i = 0 :=
              S_eq_zero_of_lt F hT (expTail 𝔰) (by omega)
            rw [hzero, map_zero, hIHk]
            exact lt_of_lt_of_le (zero_lt_iff.mpr WithZero.exp_ne_zero) le_rfl
          · exact absurd h hik
          · rw [ih hT (expTail 𝔰) i (by omega), hIHk, WithZero.exp_lt_exp]
            have hm : sSeq (k + 1) (expTail 𝔰) k < sSeq (k + 1) (expTail 𝔰) i :=
              sSeq_strictMono (k + 1) hT (expTail 𝔰) h
            omega
        rw [map_mul, hdom, val_P_iter F h2 d (𝔰 0), sSeq_succ, ← WithZero.exp_add]
        congr 1
        ring

end Blocks

section Main

/-- ★★★ **Thakur's Theorem 4 at `q = 2`**: over a field with `Nat.card F = 2`, *every*
multizeta value is nonzero. -/
theorem zeta_ne_zero_q2 (h2 : Nat.card F = 2) {r : ℕ} (hr : 0 < r) (𝔰 : Fin r → ℕ+) :
    ζ_A F 𝔰 ≠ 0 := by
  rw [zeta_eq_tsum_block F hr 𝔰]
  have hmain := val_tsum_eq_of_dominates F (fun n => S F r hr 𝔰 n) (r - 1)
    (WithZero.exp (-(sSeq r 𝔰 (r - 1)))) WithZero.exp_ne_zero
    (val_S_sSeq F h2 r hr 𝔰 (r - 1) le_rfl)
    (summable_S F hr 𝔰) ?_
  · intro hzero
    have h1 : Valued.v (∑' n, S F r hr 𝔰 n) = 0 := by rw [hzero, map_zero]
    rw [hmain] at h1
    exact WithZero.exp_ne_zero h1
  · intro n hn
    rcases lt_trichotomy n (r - 1) with h | h | h
    · have hzero : S F r hr 𝔰 n = 0 := S_eq_zero_of_lt F hr 𝔰 h
      rw [hzero, map_zero]
      exact lt_of_lt_of_le (zero_lt_iff.mpr WithZero.exp_ne_zero) le_rfl
    · exact absurd h hn
    · rw [val_S_sSeq F h2 r hr 𝔰 n (by omega), WithZero.exp_lt_exp]
      have hm : sSeq r 𝔰 (r - 1) < sSeq r 𝔰 n := sSeq_strictMono r hr 𝔰 h
      omega

/-- ★★★ **The exact degree of every MZV over `F₂`**:
`v (ζ_A 𝔰) = exp (−(sExp (r-1) 𝔰₀ + sExp (r-2) 𝔰₁ + ⋯ + sExp 0 𝔰_{r-1}))`. -/
theorem val_zeta_q2 (h2 : Nat.card F = 2) {r : ℕ} (hr : 0 < r) (𝔰 : Fin r → ℕ+) :
    Valued.v (ζ_A F 𝔰) = exp (-(sSeq r 𝔰 (r - 1))) := by
  rw [zeta_eq_tsum_block F hr 𝔰]
  exact val_tsum_eq_of_dominates F (fun n => S F r hr 𝔰 n) (r - 1)
    (WithZero.exp (-(sSeq r 𝔰 (r - 1)))) WithZero.exp_ne_zero
    (val_S_sSeq F h2 r hr 𝔰 (r - 1) le_rfl)
    (summable_S F hr 𝔰)
    (fun n hn => by
      rcases lt_trichotomy n (r - 1) with h | h | h
      · have hzero : S F r hr 𝔰 n = 0 := S_eq_zero_of_lt F hr 𝔰 h
        rw [hzero, map_zero]
        exact lt_of_lt_of_le (zero_lt_iff.mpr WithZero.exp_ne_zero) le_rfl
      · exact absurd h hn
      · rw [val_S_sSeq F h2 r hr 𝔰 n (by omega), WithZero.exp_lt_exp]
        have hm : sSeq r 𝔰 (r - 1) < sSeq r 𝔰 n := sSeq_strictMono r hr 𝔰 h
        omega)

end Main

section CrossCheck

/-- **Consistency with the earlier `StepL199`/`StepL202` results**: for entries `n ≤ q` the exact
exponent `sExp d n` of `val_P_iter` coincides with the closed form `n · Sexp d` of the
power-sum evaluation `val_P_se`. -/
theorem sExp_eq_se (h2 : Nat.card F = 2) (d : ℕ) (n : ℕ+)
    (hn : (n : ℕ) ≤ Nat.card F) :
    sExp d (n : ℕ) = (n : ℤ) * Sexp F d := by
  have h := (val_P_iter F h2 d n).symm.trans (val_P_se F n hn d)
  rw [Se] at h
  rw [WithZero.exp_inj] at h
  linarith

end CrossCheck

section Regression

attribute [local instance 100] Classical.decEq

/-- Over `F₂`, `ζ(1,1) ≠ 0` (Thakur's theorem at depth 2). -/
example : ζ_A (ZMod 2) (fun _ : Fin 2 => (1 : ℕ+)) ≠ 0 :=
  zeta_ne_zero_q2 (ZMod 2) (by simp) (by norm_num) _

/-- Over `F₂`, `ζ(5,3,2) ≠ 0` for arbitrary exponents (not only entries `≤ q`). -/
example : ζ_A (ZMod 2) ![5, 3, 2] ≠ 0 :=
  zeta_ne_zero_q2 (ZMod 2) (by simp) (by norm_num) _

/-- Consistency check at `d = 3`, `n = 1` over `F₂`: `sExp 3 1 = 14 = 1·(2+4+8)`. -/
example : sExp 3 1 = 1 * Sexp (ZMod 2) 3 :=
  sExp_eq_se (ZMod 2) (by simp) 3 1 (by simp)

end Regression

end ZagierHoffmanPositiveChar
