import Submission.ZagierHoffmanProof.PrimeVal
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
# Thakur's theorem "multizeta values do not vanish" over prime fields

Using `val_P_iter_prime` (the exact degree of every power sum over a finite field of prime
cardinality) we compute the degree of every multizeta block and deduce that no multizeta value
over a prime field vanishes — Thakur's Theorem 4 for prime `q`.
-/

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

section Monotone

/-- `sExpG F d k = ∑_{i<d} T^{i+1}(k)` is strictly increasing in `d`. -/
lemma sExpG_lt_succ (d k : ℕ) : sExpG F d k < sExpG F (d + 1) k := by
  unfold sExpG
  rw [Finset.sum_range_succ]
  have hpos : 0 < Nat.iterate (TT (Nat.card F) (two_le_card F)) (d + 1) k := by
    induction d with
    | zero => rw [Function.iterate_one]; exact TT_pos' (two_le_card F) k
    | succ d ih =>
        rw [show d + 1 + 1 = (d + 1) + 1 from rfl, Function.iterate_succ_apply']
        exact TT_pos' (two_le_card F) _
  have : (0 : ℤ) < ((Nat.iterate (TT (Nat.card F) (two_le_card F)) (d + 1) k : ℕ) : ℤ) := by
    exact_mod_cast hpos
  linarith

/-- `sExpG F · k` is strictly monotone in the level. -/
lemma sExpG_strictMono (k : ℕ) : StrictMono (fun d => sExpG F d k) :=
  strictMono_nat_of_lt_succ fun d => sExpG_lt_succ F d k

/-- **The degree jump** for prime `q`. -/
theorem val_P_lt_succ_prime (hp : (Nat.card F).Prime) (d : ℕ) (k : ℕ+) :
    Valued.v (P F (d + 1) k) < Valued.v (P F d k) := by
  rw [val_P_iter_prime F hp (d + 1) k, val_P_iter_prime F hp d k, WithZero.exp_lt_exp]
  have := sExpG_lt_succ F d (k : ℕ)
  linarith

end Monotone

section Seq

/-- The exponent of the depth-`r` block `S_d(𝔰)`. -/
noncomputable def sSeqG : (r : ℕ) → (Fin r → ℕ+) → ℕ → ℤ
  | 0, _, _ => 0
  | 1, 𝔰, d => sExpG F d (𝔰 0)
  | (r + 2), 𝔰, d => sExpG F d (𝔰 0) + sSeqG (r + 1) (expTail 𝔰) r

lemma sSeqG_one (𝔰 : Fin 1 → ℕ+) (d : ℕ) : sSeqG F 1 𝔰 d = sExpG F d (𝔰 0) := by
  rw [sSeqG]

lemma sSeqG_succ (r : ℕ) (𝔰 : Fin (r + 2) → ℕ+) (d : ℕ) :
    sSeqG F (r + 2) 𝔰 d = sExpG F d (𝔰 0) + sSeqG F (r + 1) (expTail 𝔰) r := by
  rw [sSeqG]

/-- `sSeqG F r 𝔰` is strictly increasing in the level `d`. -/
lemma sSeqG_strictMono : ∀ (r : ℕ) (hr : 0 < r) (𝔰 : Fin r → ℕ+),
    StrictMono (fun d => sSeqG F r 𝔰 d) := by
  intro r
  induction r with
  | zero => intro hr; exact absurd hr (by omega)
  | succ r ih =>
      intro hr 𝔰
      rcases Nat.eq_zero_or_pos r with hr0 | hr0
      · subst hr0
        intro a b hab
        show sSeqG F 1 𝔰 a < sSeqG F 1 𝔰 b
        rw [sSeqG_one, sSeqG_one]
        exact sExpG_strictMono F (𝔰 0) hab
      · obtain ⟨k, rfl⟩ : ∃ k, r = k + 1 := ⟨r - 1, by omega⟩
        intro a b hab
        show sSeqG F (k + 2) 𝔰 a < sSeqG F (k + 2) 𝔰 b
        rw [sSeqG_succ F k 𝔰 a, sSeqG_succ F k 𝔰 b]
        have h1 : sExpG F a (𝔰 0) < sExpG F b (𝔰 0) := sExpG_strictMono F (𝔰 0) hab
        linarith

end Seq

section Blocks

/-- ★★ The exact valuation of every multizeta block over a prime field. -/
theorem val_S_sSeqG (hp : (Nat.card F).Prime) :
    ∀ (r : ℕ) (hr : 0 < r) (𝔰 : Fin r → ℕ+) (d : ℕ),
      r - 1 ≤ d → Valued.v (S F r hr 𝔰 d) = exp (-(sSeqG F r 𝔰 d)) := by
  intro r
  induction r with
  | zero => intro hr; exact absurd hr (by omega)
  | succ r ih =>
      intro hr 𝔰 d hd
      rcases Nat.eq_zero_or_pos r with hr0 | hr0
      · subst hr0
        rw [S_one_eq_P F d (by norm_num) 𝔰, sSeqG_one]
        exact val_P_iter_prime F hp d (𝔰 0)
      · obtain ⟨k, rfl⟩ : ∃ k, r = k + 1 := ⟨r - 1, by omega⟩
        have hT : 0 < k + 1 := by omega
        have hrec : S F (k + 2) hr 𝔰 d
            = P F d (𝔰 0) * S_lt F (k + 1) hT (expTail 𝔰) d := by
          rw [S_d_recursion F (k + 2) (by omega) (by omega) (by omega) 𝔰 d]
          congr 2
        rw [hrec, S_lt_eq_sum_levels F (k + 1) hT (expTail 𝔰) d]
        have hkd : k < d := by omega
        have hIHk : Valued.v (S F (k + 1) hT (expTail 𝔰) k)
            = exp (-(sSeqG F (k + 1) (expTail 𝔰) k)) :=
          ih hT (expTail 𝔰) k (by omega)
        have hdom : Valued.v (∑ i ∈ Finset.range d, S F (k + 1) hT (expTail 𝔰) i)
            = exp (-(sSeqG F (k + 1) (expTail 𝔰) k)) := by
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
            have hm : sSeqG F (k + 1) (expTail 𝔰) k < sSeqG F (k + 1) (expTail 𝔰) i :=
              sSeqG_strictMono F (k + 1) hT (expTail 𝔰) h
            omega
        rw [map_mul, hdom, val_P_iter_prime F hp d (𝔰 0), sSeqG_succ, ← WithZero.exp_add]
        congr 1
        ring

end Blocks

section Main

/-- ★★★ **Thakur's Theorem 4 for prime `q`**: over a finite field of prime cardinality,
*every* multizeta value is nonzero. -/
theorem zeta_ne_zero_prime (hp : (Nat.card F).Prime) {r : ℕ} (hr : 0 < r) (𝔰 : Fin r → ℕ+) :
    ζ_A F 𝔰 ≠ 0 := by
  rw [zeta_eq_tsum_block F hr 𝔰]
  have hmain := val_tsum_eq_of_dominates F (fun n => S F r hr 𝔰 n) (r - 1)
    (WithZero.exp (-(sSeqG F r 𝔰 (r - 1)))) WithZero.exp_ne_zero
    (val_S_sSeqG F hp r hr 𝔰 (r - 1) le_rfl)
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
    · rw [val_S_sSeqG F hp r hr 𝔰 n (by omega), WithZero.exp_lt_exp]
      have hm : sSeqG F r 𝔰 (r - 1) < sSeqG F r 𝔰 n := sSeqG_strictMono F r hr 𝔰 h
      omega

/-- ★★★ **The exact degree of every MZV over a prime field.** -/
theorem val_zeta_prime (hp : (Nat.card F).Prime) {r : ℕ} (hr : 0 < r) (𝔰 : Fin r → ℕ+) :
    Valued.v (ζ_A F 𝔰) = exp (-(sSeqG F r 𝔰 (r - 1))) := by
  rw [zeta_eq_tsum_block F hr 𝔰]
  exact val_tsum_eq_of_dominates F (fun n => S F r hr 𝔰 n) (r - 1)
    (WithZero.exp (-(sSeqG F r 𝔰 (r - 1)))) WithZero.exp_ne_zero
    (val_S_sSeqG F hp r hr 𝔰 (r - 1) le_rfl)
    (summable_S F hr 𝔰)
    (fun n hn => by
      rcases lt_trichotomy n (r - 1) with h | h | h
      · have hzero : S F r hr 𝔰 n = 0 := S_eq_zero_of_lt F hr 𝔰 h
        rw [hzero, map_zero]
        exact lt_of_lt_of_le (zero_lt_iff.mpr WithZero.exp_ne_zero) le_rfl
      · exact absurd h hn
      · rw [val_S_sSeqG F hp r hr 𝔰 n (by omega), WithZero.exp_lt_exp]
        have hm : sSeqG F r 𝔰 (r - 1) < sSeqG F r 𝔰 n := sSeqG_strictMono F r hr 𝔰 h
        omega)

end Main

section Regression

attribute [local instance 100] Classical.decEq

/-- Over `F₂`, `ζ(5,3,2) ≠ 0` — Thakur's theorem at `q = 2` via the prime-`q` proof. -/
example : ζ_A (ZMod 2) ![5, 3, 2] ≠ 0 :=
  zeta_ne_zero_prime (ZMod 2) (by norm_num) (by norm_num) _

/-- Over `F₃`, `ζ(1,1) ≠ 0`. -/
example : ζ_A (ZMod 3) (fun _ : Fin 2 => (1 : ℕ+)) ≠ 0 :=
  zeta_ne_zero_prime (ZMod 3) (by norm_num) (by norm_num) _

/-- The degree jump over `F₃`: `v (P_2 1) < v (P_1 1)`. -/
example : Valued.v (P (ZMod 3) 2 1) < Valued.v (P (ZMod 3) 1 1) :=
  val_P_lt_succ_prime (ZMod 3) (by norm_num) 1 1

end Regression

end ZagierHoffmanPositiveChar
