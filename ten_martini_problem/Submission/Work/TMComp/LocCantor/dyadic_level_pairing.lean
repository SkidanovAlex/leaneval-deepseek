import Mathlib
import Submission.Work.TMC7Core.Scale.prop9_aux

/-!
# The scale-selection pigeonhole of the Bourgain--Jitomirskaya chain

An abstract formulation of the "existence of a good scale" step of [BJ] Proposition 9
(the step that in the paper is the sentence *"Since `100κ < L(E) ≤ L_{2N} ≤ L_N < C` for any
`N`, we may choose `N₀` with `L_{2N₀} > (9/10)L_{N₀}` and `Cκ⁻²q < N₀ < κ^{-C}q`"*).

Along a dyadic chain `t, 2t, 4t, …`, if the "pairing" `L_{2m} > (9/10)L_m` failed at every one
of `J` successive doublings, then the level would decay geometrically and could not still exceed
`100κ` after `J` steps once `J` exceeds `log(K/(100κ))/log(10/9)`, where `K` bounds the level
from above.  Hence, in a window of more than that many doublings, some scale carries the
pairing. -/
namespace Work.TMComp.LocCantor

/-- The dyadic pigeonhole behind the "good scale" selection: provably, some doubling in a
long enough dyadic chain satisfies the pairing inequality. -/
theorem dyadic_level_pairing (L : ℕ → ℝ) (t J : ℕ) (K κ : ℝ) (hκ : 0 < κ) (ht : 1 ≤ t)
    (hmono : ∀ m : ℕ, 1 ≤ m → L (2 * m) ≤ L m) (hup : ∀ m : ℕ, L m ≤ K)
    (htop : 100 * κ < L (t * 2 ^ J))
    (hJ : Real.log (K / (100 * κ)) / Real.log (10 / 9) < (J : ℝ)) :
    ∃ j : ℕ, j < J ∧ (9 / 10) * L (t * 2 ^ j) < L (t * 2 ^ (j + 1)) := by
  classical
  by_contra h
  push_neg at h
  have one_le : ∀ i : ℕ, 1 ≤ t * 2 ^ i := by
    intro i
    exact Nat.one_le_iff_ne_zero.mpr (by positivity)
  -- iterate the failing pairing along the dyadic chain
  have key : ∀ j : ℕ, j ≤ J → L (t * 2 ^ j) ≤ (9 / 10 : ℝ) ^ j * L t := by
    intro j hj
    induction j with
    | zero => simp
    | succ i ih =>
      have hi : i < J := by omega
      have hstep := h i hi
      have hprev := ih (by omega)
      have hrew : t * 2 ^ (i + 1) = 2 * (t * 2 ^ i) := by ring
      calc L (t * 2 ^ (i + 1)) ≤ (9 / 10) * L (t * 2 ^ i) := hstep
        _ ≤ (9 / 10) * ((9 / 10) ^ i * L t) :=
            mul_le_mul_of_nonneg_left hprev (by norm_num)
        _ = (9 / 10) ^ (i + 1) * L t := by ring
  have hchain : L (t * 2 ^ J) ≤ (9 / 10 : ℝ) ^ J * L t := key J le_rfl
  have hKpos : 0 < K := lt_trans (by linarith) (lt_of_lt_of_le htop (hup (t * 2 ^ J)))
  have hlt : 100 * κ < (9 / 10 : ℝ) ^ J * K := by
    have h2 : (9 / 10 : ℝ) ^ J * L t ≤ (9 / 10 : ℝ) ^ J * K :=
      mul_le_mul_of_nonneg_left (hup t) (by positivity)
    linarith
  -- take logarithms:  J * log (10/9) < log (K/(100κ))
  have hlog : (J : ℝ) * Real.log (10 / 9) < Real.log (K / (100 * κ)) := by
    have hlog1 : Real.log (100 * κ) < Real.log ((9 / 10 : ℝ) ^ J * K) :=
      Real.log_lt_log (by linarith) hlt
    rw [Real.log_mul (by positivity) (ne_of_gt hKpos), Real.log_pow] at hlog1
    have hlog9 : Real.log (9 / 10) = -Real.log (10 / 9) := by
      rw [show (9 / 10 : ℝ) = (10 / 9)⁻¹ by norm_num, Real.log_inv]
    rw [hlog9] at hlog1
    have hdiv : Real.log (K / (100 * κ)) = Real.log K - Real.log (100 * κ) :=
      Real.log_div (ne_of_gt hKpos) (by linarith)
    rw [hdiv]
    nlinarith [hlog1]
  have hlogpos : 0 < Real.log (10 / 9) := Real.log_pos (by norm_num)
  have hdiv2 := (div_lt_iff₀ hlogpos).mp hJ
  linarith [hdiv2, hlog]

/-- Monotonicity of a level sequence along dyadic multiples: the levels are non-increasing up
the dyadic chain. -/
theorem level_dyadic_iter (L : ℕ → ℝ) (t J i : ℕ) (ht : 1 ≤ t)
    (hmono : ∀ m : ℕ, 1 ≤ m → L (2 * m) ≤ L m) (hi : i ≤ J) :
    L (t * 2 ^ J) ≤ L (t * 2 ^ i) := by
  have hle1 : ∀ e : ℕ, 1 ≤ t * 2 ^ e := by
    intro e
    have h2 : (1 : ℕ) ≤ 2 ^ e := Nat.one_le_iff_ne_zero.mpr (ne_of_gt (pow_pos (by norm_num) e))
    calc (1 : ℕ) = 1 * 1 := by ring
      _ ≤ t * 2 ^ e := Nat.mul_le_mul ht h2
  have hiter : ∀ e : ℕ, L (t * 2 ^ (e + 1)) ≤ L (t * 2 ^ e) := by
    intro e
    have h := hmono (t * 2 ^ e) (hle1 e)
    have he : 2 * (t * 2 ^ e) = t * 2 ^ (e + 1) := by rw [pow_succ]; ring
    rwa [he] at h
  have hchain : ∀ d i : ℕ, i + d = J → L (t * 2 ^ J) ≤ L (t * 2 ^ i) := by
    intro d
    induction d with
    | zero =>
      intro i hi
      have h : i = J := by omega
      rw [h]
    | succ d ih =>
      intro i hi
      have h1 : L (t * 2 ^ (i + 1)) ≤ L (t * 2 ^ i) := hiter i
      have h2 : L (t * 2 ^ J) ≤ L (t * 2 ^ (i + 1)) := ih (i + 1) (by omega)
      linarith
  exact hchain (J - i) i (Nat.add_sub_of_le hi)

/-- **The usable form of the pigeonhole.**  If the level is `> 100κ` at the top `t·2^J` of a
dyadic chain and the chain is longer than `log(K/(100κ))/log(10/9)` doublings (`K` bounding the
level from above), then some scale `N₀ ∈ [t, t·2^J]` of the chain carries *both* the level
`> 100κ` (the levels are non-increasing along the chain, so the top's level propagates down) and
the pairing `(9/10)L_{N₀} < L_{2N₀}`.  This is the "existence of a good scale" step of [BJ]
Proposition 9, in the form in which the scale chain consumes it. -/
theorem paired_scale_at_dyadic_top (L : ℕ → ℝ) (t J : ℕ) (K κ : ℝ) (hκ : 0 < κ) (ht : 1 ≤ t)
    (hmono : ∀ m : ℕ, 1 ≤ m → L (2 * m) ≤ L m) (hup : ∀ m : ℕ, L m ≤ K)
    (hlevel : 100 * κ < L (t * 2 ^ J))
    (hwin : Real.log (K / (100 * κ)) / Real.log (10 / 9) < (J : ℝ)) :
    ∃ N₀ : ℕ, t ≤ N₀ ∧ N₀ ≤ t * 2 ^ J ∧ 100 * κ < L N₀ ∧ (9 / 10) * L N₀ < L (2 * N₀) := by
  obtain ⟨j, hjJ, hjpair⟩ := dyadic_level_pairing L t J K κ hκ ht hmono hup hlevel hwin
  rw [show t * 2 ^ (j + 1) = 2 * (t * 2 ^ j) by rw [pow_succ]; ring] at hjpair
  refine ⟨t * 2 ^ j, ?_, ?_, ?_, hjpair⟩
  · show t ≤ t * 2 ^ j
    have h1 : (1 : ℕ) ≤ 2 ^ j := Nat.one_le_iff_ne_zero.mpr (ne_of_gt (pow_pos (by norm_num) j))
    calc t = t * 1 := (Nat.mul_one t).symm
      _ ≤ t * 2 ^ j := Nat.mul_le_mul_left t h1
  · show t * 2 ^ j ≤ t * 2 ^ J
    have hpow : t * 2 ^ J = t * 2 ^ j * 2 ^ (J - j) := by
      rw [Nat.mul_assoc, ← pow_add, Nat.add_sub_of_le (le_of_lt hjJ)]
    rw [hpow]
    have h1 : (1 : ℕ) ≤ 2 ^ (J - j) :=
      Nat.one_le_iff_ne_zero.mpr (ne_of_gt (pow_pos (by norm_num) (J - j)))
    simpa using Nat.mul_le_mul_left (t * 2 ^ j) h1
  · show 100 * κ < L (t * 2 ^ j)
    have h := level_dyadic_iter L t J j ht hmono (le_of_lt hjJ)
    linarith

end Work.TMComp.LocCantor
