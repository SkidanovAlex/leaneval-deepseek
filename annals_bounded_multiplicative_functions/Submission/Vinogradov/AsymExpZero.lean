/-
Copyright: the formalization team of the Vinogradov mean value theorem project.
-/
import Submission.Vinogradov.LvlFloor
import Submission.Vinogradov.DecLinBridge
import Submission.Vinogradov.Section4Exp

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# GLYZ §4: the `l = 0` brick of the recursion

The recursion (4.4) of GLYZ (arXiv:1912.09798) at split `l = 1` uses the `l = 0` statement
`B_{0,a,b}` on its second factor, whose exponent is `A_0(b) = η(1−b)`.  In our formalisation the
`l = 0` statement is supplied by `DecLinBridge.asymDec_zero_of_decLinScale` (for ANY level pair),
and its exponent is the linear-decoupling exponent at scale `2^{N−⌊bN⌋}`, i.e. `e·(1 − ⌊bN⌋/N)`
for `e ∈ linExpSet k`.  This module proves that the fiat exponent `e(1−b)` also works:

  `e * (1 - b) ∈ AsymExpSet k hk 0 b`  for every `e ∈ linExpSet k`, `0 < b ≤ 1`,

the discrepancy `e(b − ⌊bN⌋/N) ∈ [0, e/N)` being a CONSTANT factor `2^e` in the bound.

The module is imported by `ROADMAP.lean` only; it is not on the comparator chain.
-/

noncomputable section
open MeasureTheory Complex Classical Filter
open scoped Real BigOperators Topology RealInnerProductSpace ENNReal NNReal
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace Submission.Vinogradov

/-- **The `l = 0` brick of the §4 recursion.**  Every exponent `e` of the linear decoupling
gives the `l = 0` element `e(1−b)` of `AsymExpSet k hk 0 b`. -/
theorem mem_asymExpSet_zero_of_linExpSet {k : ℕ} (hk : 1 ≤ k) {e b : ℝ}
    (he : e ∈ linExpSet k) (hb0 : 0 < b) (hb1 : b ≤ 1) :
    e * (1 - b) ∈ AsymExpSet k hk 0 b := by
  obtain ⟨he0, K, hK, hD⟩ := he
  set kc : ℝ := (uncConst k hk).toReal ^ (2 / (pkExp k : ℝ)) with hkc
  have hkc0 : 0 ≤ kc := by rw [hkc]; positivity
  set Kb : ℝ := max 1 (kc * K * 2 ^ e) with hKb
  have hKbpos : 0 < Kb := lt_of_lt_of_le one_pos (le_max_left _ _)
  have hKble : kc * K * 2 ^ e ≤ Kb := le_max_right _ _
  refine ⟨mul_nonneg he0 (by linarith), Kb, hKbpos, 1, fun N hN => ?_⟩
  have hm2le : lvlOf b N ≤ N := lvlOf_le_of_mul_le (by
    have hNR : (0:ℝ) ≤ (N:ℝ) := Nat.cast_nonneg N
    nlinarith [hNR, hb1])
  have hM1 : 1 ≤ 2 ^ (N - lvlOf b N) := Nat.one_le_two_pow
  have hdec := DecLinScale_lam_le (k := k) (M := 2 ^ (N - lvlOf b N)) (by positivity)
    (by norm_num : (0:ℝ) ≤ 1) (by norm_num : (1:ℝ) ≤ 2) (hD _ hM1)
  have hzero := asymDec_zero_of_decLinScale (N := N) (m₁ := lvlOf (asymRatio k 0 * b) N)
    (m₂ := lvlOf b N) hk hm2le hdec
  refine AsymDec_mono ?_ hzero
  -- the constant comparison
  have hcastN : ((N - lvlOf b N : ℕ) : ℝ) = (N : ℝ) - ((lvlOf b N : ℕ) : ℝ) :=
    Nat.cast_sub hm2le
  have hm2le' : ((lvlOf b N : ℕ) : ℝ) ≤ b * (N : ℝ) := Nat.floor_le (by positivity)
  have hbN : b * (N : ℝ) - 1 < ((lvlOf b N : ℕ) : ℝ) := by
    have hlt : b * (N : ℝ) < ((lvlOf b N : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one _
    linarith
  have hexp : ((N - lvlOf b N : ℕ) : ℝ) * e ≤ (N : ℝ) * (e * (1 - b)) + e := by
    have : ((lvlOf b N : ℕ) : ℝ) ≥ b * (N : ℝ) - 1 := hbN.le
    rw [hcastN]
    nlinarith [this, he0]
  have hpow : ((2 : ℝ) ^ (N - lvlOf b N)) ^ e
      ≤ (2 : ℝ) ^ ((N : ℝ) * (e * (1 - b))) * (2 : ℝ) ^ e := by
    rw [← Real.rpow_natCast (2:ℝ) (N - lvlOf b N),
      ← Real.rpow_mul (x := 2) (by norm_num : (0:ℝ) ≤ 2),
      ← Real.rpow_add (x := 2) (by norm_num : (0:ℝ) < 2)
        ((N:ℝ) * (e * (1 - b))) e]
    exact Real.rpow_le_rpow_of_exponent_le (x := 2) (by norm_num) hexp
  have hcast2 : (((2:ℕ) ^ (N - lvlOf b N) : ℕ) : ℝ) = (2:ℝ) ^ (N - lvlOf b N) := by
    push_cast; ring
  have hmain : (uncConst k hk) ^ (2 / (pkExp k : ℝ))
      * ENNReal.ofReal (K * (((2:ℕ) ^ (N - lvlOf b N) : ℕ) : ℝ) ^ e)
      ≤ ENNReal.ofReal (Kb * (2 : ℝ) ^ ((N : ℝ) * (e * (1 - b)))) := by
    rw [hcast2, ← ENNReal.ofReal_toReal (uncConst_ne_top k hk),
      ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg
        (div_nonneg (by norm_num) (le_of_lt (pkExp_pos hk))),
      ← hkc, ← ENNReal.ofReal_mul hkc0]
    refine ENNReal.ofReal_le_ofReal ?_
    have h1 : K * ((2:ℝ) ^ (N - lvlOf b N)) ^ e
        ≤ K * ((2:ℝ) ^ ((N:ℝ) * (e * (1-b))) * (2:ℝ) ^ e) :=
      mul_le_mul_of_nonneg_left hpow hK.le
    have h2 : kc * (K * ((2:ℝ) ^ ((N:ℝ) * (e * (1-b))) * (2:ℝ) ^ e))
        = kc * K * (2:ℝ) ^ e * (2:ℝ) ^ ((N:ℝ) * (e * (1-b))) := by ring
    have h3 : kc * K * (2:ℝ) ^ e * (2:ℝ) ^ ((N:ℝ) * (e * (1-b)))
        ≤ Kb * (2:ℝ) ^ ((N:ℝ) * (e * (1-b))) :=
      mul_le_mul_of_nonneg_right hKble (Real.rpow_nonneg (by norm_num) _)
    have h4 : kc * (K * ((2:ℝ) ^ (N - lvlOf b N)) ^ e)
        ≤ kc * (K * ((2:ℝ) ^ ((N:ℝ) * (e * (1-b))) * (2:ℝ) ^ e)) :=
      mul_le_mul_of_nonneg_left h1 hkc0
    linarith [h4, h2, h3]
  exact hmain

end Submission.Vinogradov
