import Mathlib
import Submission.Work.KMTPlan.A6.MdlWeightVarBound

namespace Work.KMTPlan.A6

/-- **Masking a monotone scale sequence.**  If `N : ℕ → ℕ` is monotone and a family of weights
`x` is variation-bounded on every tail of `N` (uniformly, in the form `x (· + n₀)`), then the whole
masked family `n ↦ if B ≤ N n then x n else 0` is variation-bounded as well: the mask is an
upward-closed tail of `N`, so it is a prepending of zeros, which costs exactly the factor `3` of
`variationalNorm_prependZeros_le`. -/
private lemma mask_le_of_tail {r : NNReal} (hr : 1 ≤ r) {B : ℕ} {N : ℕ → ℕ} (hNmono : Monotone N)
    (x : ℕ → ℂ) {C : ℝ}
    (hb : ∀ n₀, B ≤ N n₀ →
      PointwiseErgodicTheorems.variationalNorm r (fun m => x (m + n₀)) ≤ ENNReal.ofReal C) :
    PointwiseErgodicTheorems.variationalNorm r (fun n => if B ≤ N n then x n else 0)
      ≤ ENNReal.ofReal (3 * C) := by
  by_cases hex : ∃ n, B ≤ N n
  · set n₀ : ℕ := Nat.find hex with hn₀def
    have hspec : B ≤ N n₀ := Nat.find_spec hex
    have hp : ∀ n, (B ≤ N n) ↔ n₀ ≤ n := by
      intro n
      exact ⟨fun h => Nat.find_min' hex h, fun h => le_trans hspec (hNmono h)⟩
    exact masked_le_tail hr n₀ hp x (hb n₀ hspec)
  · have hhex : ∀ n, ¬ (B ≤ N n) := fun n h => hex ⟨n, h⟩
    have hzero : (fun n : ℕ => if B ≤ N n then x n else 0) = (0 : ℕ → ℂ) := by
      funext n
      exact if_neg (hhex n)
    rw [hzero, variationalNorm_zero_nat hr]
    exact bot_le

theorem lowWeightMaskBound (P : Polynomial ℤ) (hdeg : 1 ≤ P.natDegree) (r : NNReal) (hr : 1 ≤ r) :
    ∃ B : ℕ, 0 < B ∧ ∃ C : ℝ, 0 < C ∧
      ∀ (N : ℕ → ℕ) (t : ℝ), Monotone N → t ∈ Set.Icc (1 / 2 : ℝ) 1 →
        PointwiseErgodicTheorems.variationalNorm r
            (fun n : ℕ => if B ≤ N n then Work.KMTPlan.A6.mdlW1 P (N n) t else 0)
          ≤ ENNReal.ofReal C ∧
        PointwiseErgodicTheorems.variationalNorm r
            (fun n : ℕ => if B ≤ N n then Work.KMTPlan.A6.mdlW2 P (N n) t else 0)
          ≤ ENNReal.ofReal C ∧
        PointwiseErgodicTheorems.variationalNorm r
            (fun n : ℕ => if B ≤ N n then Work.KMTPlan.A6.mdlW3 P (N n) t else 0)
          ≤ ENNReal.ofReal C := by
  obtain ⟨B, hBpos, C, hCpos, hbound⟩ := MdlWeightMonoBoundSelf P hdeg r hr
  refine ⟨B, hBpos, 3 * C, mul_pos (by norm_num) hCpos, ?_⟩
  intro N t hNmono ht
  have htail : ∀ n₀, B ≤ N n₀ →
      (PointwiseErgodicTheorems.variationalNorm r (fun m => mdlW1 P (N (m + n₀)) t)
          ≤ ENNReal.ofReal C ∧
        PointwiseErgodicTheorems.variationalNorm r (fun m => mdlW2 P (N (m + n₀)) t)
          ≤ ENNReal.ofReal C ∧
        PointwiseErgodicTheorems.variationalNorm r (fun m => mdlW3 P (N (m + n₀)) t)
          ≤ ENNReal.ofReal C) := by
    intro n₀ hn₀
    exact hbound (fun m => N (m + n₀)) t
      (fun a b hab => hNmono (Nat.add_le_add_right hab n₀))
      (fun m => le_trans hn₀ (hNmono (Nat.le_add_left n₀ m))) ht
  refine ⟨mask_le_of_tail hr hNmono _ (fun n₀ hn₀ => (htail n₀ hn₀).1),
    mask_le_of_tail hr hNmono _ (fun n₀ hn₀ => (htail n₀ hn₀).2.1),
    mask_le_of_tail hr hNmono _ (fun n₀ hn₀ => (htail n₀ hn₀).2.2)⟩

end Work.KMTPlan.A6
