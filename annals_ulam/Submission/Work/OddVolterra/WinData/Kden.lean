import Mathlib
import Submission.Work.OddVolterra.WinData.Jets

/-!
# Bounds for the Abel denominator `Kden` on a general slope box

`Kden h a σ t = √(krad h σ t a)`, so the radicand bounds of `Jets.lean` transfer: on the box
`A ≤ a, σ ≤ 1`, `|t| ∈ [1/5,2]`, the denominator is bounded below by `kdenKap A = √(kradLo A)`,
differs from the unperturbed denominator by `O(δ)` (also for its `a`-derivative), and its
`a`-derivative is bounded by `kdenC A`.
-/

namespace Work.OddVolterra.WinData

open Work.OddVolterra
open scoped Topology ContDiff Interval

noncomputable section

/-- The lower bound for `Kden`. -/
noncomputable def kdenKap (A : ℝ) : ℝ := Real.sqrt (kradLo A)

lemma kdenKap_pos {A : ℝ} (hA : 0 < A) : 0 < kdenKap A :=
  Real.sqrt_pos.mpr (kradLo_pos hA)

lemma kradLo_le_seven (A : ℝ) : kradLo A ≤ 7 / 50 := by
  have h : min (2 * A / 5) (7 / 50) ≤ 7 / 50 := min_le_right _ _
  have h1 : kradLo A = (19 / 100) * min (2 * A / 5) (7 / 50) := rfl
  rw [h1]
  nlinarith [h]

/-- `1/kdenKap A ≥ 1`. -/
noncomputable def kdenK (A : ℝ) : ℝ := (kdenKap A)⁻¹

/-- The upper constant. -/
noncomputable def kdenC (A : ℝ) : ℝ := 10 ^ 8 * (kdenK A) ^ 6

lemma one_le_kdenK {A : ℝ} (hA : 0 < A) : 1 ≤ kdenK A := by
  rw [kdenK, one_le_inv₀ (kdenKap_pos hA)]
  rw [kdenKap, show (1 : ℝ) = Real.sqrt 1 by simp]
  exact Real.sqrt_le_sqrt (le_trans (kradLo_le_seven A) (by norm_num))

lemma kdenK_pos {A : ℝ} (hA : 0 < A) : 0 < kdenK A := lt_of_lt_of_le one_pos (one_le_kdenK hA)

lemma kdenK_mul_kap {A : ℝ} (hA : 0 < A) : kdenK A * kdenKap A = 1 := by
  rw [kdenK]
  exact inv_mul_cancel₀ (ne_of_gt (kdenKap_pos hA))

lemma kdenC_pos {A : ℝ} (hA : 0 < A) : 0 < kdenC A := by
  rw [kdenC]
  have h1 : 0 < kdenK A := kdenK_pos hA
  positivity

lemma kdenC_ge_pow {A : ℝ} (hA : 0 < A) {c : ℝ} (hc : 0 ≤ c) (hc8 : c ≤ 10 ^ 8)
    {m : ℕ} (hm : 1 ≤ m) (hm6 : m ≤ 6) : c * (kdenK A) ^ m ≤ kdenC A := by
  have hK : 1 ≤ kdenK A := one_le_kdenK hA
  have hle : (kdenK A) ^ m ≤ (kdenK A) ^ 6 := pow_le_pow_right₀ hK hm6
  calc c * (kdenK A) ^ m ≤ 10 ^ 8 * (kdenK A) ^ 6 :=
        mul_le_mul hc8 hle (by positivity) (by norm_num)
    _ = kdenC A := by rw [kdenC]

/-
**The remaining goal of this module** (not yet proved; stated here for the record):

```
theorem Kden_jets {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hsupp : Function.support h ⊆ Set.Icc (1 - 2 * tau) (1 - tau))
    {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 100)
    (hjet : ∀ k : ℕ, k ≤ 2 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ δ)
    {A a σ t : ℝ} (hA : 0 < A) (ha : A ≤ a) (hσ : A ≤ σ) (hσ1 : σ ≤ 1) (ha1 : a ≤ 1)
    (ht : 1 / 5 ≤ |t|) (ht2 : |t| ≤ 2) :
    kdenKap A ≤ Kden h a σ t ∧ kdenKap A ≤ Kden 0 a σ t ∧
    |Kden h a σ t - Kden 0 a σ t| ≤ kdenC A * δ ∧
    |deriv (fun a' : ℝ => Kden h a' σ t) a| ≤ kdenC A ∧
    |deriv (fun a' : ℝ => Kden 0 a' σ t) a| ≤ kdenC A ∧
    |deriv (fun a' : ℝ => Kden h a' σ t) a - deriv (fun a' : ℝ => Kden 0 a' σ t) a|
      ≤ kdenC A * δ
```

Every ingredient is available: `krad_jets` (`Jets.lean`) for the radicand data, `Kden_eq_sqrt_krad`,
the algebraic identity `√x - √y = (x - y)/(√x + √y)` and
`HasDerivAt.sqrt` for the derivative.  The lower/upper constants `kdenKap`, `kdenK`, `kdenC` and
the comparison lemmas `kdenC_ge_pow`, `kdenK_mul_kap` are proved above.
-/

end

end Work.OddVolterra.WinData
