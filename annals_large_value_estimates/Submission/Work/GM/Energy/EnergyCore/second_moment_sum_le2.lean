import Mathlib
import Submission.Work.GM.Energy.EnergyCore.Setup2

/-!
# GM Lemma 11.5 summed over all gcd-scales `d ∈ [A,2N]`

We apply the discrete second moment bound (`h2`) at scale `M = ⌈N/d⌉` for every
`d ∈ [A, 2N]` and sum the resulting inequalities.  The two elementary sums
`Σ_{d∈[A,2N]} ⌈N/d⌉` (`hS1`) and `Σ_{d∈[A,2N]} ⌈N/d⌉²` (`hS2`) control the two
"main" terms, and the constants `4 ≤ 20`, `20 ≤ 20` give the stated shape.
-/

namespace Work.GM.Energy.EnergyCore

open Finset
open scoped BigOperators

/-- GM Lemma 11.5 summed over all gcd-scales `d ∈ [A,2N]`: applying the discrete second moment
bound at scale `M = ⌈N/d⌉` for every `d` and using `Σ ⌈N/d⌉ ≤ 4N(1+log2N)`, `Σ ⌈N/d⌉² ≤ 20N^{6/5}`. -/
theorem second_moment_sum_le (ε C₂ : ℝ) (hC₂ : 0 < C₂)
    (h2 : ∀ (M : ℕ), 1 ≤ M → ∀ (T : ℝ), 1 ≤ T → ∀ (W : Finset ℝ),
      (∀ t ∈ W, t ∈ Set.Icc 0 T) → Submission.GM.Separated W 1 →
      (∑ n1 ∈ Finset.Icc M (2 * M), ∑ n2 ∈ Finset.Icc M (2 * M),
          ‖Submission.GM.Rfun W ((n1 : ℝ) / (n2 : ℝ))‖ ^ 2)
        ≤ C₂ * T ^ ε * ((W.card : ℝ) ^ 2 * (M : ℝ) + (W.card : ℝ) * (M : ℝ) ^ 2
            + (W.card : ℝ) ^ ((5 : ℝ) / 4) * T ^ ((1 : ℝ) / 2) * (M : ℝ)))
    (N A : ℕ) (hN : 1 ≤ N) (hA : 1 ≤ A)
    (W : Finset ℝ) (hW : ∀ t ∈ W, t ∈ Set.Icc 0 (Submission.LargeValues.M N))
    (hsep : Submission.GM.Separated W 1)
    (hS1 : (∑ d ∈ Finset.Icc A (2 * N), (Work.GM.Energy.EnergyCore.Md N d : ℝ))
        ≤ 4 * (N : ℝ) * (1 + Real.log (2 * N)))
    (hS2 : (∑ d ∈ Finset.Icc A (2 * N), (Work.GM.Energy.EnergyCore.Md N d : ℝ) ^ 2)
        ≤ 20 * Submission.LargeValues.M N) :
    (∑ d ∈ Finset.Icc A (2 * N),
      ∑ n1 ∈ Finset.Icc (Work.GM.Energy.EnergyCore.Md N d) (2 * Work.GM.Energy.EnergyCore.Md N d),
        ∑ n2 ∈ Finset.Icc (Work.GM.Energy.EnergyCore.Md N d) (2 * Work.GM.Energy.EnergyCore.Md N d),
          ‖Submission.GM.Rfun W ((n1 : ℝ) / (n2 : ℝ))‖ ^ 2)
    ≤ (20 * C₂ * (Submission.LargeValues.M N) ^ ε) *
        ((W.card : ℝ) ^ 2 * ((N : ℝ) * (1 + Real.log (2 * (N : ℝ))))
          + (W.card : ℝ) * Submission.LargeValues.M N
          + (W.card : ℝ) ^ ((5 : ℝ) / 4) * (Submission.LargeValues.M N) ^ ((1 : ℝ) / 2)
              * ((N : ℝ) * (1 + Real.log (2 * (N : ℝ))))) := by
  classical
  set P : ℝ := Submission.LargeValues.M N with hPdef
  set w : ℝ := (W.card : ℝ) with hwdef
  set Q : ℝ := (N : ℝ) * (1 + Real.log (2 * (N : ℝ))) with hQdef
  set S : Finset ℕ := Finset.Icc A (2 * N) with hSdef
  set T1 : ℝ := ∑ d ∈ S, (Work.GM.Energy.EnergyCore.Md N d : ℝ) with hT1def
  set T2 : ℝ := ∑ d ∈ S, (Work.GM.Energy.EnergyCore.Md N d : ℝ) ^ 2 with hT2def
  have hP1 : 1 ≤ P := by rw [hPdef]; exact Work.GM.Energy.EnergyCore.one_le_MN hN
  have hPpos : 0 < P := lt_of_lt_of_le zero_lt_one hP1
  have hPeps : 0 ≤ P ^ ε := Real.rpow_nonneg hPpos.le ε
  have hPhalf : 0 ≤ P ^ ((1 : ℝ) / 2) := Real.rpow_nonneg hPpos.le _
  have hw0 : 0 ≤ w := by rw [hwdef]; positivity
  have hw2 : 0 ≤ w ^ 2 := by positivity
  have hw54 : 0 ≤ w ^ ((5 : ℝ) / 4) := Real.rpow_nonneg hw0 _
  have hQ0 : 0 ≤ Q := by
    have h2N : (1 : ℝ) ≤ 2 * (N : ℝ) := by
      have : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
      linarith
    have hlog : 0 ≤ Real.log (2 * (N : ℝ)) := Real.log_nonneg h2N
    have hN0 : (0 : ℝ) ≤ (N : ℝ) := by positivity
    rw [hQdef]
    nlinarith
  have hS1' : T1 ≤ 4 * Q := by
    rw [hT1def, hSdef, hQdef]
    have h := hS1
    rw [show (4:ℝ) * (N:ℝ) * (1 + Real.log (2 * N)) =
        4 * ((N:ℝ) * (1 + Real.log (2 * (N:ℝ)))) from by ring] at h
    exact h
  have hS2' : T2 ≤ 20 * P := by
    rw [hT2def, hSdef, hPdef]
    exact hS2
  have hterm : ∀ d ∈ S,
      (∑ n1 ∈ Finset.Icc (Work.GM.Energy.EnergyCore.Md N d) (2 * Work.GM.Energy.EnergyCore.Md N d),
        ∑ n2 ∈ Finset.Icc (Work.GM.Energy.EnergyCore.Md N d) (2 * Work.GM.Energy.EnergyCore.Md N d),
          ‖Submission.GM.Rfun W ((n1 : ℝ) / (n2 : ℝ))‖ ^ 2)
      ≤ C₂ * P ^ ε * (w ^ 2 * (Work.GM.Energy.EnergyCore.Md N d : ℝ)
          + w * (Work.GM.Energy.EnergyCore.Md N d : ℝ) ^ 2
          + w ^ ((5:ℝ)/4) * P ^ ((1:ℝ)/2) * (Work.GM.Energy.EnergyCore.Md N d : ℝ)) := by
    intro d hd
    rw [hSdef] at hd
    have hd1 : 1 ≤ d := by
      have := (Finset.mem_Icc.mp hd).1
      omega
    have hb := h2 (Work.GM.Energy.EnergyCore.Md N d) (Work.GM.Energy.EnergyCore.Md_pos hN hd1)
      P hP1 W hW hsep
    exact hb
  have hsum_le : (∑ d ∈ S,
      ∑ n1 ∈ Finset.Icc (Work.GM.Energy.EnergyCore.Md N d) (2 * Work.GM.Energy.EnergyCore.Md N d),
        ∑ n2 ∈ Finset.Icc (Work.GM.Energy.EnergyCore.Md N d) (2 * Work.GM.Energy.EnergyCore.Md N d),
          ‖Submission.GM.Rfun W ((n1 : ℝ) / (n2 : ℝ))‖ ^ 2)
      ≤ ∑ d ∈ S, C₂ * P ^ ε * (w ^ 2 * (Work.GM.Energy.EnergyCore.Md N d : ℝ)
          + w * (Work.GM.Energy.EnergyCore.Md N d : ℝ) ^ 2
          + w ^ ((5:ℝ)/4) * P ^ ((1:ℝ)/2) * (Work.GM.Energy.EnergyCore.Md N d : ℝ)) :=
    Finset.sum_le_sum hterm
  have hfactor : (∑ d ∈ S, C₂ * P ^ ε * (w ^ 2 * (Work.GM.Energy.EnergyCore.Md N d : ℝ)
        + w * (Work.GM.Energy.EnergyCore.Md N d : ℝ) ^ 2
        + w ^ ((5:ℝ)/4) * P ^ ((1:ℝ)/2) * (Work.GM.Energy.EnergyCore.Md N d : ℝ)))
      = C₂ * P ^ ε * (w ^ 2 * T1 + w * T2 + w ^ ((5:ℝ)/4) * P ^ ((1:ℝ)/2) * T1) := by
    rw [hT1def, hT2def]
    rw [← Finset.mul_sum]
    congr 1
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    rw [← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
  have hX : w ^ 2 * T1 + w * T2 + w ^ ((5:ℝ)/4) * P ^ ((1:ℝ)/2) * T1
      ≤ w ^ 2 * (4 * Q) + w * (20 * P) + w ^ ((5:ℝ)/4) * P ^ ((1:ℝ)/2) * (4 * Q) := by
    have h1 := mul_le_mul_of_nonneg_left hS1' hw2
    have h2' := mul_le_mul_of_nonneg_left hS2' hw0
    have h3 := mul_le_mul_of_nonneg_left hS1' (mul_nonneg hw54 hPhalf)
    nlinarith [h1, h2', h3]
  have hY : w ^ 2 * (4 * Q) + w * (20 * P) + w ^ ((5:ℝ)/4) * P ^ ((1:ℝ)/2) * (4 * Q)
      ≤ 20 * (w ^ 2 * Q + w * P + w ^ ((5:ℝ)/4) * P ^ ((1:ℝ)/2) * Q) := by
    have h1 : (0:ℝ) ≤ w ^ 2 * Q := mul_nonneg hw2 hQ0
    have h2' : (0:ℝ) ≤ w * P := mul_nonneg hw0 hPpos.le
    have h3 : (0:ℝ) ≤ w ^ ((5:ℝ)/4) * P ^ ((1:ℝ)/2) * Q :=
      mul_nonneg (mul_nonneg hw54 hPhalf) hQ0
    nlinarith [h1, h2', h3]
  have hmain : C₂ * P ^ ε * (w ^ 2 * T1 + w * T2 + w ^ ((5:ℝ)/4) * P ^ ((1:ℝ)/2) * T1)
      ≤ (20 * C₂ * P ^ ε) * (w ^ 2 * Q + w * P + w ^ ((5:ℝ)/4) * P ^ ((1:ℝ)/2) * Q) := by
    have hA := mul_le_mul_of_nonneg_left hX (mul_nonneg hC₂.le hPeps)
    have hB := mul_le_mul_of_nonneg_left hY (mul_nonneg hC₂.le hPeps)
    have heq : C₂ * P ^ ε * (20 * (w ^ 2 * Q + w * P + w ^ ((5:ℝ)/4) * P ^ ((1:ℝ)/2) * Q))
        = (20 * C₂ * P ^ ε) * (w ^ 2 * Q + w * P + w ^ ((5:ℝ)/4) * P ^ ((1:ℝ)/2) * Q) := by
      ring
    linarith [hA, hB, heq]
  calc (∑ d ∈ S,
      ∑ n1 ∈ Finset.Icc (Work.GM.Energy.EnergyCore.Md N d) (2 * Work.GM.Energy.EnergyCore.Md N d),
        ∑ n2 ∈ Finset.Icc (Work.GM.Energy.EnergyCore.Md N d) (2 * Work.GM.Energy.EnergyCore.Md N d),
          ‖Submission.GM.Rfun W ((n1 : ℝ) / (n2 : ℝ))‖ ^ 2)
      ≤ _ := hsum_le
    _ = _ := hfactor
    _ ≤ _ := hmain

end Work.GM.Energy.EnergyCore
