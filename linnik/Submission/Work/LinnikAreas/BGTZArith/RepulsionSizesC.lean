import Mathlib
import Submission.Work.LinnikAreas.BGTZSetup
import Submission.Work.LinnikAreas.BGTZ.RepulsionSizes
import Submission.Work.LinnikAreas.BGTZArith.RepulsionSizesReal

namespace Work.LinnikAreas.BGTZArith

open Work.LinnikAreas.BGTZ

set_option maxHeartbeats 4000000

/-! ## Helper estimates for `RepulsionSizesC`

The three elementary inputs of the assembly below: the logarithm of the constant `C ≤ 256` is
below `log q / 1000`; the quantity `X := q^{2θ}e^{2(log q)^{3/4}}(1-β₁)^{-2}` (with
`θ = 1/4 + 1/100`) is at least `1`; and consequently the sifting level
`R := max 200 (⌈C A² X⌉ + 1)` satisfies both `C A² X ≤ R` and `R ≤ 2·sieveR A θ q β₁`
(where `sieveR A θ q β₁ = 256 A² X`). -/

/-- `log C ≤ log q / 1000` when `0 < C ≤ 256` and `log q ≥ 10^8`: `log 256 = 8 log 2 < 8` is far
below `10^5 ≤ log q / 1000`. -/
lemma repulsionSizesCLogBound {q : ℕ} {C : ℝ} (hCpos : 0 < C) (hC256 : C ≤ 256)
    (hlogq : 100000000 ≤ Real.log (q : ℝ)) : Real.log C ≤ Real.log (q : ℝ) / 1000 := by
  by_cases hC1 : C ≤ 1
  · have h1 : Real.log C ≤ 0 := Real.log_nonpos hCpos.le hC1
    have h2 : (0:ℝ) ≤ Real.log (q:ℝ) / 1000 := by linarith
    linarith
  · have h1 : Real.log C ≤ Real.log 256 := Real.log_le_log hCpos hC256
    have h256 : Real.log (256:ℝ) = 8 * Real.log 2 := by
      rw [show (256:ℝ) = 2 ^ 8 by norm_num, Real.log_pow]
      norm_num
    have h2 : Real.log (2:ℝ) < 1 := by
      have h := Real.log_lt_sub_one_of_pos (show (0:ℝ) < 2 by norm_num) (by norm_num)
      linarith
    have h3 : (100000:ℝ) ≤ Real.log (q:ℝ) / 1000 := by linarith
    linarith

/-- `X := q^{2θ}e^{2(log q)^{3/4}}(1-β₁)^{-2} ≥ 1` for `q ≥ 1`, `0 < β₁ < 1` and
`θ = 1/4 + 1/100`: every factor is at least `1`. -/
lemma repulsionSizesCXgeOne {q : ℕ} {β₁ : ℝ} (hq1 : 1 ≤ q) (hβ0 : 0 < β₁) (hβlt : β₁ < 1) :
    (1:ℝ) ≤ (q:ℝ)^((2:ℝ)*(1/4+1/100)) * Real.exp (2*(Real.log (q:ℝ))^(3/4:ℝ))
      * (1-β₁)^(-2:ℝ) := by
  have hxpos : (0:ℝ) < (q:ℝ) := by exact_mod_cast hq1
  have hx1 : (1:ℝ) ≤ (q:ℝ) := by exact_mod_cast hq1
  have hδpos : 0 < 1 - β₁ := by linarith
  have hδle1 : 1 - β₁ ≤ 1 := by linarith
  have h1 : (1:ℝ) ≤ (q:ℝ)^((2:ℝ)*(1/4+1/100)) := Real.one_le_rpow hx1 (by norm_num)
  have h2 : (1:ℝ) ≤ Real.exp (2*(Real.log (q:ℝ))^(3/4:ℝ)) := Real.one_le_exp (by positivity)
  have h3 : (1:ℝ) ≤ (1-β₁)^(-2:ℝ) := by
    have hinv : (1:ℝ) ≤ (1-β₁)⁻¹ := (one_le_inv₀ hδpos).mpr hδle1
    have hsplit : (1-β₁)^(-2:ℝ) = (1-β₁)^(-1:ℝ) * (1-β₁)^(-1:ℝ) := by
      rw [show (-2:ℝ) = (-1) + (-1) by norm_num, Real.rpow_add hδpos]
    rw [hsplit, Real.rpow_neg_one]
    nlinarith [hinv]
  have h12 : (1:ℝ) ≤ (q:ℝ)^((2:ℝ)*(1/4+1/100)) * Real.exp (2*(Real.log (q:ℝ))^(3/4:ℝ)) := by
    have h := mul_le_mul h1 h2 (by norm_num : (0:ℝ) ≤ 1) (le_trans zero_le_one h1)
    simpa using h
  have h123 : (1:ℝ) ≤ (q:ℝ)^((2:ℝ)*(1/4+1/100)) * Real.exp (2*(Real.log (q:ℝ))^(3/4:ℝ))
      * (1-β₁)^(-2:ℝ) := by
    have h := mul_le_mul h12 h3 (by norm_num : (0:ℝ) ≤ 1) (le_trans zero_le_one h12)
    simpa using h
  exact h123

/-- The sifting level `R := max 200 (⌈C A²X⌉ + 1)` is at most `2·sieveR A θ q β₁` when
`C ≤ 256`, `A ≥ 1` and `X ≥ 1` (`θ = 1/4 + 1/100`, `X = q^{2θ}e^{2(log q)^{3/4}}(1-β₁)^{-2}`,
so that `sieveR A θ q β₁ = 256 A²X`): indeed `R ≤ C A²X + 2 ≤ 258 A²X ≤ 512 A²X` and
`200 ≤ 512 A²X`. -/
lemma repulsionSizesCRBound {q : ℕ} {A C β₁ : ℝ}
    (hA1 : 1 ≤ A) (hCpos : 0 < C) (hC256 : C ≤ 256)
    (hZ1 : (1:ℝ) ≤ (q:ℝ)^((2:ℝ)*(1/4+1/100)) * Real.exp (2*(Real.log (q:ℝ))^(3/4:ℝ))
      * (1-β₁)^(-2:ℝ)) :
    ((max 200 (⌈C * A ^ 2 * (q : ℝ) ^ ((2 : ℝ) * (1 / 4 + 1 / 100))
          * Real.exp (2 * (Real.log (q : ℝ)) ^ (3 / 4 : ℝ)) * (1 - β₁) ^ (-2 : ℝ)⌉₊ + 1) : ℕ) : ℝ)
      ≤ 2 * Work.LinnikAreas.BGTZ.sieveR A (1 / 4 + 1 / 100) q β₁ := by
  have hA2ge1 : (1:ℝ) ≤ A^2 := by nlinarith
  have hY1 : (1:ℝ) ≤ A^2 * ((q:ℝ)^((2:ℝ)*(1/4+1/100)) * Real.exp (2*(Real.log (q:ℝ))^(3/4:ℝ))
      * (1-β₁)^(-2:ℝ)) := by nlinarith [hA2ge1, hZ1]
  have hYnn : (0:ℝ) ≤ A^2 * ((q:ℝ)^((2:ℝ)*(1/4+1/100)) * Real.exp (2*(Real.log (q:ℝ))^(3/4:ℝ))
      * (1-β₁)^(-2:ℝ)) := le_trans zero_le_one hY1
  have hEnn : (0:ℝ) ≤ C * A ^ 2 * (q : ℝ) ^ ((2 : ℝ) * (1 / 4 + 1 / 100))
      * Real.exp (2 * (Real.log (q : ℝ)) ^ (3 / 4 : ℝ)) * (1 - β₁) ^ (-2 : ℝ) := by
    have h := mul_nonneg hCpos.le hYnn
    simpa only [mul_assoc] using h
  have hceil : ((⌈C * A ^ 2 * (q : ℝ) ^ ((2 : ℝ) * (1 / 4 + 1 / 100))
        * Real.exp (2 * (Real.log (q : ℝ)) ^ (3 / 4 : ℝ)) * (1 - β₁) ^ (-2 : ℝ)⌉₊ : ℕ) : ℝ) + 1
      ≤ 512 * (A^2 * ((q:ℝ)^((2:ℝ)*(1/4+1/100)) * Real.exp (2*(Real.log (q:ℝ))^(3/4:ℝ))
        * (1-β₁)^(-2:ℝ))) := by
    have h1 := Nat.ceil_lt_add_one hEnn
    have h2 : C * (A^2 * ((q:ℝ)^((2:ℝ)*(1/4+1/100)) * Real.exp (2*(Real.log (q:ℝ))^(3/4:ℝ))
          * (1-β₁)^(-2:ℝ)))
        ≤ 256 * (A^2 * ((q:ℝ)^((2:ℝ)*(1/4+1/100)) * Real.exp (2*(Real.log (q:ℝ))^(3/4:ℝ))
          * (1-β₁)^(-2:ℝ))) := mul_le_mul_of_nonneg_right hC256 hYnn
    linarith only [h1, h2, hY1]
  have hmax : ((max 200 (⌈C * A ^ 2 * (q : ℝ) ^ ((2 : ℝ) * (1 / 4 + 1 / 100))
        * Real.exp (2 * (Real.log (q : ℝ)) ^ (3 / 4 : ℝ)) * (1 - β₁) ^ (-2 : ℝ)⌉₊ + 1) : ℕ) : ℝ)
      ≤ 512 * (A^2 * ((q:ℝ)^((2:ℝ)*(1/4+1/100)) * Real.exp (2*(Real.log (q:ℝ))^(3/4:ℝ))
        * (1-β₁)^(-2:ℝ))) := by
    have hcast : ((max 200 (⌈C * A ^ 2 * (q : ℝ) ^ ((2 : ℝ) * (1 / 4 + 1 / 100))
          * Real.exp (2 * (Real.log (q : ℝ)) ^ (3 / 4 : ℝ)) * (1 - β₁) ^ (-2 : ℝ)⌉₊ + 1) : ℕ) : ℝ)
        = max 200 (((⌈C * A ^ 2 * (q : ℝ) ^ ((2 : ℝ) * (1 / 4 + 1 / 100))
          * Real.exp (2 * (Real.log (q : ℝ)) ^ (3 / 4 : ℝ)) * (1 - β₁) ^ (-2 : ℝ)⌉₊ : ℕ) : ℝ) + 1) := by
      push_cast
      ring
    rw [hcast]
    refine max_le ?_ ?_
    · linarith only [hY1]
    · linarith only [hceil]
  have hEq : 512 * (A^2 * ((q:ℝ)^((2:ℝ)*(1/4+1/100)) * Real.exp (2*(Real.log (q:ℝ))^(3/4:ℝ))
        * (1-β₁)^(-2:ℝ))) = 2 * Work.LinnikAreas.BGTZ.sieveR A (1 / 4 + 1 / 100) q β₁ := by
    rw [Work.LinnikAreas.BGTZ.sieveR]
    ring_nf
  rw [← hEq]
  exact hmax

/-- **The size conditions of the BGTZ assembly, with the sifting level pinned from above.**

This is `Work.LinnikAreas.BGTZArith.RepulsionSizesReal` (the `q`-powers as *real* powers, the
constants `2·(1/4+1/100)`, `8·(1/4+1/100)`, `4·(1/4+1/100)`, which is the version that the users need)
with one extra conclusion: the sifting level `R` also satisfies the upper bound
`R ≤ 2 * sieveR A (1/4+1/100) q β₁` that the repaired interface
`Work.LinnikAreas.BGTZ.DetectorMainProp` demands.  The extra hypothesis `C ≤ 256` (the constant `C`
of that interface; `sieveR` itself is `256·A²q^{2θ}e^{2(log q)^{3/4}}(1-β₁)^{-2}`) is exactly what
makes this possible: with `X := q^{2θ}e^{2(log q)^{3/4}}(1-β₁)^{-2}`, `θ = 1/4+1/100`, the choice
`R := ⌈C·A²·X⌉ + 1` satisfies `C·A²·X ≤ R` and `R ≤ C·A²·X + 2 ≤ 258·A²·X ≤ 2·sieveR`
(since `A ≥ 1` and `X ≥ 1`, so `A²X ≥ 1`).  The only *other* difference from `RepulsionSizesReal`
is that no `Real.log C ≤ Real.log q / 1000` hypothesis is needed, because `C ≤ 256` gives
`Real.log C ≤ 6`, far inside the available slack.

The elementary estimates of `Submission.Work.LinnikAreas.BGTZ.RepulsionSizes`
(`repulsionSizesSiegelInv` in particular) and the proof of
`Submission.Work.LinnikAreas.BGTZArith.RepulsionSizesReal` (which may be imported and adapted) are
the inputs; `B ≥ 1` turns the Landau--Siegel hypothesis into `(1-β₁)^{-1} ≤ q^{1/100}(log q)²`, and
the final bound `log N ≤ log q · (11/5 + (11/10)log(5+|γ|)/log q)` is the one whose coefficients
`8θ + 2ε ≤ 11/5`, `4θ ≤ 11/10` are checked against `T ≤ 5+|γ|`. -/
theorem RepulsionSizesC {q : ℕ} [NeZero q] {A B C cZ T β₁ γ : ℝ}
    (hA1 : 1 ≤ A) (hB1 : 1 ≤ B) (hCpos : 0 < C) (hC256 : C ≤ 256)
    (hcZ : 0 < cZ) (hT : 4 ≤ T) (hγT : |γ| ≤ T) (hTγ : T ≤ 5 + |γ|) (hβ₁lt : β₁ < 1)
    (hβ₁big : 1 - 1 / (10 * Real.log q) < β₁)
    (hSiegel : B / ((q : ℝ) ^ (1 / 100 : ℝ) * (Real.log q) ^ 2) < 1 - β₁)
    (hlogq : 100000000 ≤ Real.log q)
    (hlogA : Real.log A ≤ Real.log q / 1000) (hlogB : Real.log B ≤ Real.log q / 1000) :
    ∃ R N : ℕ, 200 ≤ R ∧ 2 ≤ N ∧ 1 ≤ (N : ℝ) * (1 - β₁) ∧
      C * A ^ 2 * (q : ℝ) ^ ((2 : ℝ) * (1 / 4 + 1 / 100))
          * Real.exp (2 * (Real.log (q : ℝ)) ^ (3 / 4 : ℝ)) * (1 - β₁) ^ (-2 : ℝ) ≤ (R : ℝ) ∧
      (R : ℝ) ≤ 2 * Work.LinnikAreas.BGTZ.sieveR A (1 / 4 + 1 / 100) q β₁ ∧
      C * A ^ 8 * Real.exp (8 * (Real.log (q : ℝ)) ^ (3 / 4 : ℝ))
          * (Real.log (2 + A ^ 2 * (q : ℝ) ^ 3)) ^ 24 * (q : ℝ) ^ ((8 : ℝ) * (1 / 4 + 1 / 100))
          * T ^ ((4 : ℝ) * (1 / 4 + 1 / 100)) * (1 - β₁) ^ (-2 : ℝ) ≤ (N : ℝ) ∧
      Real.log (N : ℝ) ≤ Real.log (q : ℝ)
          * (11 / 5 + (11 / 10) * (Real.log (5 + |γ|) / Real.log (q : ℝ))) := by
  -- the constant `C` is harmless: `log C ≤ log q / 1000` follows from `C ≤ 256`
  have hlogC : Real.log C ≤ Real.log (q : ℝ) / 1000 := repulsionSizesCLogBound hCpos hC256 hlogq
  -- the existing `RepulsionSizesReal` supplies the detection length `N` (and a valid, but for us
  -- unused, sifting level)
  obtain ⟨R₀, N, hR₀, hN2, hNδ, hR₀lb, hR₀log, hNlb, hNlog⟩ :=
    RepulsionSizesReal (Cd := C) hA1 hB1 hCpos hcZ hT hγT hTγ hβ₁lt hβ₁big hSiegel hlogq
      hlogA hlogB hlogC
  -- elementary facts
  have hq1 : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hβ0 : 0 < β₁ := by
    have h10 : (0:ℝ) < 10 * Real.log (q:ℝ) := by
      have : (0:ℝ) < Real.log (q:ℝ) := by linarith
      linarith
    have h1 : 1 / (10 * Real.log (q:ℝ)) ≤ 1 := by
      rw [div_le_one h10]
      linarith
    linarith
  have hZ1 : (1:ℝ) ≤ (q:ℝ)^((2:ℝ)*(1/4+1/100)) * Real.exp (2*(Real.log (q:ℝ))^(3/4:ℝ))
      * (1-β₁)^(-2:ℝ) := repulsionSizesCXgeOne hq1 hβ0 hβ₁lt
  refine ⟨max 200 (⌈C * A ^ 2 * (q : ℝ) ^ ((2 : ℝ) * (1 / 4 + 1 / 100))
      * Real.exp (2 * (Real.log (q : ℝ)) ^ (3 / 4 : ℝ)) * (1 - β₁) ^ (-2 : ℝ)⌉₊ + 1), N,
    ?_, hN2, hNδ, ?_, ?_, hNlb, hNlog⟩
  · exact le_max_left _ _
  · have h1 : C * A ^ 2 * (q : ℝ) ^ ((2 : ℝ) * (1 / 4 + 1 / 100))
        * Real.exp (2 * (Real.log (q : ℝ)) ^ (3 / 4 : ℝ)) * (1 - β₁) ^ (-2 : ℝ)
        ≤ ((⌈C * A ^ 2 * (q : ℝ) ^ ((2 : ℝ) * (1 / 4 + 1 / 100))
          * Real.exp (2 * (Real.log (q : ℝ)) ^ (3 / 4 : ℝ)) * (1 - β₁) ^ (-2 : ℝ)⌉₊ : ℕ) : ℝ) :=
      Nat.le_ceil _
    have h2 : ((⌈C * A ^ 2 * (q : ℝ) ^ ((2 : ℝ) * (1 / 4 + 1 / 100))
          * Real.exp (2 * (Real.log (q : ℝ)) ^ (3 / 4 : ℝ)) * (1 - β₁) ^ (-2 : ℝ)⌉₊ : ℕ) : ℝ)
        ≤ ((max 200 (⌈C * A ^ 2 * (q : ℝ) ^ ((2 : ℝ) * (1 / 4 + 1 / 100))
          * Real.exp (2 * (Real.log (q : ℝ)) ^ (3 / 4 : ℝ)) * (1 - β₁) ^ (-2 : ℝ)⌉₊ + 1) : ℕ) : ℝ) := by
      have h3 : ⌈C * A ^ 2 * (q : ℝ) ^ ((2 : ℝ) * (1 / 4 + 1 / 100))
          * Real.exp (2 * (Real.log (q : ℝ)) ^ (3 / 4 : ℝ)) * (1 - β₁) ^ (-2 : ℝ)⌉₊
          ≤ max 200 (⌈C * A ^ 2 * (q : ℝ) ^ ((2 : ℝ) * (1 / 4 + 1 / 100))
          * Real.exp (2 * (Real.log (q : ℝ)) ^ (3 / 4 : ℝ)) * (1 - β₁) ^ (-2 : ℝ)⌉₊ + 1) :=
        le_trans (Nat.le_succ _) (le_max_right _ _)
      exact_mod_cast h3
    linarith
  · exact repulsionSizesCRBound hA1 hCpos hC256 hZ1

end Work.LinnikAreas.BGTZArith
