import Mathlib
import Submission.Work.LinnikAreas.BGTZSetup
import Submission.Work.LinnikAreas.BGTZ.RepulsionSizes
import Submission.Work.LinnikAreas.BGTZArith.RepulsionSizesC

namespace Work.LinnikAreas.BGTZArith

open Work.LinnikAreas.BGTZ

set_option maxHeartbeats 4000000

lemma repulsionSizesDLogBound {q : ℕ} {C : ℝ} (hCpos : 0 < C) (hC510 : C ≤ 510)
    (hlogq : 100000000 ≤ Real.log (q : ℝ)) : Real.log C ≤ Real.log (q : ℝ) / 1000 := by
  have h1 : Real.log C ≤ C - 1 := Real.log_le_sub_one_of_pos hCpos
  have h2 : C - 1 ≤ 509 := by linarith
  have h3 : (509 : ℝ) ≤ Real.log (q : ℝ) / 1000 := by linarith
  linarith

lemma repulsionSizesDRBound {q : ℕ} {A C β₁ : ℝ}
    (hA1 : 1 ≤ A) (hCpos : 0 < C) (hC510 : C ≤ 510)
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
        ≤ 510 * (A^2 * ((q:ℝ)^((2:ℝ)*(1/4+1/100)) * Real.exp (2*(Real.log (q:ℝ))^(3/4:ℝ))
          * (1-β₁)^(-2:ℝ))) := mul_le_mul_of_nonneg_right hC510 hYnn
    nlinarith [h1, h2, hY1]
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
    · nlinarith [hY1]
    · linarith [hceil]
  have hEq : 512 * (A^2 * ((q:ℝ)^((2:ℝ)*(1/4+1/100)) * Real.exp (2*(Real.log (q:ℝ))^(3/4:ℝ))
        * (1-β₁)^(-2:ℝ))) = 2 * Work.LinnikAreas.BGTZ.sieveR A (1 / 4 + 1 / 100) q β₁ := by
    rw [Work.LinnikAreas.BGTZ.sieveR]
    ring_nf
  rw [← hEq]
  exact hmax

/-- **The size conditions of the BGTZ assembly with the sifting level pinned above, maximal pin.**

`Work.LinnikAreas.BGTZArith.RepulsionSizesC` with the bound on the detector interface's constant
relaxed from `C ≤ 256` to `C ≤ 510`: with `X := q^{2θ}e^{2(log q)^{3/4}}(1-β₁)^{-2}` and
`θ = 1/4+1/100`, the choice `R := ⌈C·A²·X⌉ + 1` satisfies `C·A²·X ≤ R` and
`R ≤ C·A²·X + 2 ≤ 512·A²·X = 2·sieveR A θ q β₁` exactly when `C ≤ 510` (using `A ≥ 1`, `X ≥ 1`),
so `510` is the largest pin for which a consumer of the repaired `DetectorMainProp` can exhibit the
sifting level.  `Real.log C ≤ Real.log 510 ≤ 7` is absorbed by the slack (`log q ≥ 10^8`), so no
`Real.log C ≤ log q / 1000` hypothesis is needed.

The elementary estimates of `Submission.Work.LinnikAreas.BGTZ.RepulsionSizes` and the proof of
`Submission.Work.LinnikAreas.BGTZArith.RepulsionSizesC` (which may be imported and adapted; it is the
same statement with `C ≤ 256`) are the inputs. -/
theorem RepulsionSizesD {q : ℕ} [NeZero q] {A B C cZ T β₁ γ : ℝ}
    (hA1 : 1 ≤ A) (hB1 : 1 ≤ B) (hCpos : 0 < C) (hC510 : C ≤ 510)
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
  have hlogC : Real.log C ≤ Real.log (q : ℝ) / 1000 := repulsionSizesDLogBound hCpos hC510 hlogq
  obtain ⟨R₀, N, hR₀, hN2, hNδ, hR₀lb, hR₀log, hNlb, hNlog⟩ :=
    RepulsionSizesReal (Cd := C) hA1 hB1 hCpos hcZ hT hγT hTγ hβ₁lt hβ₁big hSiegel hlogq
      hlogA hlogB hlogC
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
  · exact repulsionSizesDRBound hA1 hCpos hC510 hZ1

end Work.LinnikAreas.BGTZArith
