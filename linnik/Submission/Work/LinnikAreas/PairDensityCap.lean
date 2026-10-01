import Mathlib
import Submission.Work.LinnikAreas.SiegelBase
import Submission.Work.LinnikAreas.RepulsionCapDefs
import Submission.Work.LinnikAreas.repelOwnCount
import Submission.Work.LinnikAreas.boxMaxZero
import Submission.Work.ZeroDensity.Deuring.deuringHeilbronnLogFree

/-!
# The `λ₁`-saving Deuring--Heilbronn density input, with the repulsion capped

`Work.LinnikAreas.Siegel.PairDensityInput` is the `λ₁`-saving log-free zero count
`pairCount χ₁ β₁ t ≤ C·λ₁·e^{ct}`, `c < 49/10`, for the exceptional pair of an *arbitrary* Siegel
datum with `λ₁ ≤ 1/2`.  The workspace's proof of it
(`Work.ZeroDensity.Deuring.deuringHeilbronnLogFree`) uses the *uncapped* repulsion
`Work.ZeroDensity.RepulsionWith (7/16)`, which is exactly the input AREA 3 (`ZeroFreeCert`)
supplies through `RepulsionWith_of_ZeroFreeCert`.

This file shows that the **uncapped** `PairDensityInput` follows from the **capped** repulsion
`Work.LinnikAreas.RepulsionWithCap ε₀ (7/16)` (`LinnikAreas/RepulsionCap.lean`, provable without
AREA 3) together with the (uncapped, proved) log-free family count `LogFreeFamHalf (5/2)`.  The
split is on `λ₁`:

* `λ₁ ≤ ε₀`: the two-exponential matching of `deuringHeilbronnLogFree`
  (`ownCount_le_of_threshold_and_logfree` with `c₃ = 5/2`, `c_r = 7/16`, exponent
  `5/2 + 16/7 = 67/14 < 49/10`), with the repulsion used only in the capped range;
* `ε₀ < λ₁ ≤ 1/2`: here **no repulsion is needed at all**.  The count is dominated by the family
  count (`restCount ≤ multCount ≤ famCount q (1-t/𝓛) 1 ≤ C e^{(5/2)t}`, the proved
  `restCount_le_multCount`, `multCount_le_famCount` and `LogFreeFamHalf (5/2)`), and
  `C e^{(5/2)t} ≤ (C/ε₀)·λ₁·e^{(67/14)t}` because
  `e^{-(16/7)t} ≤ 1 ≤ λ₁/ε₀` for `t ≥ 0`, `λ₁ > ε₀`.

Consequently AREA 6's two density consumers (`siegelRestLowCap` and `boxSumBoundCap`) can be fed
with the capped repulsion *and* the uncapped `PairDensityInput`, and AREA 3 disappears from the
AREA 6 dependency list (`LinnikAreas/area6CapChain.lean`).
-/

namespace Work.LinnikAreas

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

open Work.LinnikContract

/-- **The Deuring--Heilbronn `λ₁`-saving count with the repulsion capped at `λ₁ ≤ ε₀`.**  This is
`Work.ZeroDensity.DHLogFree c` with the Siegel datum restricted to `λ₁ ≤ ε₀`; the proof is that of
`Work.ZeroDensity.Deuring.deuringHeilbronnLogFree`, whose only use of the hypothesis `λ₁ ≤ 1/2` is
the repulsion call. -/
theorem deuringHeilbronnLogFreeCap {ε₀ : ℝ} (hcount : Work.ZeroDensity.LogFreeFamHalf (5 / 2))
    (hrep : RepulsionWithCap ε₀ (7 / 16)) :
    ∃ C : ℝ, 0 < C ∧ ∃ q₀ : ℕ,
      ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q] (χ₁ : DirichletCharacter ℂ q) (β₁ : ℝ),
        χ₁ ≠ 1 → χ₁ ^ 2 = 1 → β₁ < 1 → Work.LinnikContract.zeroMult χ₁ (β₁ : ℂ) ≠ 0 →
        Work.LinnikContract.lamOf q (β₁ : ℂ) ≤ ε₀ →
        ∀ t : ℝ, 0 < t → t ≤ Real.log q →
          Work.ZeroDensity.restCount χ₁ (β₁ : ℂ) t
            ≤ C * Work.LinnikContract.lamOf q (β₁ : ℂ) * Real.exp ((67 : ℝ) / 14 * t) := by
  obtain ⟨C, hCpos, qc, hcount'⟩ := hcount
  obtain ⟨qr, hrep'⟩ := hrep
  refine ⟨C, hCpos, max (max qc qr) 2, ?_⟩
  intro q hq _inst χ₁ β₁ hχ₁ hsq hβ₁ hzm hlam t ht _htlog
  have hqc : qc ≤ q := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hq
  have hqr : qr ≤ q := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hq
  have hq2 : 2 ≤ q := le_trans (le_max_right _ _) hq
  have hlogq : 0 < Real.log q := Real.log_pos (by exact_mod_cast (show 1 < q by omega))
  have hlam1pos : 0 < Work.LinnikContract.lamOf q (β₁ : ℂ) := by
    rw [Work.LinnikContract.lamOf, Complex.ofReal_re]
    exact mul_pos (by linarith) hlogq
  have hmain := Work.LinnikAreas.ownCount_le_of_threshold_and_logfree
      (N := fun t => Work.ZeroDensity.restCount χ₁ (β₁ : ℂ) t)
      (lam₁ := Work.LinnikContract.lamOf q (β₁ : ℂ)) (D := C) (c₃ := 5 / 2) (c_r := 7 / 16)
      hCpos hlam1pos (by norm_num) ?_ ?_ t (le_of_lt ht)
  · rwa [show (5 : ℝ) / 2 + 1 / (7 / 16) = 67 / 14 by norm_num] at hmain
  · intro t' ht'
    exact Work.ZeroDensity.Deuring.restCount_eq_zero_of_lt_repulsion
      (fun χ ρ hz him hne =>
        hrep' q hqr χ₁ β₁ hχ₁ hsq hβ₁ hzm hlam χ ρ hz him hne) ht'
  · intro t' ht'
    have hσ0 : 0 ≤ max 0 (1 - t' / Real.log q) := le_max_left _ _
    have hσ1 : max 0 (1 - t' / Real.log q) ≤ 1 := by
      refine max_le (by norm_num) ?_
      have : 0 ≤ t' / Real.log q := div_nonneg ht' (le_of_lt hlogq)
      linarith
    have hstep : Work.ZeroDensity.restCount χ₁ (β₁ : ℂ) t'
        ≤ Work.ZeroDensity.famCount q (max 0 (1 - t' / Real.log q)) 1 :=
      le_trans (Work.ZeroDensity.Deuring.restCount_le_multCount χ₁ (β₁ : ℂ) t')
        (Work.ZeroDensity.Deuring.multCount_le_famCount hq2 t')
    have hfam := hcount' q hqc (max 0 (1 - t' / Real.log q)) hσ0 hσ1
    have hem : 1 - max 0 (1 - t' / Real.log q) ≤ t' / Real.log q := by
      rcases le_total 0 (1 - t' / Real.log q) with h | h
      · rw [max_eq_right h]; linarith
      · rw [max_eq_left h]; linarith
    have hexp_le : (1 - max 0 (1 - t' / Real.log q)) * Real.log q ≤ t' := by
      have h1 : (1 - max 0 (1 - t' / Real.log q)) * Real.log q
          ≤ (t' / Real.log q) * Real.log q :=
        mul_le_mul_of_nonneg_right hem (le_of_lt hlogq)
      have h2 : (t' / Real.log q) * Real.log q = t' := by field_simp
      linarith
    calc Work.ZeroDensity.restCount χ₁ (β₁ : ℂ) t'
        ≤ Work.ZeroDensity.famCount q (max 0 (1 - t' / Real.log q)) 1 := hstep
      _ ≤ C * Real.exp ((5 / 2) * ((1 - max 0 (1 - t' / Real.log q)) * Real.log q)) := hfam
      _ ≤ C * Real.exp ((5 / 2) * t') := by
          refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (le_of_lt hCpos)
          exact mul_le_mul_of_nonneg_left hexp_le (by norm_num)

/-- **The uncapped `λ₁`-saving Deuring--Heilbronn density input from the capped repulsion.**  See
the module docstring for the split at `λ₁ = ε₀`. -/
theorem pairDensityInput_of_logFree_and_capRepulsion {ε₀ : ℝ} (hε₀ : 0 < ε₀)
    (hcount : Work.ZeroDensity.LogFreeFamHalf (5 / 2))
    (hrep : RepulsionWithCap ε₀ (7 / 16)) :
    Work.LinnikAreas.Siegel.PairDensityInput := by
  have hcount0 : Work.ZeroDensity.LogFreeFamHalf (5 / 2) := hcount
  obtain ⟨C, hCpos, qc, hcount'⟩ := hcount
  obtain ⟨C₂, hC₂pos, q₂, hcap⟩ := deuringHeilbronnLogFreeCap hcount0 hrep
  refine ⟨max C (max (C / ε₀) C₂) + 1, by positivity, 67 / 14, by norm_num, max (max qc q₂) 2, ?_⟩
  intro q hq hqne χ₁ β₁ hχ₁ hsq hβ₁ hzm hlam t ht htlog
  haveI := hqne
  have hqc : qc ≤ q := by omega
  have hq₂ : q₂ ≤ q := by omega
  have hq2 : 2 ≤ q := by omega
  have hlogq : 0 < Real.log q := Real.log_pos (by exact_mod_cast (show 1 < q by omega))
  have hlampos : 0 < Work.LinnikContract.lamOf q (β₁ : ℂ) :=
    Siegel.lamOf_pos hχ₁ hβ₁ hzm
  by_cases hle₀ : Work.LinnikContract.lamOf q (β₁ : ℂ) ≤ ε₀
  · -- ## `λ₁ ≤ ε₀`: the capped Deuring--Heilbronn count
    have h := hcap q hq₂ χ₁ β₁ hχ₁ hsq hβ₁ hzm hle₀ t ht htlog
    rw [Work.ZeroDensity.restCount] at h
    calc Work.LinnikAreas.Siegel.pairCount χ₁ (β₁ : ℂ) t
        ≤ C₂ * Work.LinnikContract.lamOf q (β₁ : ℂ) * Real.exp ((67 : ℝ) / 14 * t) := h
      _ ≤ (max C (max (C / ε₀) C₂) + 1) * Work.LinnikContract.lamOf q (β₁ : ℂ)
            * Real.exp ((67 : ℝ) / 14 * t) := by
          have h1 : C₂ ≤ max C (max (C / ε₀) C₂) + 1 := by
            have h9 := le_max_right C (max (C / ε₀) C₂)
            have h8 := le_max_right (C / ε₀) C₂
            linarith
          have h2 : (0 : ℝ) ≤ Work.LinnikContract.lamOf q (β₁ : ℂ) * Real.exp ((5 / 2 + 16 / 7) * t) :=
            mul_nonneg hlampos.le (Real.exp_nonneg _)
          nlinarith [h1, h2]
  · -- ## `ε₀ < λ₁ ≤ 1/2`: only the log-free family count
    have hgt : ε₀ < Work.LinnikContract.lamOf q (β₁ : ℂ) := not_le.mp hle₀
    have hσ0 : 0 ≤ max 0 (1 - t / Real.log q) := le_max_left _ _
    have hσ1 : max 0 (1 - t / Real.log q) ≤ 1 := by
      refine max_le (by norm_num) ?_
      have : 0 ≤ t / Real.log q := div_nonneg (le_of_lt ht) hlogq.le
      linarith
    have hstep : Work.LinnikAreas.Siegel.pairCount χ₁ (β₁ : ℂ) t
        ≤ Work.ZeroDensity.famCount q (max 0 (1 - t / Real.log q)) 1 := by
      rw [← Work.ZeroDensity.restCount]
      exact le_trans (Work.ZeroDensity.Deuring.restCount_le_multCount χ₁ (β₁ : ℂ) t)
        (Work.ZeroDensity.Deuring.multCount_le_famCount hq2 t)
    have hfam := hcount' q hqc (max 0 (1 - t / Real.log q)) hσ0 hσ1
    have hem : 1 - max 0 (1 - t / Real.log q) ≤ t / Real.log q := by
      rcases le_total 0 (1 - t / Real.log q) with h | h
      · rw [max_eq_right h]; linarith
      · rw [max_eq_left h]; linarith
    have hexp_le : (1 - max 0 (1 - t / Real.log q)) * Real.log q ≤ t := by
      have h1 : (1 - max 0 (1 - t / Real.log q)) * Real.log q
          ≤ (t / Real.log q) * Real.log q :=
        mul_le_mul_of_nonneg_right hem hlogq.le
      have h2 : (t / Real.log q) * Real.log q = t := by field_simp
      linarith
    have hfamt : Work.ZeroDensity.famCount q (max 0 (1 - t / Real.log q)) 1
        ≤ C * Real.exp ((5 / 2) * t) := by
      calc Work.ZeroDensity.famCount q (max 0 (1 - t / Real.log q)) 1
          ≤ C * Real.exp ((5 / 2) * ((1 - max 0 (1 - t / Real.log q)) * Real.log q)) := hfam
        _ ≤ C * Real.exp ((5 / 2) * t) := by
            refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (le_of_lt hCpos)
            exact mul_le_mul_of_nonneg_left hexp_le (by norm_num)
    -- `C e^{(5/2)t} ≤ (max C C₂ + 1) λ₁ e^{(67/14)t}`
    have hratio : Real.exp ((5 / 2) * t) ≤ Real.exp ((67 / 14) * t)
        * (Work.LinnikContract.lamOf q (β₁ : ℂ) / ε₀) := by
      have heq : Real.exp ((5 / 2) * t)
          = Real.exp ((67 / 14) * t) * Real.exp (-(16 / 7) * t) := by
        rw [← Real.exp_add]
        congr 1
        ring
      rw [heq]
      have h5 : Real.exp (-(16 / 7) * t) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [ht])
      have h6 : (1 : ℝ) ≤ Work.LinnikContract.lamOf q (β₁ : ℂ) / ε₀ :=
        (one_le_div hε₀).mpr (le_of_lt hgt)
      have h7 : 0 < Real.exp ((67 / 14) * t) := Real.exp_pos _
      nlinarith [h5, h6, h7]
    calc Work.LinnikAreas.Siegel.pairCount χ₁ (β₁ : ℂ) t
        ≤ Work.ZeroDensity.famCount q (max 0 (1 - t / Real.log q)) 1 := hstep
      _ ≤ C * Real.exp ((5 / 2) * t) := hfamt
      _ ≤ (max C (max (C / ε₀) C₂) + 1) * Work.LinnikContract.lamOf q (β₁ : ℂ)
            * Real.exp ((67 / 14) * t) := by
          have hC1 : C ≤ max C (max (C / ε₀) C₂) + 1 := by
            have := le_max_left C (max (C / ε₀) C₂); linarith
          have h1 : C * Real.exp ((5 / 2) * t)
              ≤ C * (Real.exp ((67 / 14) * t) * (Work.LinnikContract.lamOf q (β₁ : ℂ) / ε₀)) :=
            mul_le_mul_of_nonneg_left hratio hCpos.le
          have h2 : C * (Real.exp ((67 / 14) * t) * (Work.LinnikContract.lamOf q (β₁ : ℂ) / ε₀))
              = (C / ε₀) * Work.LinnikContract.lamOf q (β₁ : ℂ) * Real.exp ((67 / 14) * t) := by
            ring
          have h3 : (C / ε₀) ≤ max C (max (C / ε₀) C₂) + 1 := by
            have h9 := le_max_right C (max (C / ε₀) C₂)
            have h8 := le_max_left (C / ε₀) C₂
            linarith
          have h5 : (0 : ℝ) ≤ Work.LinnikContract.lamOf q (β₁ : ℂ) * Real.exp ((67 / 14) * t) :=
            mul_nonneg hlampos.le (Real.exp_nonneg _)
          calc C * Real.exp ((5 / 2) * t)
              ≤ C * (Real.exp ((67 / 14) * t) * (Work.LinnikContract.lamOf q (β₁ : ℂ) / ε₀)) := h1
            _ = (C / ε₀) * Work.LinnikContract.lamOf q (β₁ : ℂ) * Real.exp ((67 / 14) * t) := h2
            _ ≤ (max C (max (C / ε₀) C₂) + 1) * Work.LinnikContract.lamOf q (β₁ : ℂ)
                  * Real.exp ((67 / 14) * t) := by
                have := mul_le_mul_of_nonneg_right h3 h5
                linarith [this]

end

end Work.LinnikAreas
