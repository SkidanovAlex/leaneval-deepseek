import Mathlib
import Submission.Work.SiegelAbsorb.famCount_nearLine
import Submission.Work.ZeroDensity.Deuring.deuringHeilbronnLogFree
import Submission.Work.LinnikAreas.RepulsionCapDefs
import Submission.Work.ZeroDensity.Deuring.restCount_eq_zero_of_lt_repulsion
import Submission.Work.LinnikAreas.repelOwnCount
import Submission.Work.ZeroDensity.Deuring.multCount_le_famCount

/-!
# U5 of `AREA6_ROUTE_LEAD.md`: the Deuring--Heilbronn count truncated at `t ≤ (7/100)·log q`

The Deuring--Heilbronn two-exponential matching
(`Work.LinnikAreas.ownCount_le_of_threshold_and_logfree`) needs its count hypothesis for **all**
`t' ≥ 0`.  This file supplies it from a count that is only available on `t' ≤ θ𝓛` (`θ = 7/100`),
by applying the matching to the *truncated* count
`N t' := restCount χ₁ β₁ (min t' (θ𝓛))`:

* below the repulsion threshold `N` vanishes (because `min t' (θ𝓛) ≤ t'`);
* the count hypothesis is `restCount χ₁ β₁ m ≤ famCount q (1 - m/𝓛) 1` with
  `m = min t' (θ𝓛) ≤ θ𝓛`, and `σ = 1 - m/𝓛 ≥ 93/100`, so the near-line count
  (`SiegelAbsorb.famCount_nearLine`, coefficient `5/2`) applies.

The conclusion is the capped Deuring--Heilbronn count on the truncated range
`t ≤ θ𝓛`, with exponent `5/2 + 16/7 = 67/14 < 24/5`.
-/

namespace Work.SiegelAbsorb

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

open Work.LinnikContract

/-- **U5**: `restCount ≤ C·λ₁·e^{(5/2 + 16/7)t}` for `t ≤ (7/100)·log q`, from the capped repulsion
and the near-line family count. -/
theorem deuringHeilbronnCapTrunc {ε₀ : ℝ}
    (hrep : Work.LinnikAreas.RepulsionWithCap ε₀ (7 / 16)) :
    ∃ C : ℝ, 0 < C ∧ ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q]
      (χ₁ : DirichletCharacter ℂ q) (β₁ : ℝ),
      χ₁ ≠ 1 → χ₁ ^ 2 = 1 → β₁ < 1 → Work.LinnikContract.zeroMult χ₁ (β₁ : ℂ) ≠ 0 →
      Work.LinnikContract.lamOf q (β₁ : ℂ) ≤ ε₀ →
      ∀ t : ℝ, 0 < t → t ≤ (7 / 100) * Real.log q →
        Work.ZeroDensity.restCount χ₁ (β₁ : ℂ) t
          ≤ C * Work.LinnikContract.lamOf q (β₁ : ℂ)
              * Real.exp ((5 / 2 + 16 / 7) * t) := by
  obtain ⟨C₂, hC₂pos, hfam⟩ := famCount_nearLine
  obtain ⟨qr, hrep'⟩ := hrep
  refine ⟨C₂, hC₂pos, max qr 2, ?_⟩
  intro q hq _inst χ₁ β₁ hχ₁ hsq hβ₁ hzm hlam t ht htθ
  have hqr : qr ≤ q := le_trans (le_max_left _ _) hq
  have hq2 : 2 ≤ q := le_trans (le_max_right _ _) hq
  have hlogq : 0 < Real.log q := Real.log_pos (by exact_mod_cast (show 1 < q by omega))
  have hlam1pos : 0 < Work.LinnikContract.lamOf q (β₁ : ℂ) := by
    rw [Work.LinnikContract.lamOf, Complex.ofReal_re]
    exact mul_pos (by linarith) hlogq
  have hθ0 : (0 : ℝ) < (7 / 100) * Real.log q := by positivity
  have hθL : (7 / 100) * Real.log q ≤ Real.log q := by nlinarith
  have hmain := Work.LinnikAreas.ownCount_le_of_threshold_and_logfree
      (N := fun t' => Work.ZeroDensity.restCount χ₁ (β₁ : ℂ) (min t' ((7 / 100) * Real.log q)))
      (lam₁ := Work.LinnikContract.lamOf q (β₁ : ℂ)) (D := C₂) (c₃ := 5 / 2) (c_r := 7 / 16)
      hC₂pos hlam1pos (by norm_num) ?_ ?_ t (le_of_lt ht)
  · rw [min_eq_left htθ] at hmain
    rwa [show (5 / 2 + 1 / (7 / 16) : ℝ) = 5 / 2 + 16 / 7 by norm_num] at hmain
  · intro t' ht'
    have hle : min t' ((7 / 100) * Real.log q) ≤ t' := min_le_left _ _
    exact Work.ZeroDensity.Deuring.restCount_eq_zero_of_lt_repulsion
      (fun χ ρ hz him hne =>
        hrep' q hqr χ₁ β₁ hχ₁ hsq hβ₁ hzm hlam χ ρ hz him hne) (lt_of_le_of_lt hle ht')
  · intro t' ht'
    set m : ℝ := min t' ((7 / 100) * Real.log q) with hm
    have hm0 : 0 ≤ m := le_min ht' (le_of_lt hθ0)
    have hmθ : m ≤ (7 / 100) * Real.log q := min_le_right _ _
    have hmL : m ≤ Real.log q := le_trans hmθ hθL
    have hσ0 : 0 ≤ 1 - m / Real.log q := by
      have h1 : m / Real.log q ≤ 1 := (div_le_one hlogq).mpr hmL
      linarith
    have hσ93 : 93 / 100 ≤ 1 - m / Real.log q := by
      have h1 : m / Real.log q ≤ 7 / 100 := (div_le_iff₀ hlogq).mpr (by linarith [hmθ])
      linarith
    have hmax : max 0 (1 - m / Real.log q) = 1 - m / Real.log q := max_eq_right hσ0
    have hstep : Work.ZeroDensity.restCount χ₁ (β₁ : ℂ) m
        ≤ Work.ZeroDensity.famCount q (1 - m / Real.log q) 1 := by
      have h1 : Work.ZeroDensity.restCount χ₁ (β₁ : ℂ) m ≤ Work.ZeroDensity.multCount q m :=
        Work.ZeroDensity.Deuring.restCount_le_multCount χ₁ (β₁ : ℂ) m
      have h2 : Work.ZeroDensity.multCount q m
          ≤ Work.ZeroDensity.famCount q (max 0 (1 - m / Real.log q)) 1 :=
        Work.ZeroDensity.Deuring.multCount_le_famCount hq2 m
      rw [hmax] at h2
      exact le_trans h1 h2
    have hσle1 : 1 - m / Real.log q ≤ 1 := by
      have : 0 ≤ m / Real.log q := div_nonneg hm0 hlogq.le
      linarith
    have hfamq := hfam q hq2 (1 - m / Real.log q) 1 hσ93 hσle1 le_rfl
    have hEq : (1 - (1 - m / Real.log q)) * Real.log q = m := by
      rw [sub_sub_cancel]
      exact div_mul_cancel₀ m hlogq.ne'
    have hmt : m ≤ t' := min_le_left _ _
    calc Work.ZeroDensity.restCount χ₁ (β₁ : ℂ) m
        ≤ Work.ZeroDensity.famCount q (1 - m / Real.log q) 1 := hstep
      _ ≤ C₂ * Real.exp ((5 / 2) * ((1 - (1 - m / Real.log q)) * Real.log q)) * 1 ^ (3 / 2 : ℝ) :=
            hfamq
      _ = C₂ * Real.exp ((5 / 2) * m) := by rw [hEq, Real.one_rpow, mul_one]
      _ ≤ C₂ * Real.exp ((5 / 2) * t') := by
            refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (le_of_lt hC₂pos)
            linarith

end

end Work.SiegelAbsorb
