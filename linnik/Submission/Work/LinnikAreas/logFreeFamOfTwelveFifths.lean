import Mathlib
import Submission.Work.ZeroDensity.Defs
import Submission.Work.ZeroDensity.Basic
import Submission.Work.ZeroDensity.LogFree.Defs
import Submission.Work.LinnikAreas.Setup
import Submission.Work.LinnikAreas.logFreeFamHalfOfNonPrincipal
import Submission.Work.LinnikAreas.logFreeFamHeightOfNonPrincipal
import Submission.Work.LinnikAreas.principalCountIn_le_rpow

/-!
# The AREA 6 family counts from the unified non-principal input `NonPrincipalTwelveFifths`

The lead's unified route (`Submission/Work/ZeroDensity/JUTILA_UNIFIED_LEAD.md`) replaces Jutila's
sharp non-principal estimate (coefficient `2` on `σ ≥ 4/5`) by

`Work.ZeroDensity.LogFree.NonPrincipalTwelveFifths : Σ'_{χ ≠ 1} N(σ,T,χ) ≤ C (qT)^{(12/5+ε)(1-σ)}`
on `σ ≥ 3979/5000 = 0.7958`.

**Area 6 consumes exactly the coefficient `12/5 + 1/10 = 5/2`** (`LogFreeFamHalf (5/2)` and
`LogFreeFamHeight (5/2) (3/2)`), and `12/5 + 1/10 = 2.5 = 5/2` is *equality* — so the new input
fits the existing AREA 6 chain verbatim, with no change of exponent anywhere downstream.  The
range also fits: `3979/5000 = 0.7958 < 4/5 = 0.8`, so `NonPrincipalTwelveFifths` at `ε = 1/10`
covers the whole near-line range `σ ≥ 4/5` on which the old Jutila input was used, and Huxley's
`FamDensityEpsRange 0 (4/5) (12/5)` at `ε = 1/10` covers `σ ≤ 4/5` with the same exponent.

The two theorems below are therefore the *verbatim* proofs of
`Work.LinnikAreas.logFreeFamHalfOfNonPrincipal` / `...logFreeFamHeightOfNonPrincipal` with the
Jutila input (coefficient `2 + 1/10`, `σ ≥ 4/5`) replaced by `NonPrincipalTwelveFifths` at
`ε = 1/10` (coefficient `5/2`, `σ ≥ 3979/5000`); every exponent comparison in the old proof was
`2 + 1/10 ≤ 5/2` and is now an equality, and the `σ`-range hypothesis `4/5 ≤ σ` is stronger than
the new one `3979/5000 ≤ σ`.

Nothing else changes: AREA 6's downstream lemmas (`PairDensityCap`,
`RestHighFree`/`RestHighBGTZGenC`, `siegelRestLowCap`, `boxSumCap`) all consume the two
`LogFreeFam` statements with the *fixed* exponent `5/2`, so they are untouched.
-/

namespace Work.LinnikAreas

open DirichletCharacter Complex
open scoped Classical BigOperators
open Work.ZeroDensity.LogFree
noncomputable section

open Work.LinnikContract

/-- **`LogFreeFamHalf (5/2)` from `NonPrincipalTwelveFifths` and Huxley's `12/5`.**

At height `1`: the non-principal characters are counted by `NonPrincipalTwelveFifths` at
`ε = 1/10` (coefficient `5/2`) on `σ ≥ 3979/5000 ⊃ [4/5,1]`, the principal character by the
absolute height-`1` divisor bound (`zeroCountIn_one_height_one_bound`, independent of `q`), and the
range `σ ≤ 4/5` by Huxley's `12/5` at `ε = 1/10`, again with coefficient exactly `5/2`. -/
theorem logFreeFamHalf_of_nonPrincipalTwelveFifths
    (hNP : NonPrincipalTwelveFifths)
    (hH : Work.ZeroDensity.FamDensityEpsRange 0 (4 / 5) (12 / 5)) :
    Work.ZeroDensity.LogFreeFamHalf (5 / 2) := by
  obtain ⟨CNP, hCNP, hNP'⟩ := hNP (1 / 10) (by norm_num)
  obtain ⟨CH, hCH, hHb⟩ := hH (1 / 10) (by norm_num)
  obtain ⟨CZ, hCZ, hZb⟩ := zeroCountIn_one_height_one_bound
  refine ⟨CH + CNP + CZ + 1, by linarith, 2, ?_⟩
  intro q hq hqne σ hσ0 hσ1
  haveI := hqne
  have hq2 : 2 ≤ q := hq
  have hlogq : (0 : ℝ) ≤ Real.log (q : ℝ) := by
    have h1 : (1 : ℝ) ≤ (q : ℝ) := by
      have h2 : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq2
      linarith
    exact Real.log_nonneg h1
  have hEeq : (q : ℝ) ^ ((5 : ℝ) / 2 * (1 - σ))
      = Real.exp ((5 / 2) * ((1 - σ) * Real.log (q : ℝ))) := rpow_half_eq_exp q hq2 σ
  have hscale : ((12 : ℝ) / 5 + 1 / 10) * (1 - σ) = (5 : ℝ) / 2 * (1 - σ) := by ring
  by_cases h45 : (4 : ℝ) / 5 ≤ σ
  · -- ## `σ ≥ 4/5`: the non-principal characters by `NonPrincipalTwelveFifths`, the principal one by `CZ`
    have hsplit := famCount_eq_erase_add (q := q) σ 1
    rw [hsplit]
    have hq1 : (1 : ℝ) ≤ (q : ℝ) := by
      have h2 : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq2
      linarith
    have hnp := hNP' q hq2 σ 1 (by linarith) hσ1 le_rfl
    have hpr := hZb q σ h45 hσ1
    simp only [mul_one] at hnp
    rw [hscale] at hnp
    rw [hEeq] at hnp
    simp only [Work.ZeroDensity.LogFree.famCountNP, Work.ZeroDensity.zCount] at hnp
    have hsum : (∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
            Work.LinnikAreas.zeroCountIn χ σ 1)
          + Work.LinnikAreas.zeroCountIn (1 : DirichletCharacter ℂ q) σ 1
        ≤ (CH + CNP + CZ + 1) * Real.exp ((5 / 2) * ((1 - σ) * Real.log (q : ℝ))) := by
      set E : ℝ := Real.exp ((5 / 2) * ((1 - σ) * Real.log (q : ℝ))) with hEdef
      have hE1 : (1 : ℝ) ≤ E := by
        rw [hEdef, Real.one_le_exp_iff]
        exact mul_nonneg (by norm_num) (mul_nonneg (by linarith) hlogq)
      have hEpos : (0 : ℝ) < E := Real.exp_pos _
      have hstep1 : CNP * E + CZ ≤ (CNP + CZ) * E := by
        have h1 : CZ ≤ CZ * E := le_mul_of_one_le_right (le_of_lt hCZ) hE1
        nlinarith
      have hstep2 : (CNP + CZ) * E ≤ (CH + CNP + CZ + 1) * E :=
        mul_le_mul_of_nonneg_right (by linarith) hEpos.le
      linarith [hnp, hpr, hstep1, hstep2]
    exact hsum
  · -- ## `σ ≤ 4/5`: Huxley's `12/5` at `ε = 1/10` (coefficient exactly `5/2`)
    have h45' : σ ≤ (4 : ℝ) / 5 := le_of_lt (not_le.mp h45)
    have h := hHb q hq2 σ 1 hσ0 h45' le_rfl
    simp only [mul_one] at h
    rw [hscale, hEeq] at h
    refine le_trans h ?_
    refine mul_le_mul_of_nonneg_right ?_ (Real.exp_nonneg _)
    linarith

/-- **`LogFreeFamHeight (5/2) (3/2)` from `NonPrincipalTwelveFifths` and Huxley's `12/5`.**

At height `T`: the principal character contributes `≪ T^{3/2}` uniformly in the level
(`principalCountIn_le_rpow`), the non-principal ones are counted by `NonPrincipalTwelveFifths` at
`ε = 1/10` on `σ ≥ 4/5` (whose `T`-exponent `(5/2)(1-σ) ≤ 1/2 ≤ 3/2` is absorbed by the `T^{3/2}`),
by Huxley's `12/5` at `ε = 1/10` on `2/5 ≤ σ ≤ 4/5` (whose `T`-exponent is
`(5/2)(1-σ) ≤ (5/2)(3/5) = 3/2`), and by the σ-blind count on `σ ≤ 2/5`. -/
theorem logFreeFamHeight_of_nonPrincipalTwelveFifths
    (hNP : NonPrincipalTwelveFifths)
    (hH : Work.ZeroDensity.FamDensityEpsRange 0 (4 / 5) (12 / 5)) :
    Work.ZeroDensity.LogFreeFamHeight (5 / 2) (3 / 2) := by
  obtain ⟨CNP, hCNP, hNP'⟩ := hNP (1 / 10) (by norm_num)
  obtain ⟨CH, hCH, hHb⟩ := hH (1 / 10) (by norm_num)
  obtain ⟨CT, hCT, hT'⟩ := Work.ZeroDensity.trivial_bound (1 / 2) (by norm_num)
  obtain ⟨Cz, hCz, hz⟩ := principalCountIn_le_rpow
  set Cf : ℝ := max (max CT CH) (CNP + Cz) with hCf
  have hCfpos : 0 < Cf :=
    lt_of_lt_of_le hCT (le_trans (le_max_left _ _) (le_max_left _ _))
  have hCTle : CT ≤ Cf := by rw [hCf]; exact le_trans (le_max_left _ _) (le_max_left _ _)
  have hCHle : CH ≤ Cf := by rw [hCf]; exact le_trans (le_max_right _ _) (le_max_left _ _)
  have hCNPle : CNP ≤ Cf := by
    rw [hCf]; exact le_trans (le_add_of_nonneg_right hCz.le) (le_max_right _ _)
  have hCzle : Cz ≤ Cf := by
    rw [hCf]; exact le_trans (le_add_of_nonneg_left hCNP.le) (le_max_right _ _)
  refine ⟨2 * Cf, by positivity, 2, ?_⟩
  intro q hq hqne σ T hσ0 hσ1 hT
  haveI := hqne
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by
    have h2 : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
    linarith
  have hlogq : (0 : ℝ) ≤ Real.log (q : ℝ) := Real.log_nonneg hq1
  have hTpow : (0 : ℝ) ≤ T ^ ((3 : ℝ) / 2) := Real.rpow_nonneg (by linarith) _
  have hexp1 : (1 : ℝ) ≤ Real.exp ((5 / 2) * ((1 - σ) * Real.log q)) := by
    rw [Real.one_le_exp_iff]
    exact mul_nonneg (by norm_num) (mul_nonneg (by linarith) hlogq)
  have key : ∀ A : ℝ, A ≤ Cf →
      A * Real.exp ((5 / 2) * ((1 - σ) * Real.log q)) * T ^ ((3 : ℝ) / 2)
        ≤ (2 * Cf) * Real.exp ((5 / 2) * ((1 - σ) * Real.log q)) * T ^ ((3 : ℝ) / 2) := by
    intro A hA
    have h2 : A ≤ 2 * Cf := le_trans hA (by linarith)
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right h2 (Real.exp_nonneg _)) hTpow
  rcases le_total σ (2 / 5) with hA | hA
  · -- ## `σ ≤ 2/5`: the σ-blind count
    refine le_trans (hT' q hq σ T hσ0 hσ1 hT) ?_
    refine le_trans (rpow_le_expHeight_mul (σ := σ) hq hT (le_of_lt hCT) hCTle ?_ ?_) ?_
    · have h1m : (3 : ℝ) / 5 ≤ 1 - σ := by linarith
      nlinarith
    · norm_num
    · exact key Cf le_rfl
  · rcases le_total (4 / 5) σ with hB | hB
    · -- ## `σ ≥ 4/5`: the principal character and `NonPrincipalTwelveFifths`
      have hsplit : Work.ZeroDensity.famCount q σ T
          = Work.LinnikAreas.zeroCountIn (1 : DirichletCharacter ℂ q) σ T
            + ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
                Work.LinnikAreas.zeroCountIn χ σ T := by
        rw [Work.ZeroDensity.famCount_eq_sum]
        exact (Finset.add_sum_erase Finset.univ
          (fun χ : DirichletCharacter ℂ q => Work.LinnikAreas.zeroCountIn χ σ T)
          (Finset.mem_univ 1)).symm
      rw [hsplit]
      have hprin : Work.LinnikAreas.zeroCountIn (1 : DirichletCharacter ℂ q) σ T
          ≤ Cf * Real.exp ((5 / 2) * ((1 - σ) * Real.log q)) * T ^ ((3 : ℝ) / 2) := by
        refine le_trans (hz q hq σ T hσ0 hσ1 hT) ?_
        calc Cz * T ^ ((3 : ℝ) / 2) ≤ Cf * T ^ ((3 : ℝ) / 2) :=
              mul_le_mul_of_nonneg_right hCzle hTpow
          _ ≤ Cf * Real.exp ((5 / 2) * ((1 - σ) * Real.log q)) * T ^ ((3 : ℝ) / 2) :=
              mul_le_mul_of_nonneg_right
                (le_mul_of_one_le_right hCfpos.le hexp1) hTpow
      have hnon : (∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
              Work.LinnikAreas.zeroCountIn χ σ T)
          ≤ Cf * Real.exp ((5 / 2) * ((1 - σ) * Real.log q)) * T ^ ((3 : ℝ) / 2) := by
        have hnp := hNP' q hq σ T (by linarith) hσ1 hT
        have hscale : ((12 : ℝ) / 5 + 1 / 10) * (1 - σ) = (5 : ℝ) / 2 * (1 - σ) := by ring
        rw [hscale] at hnp
        refine le_trans hnp ?_
        refine rpow_le_expHeight_mul (σ := σ) hq hT (le_of_lt hCNP) hCNPle ?_ ?_
        · linarith
        · have h1m : 1 - σ ≤ 1 / 5 := by linarith
          nlinarith
      calc Work.LinnikAreas.zeroCountIn (1 : DirichletCharacter ℂ q) σ T
              + ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
                  Work.LinnikAreas.zeroCountIn χ σ T
          ≤ Cf * Real.exp ((5 / 2) * ((1 - σ) * Real.log q)) * T ^ ((3 : ℝ) / 2)
            + Cf * Real.exp ((5 / 2) * ((1 - σ) * Real.log q)) * T ^ ((3 : ℝ) / 2) :=
            add_le_add hprin hnon
        _ = (2 * Cf) * Real.exp ((5 / 2) * ((1 - σ) * Real.log q)) * T ^ ((3 : ℝ) / 2) := by
            ring
    · -- ## `2/5 ≤ σ ≤ 4/5`: Huxley's `12/5` at `ε = 1/10`
      have h := hHb q hq σ T hσ0 hB hT
      have hscale : ((12 : ℝ) / 5 + 1 / 10) * (1 - σ) = (5 : ℝ) / 2 * (1 - σ) := by ring
      rw [hscale] at h
      refine le_trans h ?_
      refine le_trans (rpow_le_expHeight_mul (σ := σ) hq hT (le_of_lt hCH) hCHle ?_ ?_) ?_
      · linarith
      · have h1m : 1 - σ ≤ 3 / 5 := by linarith
        nlinarith
      · exact key Cf le_rfl

end

end Work.LinnikAreas
