import Mathlib
import Submission.Work.LinnikAreas.RestHighFree
import Submission.Work.LinnikAreas.siegelRestHigh
import Submission.Work.LinnikAreas.BGTZ

/-!
# `Work.LinnikAreas.RestHighFreeGen` — the `λ₁`-free far-height zero bound from a general
log-free family count `LogFreeFamHeight c₃ (3/2)` with `c₃ < 49/10`

`Work.LinnikAreas.RestHighFree` (`Submission/Work/LinnikAreas/RestHighFree.lean`) proves
`Siegel.RestHighFreeSpec (-3/2)` from the *specific* input `LogFreeFamHeight (5/2) (3/2)` — the
coefficient `5/2` obtained from Jutila + Huxley.  The present file extracts the general statement:
the whole far-height argument consumes the family count only through the Abel/kernel constants and
requires nothing of its coefficient `c₃` except `c₃ < 49/10` (the exponent of the kernel decay
`e^{-(49/10)λ}`).  In particular the *larger* coefficient `c₃ = 261/100 = 2.61 < 49/10`, which is
the one available from Jutila + Montgomery alone (no Huxley), suffices.

The proof is a verbatim re-run of `RestHighFree` with the constant `5/2` replaced by the parameter
`c₃`, using the (already proved) ingredient lemmas `pairCountHeight_le_famCount_scaled`,
`high_finset_bound_hi` of `Submission/Work/LinnikAreas/RestHighFree.lean`, all of which are stated
for a general coefficient `c < 49/10`.
-/

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

namespace Work.LinnikAreas

open Work.LinnikContract

set_option linter.unusedVariables false

/-- **The `λ₁`-free far-height bound from an arbitrary log-free family count.**  For any coefficient
`c₃ < 49/10`, the height log-free family count `LogFreeFamHeight c₃ (3/2)` gives
`Siegel.RestHighFreeSpec (-3/2)`, i.e. the high-zero (`|Im ρ| > 1`) part of the AREA 6 zero sum is
`≪ (log q)^{-3/2}` uniformly in the Siegel data.  The proof is that of `RestHighFree` with `5/2`
replaced by `c₃`; only `c₃ < 49/10` is used. -/
theorem RestHighFree_of_lt {c₃ : ℝ} (hc₃ : c₃ < 49 / 10)
    (hfam : Work.ZeroDensity.LogFreeFamHeight c₃ (3 / 2)) :
    Work.LinnikAreas.Siegel.RestHighFreeSpec (-3 / 2) := by
  obtain ⟨C₂, hC₂, q₀, hfam₀⟩ := hfam
  refine ⟨4 * C₂ * (Real.exp (max c₃ 0)
        * (1 - Real.exp (max c₃ 0 - 49 / 10))⁻¹)
      * ((2 : ℝ) ^ (3 / 2 : ℝ) * (1 - (2 : ℝ) ^ ((3 / 2 : ℝ) - 2))⁻¹) + 1, ?_,
    max (max q₀ 2) 3, ?_⟩
  · -- positivity of the constant
    have hD : 0 < Real.exp (max c₃ 0)
        * (1 - Real.exp (max c₃ 0 - 49 / 10))⁻¹ := by
      have h1 : Real.exp (max c₃ 0 - 49 / 10) < 1 := by
        rw [Real.exp_lt_one_iff]
        have h2 : max c₃ 0 < 49 / 10 := max_lt hc₃ (by norm_num)
        linarith
      positivity
    have hB : 0 < (2 : ℝ) ^ (3 / 2 : ℝ) * (1 - (2 : ℝ) ^ ((3 / 2 : ℝ) - 2))⁻¹ := by
      have h1 : (2 : ℝ) ^ ((3 / 2 : ℝ) - 2) < 1 := by
        have h2 : 1 < (2 : ℝ) ^ (2 - (3 / 2 : ℝ)) :=
          Real.one_lt_rpow (by norm_num) (by norm_num)
        rw [show (3 / 2 : ℝ) - 2 = -(2 - 3 / 2) by norm_num, Real.rpow_neg (by norm_num)]
        exact inv_lt_one_of_one_lt₀ h2
      positivity
    exact add_pos (mul_pos (mul_pos (mul_pos (by norm_num) hC₂) hD) hB) (by norm_num)
  · intro q hq hNq χ₁ β₁ hχ hsq hβ hz hlam
    have hq0 : q₀ ≤ q := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hq)
    have hq2 : 2 ≤ q := le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hq)
    have hq3 : 3 ≤ q := le_trans (le_max_right _ _) hq
    have hq1 : 1 < q := by omega
    have hlog : 0 < Real.log (q : ℝ) := Real.log_pos (by exact_mod_cast hq1)
    have hlog1 : 1 ≤ Real.log (q : ℝ) := by
      have h3 : (3 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq3
      have h4 : Real.log 3 ≤ Real.log q := Real.log_le_log (by norm_num) h3
      have h5 : 1 ≤ Real.log 3 := by
        have h6 := Real.log_le_log (Real.exp_pos 1) (le_of_lt Real.exp_one_lt_three)
        rwa [Real.log_exp] at h6
      linarith
    -- (1) the `λ₁`-free counting hypothesis in the shape consumed by the Abel summation
    have hcnt : ∀ t T : ℝ, 0 < t → t ≤ Real.log q → Real.log q ≤ T →
        Work.LinnikAreas.Siegel.pairCountHeight χ₁ β₁ t T
          ≤ C₂ * (Real.log q) ^ (-(3 / 2 : ℝ))
            * Real.exp (c₃ * t) * T ^ (3 / 2 : ℝ) :=
      fun t T ht htL hT => pairCountHeight_le_famCount_scaled (q := q) hq1 χ₁ β₁
        (fun σ T h1 h2 h3 => hfam₀ q hq0 σ T h1 h2 h3) ht htL hT
    have hlam1 : 0 < (Real.log q) ^ (-(3 / 2 : ℝ)) := Real.rpow_pos_of_pos hlog _
    -- (2) the finite-set bound
    let p : DirichletCharacter ℂ q × ℂ → Prop := fun z =>
      Work.LinnikContract.zeroMult z.1 z.2 ≠ 0 ∧ 1 < |z.2.im| ∧ ¬(z.1 = χ₁ ∧ z.2 = (β₁ : ℂ))
    let F : DirichletCharacter ℂ q × ℂ → ℝ := fun z =>
      if p z then (Work.LinnikContract.zeroMult z.1 z.2 : ℝ)
          * ‖Work.LinnikContract.Hk (11 / 2) (3 / 10) ((1 - z.2) * (Real.log q : ℂ))‖ else 0
    have hFnn : 0 ≤ F := fun z => by
      simp only [F]; split_ifs with hp
      · exact mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _)
      · exact le_refl 0
    have hFbound : ∀ u : Finset (DirichletCharacter ℂ q × ℂ), ∑ z ∈ u, F z
        ≤ 4 * C₂ * (Real.log q) ^ (-(3 / 2 : ℝ))
            * (Real.exp (max c₃ 0)
              * (1 - Real.exp (max c₃ 0 - 49 / 10))⁻¹)
            * ((2 : ℝ) ^ (3 / 2 : ℝ) * (1 - (2 : ℝ) ^ ((3 / 2 : ℝ) - 2))⁻¹)
            * (Real.log q) ^ ((3 / 2 : ℝ) - 2) := by
      intro u
      have hsum_eq : ∑ z ∈ u, F z = ∑ z ∈ u.filter p, F z := by
        refine (Finset.sum_subset (Finset.filter_subset _ _) ?_).symm
        intro z hz hnotin
        have hp : ¬ p z := fun hpp => hnotin (Finset.mem_filter.mpr ⟨hz, hpp⟩)
        simp only [F]; rw [if_neg hp]
      rw [hsum_eq]
      have hSF : ∑ z ∈ u.filter p, F z = ∑ z ∈ u.filter p,
          (Work.LinnikContract.zeroMult z.1 z.2 : ℝ)
            * ‖Work.LinnikContract.Hk (11 / 2) (3 / 10) ((1 - z.2) * (Real.log q : ℂ))‖ := by
        refine Finset.sum_congr rfl (fun z hz => ?_)
        have hp : p z := (Finset.mem_filter.mp hz).2
        simp only [F]; rw [if_pos hp]
      rw [hSF]
      exact high_finset_bound_hi hq1 χ₁ β₁ (C := C₂) (c := c₃) (c' := 3 / 2)
        (lam1 := (Real.log q) ^ (-(3 / 2 : ℝ))) hC₂ hlam1 hc₃ (by norm_num) hcnt
        (u.filter p) (fun z hz => (Finset.mem_filter.mp hz).2.1)
        (fun z hz => (Finset.mem_filter.mp hz).2.2.1)
        (fun z hz => (Finset.mem_filter.mp hz).2.2.2)
    have hsumm : Summable F := summable_of_sum_le hFnn hFbound
    have htsum : ∑' z : DirichletCharacter ℂ q × ℂ, F z
        ≤ 4 * C₂ * (Real.log q) ^ (-(3 / 2 : ℝ))
            * (Real.exp (max c₃ 0)
              * (1 - Real.exp (max c₃ 0 - 49 / 10))⁻¹)
            * ((2 : ℝ) ^ (3 / 2 : ℝ) * (1 - (2 : ℝ) ^ ((3 / 2 : ℝ) - 2))⁻¹)
            * (Real.log q) ^ ((3 / 2 : ℝ) - 2) :=
      Real.tsum_le_of_sum_le hFnn hFbound
    rw [Summable.tsum_prod hsumm] at htsum
    rw [tsum_fintype] at htsum
    have hEq : Siegel.restHighZeroSum χ₁ (β₁ : ℂ) (11 / 2) (3 / 10)
        = ∑ χ : DirichletCharacter ℂ q, ∑' ρ : ℂ, F (χ, ρ) := rfl
    rw [hEq]
    -- the exponent of the target is written `(-3)/2` in the statement, `-(3/2)` here
    rw [show ((-3 : ℝ) / 2) = -(3 / 2 : ℝ) by norm_num]
    refine le_trans htsum ?_
    -- (3) the closing arithmetic: `𝓛^{-3/2}·𝓛^{-1/2} = 𝓛^{-2} ≤ 𝓛^{-3/2}` (as `𝓛 ≥ 1`)
    have hprod : (Real.log q) ^ (-(3 / 2 : ℝ)) * (Real.log q) ^ ((3 / 2 : ℝ) - 2)
        = (Real.log q) ^ (-(2 : ℝ)) := by
      rw [← Real.rpow_add hlog]
      norm_num
    have hle : (Real.log q) ^ (-(2 : ℝ)) ≤ (Real.log q) ^ (-(3 / 2 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le hlog1 (by norm_num)
    have hnn : 0 ≤ 4 * C₂ * (Real.exp (max c₃ 0)
        * (1 - Real.exp (max c₃ 0 - 49 / 10))⁻¹)
        * ((2 : ℝ) ^ (3 / 2 : ℝ) * (1 - (2 : ℝ) ^ ((3 / 2 : ℝ) - 2))⁻¹) := by
      have hD : 0 ≤ Real.exp (max c₃ 0)
          * (1 - Real.exp (max c₃ 0 - 49 / 10))⁻¹ := by
        have h1 : Real.exp (max c₃ 0 - 49 / 10) < 1 := by
          rw [Real.exp_lt_one_iff]
          have h2 : max c₃ 0 < 49 / 10 := max_lt hc₃ (by norm_num)
          linarith
        positivity
      have hB : 0 ≤ (2 : ℝ) ^ (3 / 2 : ℝ) * (1 - (2 : ℝ) ^ ((3 / 2 : ℝ) - 2))⁻¹ := by
        have h1 : (2 : ℝ) ^ ((3 / 2 : ℝ) - 2) < 1 := by
          have h2 : 1 < (2 : ℝ) ^ (2 - (3 / 2 : ℝ)) :=
            Real.one_lt_rpow (by norm_num) (by norm_num)
          rw [show (3 / 2 : ℝ) - 2 = -(2 - 3 / 2) by norm_num, Real.rpow_neg (by norm_num)]
          exact inv_lt_one_of_one_lt₀ h2
        positivity
      exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hC₂.le) hD) hB
    rw [show 4 * C₂ * (Real.log q) ^ (-(3 / 2 : ℝ))
          * (Real.exp (max c₃ 0)
            * (1 - Real.exp (max c₃ 0 - 49 / 10))⁻¹)
          * ((2 : ℝ) ^ (3 / 2 : ℝ) * (1 - (2 : ℝ) ^ ((3 / 2 : ℝ) - 2))⁻¹)
          * (Real.log q) ^ ((3 / 2 : ℝ) - 2)
        = 4 * C₂ * (Real.exp (max c₃ 0)
            * (1 - Real.exp (max c₃ 0 - 49 / 10))⁻¹)
          * ((2 : ℝ) ^ (3 / 2 : ℝ) * (1 - (2 : ℝ) ^ ((3 / 2 : ℝ) - 2))⁻¹)
          * ((Real.log q) ^ (-(3 / 2 : ℝ)) * (Real.log q) ^ ((3 / 2 : ℝ) - 2)) by ring,
      hprod]
    have hscalar : 4 * C₂ * (Real.exp (max c₃ 0)
          * (1 - Real.exp (max c₃ 0 - 49 / 10))⁻¹)
          * ((2 : ℝ) ^ (3 / 2 : ℝ) * (1 - (2 : ℝ) ^ ((3 / 2 : ℝ) - 2))⁻¹)
        ≤ (4 * C₂ * (Real.exp (max c₃ 0)
            * (1 - Real.exp (max c₃ 0 - 49 / 10))⁻¹)
          * ((2 : ℝ) ^ (3 / 2 : ℝ) * (1 - (2 : ℝ) ^ ((3 / 2 : ℝ) - 2))⁻¹)) + 1 :=
      le_add_of_nonneg_right (by norm_num)
    exact le_trans (mul_le_mul_of_nonneg_left hle hnn)
      (mul_le_mul_of_nonneg_right hscalar hlam1.le)

/-- **The `λ₁`-free far-height bound from the Jutila + Montgomery family count.**  The coefficient
`c₃ = 261/100 = 2.61` (available from Jutila's theorem together with Montgomery's sharp large-sieve
estimate, without Huxley) satisfies `261/100 < 49/10`, so the general far-height argument applies
and the high-zero part of the AREA 6 zero sum is `≪ (log q)^{-3/2}` uniformly in the Siegel data. -/
theorem RestHighFreeGen (hfam : Work.ZeroDensity.LogFreeFamHeight ((261 : ℝ) / 100) (3 / 2)) :
    Work.LinnikAreas.Siegel.RestHighFreeSpec (-3 / 2) :=
  RestHighFree_of_lt (by norm_num) hfam

end Work.LinnikAreas
