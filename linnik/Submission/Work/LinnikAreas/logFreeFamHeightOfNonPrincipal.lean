import Mathlib
import Submission.Work.ZeroDensity.Defs
import Submission.Work.ZeroDensity.Basic
import Submission.Work.LinnikAreas.Setup
import Submission.Work.ZeroDensity.Montgomery.inGhamZetaDensity
import Submission.Work.LinnikAreas.boxMaxZero
import Submission.Work.LinnikAreas.principalCountIn_le_rpow
import Submission.Work.LinnikAreas.rpow_le_expHeight_mul

namespace Work.LinnikAreas

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

open Work.ZeroDensity (famCount)

/-- **The log-free family height count `(5/2, 3/2)` from a non-principal Jutila-type input.**

Assume (i) the family zero density estimate `Σ_{χ ≠ 1} N(σ,T,χ) ≤ C_ε (qT)^{(2+ε)(1-σ)}` on
`4/5 ≤ σ ≤ 1` for the *non-principal* characters only, and (ii) Huxley's `12/5` family estimate
`FamDensityEpsRange 0 (4/5) (12/5)` (which includes the principal character).  Then
`Σ_χ N(σ,T,χ) ≤ C e^{(5/2)(1-σ)𝓛} T^{3/2}` for `0 ≤ σ ≤ 1`, `T ≥ 1`, `𝓛 = log q`, i.e.
`Work.ZeroDensity.LogFreeFamHeight (5/2) (3/2)`.

The three ranges of `σ` are handled by three different inputs:

* `σ ≤ 2/5`: the σ-blind family count `trivial_bound` gives `(qT)^{1+ε}`, and
  `1 + ε ≤ (5/2)(1-σ)` because `1 - σ ≥ 3/5`;
* `2/5 ≤ σ ≤ 4/5`: Huxley's `12/5` estimate at `ε = 1/10` gives exactly the exponent `(5/2)(1-σ)`,
  which is `≤ 3/2` since `1 - σ ≤ 3/5`;
* `σ ≥ 4/5`: the family sum splits into the principal character and the rest.  The non-principal
  part is the hypothesis (i) at `ε = 1/4`, whose exponent `(9/4)(1-σ)` is below both `(5/2)(1-σ)`
  and `3/2` (as `1 - σ ≤ 1/5`).  The principal character contributes `≪ T^{3/2}` uniformly in the
  level (`principalCountIn_le_rpow`), which is absorbed by the exponential factor since
  `q^{(5/2)(1-σ)} ≥ 1`.

Each estimate is then converted into the `λ`-units shape by `rpow_le_expHeight_mul`, which splits
`(qT)^e = q^e T^e` and absorbs the two factors into `e^{(5/2)(1-σ)𝓛}` and `T^{3/2}`. -/
theorem logFreeFamHeightOfNonPrincipal
    (hJ : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
      ∀ q : ℕ, 2 ≤ q → ∀ [NeZero q] (σ T : ℝ), (4 : ℝ) / 5 ≤ σ → σ ≤ 1 → 1 ≤ T →
        (∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
            Work.LinnikAreas.zeroCountIn χ σ T)
          ≤ C * ((q : ℝ) * T) ^ ((2 + ε) * (1 - σ)))
    (hH : Work.ZeroDensity.FamDensityEpsRange 0 (4/5) (12/5)) :
    Work.ZeroDensity.LogFreeFamHeight (5/2) (3/2) := by
  obtain ⟨CJ, hCJ, hJ'⟩ := hJ (1 / 4) (by norm_num)
  obtain ⟨CH, hCH, hH'⟩ := hH (1 / 10) (by norm_num)
  obtain ⟨CT, hCT, hT'⟩ := Work.ZeroDensity.trivial_bound (1 / 2) (by norm_num)
  obtain ⟨Cz, hCz, hz⟩ := principalCountIn_le_rpow
  set Cf : ℝ := max (max CT CH) (CJ + Cz) with hCf
  have hCfpos : 0 < Cf :=
    lt_of_lt_of_le hCT (le_trans (le_max_left _ _) (le_max_left _ _))
  have hCTle : CT ≤ Cf := by rw [hCf]; exact le_trans (le_max_left _ _) (le_max_left _ _)
  have hCHle : CH ≤ Cf := by rw [hCf]; exact le_trans (le_max_right _ _) (le_max_left _ _)
  have hCJle : CJ ≤ Cf := by
    rw [hCf]; exact le_trans (le_add_of_nonneg_right hCz.le) (le_max_right _ _)
  have hCzle : Cz ≤ Cf := by
    rw [hCf]; exact le_trans (le_add_of_nonneg_left hCJ.le) (le_max_right _ _)
  refine ⟨2 * Cf, by positivity, 2, ?_⟩
  intro q hq hqne σ T hσ0 hσ1 hT
  haveI : NeZero q := hqne
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by
    have : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
    linarith
  have hlogq : (0 : ℝ) ≤ Real.log (q : ℝ) := Real.log_nonneg hq1
  have hTpow : (0 : ℝ) ≤ T ^ ((3 : ℝ) / 2) := Real.rpow_nonneg (by linarith) _
  have hexp1 : (1 : ℝ) ≤ Real.exp ((5 / 2) * ((1 - σ) * Real.log q)) := by
    rw [Real.one_le_exp_iff]
    exact mul_nonneg (by norm_num) (mul_nonneg (by linarith) hlogq)
  -- the final constant is `2 * Cf`, so it suffices that every piece is `≤ Cf · e^{…} · T^{3/2}`
  have key : ∀ A : ℝ, A ≤ Cf →
      A * Real.exp ((5 / 2) * ((1 - σ) * Real.log q)) * T ^ ((3 : ℝ) / 2)
        ≤ (2 * Cf) * Real.exp ((5 / 2) * ((1 - σ) * Real.log q)) * T ^ ((3 : ℝ) / 2) := by
    intro A hA
    have h2 : A ≤ 2 * Cf := le_trans hA (by linarith)
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right h2 (Real.exp_nonneg _)) hTpow
  rcases le_total σ (2 / 5) with hA | hA
  · -- ## `σ ≤ 2/5`: the σ-blind family count
    refine le_trans (hT' q hq σ T hσ0 hσ1 hT) ?_
    refine le_trans (rpow_le_expHeight_mul (σ := σ) hq hT (le_of_lt hCT) hCTle ?_ ?_) ?_
    · have h1m : (3 : ℝ) / 5 ≤ 1 - σ := by linarith
      nlinarith
    · norm_num
    · exact key Cf le_rfl
  · rcases le_total (4 / 5) σ with hB | hB
    · -- ## `σ ≥ 4/5`: split off the principal character
      have hsplit : famCount q σ T
          = Work.LinnikAreas.zeroCountIn (1 : DirichletCharacter ℂ q) σ T
            + ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
                Work.LinnikAreas.zeroCountIn χ σ T := by
        rw [Work.ZeroDensity.famCount_eq_sum]
        exact (Finset.add_sum_erase Finset.univ
          (fun χ : DirichletCharacter ℂ q => Work.LinnikAreas.zeroCountIn χ σ T)
          (Finset.mem_univ 1)).symm
      rw [hsplit]
      -- the principal character: `≪ T^{3/2} ≤ e^{(5/2)(1-σ)𝓛} T^{3/2}`
      have hprin : Work.LinnikAreas.zeroCountIn (1 : DirichletCharacter ℂ q) σ T
          ≤ Cf * Real.exp ((5 / 2) * ((1 - σ) * Real.log q)) * T ^ ((3 : ℝ) / 2) := by
        refine le_trans (hz q hq σ T hσ0 hσ1 hT) ?_
        calc Cz * T ^ ((3 : ℝ) / 2) ≤ Cf * T ^ ((3 : ℝ) / 2) :=
              mul_le_mul_of_nonneg_right hCzle hTpow
          _ ≤ Cf * Real.exp ((5 / 2) * ((1 - σ) * Real.log q)) * T ^ ((3 : ℝ) / 2) :=
              mul_le_mul_of_nonneg_right
                (le_mul_of_one_le_right hCfpos.le hexp1) hTpow
      -- the non-principal characters: the Jutila-type input at `ε = 1/4`
      have hnon : (∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
              Work.LinnikAreas.zeroCountIn χ σ T)
          ≤ Cf * Real.exp ((5 / 2) * ((1 - σ) * Real.log q)) * T ^ ((3 : ℝ) / 2) := by
        refine le_trans (hJ' q hq σ T hB hσ1 hT) ?_
        refine rpow_le_expHeight_mul (σ := σ) hq hT (le_of_lt hCJ) hCJle ?_ ?_
        · have h2 : (2 : ℝ) + 1 / 4 ≤ 5 / 2 := by norm_num
          exact mul_le_mul_of_nonneg_right h2 (by linarith)
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
    · -- ## `2/5 ≤ σ ≤ 4/5`: Huxley's `12/5` family estimate
      refine le_trans (hH' q hq σ T hσ0 hB hT) ?_
      refine le_trans (rpow_le_expHeight_mul (σ := σ) hq hT (le_of_lt hCH) hCHle ?_ ?_) ?_
      · have h2 : (12 : ℝ) / 5 + 1 / 10 ≤ 5 / 2 := by norm_num
        exact mul_le_mul_of_nonneg_right h2 (by linarith)
      · have h1m : 1 - σ ≤ 3 / 5 := by linarith
        nlinarith
      · exact key Cf le_rfl

end

end Work.LinnikAreas
