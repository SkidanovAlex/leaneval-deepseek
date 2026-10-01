import Mathlib
import Submission.Work.LinnikAreas.LogFreeAux.logFreeNP93
import Submission.Work.LinnikAreas.principalCountIn_le_rpow

/-!
# `famCount_nearLine` — the near-line family zero count in the Siegel-absorption normalisation

For `σ` in the near-line range `93/100 ≤ σ ≤ 1` and `T ≥ 1`, the family zero count
`Σ_{χ mod q} N(σ,T,χ)` is at most `C · e^{(5/2)(1-σ)𝓛} · T^{3/2}`, `𝓛 = log q`.

This is the `T^{3/2}` (i.e. `c' = 3/2`) family count that the Siegel-absorption route of Area 6
consumes: it is proved by splitting off the principal character,

* `Σ'_{χ ≠ 1} N(σ,T,χ) ≤ C₁ (qT)^{(12/5)(1-σ)}` — `logFreeNP (93/100) (12/5)`;
* `N(σ,T,1) ≤ C₂ T^{3/2}` — `principalCountIn_le_rpow` (zeros of `ζ`),

and then using `(12/5)(1-σ) ≤ 5/2(1-σ)` and `(12/5)(1-σ) ≤ 3/2` (the latter because `1-σ ≤ 7/100`
on the range) together with `T ≥ 1`, `q ≥ 1` and `q^{5/2(1-σ)} = e^{(5/2)(1-σ)𝓛}`.
-/

namespace Work.SiegelAbsorb

/-- The family zero count is the non-principal part plus the principal character. -/
lemma famCount_eq_famCountNP_add_zCount_one (q : ℕ) [NeZero q] (σ T : ℝ) :
    Work.ZeroDensity.famCount q σ T
      = Work.ZeroDensity.LogFree.famCountNP q σ T
        + Work.ZeroDensity.zCount (1 : DirichletCharacter ℂ q) σ T := by
  rw [Work.ZeroDensity.famCount, Work.ZeroDensity.LogFree.famCountNP,
    ← Finset.sum_erase_add _ _ (Finset.mem_univ (1 : DirichletCharacter ℂ q))]

theorem famCount_nearLine :
    ∃ C : ℝ, 0 < C ∧ ∀ q : ℕ, 2 ≤ q → ∀ [NeZero q] (σ T : ℝ), 93 / 100 ≤ σ → σ ≤ 1 → 1 ≤ T →
      Work.ZeroDensity.famCount q σ T
        ≤ C * Real.exp ((5 / 2) * ((1 - σ) * Real.log q)) * T ^ (3 / 2 : ℝ) := by
  obtain ⟨C₁, hC₁, hnp⟩ := Work.LinnikAreas.LogFreeAux.logFreeNP_93_100_clean
  obtain ⟨C₂, hC₂, hprin⟩ := Work.LinnikAreas.principalCountIn_le_rpow
  refine ⟨C₁ + C₂, by linarith, ?_⟩
  intro q hq _inst σ T hσ93 hσ1 hT
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by
    have : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
    linarith
  have hqpos : (0 : ℝ) < (q : ℝ) := by linarith
  have hTpos : (0 : ℝ) < T := by linarith
  have hσ0 : (0 : ℝ) ≤ σ := by linarith
  have h1σ : (0 : ℝ) ≤ 1 - σ := by linarith
  have hlogq : (0 : ℝ) ≤ Real.log q := Real.log_nonneg hq1
  have hexpnn : (0 : ℝ) ≤ (5 / 2) * ((1 - σ) * Real.log q) :=
    mul_nonneg (by norm_num) (mul_nonneg h1σ hlogq)
  have hE1 : (1 : ℝ) ≤ Real.exp ((5 / 2) * ((1 - σ) * Real.log q)) := Real.one_le_exp hexpnn
  have hE0 : (0 : ℝ) ≤ Real.exp ((5 / 2) * ((1 - σ) * Real.log q)) := le_trans zero_le_one hE1
  have hT32 : (0 : ℝ) ≤ T ^ (3 / 2 : ℝ) := Real.rpow_nonneg (le_of_lt hTpos) _
  -- the non-principal part
  have hA : Work.ZeroDensity.LogFree.famCountNP q σ T
      ≤ C₁ * Real.exp ((5 / 2) * ((1 - σ) * Real.log q)) * T ^ (3 / 2 : ℝ) := by
    have ha := hnp q hq σ T hσ93 hσ1 hT
    have hpow : ((q : ℝ) * T) ^ ((12 / 5) * (1 - σ))
        ≤ Real.exp ((5 / 2) * ((1 - σ) * Real.log q)) * T ^ (3 / 2 : ℝ) := by
      rw [Real.mul_rpow (le_of_lt hqpos) (le_of_lt hTpos)]
      have hqa : (q : ℝ) ^ ((12 / 5) * (1 - σ))
          ≤ (q : ℝ) ^ ((5 / 2) * (1 - σ)) :=
        Real.rpow_le_rpow_of_exponent_le hq1 (by nlinarith [h1σ])
      have hTa : T ^ ((12 / 5) * (1 - σ)) ≤ T ^ (3 / 2 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hT (by nlinarith [hσ93])
      have hqE : (q : ℝ) ^ ((5 / 2) * (1 - σ))
          = Real.exp ((5 / 2) * ((1 - σ) * Real.log q)) := by
        rw [Real.rpow_def_of_pos hqpos]
        congr 1
        ring
      calc (q : ℝ) ^ ((12 / 5) * (1 - σ)) * T ^ ((12 / 5) * (1 - σ))
          ≤ (q : ℝ) ^ ((5 / 2) * (1 - σ)) * T ^ (3 / 2 : ℝ) :=
            mul_le_mul hqa hTa (Real.rpow_nonneg (le_of_lt hTpos) _)
              (Real.rpow_nonneg hqpos.le _)
        _ = Real.exp ((5 / 2) * ((1 - σ) * Real.log q)) * T ^ (3 / 2 : ℝ) := by rw [hqE]
    calc Work.ZeroDensity.LogFree.famCountNP q σ T
        ≤ C₁ * ((q : ℝ) * T) ^ ((12 / 5) * (1 - σ)) := ha
      _ ≤ C₁ * (Real.exp ((5 / 2) * ((1 - σ) * Real.log q)) * T ^ (3 / 2 : ℝ)) :=
            mul_le_mul_of_nonneg_left hpow hC₁.le
      _ = C₁ * Real.exp ((5 / 2) * ((1 - σ) * Real.log q)) * T ^ (3 / 2 : ℝ) := by ring
  -- the principal character
  have hB : Work.ZeroDensity.zCount (1 : DirichletCharacter ℂ q) σ T
      ≤ C₂ * Real.exp ((5 / 2) * ((1 - σ) * Real.log q)) * T ^ (3 / 2 : ℝ) := by
    have hb := hprin q hq σ T hσ0 hσ1 hT
    calc Work.ZeroDensity.zCount (1 : DirichletCharacter ℂ q) σ T
        ≤ C₂ * T ^ (3 / 2 : ℝ) := hb
      _ ≤ C₂ * Real.exp ((5 / 2) * ((1 - σ) * Real.log q)) * T ^ (3 / 2 : ℝ) := by
            have h2 : C₂ * T ^ (3 / 2 : ℝ)
                ≤ (C₂ * Real.exp ((5 / 2) * ((1 - σ) * Real.log q))) * T ^ (3 / 2 : ℝ) :=
              mul_le_mul_of_nonneg_right
                (by nlinarith [hC₂, hE1]) hT32
            linarith [h2]
  rw [famCount_eq_famCountNP_add_zCount_one]
  calc Work.ZeroDensity.LogFree.famCountNP q σ T
        + Work.ZeroDensity.zCount (1 : DirichletCharacter ℂ q) σ T
      ≤ (C₁ * Real.exp ((5 / 2) * ((1 - σ) * Real.log q)) * T ^ (3 / 2 : ℝ))
        + (C₂ * Real.exp ((5 / 2) * ((1 - σ) * Real.log q)) * T ^ (3 / 2 : ℝ)) :=
          add_le_add hA hB
    _ = (C₁ + C₂) * Real.exp ((5 / 2) * ((1 - σ) * Real.log q)) * T ^ (3 / 2 : ℝ) := by ring

end Work.SiegelAbsorb
