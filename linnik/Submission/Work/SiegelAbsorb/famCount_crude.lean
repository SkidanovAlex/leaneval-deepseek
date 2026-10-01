import Mathlib
import Submission.Work.SiegelAbsorb.logFreeNP34
import Submission.Work.LinnikAreas.principalCountIn_le_rpow

namespace Work.SiegelAbsorb

/-- The family zero count splits into the non-principal part and the principal character. -/
theorem famCount_crude_split (q : ℕ) [NeZero q] (σ T : ℝ) :
    Work.ZeroDensity.famCount q σ T
      = Work.ZeroDensity.LogFree.famCountNP q σ T
        + Work.ZeroDensity.zCount (1 : DirichletCharacter ℂ q) σ T := by
  rw [Work.ZeroDensity.famCount, Work.ZeroDensity.LogFree.famCountNP,
    ← Finset.sum_erase_add _ _ (Finset.mem_univ (1 : DirichletCharacter ℂ q))]

/-- **The crude family zero count in the Siegel-absorption normalisation.**

For every `q ≥ 2`, every `0 ≤ σ ≤ 1` and every `T ≥ 1`, the family zero count
`Σ_{χ mod q} N(σ,T,χ)` is at most `C · e^{(9/2)(1-σ)𝓛} · T^{3/2}`, `𝓛 = log q`.

The proof splits off the principal character and glues two inputs:

* on the near-line range `σ ≥ 3/4` the non-principal part is bounded by the crude log-free
  estimate `logFreeNP (3/4) (9/2)` (`logFreeNP_34_nineHalves`) and the principal character by
  `T^{3/2}` (`principalCountIn_le_rpow`): here `T^{(9/2)(1-σ)} ≤ T^{3/2}` because `1-σ ≤ 1/4`;
* on `σ ≤ 3/4` the σ-blind bound `trivial_bound (1/8)`, `Σ_χ N(σ,T,χ) ≪ (qT)^{9/8}`, suffices:
  `9/8 ≤ (9/2)(1-σ)` and `9/8 ≤ 3/2`. -/
theorem famCount_crude :
    ∃ C : ℝ, 0 < C ∧ ∀ q : ℕ, 2 ≤ q → ∀ [NeZero q] (σ T : ℝ), 0 ≤ σ → σ ≤ 1 → 1 ≤ T →
      Work.ZeroDensity.famCount q σ T
        ≤ C * Real.exp ((9 / 2) * ((1 - σ) * Real.log q)) * T ^ (3 / 2 : ℝ) := by
  obtain ⟨C₁, hC₁, hnp⟩ := logFreeNP_34_nineHalves
  obtain ⟨C₂, hC₂, hprin⟩ := Work.LinnikAreas.principalCountIn_le_rpow
  obtain ⟨C₃, hC₃, htriv⟩ := Work.ZeroDensity.trivial_bound (1 / 8) (by norm_num)
  refine ⟨C₁ + C₂ + C₃, by linarith, ?_⟩
  intro q hq _inst σ T hσ0 hσ1 hT
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by
    have : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
    linarith
  have hqpos : (0 : ℝ) < (q : ℝ) := by linarith
  have hTpos : (0 : ℝ) < T := by linarith
  have hlogq : (0 : ℝ) ≤ Real.log q := Real.log_nonneg hq1
  have hT32 : (0 : ℝ) ≤ T ^ (3 / 2 : ℝ) := Real.rpow_nonneg hTpos.le _
  -- The near-line bound `σ ≥ 3/4`, the only case where the log-free estimate applies.
  have key : ∀ s : ℝ, 3 / 4 ≤ s → s ≤ 1 →
      Work.ZeroDensity.famCount q s T
        ≤ (C₁ + C₂ + C₃) * Real.exp ((9 / 2) * ((1 - s) * Real.log q))
            * T ^ (3 / 2 : ℝ) := by
    intro s hs hs1
    have hs0 : (0 : ℝ) ≤ s := by linarith
    have h1s : (0 : ℝ) ≤ 1 - s := by linarith
    have hexpnn : (0 : ℝ) ≤ (9 / 2) * ((1 - s) * Real.log q) :=
      mul_nonneg (by norm_num) (mul_nonneg h1s hlogq)
    have hE1 : (1 : ℝ) ≤ Real.exp ((9 / 2) * ((1 - s) * Real.log q)) := Real.one_le_exp hexpnn
    have hE0 : (0 : ℝ) ≤ Real.exp ((9 / 2) * ((1 - s) * Real.log q)) := le_trans zero_le_one hE1
    -- the non-principal part
    have hA : Work.ZeroDensity.LogFree.famCountNP q s T
        ≤ C₁ * Real.exp ((9 / 2) * ((1 - s) * Real.log q)) * T ^ (3 / 2 : ℝ) := by
      have ha := hnp q hq s T hs hs1 hT
      have hpow : ((q : ℝ) * T) ^ ((9 / 2) * (1 - s))
          ≤ Real.exp ((9 / 2) * ((1 - s) * Real.log q)) * T ^ (3 / 2 : ℝ) := by
        rw [Real.mul_rpow hqpos.le hTpos.le]
        have hqE : (q : ℝ) ^ ((9 / 2) * (1 - s))
            = Real.exp ((9 / 2) * ((1 - s) * Real.log q)) := by
          rw [Real.rpow_def_of_pos hqpos]
          congr 1
          ring
        have hTa : T ^ ((9 / 2) * (1 - s)) ≤ T ^ (3 / 2 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hT (by nlinarith [hs])
        rw [hqE]
        exact mul_le_mul_of_nonneg_left hTa (Real.exp_nonneg _)
      calc Work.ZeroDensity.LogFree.famCountNP q s T
          ≤ C₁ * ((q : ℝ) * T) ^ ((9 / 2) * (1 - s)) := ha
        _ ≤ C₁ * (Real.exp ((9 / 2) * ((1 - s) * Real.log q)) * T ^ (3 / 2 : ℝ)) :=
              mul_le_mul_of_nonneg_left hpow hC₁.le
        _ = C₁ * Real.exp ((9 / 2) * ((1 - s) * Real.log q)) * T ^ (3 / 2 : ℝ) := by ring
    -- the principal character
    have hB : Work.ZeroDensity.zCount (1 : DirichletCharacter ℂ q) s T
        ≤ C₂ * Real.exp ((9 / 2) * ((1 - s) * Real.log q)) * T ^ (3 / 2 : ℝ) := by
      have hb := hprin q hq s T hs0 hs1 hT
      have h2 : C₂ * T ^ (3 / 2 : ℝ)
          ≤ (C₂ * Real.exp ((9 / 2) * ((1 - s) * Real.log q))) * T ^ (3 / 2 : ℝ) :=
        mul_le_mul_of_nonneg_right (by nlinarith [hC₂, hE1]) hT32
      calc Work.ZeroDensity.zCount (1 : DirichletCharacter ℂ q) s T
          ≤ C₂ * T ^ (3 / 2 : ℝ) := hb
        _ ≤ C₂ * Real.exp ((9 / 2) * ((1 - s) * Real.log q)) * T ^ (3 / 2 : ℝ) := by
              linarith [h2]
    rw [famCount_crude_split]
    calc Work.ZeroDensity.LogFree.famCountNP q s T
          + Work.ZeroDensity.zCount (1 : DirichletCharacter ℂ q) s T
        ≤ (C₁ * Real.exp ((9 / 2) * ((1 - s) * Real.log q)) * T ^ (3 / 2 : ℝ))
          + (C₂ * Real.exp ((9 / 2) * ((1 - s) * Real.log q)) * T ^ (3 / 2 : ℝ)) :=
            add_le_add hA hB
      _ = (C₁ + C₂) * Real.exp ((9 / 2) * ((1 - s) * Real.log q)) * T ^ (3 / 2 : ℝ) := by ring
      _ ≤ (C₁ + C₂ + C₃) * Real.exp ((9 / 2) * ((1 - s) * Real.log q)) * T ^ (3 / 2 : ℝ) := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right (by linarith [hC₃]) hE0) hT32
  by_cases hge : (3 / 4 : ℝ) ≤ σ
  · exact key σ hge hσ1
  · -- `σ ≤ 3/4`: the σ-blind bound in the form `(qT)^{9/8}`
    have hlt : σ < 3 / 4 := not_le.mp hge
    have hpow : ((q : ℝ) * T) ^ ((1 : ℝ) + 1 / 8)
        ≤ Real.exp ((9 / 2) * ((1 - σ) * Real.log q)) * T ^ (3 / 2 : ℝ) := by
      have h89 : (1 : ℝ) + 1 / 8 = 9 / 8 := by norm_num
      rw [h89, Real.mul_rpow hqpos.le hTpos.le]
      have hEeq : Real.exp ((9 / 2) * ((1 - σ) * Real.log q))
          = (q : ℝ) ^ ((9 / 2) * (1 - σ)) := by
        rw [Real.rpow_def_of_pos hqpos]
        congr 1
        ring
      have hqE : (q : ℝ) ^ ((9 : ℝ) / 8)
          ≤ Real.exp ((9 / 2) * ((1 - σ) * Real.log q)) := by
        rw [hEeq]
        exact Real.rpow_le_rpow_of_exponent_le hq1 (by nlinarith [hlt])
      have hTa : T ^ ((9 : ℝ) / 8) ≤ T ^ (3 / 2 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hT (by norm_num)
      exact mul_le_mul hqE hTa (Real.rpow_nonneg hTpos.le _) (Real.exp_nonneg _)
    have hE0 : (0 : ℝ) ≤ Real.exp ((9 / 2) * ((1 - σ) * Real.log q)) := Real.exp_nonneg _
    calc Work.ZeroDensity.famCount q σ T
        ≤ C₃ * ((q : ℝ) * T) ^ ((1 : ℝ) + 1 / 8) := htriv q hq σ T hσ0 hσ1 hT
      _ ≤ C₃ * (Real.exp ((9 / 2) * ((1 - σ) * Real.log q)) * T ^ (3 / 2 : ℝ)) :=
            mul_le_mul_of_nonneg_left hpow hC₃.le
      _ = C₃ * Real.exp ((9 / 2) * ((1 - σ) * Real.log q)) * T ^ (3 / 2 : ℝ) := by ring
      _ ≤ (C₁ + C₂ + C₃) * Real.exp ((9 / 2) * ((1 - σ) * Real.log q)) * T ^ (3 / 2 : ℝ) :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right (by linarith [hC₁, hC₂]) hE0) hT32

end Work.SiegelAbsorb
