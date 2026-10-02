import Mathlib
import Submission.Work.ELNest.T_iterate_bAng

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.ELAssembly

open Filter
open scoped Topology

/-- The nest angle `bAng n = α₁ − (α₁ − β₀)/1024ⁿ` accumulates at `α₁`. -/
theorem tendsto_bAng : Tendsto (fun n : ℕ => Work.ELNest.bAng n) atTop (𝓝 Work.ELNest.alpha1) := by
  have hpow : Tendsto (fun n : ℕ => ((1024 : ℝ) ^ n)⁻¹) atTop (𝓝 0) :=
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 1024)).inv_tendsto_atTop
  have hlim : Tendsto (fun n : ℕ => (Work.ELNest.alpha1 - Work.ELNest.beta0) / (1024 : ℝ) ^ n)
      atTop (𝓝 0) := by
    have h := hpow.const_mul (Work.ELNest.alpha1 - Work.ELNest.beta0)
    simpa [div_eq_mul_inv] using h
  have hc : Tendsto (fun _ : ℕ => Work.ELNest.alpha1) atTop (𝓝 Work.ELNest.alpha1) :=
    tendsto_const_nhds
  have h := hc.sub hlim
  simpa only [Work.ELNest.bAng, sub_zero] using h

/-- The nest angle `bAng' n = α₂ + (β₀' − α₂)/1024ⁿ` accumulates at `α₂`. -/
theorem tendsto_bAng' : Tendsto (fun n : ℕ => Work.ELNest.bAng' n) atTop (𝓝 Work.ELNest.alpha2) := by
  have hpow : Tendsto (fun n : ℕ => ((1024 : ℝ) ^ n)⁻¹) atTop (𝓝 0) :=
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 1024)).inv_tendsto_atTop
  have hlim : Tendsto (fun n : ℕ => (Work.ELNest.beta0' - Work.ELNest.alpha2) / (1024 : ℝ) ^ n)
      atTop (𝓝 0) := by
    have h := hpow.const_mul (Work.ELNest.beta0' - Work.ELNest.alpha2)
    simpa [div_eq_mul_inv] using h
  have hc : Tendsto (fun _ : ℕ => Work.ELNest.alpha2) atTop (𝓝 Work.ELNest.alpha2) :=
    tendsto_const_nhds
  have h := hc.add hlim
  simpa only [Work.ELNest.bAng', add_zero] using h

/-- **The limit step that pins the `α`-pair down.**  Let `a, b : ℝ` with `α₁ ≤ a` and
`b ≤ α₂` (so that `S = (α₂ - b) + (a - α₁) ≥ 0`).  If for every `n`

  `1024 · ((β'_{n+1} - b) + (a - β_{n+1})) ≤ 2 · ((β'ₙ - b) + (a - βₙ))`,

then `a = α₁` and `b = α₂`.

Proof: `βₙ = α₁ - (α₁ - β₀)/1024ⁿ → α₁` and `β'ₙ = α₂ + (β₀' - α₂)/1024ⁿ → α₂`
(`(1024ⁿ)⁻¹ → 0`, `tendsto_pow_atTop_atTop_of_one_lt` + `tendsto_inv_atTop_zero`), so both sides
of the displayed inequality tend to `1024 · S` and `2 · S`; `le_of_tendsto_of_tendsto` gives
`1024 S ≤ 2 S`, i.e. `S ≤ 0`, and `S ≥ 0` forces `S = 0`, so both nonnegative summands vanish. -/
theorem limit_step_bAng {a b : ℝ} (h1 : Work.ELNest.alpha1 ≤ a) (h2 : b ≤ Work.ELNest.alpha2)
    (h : ∀ n : ℕ,
      (1024 : ℝ) * ((Work.ELNest.bAng' (n + 1) - b) + (a - Work.ELNest.bAng (n + 1)))
        ≤ 2 * ((Work.ELNest.bAng' n - b) + (a - Work.ELNest.bAng n))) :
    a = Work.ELNest.alpha1 ∧ b = Work.ELNest.alpha2 := by
  -- The two quantities that the summands measure.
  set S : ℝ := (Work.ELNest.alpha2 - b) + (a - Work.ELNest.alpha1) with hS
  set K : ℝ := (Work.ELNest.alpha1 - Work.ELNest.beta0)
    + (Work.ELNest.beta0' - Work.ELNest.alpha2) with hK
  -- The pair sums are `S + K/1024ⁿ`.
  have hident : ∀ n : ℕ,
      (Work.ELNest.bAng' n - b) + (a - Work.ELNest.bAng n) = S + K / 1024 ^ n := by
    intro n
    rw [hS, hK]
    simp only [Work.ELNest.bAng, Work.ELNest.bAng']
    ring_nf
  -- The displayed inequality collapses to `1022 S ≤ K/1024ⁿ`.
  have hbound : ∀ n : ℕ, (1022 : ℝ) * S ≤ K / 1024 ^ n := by
    intro n
    have hn := h n
    rw [hident (n + 1), hident n] at hn
    have hEq : (1024 : ℝ) * (K / 1024 ^ (n + 1)) = K / 1024 ^ n := by
      rw [pow_succ]
      field_simp
    linarith [hEq, hn]
  -- `S ≥ 0` from the hypotheses.
  have hSnn : 0 ≤ S := by rw [hS]; linarith
  -- Let `n → ∞`.
  have hlim : Tendsto (fun n : ℕ => K / 1024 ^ n) atTop (𝓝 0) := by
    have hpow : Tendsto (fun n : ℕ => ((1024 : ℝ) ^ n)⁻¹) atTop (𝓝 0) :=
      (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 1024)).inv_tendsto_atTop
    have h := hpow.const_mul K
    simpa [div_eq_mul_inv] using h
  have hle : (1022 : ℝ) * S ≤ 0 :=
    le_of_tendsto_of_tendsto tendsto_const_nhds hlim (Filter.Eventually.of_forall hbound)
  have hSle : S ≤ 0 := by linarith
  have hS0 : S = 0 := le_antisymm hSle hSnn
  have hsum : (Work.ELNest.alpha2 - b) + (a - Work.ELNest.alpha1) = 0 := by
    rw [← hS]; exact hS0
  exact ⟨by linarith, by linarith⟩

end Work.ELAssembly
