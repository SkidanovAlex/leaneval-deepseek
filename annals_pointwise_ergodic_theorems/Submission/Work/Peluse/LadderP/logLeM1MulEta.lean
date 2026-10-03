import Mathlib
import Submission.Work.Peluse.LadderP.stepPState

/-!
# Absorbing the `log`-factor into `M₁ · η` in the ladder one-step lemma

The one-step lemma of the power-loss ladder is stated with a right-hand side
`C * (M₁ * η + Real.log (j + 2))`: the geometrical losses produced by the ladder step are paid by
the *state* `M₁ * η`, while `Real.log (j + 2)` is exactly the (logarithmically growing) factor that
accumulates over the `j` steps.  Turning that sum into a *single* term `M₁ * η` requires a lower
bound for the state in terms of the logarithm, which is what this file provides.

The data are the ones fixed by the ladder constructor:

* `γ = u ^ (2 ^ (2 ^ (j+1) - 1 + n)) / 4` is the (one-step) geometrical loss attached to the state
  at level `j`, with `0 < u ≤ 1`;
* `η = cη * γ ^ (2 * e₅₁)` is the state increment, `cη > 0`;
* `e` is the exponent of the non-degeneracy hypothesis
  `(M₁ L)^e ≤ C (u D)^e L`, and `e₅₁` the number of `U²`-norm increments at the level `2` step;
  the hypothesis `2 ^ (2 ^ (j+1) - 1 + n + 1) * e₅₁ + 1 ≤ e` is exactly
  `2 (2 ^ (2 ^ (j+1) - 1 + n)) e₅₁ < e`, i.e. the loss exponent `2 ^ (2 ^ (j+1) - 1 + n) * (2 e₅₁)`
  is (strictly) dominated by `e`;
* `D ≤ M₁ L` and `L ≥ 2` so that the non-degeneracy hypothesis is genuinely *non-degenerate*;
* `C * Real.log (j + 2) ≤ cη / 4 ^ (2 e₅₁)` is the logarithm-absorption threshold on the constant.

The proof is the chain

  `1 ≤ C u^e L ≤ C u^{2^K (2 e₅₁)} M₁ = C M₁ (4 γ)^{2 e₅₁} = C M₁ 4^{2 e₅₁} γ^{2 e₅₁}`

(`u^e ≤ u^{2^K (2 e₅₁)}` because `0 < u ≤ 1` and the exponent `2^K (2 e₅₁)` is below `e`), whence
`1 / (C 4^{2 e₅₁}) ≤ M₁ γ^{2 e₅₁}`; multiplying the threshold `C * Real.log (j + 2) ≤ cη / 4^{2 e₅₁}`
by `1/C` and by the positivity of `cη` gives the claim.
-/

namespace Work.Peluse.LadderP

/-- In the ladder one-step datum the state `M₁ * η` dominates `Real.log (j + 2)`, so the
logarithmic factor of the loss can be absorbed into the state. -/
theorem logLeM1MulEta (j n M₁ : ℕ) (hM₁ : 1 ≤ M₁) (L D : ℕ) {u γ η : ℝ} {e e₅₁ : ℕ}
    {C cη : ℝ} (hC : 0 < C) (hcη : 0 < cη) (he₅₁ : 1 ≤ e₅₁)
    (hγ : γ = u ^ (2 ^ (2 ^ (j+1) - 1 + n)) / 4)
    (hη : η = cη * γ ^ (2 * e₅₁))
    (hu0 : 0 < u) (hu1 : u ≤ 1) (hL2 : 2 ≤ L) (hLM : L ≤ M₁)
    (hege : 2 ^ (2 ^ (j+1) - 1 + n + 1) * e₅₁ + 1 ≤ e)
    (hDle : (D : ℝ) ≤ (M₁ : ℝ) * (L : ℝ))
    (hnondeg : ((M₁ : ℝ) * (L : ℝ)) ^ e ≤ C * (u * (D : ℝ)) ^ e * (L : ℝ))
    (hlogconst : C * Real.log ((j : ℝ) + 2) ≤ cη / 4 ^ (2 * e₅₁)) :
    Real.log ((j : ℝ) + 2) ≤ (M₁ : ℝ) * η := by
  -- Positivity of the elementary quantities.
  have hLpos : (0:ℝ) < (L:ℝ) := by exact_mod_cast (by omega : 0 < L)
  have hM1pos : (0:ℝ) < (M₁:ℝ) := by exact_mod_cast hM₁
  have hApos : 0 < (M₁:ℝ)*(L:ℝ) := mul_pos hM1pos hLpos
  have hAepos : 0 < ((M₁:ℝ)*(L:ℝ))^e := pow_pos hApos e
  -- ## Step 1: the non-degeneracy hypothesis gives `1 ≤ C u^e L`.
  have huDnonneg : (0:ℝ) ≤ u * (D:ℝ) := by positivity
  have hDle' : u * (D:ℝ) ≤ u * ((M₁:ℝ)*(L:ℝ)) :=
    mul_le_mul_of_nonneg_left hDle (le_of_lt hu0)
  have hpow : (u * (D:ℝ))^e ≤ (u * ((M₁:ℝ)*(L:ℝ)))^e :=
    pow_le_pow_left₀ huDnonneg hDle' e
  have hstep : ((M₁:ℝ)*(L:ℝ))^e ≤ C * (u * ((M₁:ℝ)*(L:ℝ)))^e * (L:ℝ) := by
    calc ((M₁:ℝ)*(L:ℝ))^e ≤ C * (u*(D:ℝ))^e * (L:ℝ) := hnondeg
      _ ≤ C * (u*((M₁:ℝ)*(L:ℝ)))^e * (L:ℝ) := by
            have h1 : C * (u*(D:ℝ))^e ≤ C * (u*((M₁:ℝ)*(L:ℝ)))^e :=
              mul_le_mul_of_nonneg_left hpow (le_of_lt hC)
            exact mul_le_mul_of_nonneg_right h1 (le_of_lt hLpos)
  have hstep' : ((M₁:ℝ)*(L:ℝ))^e ≤ (C * u^e * (L:ℝ)) * ((M₁:ℝ)*(L:ℝ))^e := by
    calc ((M₁:ℝ)*(L:ℝ))^e ≤ C * (u*((M₁:ℝ)*(L:ℝ)))^e * (L:ℝ) := hstep
      _ = (C * u^e * (L:ℝ)) * ((M₁:ℝ)*(L:ℝ))^e := by rw [mul_pow]; ring
  have h1 : 1 ≤ C * u^e * (L:ℝ) := by
    have h' : (1:ℝ) * ((M₁:ℝ)*(L:ℝ))^e ≤ (C * u^e * (L:ℝ)) * ((M₁:ℝ)*(L:ℝ))^e := by
      simpa using hstep'
    exact le_of_mul_le_mul_right h' hAepos
  -- ## Step 2: the exponent `2 ^ (2^(j+1)-1+n) * (2 e₅₁)` is below `e`.
  have hK2 : 2 ^ (2 ^ (j+1) - 1 + n) * (2 * e₅₁) ≤ e := by
    have h := hege
    rw [pow_succ] at h
    rw [← Nat.mul_assoc]
    exact Nat.le_of_succ_le h
  have hue : u ^ e ≤ u ^ (2 ^ (2 ^ (j+1) - 1 + n) * (2 * e₅₁)) :=
    pow_le_pow_of_le_one (le_of_lt hu0) hu1 hK2
  have hLcast : (L:ℝ) ≤ (M₁:ℝ) := by exact_mod_cast hLM
  have hkey : 1 ≤ C * u ^ (2 ^ (2 ^ (j+1) - 1 + n) * (2 * e₅₁)) * (M₁:ℝ) := by
    have hCu : C * u^e ≤ C * u^(2^(2^(j+1)-1+n) * (2*e₅₁)) :=
      mul_le_mul_of_nonneg_left hue (le_of_lt hC)
    calc (1:ℝ) ≤ C * u^e * (L:ℝ) := h1
      _ ≤ C * u^(2^(2^(j+1)-1+n)*(2*e₅₁)) * (L:ℝ) :=
          mul_le_mul_of_nonneg_right hCu (le_of_lt hLpos)
      _ ≤ C * u^(2^(2^(j+1)-1+n)*(2*e₅₁)) * (M₁:ℝ) :=
          mul_le_mul_of_nonneg_left hLcast (by positivity)
  -- ## Step 3: rewrite `u ^ (2^(...) * (2 e₅₁))` in terms of `γ`.
  have h4g : 4 * γ = u ^ (2 ^ (2 ^ (j+1) - 1 + n)) := by
    rw [hγ]; ring
  have hP : (4:ℝ) ^ (2*e₅₁) * γ ^ (2*e₅₁) = u ^ (2 ^ (2 ^ (j+1) - 1 + n) * (2*e₅₁)) := by
    rw [← mul_pow, h4g, ← pow_mul]
  have hkey2 : 1 ≤ C * (M₁:ℝ) * ((4:ℝ)^(2*e₅₁) * γ^(2*e₅₁)) := by
    rw [hP]
    calc (1:ℝ) ≤ C * u^(2^(2^(j+1)-1+n)*(2*e₅₁)) * (M₁:ℝ) := hkey
      _ = C * (M₁:ℝ) * u^(2^(2^(j+1)-1+n)*(2*e₅₁)) := by ring
  have hC4 : 0 < C * (4:ℝ)^(2*e₅₁) := by positivity
  have hl : 1 / (C * (4:ℝ)^(2*e₅₁)) ≤ (M₁:ℝ) * γ^(2*e₅₁) := by
    rw [div_le_iff₀ hC4]
    calc (1:ℝ) ≤ C * (M₁:ℝ) * ((4:ℝ)^(2*e₅₁) * γ^(2*e₅₁)) := hkey2
      _ = (M₁:ℝ) * γ^(2*e₅₁) * (C * (4:ℝ)^(2*e₅₁)) := by ring
  -- ## Step 4: divide the logarithm threshold by `C` and multiply by the state bound.
  have hlog1 : Real.log ((j:ℝ)+2) ≤ (cη / 4^(2*e₅₁)) / C := by
    rw [le_div_iff₀ hC]
    calc Real.log ((j:ℝ)+2) * C = C * Real.log ((j:ℝ)+2) := by ring
      _ ≤ cη / 4^(2*e₅₁) := hlogconst
  have hlog : Real.log ((j:ℝ)+2) ≤ cη / (C * (4:ℝ)^(2*e₅₁)) := by
    calc Real.log ((j:ℝ)+2) ≤ (cη / 4^(2*e₅₁)) / C := hlog1
      _ = cη / (C * (4:ℝ)^(2*e₅₁)) := by rw [div_div]; ring_nf
  calc Real.log ((j:ℝ)+2) ≤ cη / (C * (4:ℝ)^(2*e₅₁)) := hlog
    _ = cη * (1 / (C * (4:ℝ)^(2*e₅₁))) := by rw [mul_one_div]
    _ ≤ cη * ((M₁:ℝ) * γ^(2*e₅₁)) := mul_le_mul_of_nonneg_left hl (le_of_lt hcη)
    _ = (M₁:ℝ) * η := by rw [hη]; ring

end Work.Peluse.LadderP
