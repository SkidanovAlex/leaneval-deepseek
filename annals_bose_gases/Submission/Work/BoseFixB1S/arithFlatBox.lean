import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseFixB1S.flatBranchDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB1S

/-- The `G`-comparison of the flat branch: with `σ := n/volA` (`n : ℕ`, `volA > 0`, `μ > 0`),
`G := ½·ψ(σ)·volA − ½μ²·volA − ½·n(n−1)/volA + μn`, where `ψ = psiWeight 1 μ σ`, satisfies
`G ≤ 5μ/2`.  Indeed `G = σ/2 − (n/2)(σ−μ)²/(μ+σ)`, and splitting on `σ ≤ 5μ` gives the claim. -/
theorem flatG_le {n : ℕ} {μ volA : ℝ} (hμ : 0 < μ) (hvol : 0 < volA) :
    (1 / 2) * Work.SmallBoxSliding.psiWeight 1 μ ((n : ℝ) / volA) * volA
      - (1 / 2) * μ ^ 2 * volA - (1 / 2) * ((n : ℝ) * ((n : ℝ) - 1)) / volA + μ * (n : ℝ)
      ≤ 5 * μ / 2 := by
  -- first rewrite `psiWeight 1 μ σ = μ(σ−μ)²/(μ+σ)`, with `σ = n/volA`
  have hψ : Work.SmallBoxSliding.psiWeight 1 μ ((n : ℝ) / volA)
      = μ * (((n : ℝ) / volA) - μ) ^ 2 / (μ + (n : ℝ) / volA) := by
    rw [Work.SmallBoxSliding.psiWeight, one_mul]
    have hden : 1 + (n : ℝ) / volA * μ⁻¹ = (μ + (n : ℝ) / volA) / μ := by
      field_simp
    rw [hden, div_div_eq_mul_div]
    ring
  have hσ0 : 0 ≤ (n : ℝ) / volA := by positivity
  have hd0 : 0 < μ + (n : ℝ) / volA := by positivity
  -- the replacement of `G` by `σ/2 − (n/2)(σ−μ)²/(μ+σ)`
  have hGid : (1 / 2) * Work.SmallBoxSliding.psiWeight 1 μ ((n : ℝ) / volA) * volA
      - (1 / 2) * μ ^ 2 * volA - (1 / 2) * ((n : ℝ) * ((n : ℝ) - 1)) / volA + μ * (n : ℝ)
      = ((n : ℝ) / volA) / 2 - ((n : ℝ) / 2) * (((n : ℝ) / volA) - μ) ^ 2 / (μ + (n : ℝ) / volA) := by
    rw [hψ]
    field_simp
    ring
  rw [hGid]
  by_cases hcase : 5 * μ ≤ (n : ℝ) / volA
  · -- `σ ≥ 5μ`: use `n ≥ 1` and `(σ−5μ)(μ+σ) ≤ (σ−μ)²`
    have hσgt : 0 < (n : ℝ) / volA := lt_of_lt_of_le (by linarith) hcase
    have hnpos : 0 < (n : ℝ) := (div_pos_iff_of_pos_right hvol).mp hσgt
    have hnpos_nat : 0 < n := by exact_mod_cast hnpos
    have hn1 : (1 : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast (show (1 : ℕ) ≤ n by omega)
    have h1 : ((n : ℝ) / volA - 5 * μ) * (μ + (n : ℝ) / volA) ≤ ((n : ℝ) / volA - μ) ^ 2 := by
      nlinarith [hμ, hσ0]
    have h2 : ((n : ℝ) / volA - μ) ^ 2 ≤ (n : ℝ) * ((n : ℝ) / volA - μ) ^ 2 := by
      nlinarith [sq_nonneg (((n : ℝ) / volA) - μ), hn1]
    have hpoly : ((n : ℝ) / volA - 5 * μ) * (μ + (n : ℝ) / volA)
        ≤ (n : ℝ) * ((n : ℝ) / volA - μ) ^ 2 := le_trans h1 h2
    have hhalf : (((n : ℝ) / volA) - 5 * μ) / 2
        ≤ ((n : ℝ) / 2) * (((n : ℝ) / volA) - μ) ^ 2 / (μ + (n : ℝ) / volA) := by
      rw [le_div_iff₀ hd0]
      nlinarith [hpoly]
    linarith
  · -- `σ ≤ 5μ`: the subtracted term is nonnegative, so `G ≤ σ/2 ≤ 5μ/2`
    push Not at hcase
    have h0 : 0 ≤ ((n : ℝ) / 2) * (((n : ℝ) / volA) - μ) ^ 2 / (μ + (n : ℝ) / volA) := by
      positivity
    linarith

/-- The `C`-comparison of the flat branch: with `W ≤ K·av·volA` (`W > 0`) and `br ≥ μ·av`,
`C ≥ 5K/2`, the quotient `C·br·volA/W` dominates `5μ/2`. -/
theorem flatC_le {μ volA W K av br C : ℝ} (hav : 0 < av) (hμ : 0 < μ) (hvol : 0 < volA)
    (hW : 0 < W) (hK : 0 ≤ K) (hC : 5 * K / 2 ≤ C) (hWK : W ≤ K * av * volA)
    (hbr : μ * av ≤ br) :
    5 * μ / 2 ≤ C * br * volA / W := by
  have hC0 : 0 ≤ C := by linarith
  have hbr0 : 0 ≤ br := le_trans (le_of_lt (mul_pos hμ hav)) hbr
  rw [le_div_iff₀ hW]
  have step1 : (5 * μ / 2) * W ≤ (5 * μ / 2) * (K * av * volA) :=
    mul_le_mul_of_nonneg_left hWK (by positivity)
  have step2 : (5 * μ / 2) * (K * av * volA) = (5 * K / 2) * (μ * av * volA) := by ring
  have step3 : (5 * K / 2) * (μ * av * volA) ≤ C * (μ * av * volA) :=
    mul_le_mul_of_nonneg_right hC (by positivity)
  have step4 : C * (μ * av * volA) ≤ C * (br * volA) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hbr (le_of_lt hvol)) hC0
  have step5 : C * (br * volA) = C * br * volA := by ring
  linarith [step1, step2, step3, step4, step5]

/-- **The pure-real core of the `Q = 0` (flat) branch.**  With `σ := n/volA` (`n : ℕ`),
`ψ := psiWeight 1 μ σ = μ(σ−μ)²/(μ+σ)`, `W ≤ K·av·volA` and `br ≥ μ·av`, the flat-branch
inequality closes with `C ≥ 5K/2`:
`½ψ·W·I − ½μ²·W·I − C·br·I ≤ ½(W/volA²)((nI)² − (nI)I)/I − μ(W/volA)(nI)`.
Both sides are `I` times a coefficient, so it suffices to prove the coefficient inequality
`½ψW − ½μ²W − C·br ≤ ½(W/volA²)n(n−1) − μWn/volA`; divide by `W/volA` (the cases `W = 0` and
`I = 0` are immediate) and reduce to `F ≤ C·br·volA/W` with
`F := volA(½ψ − ½(σ−μ)²) + σ/2`; then `F ≤ σ/2` (as `ψ ≤ (σ−μ)²`), and if `σ ≥ 5μ` then
`F = σ/2 − (n/2)(σ−μ)²/(μ+σ) ≤ σ/2 − ½(σ−μ)²/(μ+σ) ≤ 5μ/2` (using `n ≥ 1` and
`(σ−5μ)(μ+σ) ≤ (σ−μ)²`), while for `σ ≤ 5μ` we have `F ≤ σ/2 ≤ 5μ/2`.  Finally
`C·br·volA/W ≥ C·μ·av·volA/(K·av·volA) = Cμ/K ≥ 5μ/2`. -/
theorem arithFlatBox {n : ℕ} {μ volA W I K av br C : ℝ} (hav : 0 < av) (hμ : 0 < μ)
    (hvol : 0 < volA) (hW : 0 ≤ W) (hI : 0 ≤ I) (hK : 0 ≤ K)
    (hC : 5 * K / 2 ≤ C) (hWK : W ≤ K * av * volA) (hbr : μ * av ≤ br) :
    (1 / 2) * Work.SmallBoxSliding.psiWeight 1 μ ((n : ℝ) / volA) * W * I
        - (1 / 2) * μ ^ 2 * W * I - C * br * I
      ≤ (1 / 2) * (W / volA ^ 2) * ((((n : ℝ) * I) ^ 2 - ((n : ℝ) * I) * I)) / I
        - μ * (W / volA) * ((n : ℝ) * I) := by
  -- `C ≥ 0` and `br ≥ 0` (used to keep products nonnegative).
  have hC0 : 0 ≤ C := by linarith
  have hbr0 : 0 ≤ br := le_trans (le_of_lt (mul_pos hμ hav)) hbr
  -- **Step 1 (coefficient inequality).**  Discarding the common factor `I` we prove
  -- `A ≤ B` with `A := ½ψW − ½μ²W − C·br` and `B := ½(W/volA²)n(n−1) − μ(W/volA)n`.
  have hAB : (1 / 2) * Work.SmallBoxSliding.psiWeight 1 μ ((n : ℝ) / volA) * W
        - (1 / 2) * μ ^ 2 * W - C * br
      ≤ (1 / 2) * (W / volA ^ 2) * ((n : ℝ) * ((n : ℝ) - 1)) - μ * (W / volA) * (n : ℝ) := by
    by_cases hW0 : W = 0
    · -- `W = 0`: the inequality is `−C·br ≤ 0`.
      subst hW0
      have : 0 ≤ C * br := mul_nonneg hC0 hbr0
      simp only [mul_zero, zero_div]
      linarith
    · have hWpos : 0 < W := lt_of_le_of_ne hW (Ne.symm hW0)
      have hGle : (1 / 2) * Work.SmallBoxSliding.psiWeight 1 μ ((n : ℝ) / volA) * volA
            - (1 / 2) * μ ^ 2 * volA - (1 / 2) * ((n : ℝ) * ((n : ℝ) - 1)) / volA + μ * (n : ℝ)
          ≤ 5 * μ / 2 := flatG_le hμ hvol
      have h5C : 5 * μ / 2 ≤ C * br * volA / W :=
        flatC_le hav hμ hvol hWpos hK hC hWK hbr
      -- `B − A = C·br − (W/volA)·G`, where `G` is the left side of `hGle`; multiplying
      -- `G ≤ 5μ/2 ≤ C·br·volA/W` by `W/volA > 0` therefore gives `B − A ≥ 0`.
      have hkey : (W / volA) * ((1 / 2) * Work.SmallBoxSliding.psiWeight 1 μ ((n : ℝ) / volA) * volA
            - (1 / 2) * μ ^ 2 * volA - (1 / 2) * ((n : ℝ) * ((n : ℝ) - 1)) / volA + μ * (n : ℝ))
          ≤ C * br := by
        have h1 : (W / volA) * ((1 / 2) * Work.SmallBoxSliding.psiWeight 1 μ ((n : ℝ) / volA) * volA
              - (1 / 2) * μ ^ 2 * volA - (1 / 2) * ((n : ℝ) * ((n : ℝ) - 1)) / volA + μ * (n : ℝ))
            ≤ (W / volA) * (C * br * volA / W) :=
          mul_le_mul_of_nonneg_left (le_trans hGle h5C) (by positivity)
        have h2 : (W / volA) * (C * br * volA / W) = C * br := by
          field_simp
        linarith [h1, h2]
      have hid : (1 / 2) * (W / volA ^ 2) * ((n : ℝ) * ((n : ℝ) - 1)) - μ * (W / volA) * (n : ℝ)
            - ((1 / 2) * Work.SmallBoxSliding.psiWeight 1 μ ((n : ℝ) / volA) * W
                - (1 / 2) * μ ^ 2 * W - C * br)
          = C * br - (W / volA) * ((1 / 2) * Work.SmallBoxSliding.psiWeight 1 μ ((n : ℝ) / volA) * volA
              - (1 / 2) * μ ^ 2 * volA - (1 / 2) * ((n : ℝ) * ((n : ℝ) - 1)) / volA + μ * (n : ℝ)) := by
        field_simp
        ring
      linarith
  -- **Step 2 (clearing the `I`-divisions).**  Both sides are `I` times the corresponding
  -- coefficient; the identity below holds also at `I = 0` (both sides vanish).
  have hIeq2 : (1 / 2) * (W / volA ^ 2) * ((((n : ℝ) * I) ^ 2 - ((n : ℝ) * I) * I)) / I
      = I * ((1 / 2) * (W / volA ^ 2) * ((n : ℝ) * ((n : ℝ) - 1))) := by
    by_cases hI0 : I = 0
    · subst hI0; simp
    · field_simp
  calc (1 / 2) * Work.SmallBoxSliding.psiWeight 1 μ ((n : ℝ) / volA) * W * I
        - (1 / 2) * μ ^ 2 * W * I - C * br * I
      = I * ((1 / 2) * Work.SmallBoxSliding.psiWeight 1 μ ((n : ℝ) / volA) * W
            - (1 / 2) * μ ^ 2 * W - C * br) := by ring
    _ ≤ I * ((1 / 2) * (W / volA ^ 2) * ((n : ℝ) * ((n : ℝ) - 1)) - μ * (W / volA) * (n : ℝ)) :=
        mul_le_mul_of_nonneg_left hAB hI
    _ = (1 / 2) * (W / volA ^ 2) * ((((n : ℝ) * I) ^ 2 - ((n : ℝ) * I) * I)) / I
        - μ * (W / volA) * ((n : ℝ) * I) := by
        rw [hIeq2]; ring

end Work.BoseFixB1S
