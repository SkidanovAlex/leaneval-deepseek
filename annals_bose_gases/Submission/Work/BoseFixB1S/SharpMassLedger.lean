import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseFixB1S.WindowedGrouping.GroupingArith
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1S.SharpMassLedger` — the missing *arithmetic core* of FS `thm:smallbox`'s grouping

FS's proof of `thm:smallbox` (`final_v2.tex` 3960–4048) is a **grouping**: for
`n = m n' + n''` with the group densities in a window, the group bounds are summed and compared.
The *last* step of that comparison is already in the corpus — `Work.BoseFixB1S.groupingArith`
(`WindowedGrouping/GroupingArith.lean`, PROVED):

    ¼(s−μ)² + (1/18)·μ·(mρ') ≥ (1/40)·μ(ρ−μ)²/(ρ+μ) ,     ρ = mρ' + s ,

    (or the corpus `groupingArith`'s exact form)  with  `ρ' ≥ 2μ`, `0 ≤ s ≤ ρ'`.

What is **not** in the corpus is the pair of arithmetic steps that *produce* the two group
bounds in that shape.  They are recorded here (all three lemmas are pure real; `A` and `B` are
the two missing ones, `C` is the window comparison used by `B`):

* **(A)** the `n''`-group: substituting FS's sharp mass row `eq:w>g`
  (`M₂ ≥ M₁ + (1+ε)·D·χ`, `D = ĝω(0)`) into the `A₀`-form of `lm:appinteractionestimate`
  cancels the Bogoliubov payer `½(1+ε)D(n''/|B|)²χ` **exactly**, and the remainder completes
  the square against `M₁`:

        ½(M₂/V²)n² − (μ(n/V) + ¼(μ − n/V)²)M₁ − ½(1+ε)D(n/V)²χ
            = [¼(n/V − μ)²M₁ − ½μ²M₁] + (M₂ − M₁ − (1+ε)Dχ)·(n/V)²/2
          ≥ ¼(n/V − μ)²M₁ − ½μ²M₁ .

    (The identity is the whole content: **no** bound `M₂ ≥ 2M₁` is used — and indeed
    `M₂ ≥ 2M₁` is false for FS's kernels, `M₂ − 2M₁ = ∫(g+gω) − 2∫g = −∫g²/(v·(χ⋆χ)) < 0`;
    see `FINDING_LowCountWindowB1copy_audit.md` §4.)

* **(B)** the `m`-group: the `(1/8)(μ − ρ')²M₁` bound produced by `lm:appinteractionestimate`
  plus the mass law `M₁ ≥ K·a·χ` (`FS eq:w1>`) absorbs its `Cμaρ'χ` error row and sharpens to
  `(1/9)(μ − ρ')²M₁`, provided the window constant `C_n` and `K` satisfy the *frozen* condition
  `144·C·C_n ≤ (C_n − 1)²·K` (satisfiable by taking `C_n` large: `K` and `C` are FS's
  universal constants).

* **(C)** `(1/9)(μ − ρ')² ≥ (1/18)μρ'` for `ρ' ≥ 2μ` — the comparison that converts FS's
  `(1/9)(μ − n'/|B|)²∬w₁` into the `(1/18)μ(n'/|B|)∬w₁` of the grouping.

`groupingArith_mul` then carries `groupingArith` to the mass-weighted form that the state-level
ledger consumes.
-/

noncomputable section
open scoped Real BigOperators

namespace Work.BoseFixB1S

set_option autoImplicit false

/-- **(A) the `n''`-group: the sharp mass row `eq:w>g` cancels the Bogoliubov payer exactly.**

`V = |B|`, `D = ĝω(0)`, `χ = ∫χ_B²`, `M₂ = ∬w₂`, `M₁ = ∬w₁`, `n` the group count.  The
hypothesis `M₁ + (1+ε)Dχ ≤ M₂` is FS `eq:w>g`. -/
theorem sharpMassLedgerNdoublePrime {V μ M₁ M₂ D χ n ε : ℝ} (hV : V ≠ 0)
    (hrow : M₁ + (1 + ε) * D * χ ≤ M₂) :
    (1 / 4) * (n / V - μ) ^ 2 * M₁ - (1 / 2) * μ ^ 2 * M₁
      ≤ (1 / 2) * (M₂ / V ^ 2) * n ^ 2
        - (μ * (n / V) + (1 / 4) * (μ - n / V) ^ 2) * M₁
        - (1 / 2) * (1 + ε) * D * (n / V) ^ 2 * χ := by
  have hid : (1 / 2) * (M₂ / V ^ 2) * n ^ 2
        - (μ * (n / V) + (1 / 4) * (μ - n / V) ^ 2) * M₁
        - (1 / 2) * (1 + ε) * D * (n / V) ^ 2 * χ
      = ((1 / 4) * (n / V - μ) ^ 2 * M₁ - (1 / 2) * μ ^ 2 * M₁)
        + (M₂ - M₁ - (1 + ε) * D * χ) * ((n / V) ^ 2 / 2) := by
    field_simp
    ring
  rw [hid]
  have hsq : 0 ≤ (n / V) ^ 2 / 2 := by positivity
  have h0 : 0 ≤ M₂ - M₁ - (1 + ε) * D * χ := by linarith
  have := mul_nonneg h0 hsq
  linarith

/-- **(C)** `(1/9)(μ − ρ')² ≥ (1/18)μρ'` for `ρ' ≥ 2μ ≥ 0` (the grouping window). -/
theorem sharpMassLedgerGroupWindow {μ ρ' : ℝ} (hμ : 0 ≤ μ) (h2 : 2 * μ ≤ ρ') :
    (1 / 18) * μ * ρ' ≤ (1 / 9) * (μ - ρ') ^ 2 := by
  nlinarith [hμ, h2, mul_self_nonneg (ρ' - 2 * μ), mul_self_nonneg (2 * ρ' - μ)]

/-- **(B) the `m`-group: `(1/8)(μ − ρ')²M₁ − Cμaρ'χ ≥ (1/9)(μ − ρ')²M₁`.**

Inputs: the mass law `M₁ ≥ K·a·χ` (FS `eq:w1>`, `K` a universal constant) and the frozen
window discipline `144·C·C_n ≤ (C_n − 1)²·K` (satisfiable by taking `C_n` large).  `C_nμ ≤ ρ'`
is the *group window* (`ρ' = n'/|B|`), `ρ' ≤ 2C_nμ` FS's "both `n'` and `n''` are less than
`(C_n+1)μ|B| ≤ 2C_nμ|B|`". -/
theorem sharpMassLedgerMgroup {μ a χ M₁ ρ' C C_n K : ℝ} (hC : 0 ≤ C) (hCn : 1 ≤ C_n)
    (hμ : 0 ≤ μ) (ha : 0 ≤ a) (hχ : 0 ≤ χ) (hK : 1 ≤ K) (hM₁ : K * a * χ ≤ M₁)
    (hlo : C_n * μ ≤ ρ') (hhi : ρ' ≤ 2 * C_n * μ)
    (hconst : 144 * C * C_n ≤ (C_n - 1) ^ 2 * K) :
    (1 / 9) * (μ - ρ') ^ 2 * M₁ ≤ (1 / 8) * (μ - ρ') ^ 2 * M₁ - C * μ * a * ρ' * χ := by
  have hM₁0 : 0 ≤ M₁ := le_trans (by positivity) hM₁
  have haχ : 0 ≤ a * χ := mul_nonneg ha hχ
  have hfac : 0 ≤ C * μ * a * χ := by positivity
  have hCn1 : 0 ≤ C_n - 1 := by linarith
  -- `ρ' - μ ≥ (C_n - 1) μ ≥ 0`
  have h1 : 0 ≤ (C_n - 1) * μ := mul_nonneg hCn1 hμ
  have h2 : (C_n - 1) * μ ≤ ρ' - μ := by linarith
  have hsq : (C_n - 1) ^ 2 * μ ^ 2 ≤ (ρ' - μ) ^ 2 := by
    have hB : (C_n - 1) * μ ≤ ρ' - μ := h2
    have hB0 : 0 ≤ ρ' - μ := le_trans h1 hB
    have hmul := mul_self_le_mul_self h1 hB
    have hsq' : ((C_n - 1) * μ) * ((C_n - 1) * μ) ≤ (ρ' - μ) * (ρ' - μ) := hmul
    nlinarith [hsq', hB0]
  -- (1) the `ρ' ≤ 2 C_n μ` error bound
  have herr1 : C * μ * a * ρ' * χ ≤ 2 * (C * C_n) * (μ ^ 2 * (a * χ)) := by
    have hmul := mul_le_mul_of_nonneg_left hhi hfac
    have heq : C * μ * a * χ * (2 * C_n * μ) = 2 * (C * C_n) * (μ ^ 2 * (a * χ)) := by ring
    have hgoal : C * μ * a * χ * ρ' ≤ C * μ * a * χ * (2 * C_n * μ) := hmul
    rw [heq] at hgoal
    have heq2 : C * μ * a * ρ' * χ = C * μ * a * χ * ρ' := by ring
    rw [heq2]
    exact hgoal
  -- (2) the frozen window discipline
  have hconst' : 2 * (C * C_n) ≤ (1 / 72) * ((C_n - 1) ^ 2 * K) := by linarith
  have hstep1 : 2 * (C * C_n) * (μ ^ 2 * (a * χ)) ≤
      (1 / 72) * ((C_n - 1) ^ 2 * K) * (μ ^ 2 * (a * χ)) :=
    mul_le_mul_of_nonneg_right hconst' (by positivity)
  -- (3) the mass law `K a χ ≤ M₁`
  have hstep2 : (1 / 72) * ((C_n - 1) ^ 2 * K) * (μ ^ 2 * (a * χ))
      ≤ (1 / 72) * (C_n - 1) ^ 2 * (μ ^ 2 * M₁) := by
    have hfac2 : 0 ≤ (1 / 72 : ℝ) * (C_n - 1) ^ 2 * μ ^ 2 := by positivity
    have hmul := mul_le_mul_of_nonneg_left hM₁ hfac2
    have e1 : (1 / 72 : ℝ) * (C_n - 1) ^ 2 * μ ^ 2 * (K * a * χ)
        = (1 / 72) * ((C_n - 1) ^ 2 * K) * (μ ^ 2 * (a * χ)) := by ring
    have e2 : (1 / 72 : ℝ) * (C_n - 1) ^ 2 * μ ^ 2 * M₁
        = (1 / 72) * (C_n - 1) ^ 2 * (μ ^ 2 * M₁) := by ring
    linarith [hmul, e1, e2]
  -- (4) the square comparison
  have hstep3 : (1 / 72) * (C_n - 1) ^ 2 * (μ ^ 2 * M₁) ≤ (1 / 72) * (ρ' - μ) ^ 2 * M₁ := by
    have hfac3 : 0 ≤ (1 / 72 : ℝ) * M₁ := by positivity
    have hmul := mul_le_mul_of_nonneg_right hsq hfac3
    have e1 : (1 / 72 : ℝ) * (C_n - 1) ^ 2 * (μ ^ 2 * M₁)
        = (C_n - 1) ^ 2 * μ ^ 2 * ((1 / 72 : ℝ) * M₁) := by ring
    have e2 : (1 / 72 : ℝ) * (ρ' - μ) ^ 2 * M₁
        = (ρ' - μ) ^ 2 * ((1 / 72 : ℝ) * M₁) := by ring
    linarith [hmul, e1, e2]
  have hmain : C * μ * a * ρ' * χ ≤ (1 / 72) * (ρ' - μ) ^ 2 * M₁ :=
    le_trans herr1 (le_trans hstep1 (le_trans hstep2 hstep3))
  have hsqeq : (μ - ρ') ^ 2 = (ρ' - μ) ^ 2 := by ring
  rw [hsqeq]
  linarith

/-- **`groupingArith` in the mass-weighted form consumed by the state-level ledger.** -/
theorem groupingArith_mul {μ ρ' s M₁ : ℝ} (m : ℕ) (hμ : 0 < μ) (h2 : 2 * μ ≤ ρ')
    (hs0 : 0 ≤ s) (hsρ : s ≤ ρ') (hM₁ : 0 ≤ M₁) :
    (1 / 40) * (μ * ((((m : ℝ) * ρ' + s) - μ) ^ 2 / (((m : ℝ) * ρ' + s) + μ))) * M₁
      ≤ ((1 / 4) * (s - μ) ^ 2 + (1 / 18) * μ * ((m : ℝ) * ρ')) * M₁ := by
  have h := groupingArith m hμ h2 hs0 hsρ
  exact mul_le_mul_of_nonneg_right h hM₁

end Work.BoseFixB1S
