import Mathlib

/-!
# `Work.CNum.SerCorePlan` — the elementary route to the `serUp` core inequality

The analytic core inequality behind the `serUp` certificate is

  `∑_{J=1}^{44} max (A_J) (B_J) ≤ R^90/(2(1-R²)) - R^135/(3(1-R³))`,  `R = c + ρ`,

where

  `A_J = log (1 - c^J + (R^J - c^J)) - log (1 - c^J + (45-J) R^{J-1} ρ)`,
  `B_J = log (1 + c^J + (R^J - c^J)) - log (1 + c^J + (45-J) R^{J-1} ρ)`.

On the full range `0 < c < R < 1`, `ρ < c` this is true but delicate (the certificate needs
`R ≤ 4/5` and `ρ ≤ 1/1000` anyway — both hold for every box of the `C` certificate).  With these
two extra hypotheses the inequality becomes **elementary**, by a first-order pairing:

* Step 1 (`log x - log y ≤ (x-y)/y` for `y > 0`) and
  `R^J - c^J ≤ J R^{J-1} ρ` (geometric sum, `c ≤ R`) give, with
  `Δ_J := (2J-45) R^{J-1} ρ`:

    `A_J ≤ Δ_J / yA_J`,  `yA_J = 1 - c^J + (45-J) R^{J-1} ρ`,
    `B_J ≤ Δ_J / yB_J`,  `yB_J = 1 + c^J + (45-J) R^{J-1} ρ`.

* Step 2: for `J ≥ 23` (`Δ_J ≥ 0`), `yA_J, yB_J ≥ 1 - c^J ≥ 1 - R^J`, hence
  `max (A_J) (B_J) ≤ Δ_J / (1 - R^J)`; for `J ≤ 22` (`Δ_J ≤ 0`),
  `yA_J, yB_J ≤ 1 + R^J + 45ρ`, hence `max (A_J) (B_J) ≤ Δ_J / (1 + R^J + 45ρ)`.

* Step 3 (pairing `J ↔ 45-J`, `1 ≤ J ≤ 22`): the two bounds add up to
  `(45-2J) R^{44-J} ρ / (1 - R^{45-J}) - (45-2J) R^{J-1} ρ / (1 + R^J + 45ρ) ≤ 0`,
  which is equivalent to `R^{45-2J} (1 + R^J + 45ρ) ≤ 1 - R^{45-J}`.

  This holds for `R ≤ 4/5`, `ρ ≤ 1/1000`: the left side is monotone in `R` and `ρ`, so it suffices
  at `R = 4/5`, `ρ = 1/1000` (a finite rational check, `22` values of `J`); numerically the worst
  case is `J = 22`, where `0.848 < 1`.

* Step 4: summing the `22` pairs gives `∑_{J=1}^{44} max (A_J) (B_J) ≤ 0 ≤ R^90/(2(1-R²)) -
  R^135/(3(1-R³))` (the right side is nonnegative for `0 < R < 1`).

The final statement to prove is `Work.CNum.SerCoreIneqR`.

In the application (`SerUpSpecR`) the two extra hypotheses are instantiated at
`c = ‖spt x y‖`, `ρ = m2r e`, `R = c + ρ = srad x y e`, where they follow from
`Work.CNum.BoxOK.sigma_le_real` (`c + ρ ≤ 79/100 ≤ 4/5`) and `Work.CNum.BoxOK.e_le_real`
(`ρ ≤ 10⁻⁶ ≤ 1/1000`).
-/

namespace Work.CNum

/-- The first-order coefficient `Δ_J = (2J-45) R^{J-1} ρ` (`R = c + ρ`). -/
noncomputable def serDelta (R ρ : ℝ) (J : ℕ) : ℝ := (2 * (J : ℝ) - 45) * R ^ (J - 1) * ρ

end Work.CNum
