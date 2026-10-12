import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseB1Cube

/-- Pure real-arithmetic bookkeeping for the small-`Q` / small-weight branch of the cube
(`BoseFixB1*`) assembly.

Notation: `S` = flat (condensate) count, `Q` = excited count, `n = S + Q` the total count,
`Cn` the count constant (`Cn ≥ 4`), `Kg` the Bogoliubov gap coefficient (`Kg ≥ 60000 Cn`).

Given
* `Cn * μ * V ≤ n ≤ 2 * Cn * μ * V` (the count window) and `1 ≤ μ * V`,
* the small-weight bound `Q ≤ k * W * S / (2 * Kg * V * av)`,
* the mass bound `W ≤ 17 π av d79 V` with `d79 ≤ 1`, and `k ≤ 1.06`,

one concludes
* `Q ≤ 17 π k Cn (μ V) / Kg`  (the `Q`-column is controlled by the count window), and
* `S - 1 ≥ 2.99 μ V`  (hence `S` is comparable to `n`, i.e. the flat branch really is the
  dominant one — this is the "`S ⇝ n`" step).

Proof.  With `c := 17 π k / (2 Kg)` one has `c ≤ 1/6000` (from `17 π k ≤ 80` and
`Kg ≥ 60000 Cn ≥ 240000`).  From the hypotheses, `Q ≤ c * S` (using `W ≤ 17 π av V`), so
`n = S + Q ≤ (1 + c) S` and `S ≥ n/(1 + c) ≥ 4 μ V /(1 + c)`.  Since
`(2.99 μ V + 1)(1 + c) ≤ 4 μ V` (here `c ≤ 1/6000` and `1 ≤ μ V`), this gives
`S - 1 ≥ 2.99 μ V`.  The first claim is `Q ≤ c S ≤ c * 2 Cn μ V = 17 π k Cn (μ V)/Kg`. -/
theorem swhQBound {μ av V W S Q n Cn Kg k d79 : ℝ}
    (hμ : 0 < μ) (hav : 0 < av) (hV : 0 < V) (hW : 0 ≤ W) (hS : 0 ≤ S) (hQ : 0 ≤ Q)
    (hCn : 4 ≤ Cn) (hKg : 0 < Kg) (hk : 0 ≤ k) (hk1 : k ≤ 1.06)
    (hd79 : 0 ≤ d79) (hd1 : d79 ≤ 1)
    (hSQ : S + Q = n) (hng : Cn * μ * V ≤ n) (hn : n ≤ 2 * Cn * μ * V)
    (hμV : 1 ≤ μ * V)
    (hQsm : Q ≤ k * W * S / (2 * Kg * V * av))
    (hWup : W ≤ 17 * Real.pi * av * d79 * V)
    (hKgbig : 60000 * Cn ≤ Kg) :
    Q ≤ 17 * Real.pi * k * Cn * (μ * V) / Kg ∧ 2.99 * μ * V ≤ S - 1 := by
  -- `W ≤ 17 π av V` (drop the `d79 ≤ 1` factor)
  have hW17 : W ≤ 17 * Real.pi * av * V := by
    have hmono : 17 * Real.pi * av * d79 * V ≤ 17 * Real.pi * av * V := by
      have h := mul_le_mul_of_nonneg_left hd1 (show (0:ℝ) ≤ 17 * Real.pi * av * V by positivity)
      linarith [h]
    linarith [hWup, hmono]
  have hden : (0:ℝ) < 2 * Kg * V * av := by positivity
  -- multiply the small-weight bound by the (positive) `17 π av V`
  have hnum : k * W * S ≤ k * (17 * Real.pi * av * V) * S := by
    have hWS : W * S ≤ (17 * Real.pi * av * V) * S := mul_le_mul_of_nonneg_right hW17 hS
    calc k * W * S = k * (W * S) := by ring
      _ ≤ k * ((17 * Real.pi * av * V) * S) := mul_le_mul_of_nonneg_left hWS hk
      _ = k * (17 * Real.pi * av * V) * S := by ring
  have hstep : k * W * S / (2 * Kg * V * av) ≤ k * (17 * Real.pi * av * V) * S / (2 * Kg * V * av) :=
    div_le_div_of_nonneg_right hnum (le_of_lt hden)
  -- simplify the right-hand side: `c := 17 π k / (2 Kg)`
  have heq : k * (17 * Real.pi * av * V) * S / (2 * Kg * V * av)
      = (17 * Real.pi * k / (2 * Kg)) * S := by
    have e1 : k * (17 * Real.pi * av * V) * S / (2 * Kg * V * av)
        = 17 * Real.pi * k * S / (2 * Kg) := by
      rw [div_eq_div_iff (by positivity : (2 * Kg * V * av : ℝ) ≠ 0)
          (by positivity : (2 * Kg : ℝ) ≠ 0)]
      ring
    rw [e1]; ring
  have hQleS : Q ≤ (17 * Real.pi * k / (2 * Kg)) * S := by
    rw [heq] at hstep
    linarith
  have hc0 : (0:ℝ) ≤ 17 * Real.pi * k / (2 * Kg) := by positivity
  have hpos1 : (0:ℝ) < 1 + 17 * Real.pi * k / (2 * Kg) := by linarith
  have hSle : S ≤ n := by linarith
  have hSn : S ≤ 2 * Cn * (μ * V) := by
    have hh : (2:ℝ) * Cn * μ * V = 2 * Cn * (μ * V) := by ring
    linarith
  have hQn : Q ≤ (17 * Real.pi * k / (2 * Kg)) * (2 * Cn * (μ * V)) :=
    le_trans hQleS (mul_le_mul_of_nonneg_left hSn hc0)
  -- first conjunct
  have hclaim1 : Q ≤ 17 * Real.pi * k * Cn * (μ * V) / Kg := by
    calc Q ≤ (17 * Real.pi * k / (2 * Kg)) * (2 * Cn * (μ * V)) := hQn
      _ = 17 * Real.pi * k * Cn * (μ * V) / Kg := by ring
  -- the constant `c := 17 π k / (2 Kg)` is at most `1/6000`
  have hc_le : 17 * Real.pi * k / (2 * Kg) ≤ 1 / 6000 := by
    have hnumπ : 17 * Real.pi * k ≤ 80 := by
      have h1 : Real.pi * k ≤ 4 * 1.06 := by nlinarith [Real.pi_lt_four, hk, hk1]
      linarith
    have hden2 : (480000:ℝ) ≤ 2 * Kg := by nlinarith [hKgbig, hCn]
    rw [div_le_iff₀ (by positivity : (0:ℝ) < 2 * Kg)]
    nlinarith [hnumπ, hden2]
  have hn4 : 4 * (μ * V) ≤ n := by
    have hh : Cn * μ * V = Cn * (μ * V) := by ring
    nlinarith [hng, hCn, hμV]
  have hkey : (2.99 * (μ * V) + 1) * (1 + 17 * Real.pi * k / (2 * Kg)) ≤ 4 * (μ * V) := by
    have h1 : 1 + 17 * Real.pi * k / (2 * Kg) ≤ 1 + 1/6000 := by linarith
    have hpos : 0 ≤ 2.99 * (μ * V) + 1 := by nlinarith [hμV]
    calc (2.99 * (μ * V) + 1) * (1 + 17 * Real.pi * k / (2 * Kg))
        ≤ (2.99 * (μ * V) + 1) * (1 + 1/6000) := mul_le_mul_of_nonneg_left h1 hpos
      _ ≤ 4 * (μ * V) := by nlinarith [hμV]
  have hnle : n ≤ (1 + 17 * Real.pi * k / (2 * Kg)) * S := by
    have h1 : S + 17 * Real.pi * k * S / (2 * Kg) = (1 + 17 * Real.pi * k / (2 * Kg)) * S := by ring
    rw [← h1, ← hSQ]
    have h2 : (17 * Real.pi * k / (2 * Kg)) * S = 17 * Real.pi * k * S / (2 * Kg) := by ring
    rw [h2] at hQleS
    linarith [hQleS]
  have hSq : 4 * (μ * V) / (1 + 17 * Real.pi * k / (2 * Kg)) ≤ S := by
    rw [div_le_iff₀ hpos1]
    nlinarith [hnle, hn4]
  have hfin : 2.99 * (μ * V) + 1 ≤ 4 * (μ * V) / (1 + 17 * Real.pi * k / (2 * Kg)) := by
    rw [le_div_iff₀ hpos1]
    exact hkey
  exact ⟨hclaim1, by linarith⟩

end Work.BoseB1Cube
