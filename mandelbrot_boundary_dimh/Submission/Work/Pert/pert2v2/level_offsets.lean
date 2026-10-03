import Mathlib
import Submission.Work.Pert.pert2v2.orbit_pieces

/-!
# `Work.Pert.pert2v2.level_offsets` — the level bookkeeping of the low band, isolated

This file isolates the *level discrepancy* of the two-piece return map: the arithmetic obstruction
that separates the recorded design from a proof of `PertData.orbit` on the low band.

## The setting (`orbit_pieces`)

In `Work.Pert.pert2v2.orbit_pieces` the walk is telescoped through the two charts: the walk points
are `R^[j] w = x_j + k_j` (`x_j` a chart point, `k_j : ℤ`), the free offsets `t_j ∈ ℕ` satisfy
`t_0 = 0`, `t_m = n` and are monotone, and the piece relation at `x_j` is applied at the shift
`lo_j := k_j + t_{j+1}`.  The piece relation is available

* for the **low** chart at every `lo ≥ mₓ` (the crux's landing time), by
  `Work.Pert.pert2v2.Rlow_phi_add_nat` — the clean range, **no injectivity**;
* for the **low** chart at every `lo ≥ 1` at the price of `InjOn (f^[mₓ−lo]) (ball 0 δ)` with both
  compared values in the ball (`Work.Pert.pert2v2.Rlow_phi_pos`, `Rlow_phi_translate_lt`);
* for the **high** chart at every `lo ≥ 0` (`Work.Pert.pert2v2.retP_phi_shift`).

## The reduction (proved here)

`exists_level_offsets`: the free offsets are **powerless**.  The level conditions
`∀ j < m, m₀ ≤ k_j + t_{j+1}` (with `t_0 = 0`, `t_m = n`, `t` monotone) hold for *some* `t` iff
they hold with the canonical `t_j := n` (`j ≥ 1`), iff `∀ j < m, m₀ ≤ k_j + n`.  So no re-choosing
of the offsets can absorb a shortfall, and the whole burden is on `k_j + n ≥ m₀`.

`level_condition_of_antitone`: when the chart shifts decrease along the walk (which is the design's
case, `k_j ≈ Re R^[j]w` and `Re` drops by `Re (1/α)` per step), the binding index is the **last**
one, `j = m − 1`.

## The design's arithmetic (the `≈ 20` discrepancy)

With `k_j = Re R^[j]w − Re x_j` (`|Re x_j| < R1`), `n = Re w' − Re R^[m]w`, and
`Re R^[j]w ≈ Re w − j·Re (1/α)` (`R_close` on the band), the binding condition at `j = m−1` reads

  `k_{m-1} + n = (Re w' − Re x_{m-1}) + (Re R^[m-1]w − Re R^[m]w) ≈ Re w' + Re (1/α) − Re x_{m-1},`

so the level condition for the clean range `m₀ = mₓ` is

  **`Re w' + Re (1/α) ≳ mₓ`.**

On the other hand `w' ∈ Dφ = DphiP f Df τ Φ (Qm Ξ α)` only says (with `k' = mIdx (w') ≥ 0`) that
`w' − k'` lies in the image of the gate, i.e.

  `Re w' + Re (1/α) > Ξabs − |Im w' + Im (1/α)| + k',`

which allows `Re w' + Re (1/α)` to be as small as `Ξabs − |Im w|` (the minimal level `k' = 0`, the
**left end** of the gate image; the `Re`-range of `DphiP` is unbounded only to the *right*, because
`GoodP` is closed under `w ↦ w + 1` but not under `w ↦ w − 1`).  For those instances the level route
fails by

  `mₓ − (Ξabs − |Im w|) ≈ mₓ − Ξabs ≈ 20·Ξabs`

— the `≈ 20` shortfall.  The injectivity route at the same index needs
`InjOn (f^[mₓ−lo])` with `mₓ − lo ≈ mₓ − Ξabs` in the ball around `0`, while the two compared values
are `(mₓ−lo)`-th preimages of `τ u`, of size `≈ max(2π‖α‖, 4π/(c₀Ξ'))` — a mismatch of two to three
orders of magnitude given the crux's `ρ Ξ' ≳ 16π`.
-/

namespace Work.Pert.pert2v2

open Work.Pert

noncomputable section

/-- **The free offsets cannot absorb a level shortfall.**  Given the chart shifts `k : ℕ → ℤ`, the
total shift `n` and the threshold `m₀`, the existence of offsets `t` (`t_0 = 0`, `t_m = n`,
monotone) with `m₀ ≤ k_j + t_{j+1}` for all `j < m` is equivalent to the per-step condition
`m₀ ≤ k_j + n` — in particular it is *independent of the interior values* of `t`. -/
theorem exists_level_offsets {k : ℕ → ℤ} {n m₀ m : ℕ} (hm : 0 < m) :
    (∃ t : ℕ → ℕ, t 0 = 0 ∧ t m = n ∧ Monotone t ∧
        ∀ j < m, (m₀ : ℤ) ≤ k j + (t (j + 1) : ℤ)) ↔
      (∀ j < m, (m₀ : ℤ) ≤ k j + (n : ℤ)) := by
  constructor
  · rintro ⟨t, -, htm, htmono, ht⟩ j hj
    have h1 : t (j + 1) ≤ n := by
      rw [← htm]
      exact htmono (by omega)
    have h2 : (k j + (t (j + 1) : ℤ)) ≤ k j + (n : ℤ) := by
      have : (t (j + 1) : ℤ) ≤ (n : ℤ) := by exact_mod_cast h1
      linarith
    exact le_trans (ht j hj) h2
  · intro h
    refine ⟨fun j => if j = 0 then 0 else n, by simp, ?_, ?_, ?_⟩
    · -- `t m = n`: `m ≠ 0`
      by_cases hm0 : m = 0
      · omega
      · simp [hm0]
    · -- the canonical choice is monotone because `n` is a natural number
      intro a b hab
      by_cases ha : a = 0
      · subst ha
        simp only [↓reduceIte]
        split <;> omega
      · have hb : ¬ (b = 0) := fun hb0 => ha (by omega)
        simp only [ha, hb, ↓reduceIte, le_refl]
    · intro j hj
      by_cases hj0 : j + 1 = 0
      · omega
      · simp only [hj0, ↓reduceIte]
        exact h j hj

/-- **The binding index is the last one** when the chart shifts decrease along the walk (the
design's case: `k_j ≈ Re R^[j]w` and the real part drops by `Re (1/α)` per step). -/
theorem level_condition_of_antitone {k : ℕ → ℤ} {n m₀ m : ℕ} (hm : 0 < m)
    (hanti : Antitone k) :
    (∀ j < m, (m₀ : ℤ) ≤ k j + (n : ℤ)) ↔ (m₀ : ℤ) ≤ k (m - 1) + (n : ℤ) := by
  constructor
  · intro h
    exact h (m - 1) (by omega)
  · intro h j hj
    have hjm : j ≤ m - 1 := by omega
    have h1 : k (m - 1) ≤ k j := hanti hjm
    linarith

end

end Work.Pert.pert2v2
