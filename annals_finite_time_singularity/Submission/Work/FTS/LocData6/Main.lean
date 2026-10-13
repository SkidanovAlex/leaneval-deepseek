/-
# `Work.FTS.LocData6.Main` — the order-`6` localised datum of the strong-solution route

This is the main module of the chapter: it packages the localised datum `locG α L β (hLoc α)` of
N9 with the properties the strong-solution route consumes, at the order `6` of the class
`RegQ α 6` / `GalClass α`:

```
Work.FTS.LocData6.locG6_data
```
> for every `0 < α ≤ 1` and every `K > 0` there is `L₀ > 0` such that for every `L ≥ L₀` there is
> a scalar `β` with `|β| ≤ K·α²`, `DataAdm α (locG6 α L β)`, `RegQ α 6 (locG6 α L β)`,
> `GalClass α (locG6 α L β)`, `L₁₂(locG6 α L β)(0) = 0`, `Xn α (locG6 α L β) ≤ α²` and
> `Xn₆(locG6 α L β) ≤ K·α²`.

(`locG6 α L β = Work.FTS.LocData.locG α L β (Work.FTS.LocData.hLoc α)` and
`Xn6 α g = Work.Spaces.HkNorm α 6 g` are the two abbreviations of `LocData6.Defs`; `Xn` is the
frozen `Work.FTS.Nonlin.Xn = HkNorm α 4`.)

The conjuncts `RegQ α 6 (·)`, `Xn (·) ≤ α²` and `Xn₆(·) ≤ K·α²` are *exactly* the three
`g₀`-hypotheses of `Work.FTS.StrongGlobal.global_strong` (`hData`, `hXn4₀`, `hXn6₀`), and
`RegQ α 6 (·)` together with `Xn₆(·) ≤ K·α²` are those of
`Work.FTS.StrongGlobal.LWPStrong α Φs EllSol α₀ K δ` — the statements being copied from
`Submission/Work/FTS/StrongGlobal/Defs.lean` §2–§3.  `locG6_LWP_data` records the three
hypotheses alone, `locG6_data_min` omits the `GalClass` conjunct (so that it does not depend on
the decay clause), and `locG6_data_one` is the literal `∃ K` form of the deliverable (take
`K := 1`).

The scalar `β` is N9's normalising scalar `L₁₂(zfar L F_*)(0)/L₁₂(hLoc α)(0)`: the two
statements (order `4`, `ε = α²`, `Work.FTS.LocData.locData_small`; order `6`, `ε = K·α²`,
`LocData6.locG6_small`) produce the *same* `β`, and `locG6_data` combines them by the uniqueness
of the `L₁₂`-orthogonality.

Everything here rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.LocData6.Defs
import Submission.Work.FTS.LocData6.Small6
import Submission.Work.FTS.LocData6.RegQ6
import Submission.Work.FTS.LocData6.GalClass6
import Submission.Work.FTS.LocData6.decayAll_locG6

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.LocData6

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-- **THE ORDER-`6` LOCALISED DATUM** (without the `GalClass` conjunct).  For every `0 < α ≤ 1`
and every `K > 0` there is `L₀ > 0` such that for every `L ≥ L₀` there is `β` with

* `|β| ≤ K·α²`;
* `DataAdm α (locG α L β (hLoc α))` (N9's datum class);
* `RegQ α 6 (locG α L β (hLoc α))` (the interior regularity class of `LWPStrong`);
* `L₁₂(locG α L β (hLoc α))(0) = 0` (the orthogonality of N9);
* `Xn α (locG α L β (hLoc α)) ≤ α²` (the order-`4` smallness);
* `Xn₆(locG α L β (hLoc α)) ≤ K·α²` (the order-`6` smallness). -/
theorem locG6_data_min (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (K : ℝ) (hK : 0 < K) :
    ∃ L₀ : ℝ, 0 < L₀ ∧ ∀ L : ℝ, L₀ ≤ L → ∃ β : ℝ,
      |β| ≤ K * α ^ 2 ∧
      Work.FTS.LocData.DataAdm α (locG6 α L β) ∧
      Work.FTS.Nonlin.RegQ α 6 (locG6 α L β) ∧
      Work.Construction.L12 (locG6 α L β) 0 = 0 ∧
      Work.FTS.Nonlin.Xn α (locG6 α L β) ≤ α ^ 2 ∧
      Xn6 α (locG6 α L β) ≤ K * α ^ 2 := by
  have hα2 : 0 < α ^ 2 := by positivity
  obtain ⟨L4, h4⟩ := Work.FTS.LocData.locData_small α hα hα1 (α ^ 2) hα2
  obtain ⟨L6, h6⟩ := locG6_small α hα hα1 (K * α ^ 2) (by positivity)
  refine ⟨max 1 (max L4 L6), lt_of_lt_of_le zero_lt_one (le_max_left _ _),
    fun L hL => ?_⟩
  have hL1 : 1 ≤ L := le_trans (le_max_left _ _) hL
  have hL4 : L4 ≤ L := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hL
  have hL6 : L6 ≤ L := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hL
  obtain ⟨b4, _hb4, h12a, hnorm4, hadm⟩ := h4 L hL4
  obtain ⟨b6, hb6, h12b, hnorm6⟩ := h6 L hL6
  -- the two scalars coincide: `L₁₂(locG α L · (hLoc α))(0) = 0` determines `β`
  have hDpos : 0 < Work.Construction.L12 (Work.FTS.LocData.hLoc α) 0 :=
    (Work.FTS.LocData.L12_hLoc α hα hα1).2
  have hkey4 := Work.FTS.LocData.L12_locG α L b4 hα hα1 hL1
  have hkey6 := Work.FTS.LocData.L12_locG α L b6 hα hα1 hL1
  have hbeq : b4 = b6 := by
    have h : b4 * Work.Construction.L12 (Work.FTS.LocData.hLoc α) 0
        = b6 * Work.Construction.L12 (Work.FTS.LocData.hLoc α) 0 := by linarith
    exact mul_right_cancel₀ (ne_of_gt hDpos) h
  rw [← hbeq] at hb6 hnorm6
  exact ⟨b4, hb6, hadm, regQ_locG6_uncond α L b4 hα hα1 hL1, h12a, hnorm4, hnorm6⟩

/-- **THE ORDER-`6` LOCALISED DATUM**: `locG6_data_min` together with the class `GalClass α`
(assembled by `LocData6.galClass_locG6_of` from the decay clause `LocData6.decayAll_locG6`). -/
theorem locG6_data (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (K : ℝ) (hK : 0 < K) :
    ∃ L₀ : ℝ, 0 < L₀ ∧ ∀ L : ℝ, L₀ ≤ L → ∃ β : ℝ,
      |β| ≤ K * α ^ 2 ∧
      Work.FTS.LocData.DataAdm α (locG6 α L β) ∧
      Work.FTS.Nonlin.RegQ α 6 (locG6 α L β) ∧
      Work.FTS.Nonlin.GalClass α (locG6 α L β) ∧
      Work.Construction.L12 (locG6 α L β) 0 = 0 ∧
      Work.FTS.Nonlin.Xn α (locG6 α L β) ≤ α ^ 2 ∧
      Xn6 α (locG6 α L β) ≤ K * α ^ 2 := by
  obtain ⟨L₀, hL₀, h⟩ := locG6_data_min α hα hα1 K hK
  refine ⟨max L₀ 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), fun L hL => ?_⟩
  obtain ⟨β, hβ, hadm, hreg, h12, hX4, hX6⟩ := h L (le_trans (le_max_left _ _) hL)
  have hL1 : 1 ≤ L := le_trans (le_max_right _ _) hL
  exact ⟨β, hβ, hadm, hreg,
    galClass_locG6_of α L β hα hα1 hL1 hreg (decayAll_locG6 α L β hL1) h12,
    h12, hX4, hX6⟩

/-- **The order-`6` localised datum, at `K = 1`**: the literal `∃ K` form of the deliverable
(`Xn₆(locG α L β (hLoc α)) ≤ K·α²` for a fixed `K`). -/
theorem locG6_data_one (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) :
    ∃ K : ℝ, 0 < K ∧ ∃ L₀ : ℝ, 0 < L₀ ∧ ∀ L : ℝ, L₀ ≤ L → ∃ β : ℝ,
      |β| ≤ K * α ^ 2 ∧
      Work.FTS.LocData.DataAdm α (locG6 α L β) ∧
      Work.FTS.Nonlin.RegQ α 6 (locG6 α L β) ∧
      Work.FTS.Nonlin.GalClass α (locG6 α L β) ∧
      Work.Construction.L12 (locG6 α L β) 0 = 0 ∧
      Work.FTS.Nonlin.Xn α (locG6 α L β) ≤ α ^ 2 ∧
      Xn6 α (locG6 α L β) ≤ K * α ^ 2 :=
  ⟨1, one_pos, locG6_data α hα hα1 1 one_pos⟩

/-- **The three `g₀`-hypotheses of `Work.FTS.StrongGlobal.global_strong`, verbatim**: for every
`0 < α ≤ 1` and every `K > 0` there is `L₀ > 0` such that for every `L ≥ L₀` there is `g₀` of the
form `locG α L β (hLoc α)` with `RegQ α 6 g₀`, `Xn g₀ ≤ α²` and `Xn₆ g₀ ≤ K·α²`. -/
theorem locG6_LWP_data (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (K : ℝ) (hK : 0 < K) :
    ∃ L₀ : ℝ, 0 < L₀ ∧ ∀ L : ℝ, L₀ ≤ L → ∃ β : ℝ,
      Work.FTS.Nonlin.RegQ α 6 (locG6 α L β) ∧
      Work.FTS.Nonlin.Xn α (locG6 α L β) ≤ α ^ 2 ∧
      Xn6 α (locG6 α L β) ≤ K * α ^ 2 := by
  obtain ⟨L₀, hL₀, h⟩ := locG6_data_min α hα hα1 K hK
  exact ⟨L₀, hL₀, fun L hL => by
    obtain ⟨β, _, _, hreg, _, hX4, hX6⟩ := h L hL
    exact ⟨β, hreg, hX4, hX6⟩⟩

end Work.FTS.LocData6
