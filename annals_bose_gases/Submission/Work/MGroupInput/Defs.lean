import ChallengeDeps
import Submission.Work.DLRepoint.UBBChain
import Submission.Work.UBB.Consumer
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.MGroupInput` — the `m`-arm of FS's `thm:smallbox`: the per-group bound

**Assignment.** `Submission/Work/DLRepoint/README.md` §3 carries the `m`-arm of
FS's two-arm split of `thm:smallbox` as the ONE named input of the delivered DL
bound: `Work.DLRepoint.MGroupInput s μ v h c₀ cgap`, i.e.

```
∀ P ≥ 1, 2μs³ ≤ P → (1/9)(μ − P/s³)²·8π(av)s³ ≤ diagWeBAt P s μ v h c₀ cgap .
```

This chapter is that area.  It contains

* `Defs.lean` (this file) — the vocabulary: the *windowed* per-group bound
  `MGroupWindow Cn` (FS's `m`-arm on the honest group window `u ≥ Cn μ`), the
  linear shape `MGroupLinear`, and their basic API;
* `NoGo.lean` — **the falsity of the delivered input as stated**: on the group
  window of `Work.DLRepoint.exists_two_arm_split` (`n′ = ⌈2μs³⌉`, i.e.
  `2μ ≤ u < 3μ`) the per-group bound is FALSE, because the all-condensate trial
  state has energy `μ(D − 8π(av)) ≤ 0` there while the claimed right-hand side
  is `(8π/9)(av)μ²s³ > 0` (`D := g0w0Mass` the `ĝω(0)`-mass of the corpus).
  MGroupInput therefore forces `D ≥ (80π/9)(av)`, which contradicts the
  PROVED corpus bound `D ≤ 8π(av)` (`Submission.ScatGChosen`).
* `Arith.lean` — FS's own `m`-arm arithmetic, machine-checked.
* `Window.lean` — the repaired two-arm assembly: `MGroupWindow Cn` (+ the
  tight block bound at the remainder) gives `d4_dl_bound_of_groups`'s shape for
  every `Cn ∈ [4, 8]`, i.e. a drop-in repair of the DL re-point.
* `Residual.lean` — the conditional derivation of `MGroupWindow Cn` from the
  named residuals of FS's *simple* chain (`SimpleA2`/`SimpleA0`) and the exact
  record of what the corpus still lacks.

## Conventions

`ℝ³ = EuclideanSpace ℝ (Fin 3)`, `X N = Fin N → ℝ³`, `acube s`/`abox N s` the
centred boxes of side `s`, `a v` the scattering length, `u := P/s³` the group
density, `μ` the chemical potential, `diagWeBAt P s μ v h c₀ cgap` Door 4's
faithful per-box ground energy (`Work.BlockBound4.diagWeBAt`).

The group window of FS's `m`-arm is `u ∈ [Cn μ, (Cn+1) μ)`: FS's own text
(*"if we choose the constant `C_n` large enough"*, `final_v2.tex` l.4004) makes
the window constant part of the proof, not a fixed `2`.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.MGroupInput

open Submission BoseGases

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-! ## 1  The windowed per-group bound -/

/-- **FS's `m`-arm on the honest group window.**  For every group count `P`
whose density `u := P/s³` lies above `Cn·μ` (FS's group window
`[Cn μ, (Cn+1) μ)` is a *sub*window of this),

    `(1/9)(μ − u)²·8π(av)s³ ≤ diagWeBAt P s μ v h c₀ cgap`.

This is the statement FS's text actually proves (`final_v2.tex` ll. 3994–4012),
with the window constant `Cn` an explicit parameter: FS's proof needs
`Cn ≥ C_ε`-large, while `Work.DLRepoint.MGroupInput` is this at `Cn := 2`. -/
def MGroupWindow (Cn s μ : ℝ) (v : ℝ³ → ℝ)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v) (c₀ cgap : ℝ) : Prop :=
  ∀ P : ℕ, 1 ≤ P → Cn * μ * s ^ 3 ≤ (P : ℝ) →
    (1 / 9) * (μ - (P : ℝ) / s ^ 3) ^ 2 * (8 * π * (a v) * s ^ 3)
      ≤ Work.BlockBound4.diagWeBAt P s μ v h c₀ cgap

/-- **The linear shape FS's assembly consumes**: at a group count whose density
`u := P/s³` is at least `Cn μ` with `Cn ≥ 2`,

    `(1/18)·μ·u·8π(av)s³ ≤ diagWeBAt P …`

(`(1/18)μu ≤ (1/9)(μ−u)²` for `u ≥ 2μ`; `Submission.BoseGases.two_arm_group_bound`). -/
def MGroupLinear (Cn s μ : ℝ) (v : ℝ³ → ℝ)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v) (c₀ cgap : ℝ) : Prop :=
  ∀ P : ℕ, 1 ≤ P → Cn * μ * s ^ 3 ≤ (P : ℝ) →
    (1 / 18) * μ * ((P : ℝ) / s ^ 3) * (8 * π * (a v) * s ^ 3)
      ≤ Work.BlockBound4.diagWeBAt P s μ v h c₀ cgap

/-- **FS's `m`-arm on a CAPPED group window** `u ∈ [Cn μ, Cn′ μ]`.

This is the form the corpus's own machinery can actually prove: the sharp
potential-side transcription `Work.SmallBoxA0.pot_sharp_summary` (and the whole
`D4Regime`/`hblk` block architecture) carries the hypothesis
`N/s³ ≤ 9μ` (the count window), so a per-state proof of the `m`-arm is only
available for `u ≤ 9μ`.  The DL assembly applies its `m`-arm input at the
*single* group count `n′` of `exists_two_arm_split_gen`, and that count is
trapped in `[Cn μ s³, (Cn+1) μ s³]`; a capped input at `Cn′ ≥ Cn+1` therefore
suffices for every consumer, and `Cn+1 ≤ 9` puts it inside the corpus's
provable range. -/
def MGroupWindowCapped (Cn Cn' s μ : ℝ) (v : ℝ³ → ℝ)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v) (c₀ cgap : ℝ) : Prop :=
  ∀ P : ℕ, 1 ≤ P → Cn * μ * s ^ 3 ≤ (P : ℝ) → (P : ℝ) ≤ Cn' * μ * s ^ 3 →
    (1 / 9) * (μ - (P : ℝ) / s ^ 3) ^ 2 * (8 * π * (a v) * s ^ 3)
      ≤ Work.BlockBound4.diagWeBAt P s μ v h c₀ cgap

/-- **The linear shape on a capped window** — what the two-arm assembly's
`m`-slot actually consumes (at the group count `n′ ∈ [Cn μ s³, (Cn+1) μ s³]`). -/
def MGroupLinearCapped (Cn Cn' s μ : ℝ) (v : ℝ³ → ℝ)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v) (c₀ cgap : ℝ) : Prop :=
  ∀ P : ℕ, 1 ≤ P → Cn * μ * s ^ 3 ≤ (P : ℝ) → (P : ℝ) ≤ Cn' * μ * s ^ 3 →
    (1 / 18) * μ * ((P : ℝ) / s ^ 3) * (8 * π * (a v) * s ^ 3)
      ≤ Work.BlockBound4.diagWeBAt P s μ v h c₀ cgap

/-! ## 2  Basic API -/

/-- The windowed bound is *weaker* for a larger window constant (the hypothesis
`Cn μ s³ ≤ P` is harder to satisfy). -/
theorem mGroupWindow_mono {Cn Cn' s μ : ℝ} {v : ℝ³ → ℝ}
    {h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v} {c₀ cgap : ℝ}
    (hCn : Cn ≤ Cn') (hμ : 0 ≤ μ) (hs : 0 ≤ s)
    (hM : MGroupWindow Cn s μ v h c₀ cgap) :
    MGroupWindow Cn' s μ v h c₀ cgap := by
  intro P hP1 hP2
  refine hM P hP1 (le_trans ?_ hP2)
  have hs3 : (0 : ℝ) ≤ s ^ 3 := pow_nonneg hs 3
  have h1 : Cn * μ ≤ Cn' * μ := mul_le_mul_of_nonneg_right hCn hμ
  exact mul_le_mul_of_nonneg_right h1 hs3

/-- **`Work.DLRepoint.MGroupInput` is the windowed bound at `Cn := 2`** (the
window `2μs³ ≤ P` is exactly `Cn μ s³ ≤ P` for `Cn = 2`).  Conversely the
windowed bound at any `Cn ≥ 2` implies the delivered input. -/
theorem mgroupInput_iff_mGroupWindow_two {s μ : ℝ} {v : ℝ³ → ℝ}
    {h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v} {c₀ cgap : ℝ} :
    Work.DLRepoint.MGroupInput s μ v h c₀ cgap
      ↔ MGroupWindow 2 s μ v h c₀ cgap := by
  constructor
  · intro hM P hP1 hP2
    exact hM P hP1 (by linarith)
  · intro hM P hP1 hP2
    exact hM P hP1 (by linarith)

/-- The delivered input gives the windowed bound at every `Cn ≥ 2`. -/
theorem mGroupWindow_of_mgroupInput {Cn s μ : ℝ} {v : ℝ³ → ℝ}
    {h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v} {c₀ cgap : ℝ}
    (hCn : 2 ≤ Cn) (hμ : 0 ≤ μ) (hs : 0 ≤ s)
    (hM : Work.DLRepoint.MGroupInput s μ v h c₀ cgap) :
    MGroupWindow Cn s μ v h c₀ cgap := by
  rw [mgroupInput_iff_mGroupWindow_two] at hM
  exact mGroupWindow_mono (Cn := (2 : ℝ)) (Cn' := Cn) hCn hμ hs hM

/-- The windowed `(1/9)`-bound gives the linear `(1/18)`-shape on any window
with `Cn ≥ 2`. -/
theorem mGroupLinear_of_mGroupWindow {Cn s μ : ℝ} {v : ℝ³ → ℝ}
    {h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v} {c₀ cgap : ℝ}
    (hCn : 2 ≤ Cn) (hμ : 0 < μ) (hs : 0 < s) (hav : 0 ≤ a v)
    (hM : MGroupWindow Cn s μ v h c₀ cgap) :
    MGroupLinear Cn s μ v h c₀ cgap := by
  intro P hP1 hP2
  have hs3 : 0 < s ^ 3 := by positivity
  have hu : 2 * μ ≤ (P : ℝ) / s ^ 3 := by
    rw [le_div_iff₀ hs3]
    have h1 : 2 * μ ≤ Cn * μ := mul_le_mul_of_nonneg_right hCn (le_of_lt hμ)
    have h2 : 2 * μ * s ^ 3 ≤ Cn * μ * s ^ 3 :=
      mul_le_mul_of_nonneg_right h1 (le_of_lt hs3)
    linarith
  have hgrp := Submission.BoseGases.two_arm_group_bound (μ := μ) (u := (P : ℝ) / s ^ 3) hμ hu
  have h8 : (0 : ℝ) ≤ 8 * π * (a v) * s ^ 3 :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) Real.pi_pos.le) hav) (le_of_lt hs3)
  calc (1 / 18) * μ * ((P : ℝ) / s ^ 3) * (8 * π * (a v) * s ^ 3)
      = ((1 / 18) * μ * ((P : ℝ) / s ^ 3)) * (8 * π * (a v) * s ^ 3) := by ring
    _ ≤ ((1 / 9) * (μ - (P : ℝ) / s ^ 3) ^ 2) * (8 * π * (a v) * s ^ 3) :=
        mul_le_mul_of_nonneg_right hgrp h8
    _ = (1 / 9) * (μ - (P : ℝ) / s ^ 3) ^ 2 * (8 * π * (a v) * s ^ 3) := by ring
    _ ≤ Work.BlockBound4.diagWeBAt P s μ v h c₀ cgap := hM P hP1 hP2

/-- The uncapped windowed bound gives the capped one (trivially). -/
theorem mGroupWindowCapped_of_mGroupWindow {Cn Cn' s μ : ℝ} {v : ℝ³ → ℝ}
    {h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v} {c₀ cgap : ℝ}
    (hM : MGroupWindow Cn s μ v h c₀ cgap) :
    MGroupWindowCapped Cn Cn' s μ v h c₀ cgap :=
  fun P hP1 hP2 _ => hM P hP1 hP2

/-- The uncapped linear bound gives the capped one (trivially). -/
theorem mGroupLinearCapped_of_mGroupLinear {Cn Cn' s μ : ℝ} {v : ℝ³ → ℝ}
    {h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v} {c₀ cgap : ℝ}
    (hM : MGroupLinear Cn s μ v h c₀ cgap) :
    MGroupLinearCapped Cn Cn' s μ v h c₀ cgap :=
  fun P hP1 hP2 _ => hM P hP1 hP2

/-- The capped `(1/9)`-bound gives the capped linear shape on any window with
`Cn ≥ 2` (`(1/18)μu ≤ (1/9)(μ−u)²` for `u ≥ 2μ`). -/
theorem mGroupLinearCapped_of_mGroupWindowCapped {Cn Cn' s μ : ℝ} {v : ℝ³ → ℝ}
    {h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v} {c₀ cgap : ℝ}
    (hCn : 2 ≤ Cn) (hμ : 0 < μ) (hs : 0 < s) (hav : 0 ≤ a v)
    (hM : MGroupWindowCapped Cn Cn' s μ v h c₀ cgap) :
    MGroupLinearCapped Cn Cn' s μ v h c₀ cgap := by
  intro P hP1 hP2 hP3
  have hs3 : 0 < s ^ 3 := by positivity
  have hu : 2 * μ ≤ (P : ℝ) / s ^ 3 := by
    rw [le_div_iff₀ hs3]
    have h1 : 2 * μ ≤ Cn * μ := mul_le_mul_of_nonneg_right hCn (le_of_lt hμ)
    have h2 : 2 * μ * s ^ 3 ≤ Cn * μ * s ^ 3 :=
      mul_le_mul_of_nonneg_right h1 (le_of_lt hs3)
    linarith
  have hgrp := Submission.BoseGases.two_arm_group_bound (μ := μ) (u := (P : ℝ) / s ^ 3) hμ hu
  have h8 : (0 : ℝ) ≤ 8 * π * (a v) * s ^ 3 :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) Real.pi_pos.le) hav) (le_of_lt hs3)
  calc (1 / 18) * μ * ((P : ℝ) / s ^ 3) * (8 * π * (a v) * s ^ 3)
      = ((1 / 18) * μ * ((P : ℝ) / s ^ 3)) * (8 * π * (a v) * s ^ 3) := by ring
    _ ≤ ((1 / 9) * (μ - (P : ℝ) / s ^ 3) ^ 2) * (8 * π * (a v) * s ^ 3) :=
        mul_le_mul_of_nonneg_right hgrp h8
    _ = (1 / 9) * (μ - (P : ℝ) / s ^ 3) ^ 2 * (8 * π * (a v) * s ^ 3) := by ring
    _ ≤ Work.BlockBound4.diagWeBAt P s μ v h c₀ cgap := hM P hP1 hP2 hP3

end Work.MGroupInput
