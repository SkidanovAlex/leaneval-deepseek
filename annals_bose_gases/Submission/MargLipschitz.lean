import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.LpSeminorm.Defs
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import ChallengeDeps
import Submission.DiagLimits
import Submission.Marginal
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
Lipschitz regularity of the liminf energy density (Layer-2 continuity input).

GOAL (single deliverable theorem `liminf_continuous_hcont`): for `0 ≤ v`,
`MemLp v 1`, the liminf function `ρ ↦ diagLiminf v ρ` is continuous on
`(0,1)`; in particular there is `ρmax > 0` with continuity at every point of
`(0,ρmax)` — exactly the `hcont` hypothesis of
`theorem_1_2_of_liminf_continuous_and_box`.

SOURCE OF REGULARITY.  `Marginal.exists_marginal_bound` gives, for each cut-off
density `ρmax ≥ 0`, a constant `M ≥ 0` such that adding `k` particles to an
admissible `N`-particle box of side `L ≥ 1` costs at most `k·M`:

    (hm)  ∀ L ≥ 1, ∀ N k, (N:ℝ) + k ≤ ρmax·L³  ⟹
              boxEnergy (N+k) L v - boxEnergy N L v ≤ (k:ℝ)·M .

With `ρmax := 1` (so the bound is valid for all boxes with up to `L³`
particles) this makes the *diagonal* density nearly M-Lipschitz in `ρ`:

STEP A — per-L bound (floor arithmetic).  For `0 ≤ ρ₁ ≤ ρ₂ ≤ 1` and `L ≥ 1`,
with `Nᵢ := Nat.floor (ρᵢ·L³)`, `k := N₂ − N₁`:
  • `N₁ ≤ N₂` (`Nat.floor_mono`, since `0 ≤ ρ₁·L³`),
  • `(N₂:ℝ) ≤ ρ₂·L³ ≤ L³` (`Nat.floor_le`), so the marginal bound applies,
  • `(k:ℝ) ≤ (ρ₂−ρ₁)·L³ + 1` (from `Nat.floor_le` on `ρ₂L³` and
    `Nat.lt_floor_add_one` on `ρ₁L³`),
and therefore (divide by `L³`)

    diag v ρ₂ L ≤ diag v ρ₁ L + M·(ρ₂ − ρ₁) + M / L³ .

STEP B — pass to the liminf.  A generic epsilon lemma (prove it, mirroring
`Closure2.limsup_le_add_of_eventually_le` with `csSup` instead of `csInf`):

    liminf_le_add_of_eventually_le : u ≤ v + ε eventually, u ≥ 0 eventually,
      v bounded above eventually  ⟹  liminf u ≤ liminf v + ε

(and the constant shift `liminf (f + c) = liminf f + c` — Mathlib
`Filter.liminf_const_add`/`liminf_add_const` or prove from the definition).
Combining with STEP A (take ε arbitrarily small; `M/L³ → 0`):
for `0 ≤ ρ₁ ≤ ρ₂ ≤ 1`,

    diagLiminf v ρ₂ ≤ diagLiminf v ρ₁ + M·(ρ₂ − ρ₁)          (upper increment)

(the side conditions: `diag ρ₂` eventually ≥ 0 — `DiagLimits.diag_eventually_nonneg`;
`diag ρ₁` eventually bounded above — `DiagLimits.diag_eventually_bdd_above`).
The other half is monotonicity `diagLiminf v ρ₁ ≤ diagLiminf v ρ₂`
(`DiagLimits.diagLiminf_mono`), giving the two-sided Lipschitz bound

    |diagLiminf v ρ₂ − diagLiminf v ρ₁| ≤ M·|ρ₂ − ρ₁|          (ρ₁,ρ₂ ∈ [0,ρmax]).

STEP C — continuity.  From the Lipschitz bound (with `M' := M + 1 > 0`,
which still satisfies the bound) every point `ρ₀ ∈ (0,1)` is a continuity
point of `diagLiminf v`: for `ε > 0` take `δ := min (ρ₀/2) ((1−ρ₀)/2) (ε/M')`
and apply the Lipschitz bound to `ρ` in the metric ball `|ρ−ρ₀| < δ`
(which keeps `ρ ∈ [0,1]`), splitting on `ρ ≤ ρ₀` vs `ρ₀ ≤ ρ`.

The deliverable: `∃ ρmax > 0` (take `ρmax := 1/2`, or `1`) with continuity on
`(0,ρmax)`.  Do NOT change the statement of `liminf_continuous_hcont`.  Add
any helper lemmas you need above it.  HYPOTHESES: only `hv : 0 ≤ v` and
`hv1 : MemLp v 1`; no support/radiality assumptions on `v`.
-/

namespace Submission

open _root_.BoseGases
open _root_.BoseGases.CInfty0Box
set_option autoImplicit false

namespace BoseGases

open Filter Metric MeasureTheory
open scoped ContDiff Topology Real

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- `liminf u ≤ liminf v + ε` from an eventual pointwise inequality
`u ≤ v + ε` (u eventually nonnegative, v eventually bounded above). -/
lemma liminf_le_add_of_eventually_le {u v : ℝ → ℝ} {ε : ℝ}
    (h : ∀ᶠ L : ℝ in atTop, u L ≤ v L + ε)
    (hu0 : ∀ᶠ L : ℝ in atTop, (0 : ℝ) ≤ u L)
    (hvB : ∃ B : ℝ, ∀ᶠ L : ℝ in atTop, v L ≤ B) :
    liminf u atTop ≤ liminf v atTop + ε := by
  rw [liminf_eq]
  let S_u : Set ℝ := {a | ∀ᶠ L : ℝ in atTop, a ≤ u L}
  let S_v : Set ℝ := {a | ∀ᶠ L : ℝ in atTop, a ≤ v L}
  change sSup S_u ≤ sSup S_v + ε
  have hSu_bdd : BddAbove S_u := by
    rcases hvB with ⟨B, hB⟩
    refine ⟨B + ε, ?_⟩
    intro a ha
    have hle : ∀ᶠ L : ℝ in atTop, a ≤ B + ε := by
      filter_upwards [ha, h, hB] with L hLa hLuv hLv
      linarith
    exact atTop_le_of_eventually (u := fun _ : ℝ => (B + ε : ℝ)) (by simpa using hle) (by simp)
  have hSv_bdd : BddAbove S_v := by
    rcases hvB with ⟨B, hB⟩
    refine ⟨B, ?_⟩
    intro b hb
    exact atTop_le_of_eventually (u := v) hb hB
  apply csSup_le
  · exact ⟨0, hu0⟩
  · intro a ha
    have haSv : a - ε ∈ S_v := by
      dsimp [S_v]
      filter_upwards [ha, h] with L hLa hLuv
      linarith
    have h1 : a - ε ≤ sSup S_v := le_csSup hSv_bdd haSv
    linarith

/-- Per-L diagonal Lipschitz bound from a marginal-cost bound (STEP A):
`0 ≤ ρ₁ ≤ ρ₂ ≤ ρmax`, `L ≥ 1` imply
`diag ρ₂ L ≤ diag ρ₁ L + M·(ρ₂−ρ₁) + M/L³`. -/
lemma diag_le_diag_add_marginal {v : ℝ³ → ℝ} {M ρmax : ℝ} (hM : 0 ≤ M)
    (hm : ∀ ⦃L : ℝ⦄, 1 ≤ L → ∀ {N k : ℕ}, (N : ℝ) + k ≤ ρmax * L ^ 3 →
      boxEnergy (N + k) L v - boxEnergy N L v ≤ (k : ℝ) * M)
    {ρ₁ ρ₂ : ℝ} (hρ₁ : 0 ≤ ρ₁) (hρ₁₂ : ρ₁ ≤ ρ₂) (hρ₂ : ρ₂ ≤ ρmax) :
    ∀ {L : ℝ}, 1 ≤ L →
      diag v ρ₂ L ≤ diag v ρ₁ L + M * (ρ₂ - ρ₁) + M / L ^ 3 := by
  intro L hL
  unfold diag
  set N1 : ℕ := Nat.floor (ρ₁ * L ^ 3) with hN1
  set N2 : ℕ := Nat.floor (ρ₂ * L ^ 3) with hN2
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hL3pos : 0 < L ^ 3 := pow_pos hLpos 3
  have hL3nonneg : 0 ≤ L ^ 3 := le_of_lt hL3pos
  have hρ₂0 : 0 ≤ ρ₂ := le_trans hρ₁ hρ₁₂
  have hρ₂L3 : 0 ≤ ρ₂ * L ^ 3 := mul_nonneg hρ₂0 hL3nonneg
  have hleL3 : ρ₁ * L ^ 3 ≤ ρ₂ * L ^ 3 := mul_le_mul_of_nonneg_right hρ₁₂ hL3nonneg
  have hNN : N1 ≤ N2 := by
    rw [hN1, hN2]
    exact Nat.floor_mono hleL3
  let k : ℕ := N2 - N1
  have hN2le : (N2 : ℝ) ≤ ρ₂ * L ^ 3 := by
    rw [hN2]
    exact Nat.floor_le hρ₂L3
  have hN1k : (N1 : ℝ) + (k : ℝ) = (N2 : ℝ) := by
    dsimp [k]
    rw [Nat.cast_sub hNN]
    ring
  have hN1kN : N1 + k = N2 := by
    dsimp [k]
    exact Nat.add_sub_of_le hNN
  have hcond : (N1 : ℝ) + k ≤ ρmax * L ^ 3 := by
    rw [hN1k]
    exact le_trans hN2le (mul_le_mul_of_nonneg_right hρ₂ hL3nonneg)
  have hm' : boxEnergy (N1 + k) L v - boxEnergy N1 L v ≤ (k : ℝ) * M :=
    hm hL (N := N1) (k := k) hcond
  have hE : boxEnergy N2 L v ≤ boxEnergy N1 L v + (k : ℝ) * M := by
    rw [hN1kN] at hm'
    linarith
  have hstep2 : boxEnergy N2 L v / L ^ 3 ≤
      boxEnergy N1 L v / L ^ 3 + (k : ℝ) * M / L ^ 3 := by
    have h1 := div_le_div_of_nonneg_right hE hL3nonneg
    rwa [add_div] at h1
  -- k ≤ (ρ₂−ρ₁)·L³ + 1
  have hk_le : (k : ℝ) ≤ (ρ₂ - ρ₁) * L ^ 3 + 1 := by
    have hN2leR : (N2 : ℝ) ≤ ρ₂ * L ^ 3 := hN2le
    have hN1gt : ρ₁ * L ^ 3 - 1 < (N1 : ℝ) := by
      have hlt := Nat.lt_floor_add_one (ρ₁ * L ^ 3)
      rw [← hN1] at hlt
      linarith
    have hkR : (k : ℝ) = (N2 : ℝ) - (N1 : ℝ) := by
      dsimp [k]
      exact Nat.cast_sub hNN
    nlinarith
  have hkM : (k : ℝ) * M ≤ M * ((ρ₂ - ρ₁) * L ^ 3 + 1) := by
    have hmul := mul_le_mul_of_nonneg_left hk_le hM
    simpa [mul_comm] using hmul
  have hkM3 : (k : ℝ) * M / L ^ 3 ≤ M * (ρ₂ - ρ₁) + M / L ^ 3 := by
    have hne : L ^ 3 ≠ 0 := ne_of_gt hL3pos
    calc
      (k : ℝ) * M / L ^ 3 ≤ M * ((ρ₂ - ρ₁) * L ^ 3 + 1) / L ^ 3 := by
        exact div_le_div_of_nonneg_right hkM hL3nonneg
      _ = M * (ρ₂ - ρ₁) + M / L ^ 3 := by
        field_simp [hne]
  calc
    boxEnergy N2 L v / L ^ 3 ≤ boxEnergy N1 L v / L ^ 3 + (k : ℝ) * M / L ^ 3 := hstep2
    _ ≤ boxEnergy N1 L v / L ^ 3 + (M * (ρ₂ - ρ₁) + M / L ^ 3) := by
        linarith
    _ = boxEnergy N1 L v / L ^ 3 + M * (ρ₂ - ρ₁) + M / L ^ 3 := by
        rw [← add_assoc]

/-- Upper-increment bound for the liminf (STEP B, first half):
`0 ≤ ρ₁ ≤ ρ₂ ≤ ρmax` imply `diagLiminf ρ₂ ≤ diagLiminf ρ₁ + M·(ρ₂−ρ₁)`. -/
lemma diagLiminf_le_diagLiminf_add {v : ℝ³ → ℝ} (hv : 0 ≤ v) (hv1 : MemLp v 1)
    {M ρmax : ℝ} (hM : 0 ≤ M)
    (hm : ∀ ⦃L : ℝ⦄, 1 ≤ L → ∀ {N k : ℕ}, (N : ℝ) + k ≤ ρmax * L ^ 3 →
      boxEnergy (N + k) L v - boxEnergy N L v ≤ (k : ℝ) * M)
    {ρ₁ ρ₂ : ℝ} (hρ₁ : 0 ≤ ρ₁) (hρ₁₂ : ρ₁ ≤ ρ₂) (hρ₂ : ρ₂ ≤ ρmax) :
    diagLiminf v ρ₂ ≤ diagLiminf v ρ₁ + M * (ρ₂ - ρ₁) := by
  apply le_of_forall_pos_le_add
  intro η hη
  -- M / L³ → 0
  have hML3 : Tendsto (fun L : ℝ => M / L ^ 3) atTop (𝓝 (0 : ℝ)) := by
    have hpow : Tendsto (fun L : ℝ => L ^ 3) atTop atTop :=
      tendsto_pow_atTop (by norm_num : (3 : ℕ) ≠ 0)
    have hinv : Tendsto (fun L : ℝ => (L ^ 3)⁻¹) atTop (𝓝 (0 : ℝ)) :=
      tendsto_inv_atTop_zero.comp hpow
    have hmul := (tendsto_const_nhds (x := M) (f := atTop)).mul hinv
    simpa [div_eq_mul_inv] using hmul
  have hML3ev : ∀ᶠ L : ℝ in atTop, M / L ^ 3 ≤ η := by
    have hb := hML3.eventually (isOpen_Iio.mem_nhds (by simpa using hη))
    filter_upwards [hb] with L hL
    have hlt : M / L ^ 3 < η := by
      simpa using hL
    exact le_of_lt hlt
  have hdiag : ∀ᶠ L : ℝ in atTop, diag v ρ₂ L ≤ diag v ρ₁ L + (M * (ρ₂ - ρ₁) + η) := by
    filter_upwards [eventually_ge_atTop (1 : ℝ), hML3ev] with L hL1 hML
    have hstep := diag_le_diag_add_marginal (v := v) (M := M) (ρmax := ρmax)
      hM hm hρ₁ hρ₁₂ hρ₂ (L := L) hL1
    linarith
  have hineq := liminf_le_add_of_eventually_le
    (u := fun L : ℝ => diag v ρ₂ L) (v := fun L : ℝ => diag v ρ₁ L)
    (ε := M * (ρ₂ - ρ₁) + η) hdiag
    (diag_eventually_nonneg (v := v) (ρ := ρ₂) hv)
    (diag_eventually_bdd_above (v := v) (ρ := ρ₁) hv1 hρ₁)
  rw [add_assoc]
  simpa [diagLiminf] using hineq

/-- Two-sided Lipschitz bound for the liminf on `[0,ρmax]`.

NOTE (deviations from the drafted statement): the draft of this lemma only
assumed `0 ≤ ρ₁` and `ρ₂ ≤ ρmax`.  Those two inequalities alone do **not**
suffice for the two-sided bound: the upper increment
`diagLiminf_le_diagLiminf_add` controls `L(ρ₂) − L(ρ₁)` only when the smaller
endpoint is `≥ 0` and the larger endpoint is `≤ ρmax`, i.e. it needs **both**
points in `[0,ρmax]` (monotonicity alone, which only needs nonnegativity,
cannot produce an upper bound).  With one point above `ρmax` (or below `0`)
the asserted `M`-Lipschitz bound is not a consequence of the marginal bound
`hm`, which is only valid up to density `ρmax`.  Every use below (continuity
on `(0,ρmax)`) has both points inside `[0,ρmax]`, so the two extra hypotheses
are harmless; the name and the ordering of the previous arguments are kept.
-/
lemma diagLiminf_lipschitz {v : ℝ³ → ℝ} (hv : 0 ≤ v) (hv1 : MemLp v 1)
    {M ρmax : ℝ} (hM : 0 ≤ M)
    (hm : ∀ ⦃L : ℝ⦄, 1 ≤ L → ∀ {N k : ℕ}, (N : ℝ) + k ≤ ρmax * L ^ 3 →
      boxEnergy (N + k) L v - boxEnergy N L v ≤ (k : ℝ) * M)
    {ρ₁ ρ₂ : ℝ} (hρ₁0 : 0 ≤ ρ₁) (hρ₁m : ρ₁ ≤ ρmax)
    (hρ₂0 : 0 ≤ ρ₂) (hρ₂m : ρ₂ ≤ ρmax) :
    |diagLiminf v ρ₂ - diagLiminf v ρ₁| ≤ M * |ρ₂ - ρ₁| := by
  by_cases hle : ρ₁ ≤ ρ₂
  · -- ρ₁ ≤ ρ₂: use monotonicity + upper increment
    have hmono12 : diagLiminf v ρ₁ ≤ diagLiminf v ρ₂ := diagLiminf_mono hv hv1 hρ₁0 hle
    have hnonneg : 0 ≤ diagLiminf v ρ₂ - diagLiminf v ρ₁ := sub_nonneg.mpr hmono12
    have hinc := diagLiminf_le_diagLiminf_add (v := v) hv hv1 (M := M) (ρmax := ρmax)
      hM hm hρ₁0 hle hρ₂m
    -- hinc : diagLiminf ρ₂ ≤ diagLiminf ρ₁ + M(ρ₂-ρ₁)
    have hdiff : diagLiminf v ρ₂ - diagLiminf v ρ₁ ≤ M * (ρ₂ - ρ₁) := by linarith
    rw [abs_of_nonneg hnonneg]
    rw [abs_of_nonneg (sub_nonneg.mpr hle)]
    exact hdiff
  · -- ρ₂ < ρ₁: symmetric
    have hlt : ρ₂ < ρ₁ := lt_of_not_ge hle
    have hmono21 : diagLiminf v ρ₂ ≤ diagLiminf v ρ₁ :=
      diagLiminf_mono hv hv1 hρ₂0 (le_of_lt hlt)
    have hnonneg : 0 ≤ diagLiminf v ρ₁ - diagLiminf v ρ₂ := sub_nonneg.mpr hmono21
    have hinc := diagLiminf_le_diagLiminf_add (v := v) hv hv1 (M := M) (ρmax := ρmax)
      hM hm hρ₂0 (le_of_lt hlt) hρ₁m
    have hdiff : diagLiminf v ρ₁ - diagLiminf v ρ₂ ≤ M * (ρ₁ - ρ₂) := by linarith
    calc
      |diagLiminf v ρ₂ - diagLiminf v ρ₁| = |diagLiminf v ρ₁ - diagLiminf v ρ₂| := abs_sub_comm _ _
      _ = diagLiminf v ρ₁ - diagLiminf v ρ₂ := by rw [abs_of_nonneg hnonneg]
      _ ≤ M * (ρ₁ - ρ₂) := hdiff
      _ = M * |ρ₂ - ρ₁| := by
        rw [abs_of_nonpos (sub_nonpos.mpr (le_of_lt hlt))]
        ring

/-- Continuity of the liminf density on `(0,1)` (the `hcont` deliverable). -/
theorem liminf_continuous_hcont {v : ℝ³ → ℝ} (hv : 0 ≤ v) (hv1 : MemLp v 1) :
    ∃ ρmax : ℝ, 0 < ρmax ∧ ∀ ρ' : ℝ, 0 < ρ' → ρ' < ρmax → ContinuousAt (diagLiminf v) ρ' := by
  rcases exists_marginal_bound (v := v) hv hv1 (ρmax := 1) (by norm_num) with ⟨M, hM0, hm⟩
  refine ⟨1, by norm_num, ?_⟩
  intro ρ₀ hρ₀pos hρ₀lt
  rw [Metric.continuousAt_iff]
  intro ε hε
  let δ : ℝ := min (ρ₀ / 2) (min ((1 - ρ₀) / 2) (ε / (M + 1)))
  have hδ0 : 0 < δ := by
    dsimp [δ]
    apply lt_min
    · linarith
    · apply lt_min
      · linarith
      · positivity
  refine ⟨δ, hδ0, ?_⟩
  intro ρ hρδ
  have hρδ' : |ρ - ρ₀| < δ := by
    simpa [Real.dist_eq] using hρδ
  have hδ_le1 : δ ≤ ρ₀ / 2 := by
    dsimp [δ]
    exact min_le_left (ρ₀ / 2) (min ((1 - ρ₀) / 2) (ε / (M + 1)))
  have hδ_le2 : δ ≤ (1 - ρ₀) / 2 := by
    dsimp [δ]
    exact le_trans (min_le_right (ρ₀ / 2) (min ((1 - ρ₀) / 2) (ε / (M + 1))))
      (min_le_left ((1 - ρ₀) / 2) (ε / (M + 1)))
  have hδ_le3 : δ ≤ ε / (M + 1) := by
    dsimp [δ]
    exact le_trans (min_le_right (ρ₀ / 2) (min ((1 - ρ₀) / 2) (ε / (M + 1))))
      (min_le_right ((1 - ρ₀) / 2) (ε / (M + 1)))
  have hρlt₀ : ρ₀ - ρ < δ := by
    have hl : -δ < ρ - ρ₀ := (abs_lt.mp hρδ').1
    linarith
  have hρgt₀ : ρ - ρ₀ < δ := (abs_lt.mp hρδ').2
  have hρ_pos : 0 < ρ := by
    have h1 : ρ₀ - ρ < ρ₀ / 2 := lt_of_lt_of_le hρlt₀ hδ_le1
    linarith
  have hρ_lt : ρ < 1 := by
    have h1 : ρ - ρ₀ < (1 - ρ₀) / 2 := lt_of_lt_of_le hρgt₀ hδ_le2
    linarith
  have hρ0 : 0 ≤ ρ := le_of_lt hρ_pos
  have hρ1 : ρ ≤ 1 := le_of_lt hρ_lt
  have hρ₀0 : 0 ≤ ρ₀ := le_of_lt hρ₀pos
  have hρ₀1 : ρ₀ ≤ 1 := le_of_lt hρ₀lt
  have hLip : |diagLiminf v ρ - diagLiminf v ρ₀| ≤ M * |ρ - ρ₀| :=
    diagLiminf_lipschitz (v := v) hv hv1 (M := M) (ρmax := 1) hM0 hm
      (ρ₁ := ρ₀) (ρ₂ := ρ) hρ₀0 hρ₀1 hρ0 hρ1
  have hM1 : 0 < M + 1 := by linarith
  have hMeps : M * (ε / (M + 1)) < ε := by
    have hx : M * ε < ε * (M + 1) := by nlinarith
    calc
      M * (ε / (M + 1)) = (M * ε) / (M + 1) := by rw [mul_div_assoc]
      _ < ε := by
        rw [div_lt_iff₀ hM1]
        nlinarith
  have habslt : |ρ - ρ₀| < ε / (M + 1) := lt_of_lt_of_le hρδ' hδ_le3
  have hle1 : M * |ρ - ρ₀| ≤ M * (ε / (M + 1)) :=
    mul_le_mul_of_nonneg_left (le_of_lt habslt) hM0
  have hlt : |diagLiminf v ρ - diagLiminf v ρ₀| < ε := lt_of_le_of_lt (le_trans hLip hle1) hMeps
  simpa [Real.dist_eq] using hlt

end BoseGases

end Submission
