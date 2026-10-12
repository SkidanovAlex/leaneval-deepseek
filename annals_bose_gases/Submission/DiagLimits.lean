import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.LpSeminorm.Defs
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import ChallengeDeps
import Submission.DiagUpper
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
Layer 2 — extremal limits of the diagonal box-energy density.

`diag v ρ L := E(⌊ρL³⌋, L)/L³` (box-energy density at density `ρ`, side `L`).
`diagLiminf v ρ` / `diagLimsup v ρ` are the liminf / limsup as `L → ∞`.

This module records the elementary analytic facts about these extremal
limits for a nonnegative finite-range potential `v ∈ L¹`:

- boundedness: `0 ≤ liminf ≤ limsup ≤ C(ρ²‖v‖₁ + ρ)` for `0 ≤ ρ`;
- monotonicity in the density of the liminf;
- the *grid-window* machinery: with `G_m := mℓ + (m−1)R` the intervals
  `[G_m, G_{m+1}]` (`m ≥ 1`) cover `[G_1, ∞)`, the window index of `L` is
  `⌊(L+R)/(ℓ+R)⌋`, and the rescaling factor `(m/G_m)³` tends to
  `(ℓ+R)^{-3}`.  These are the ingredients of the upper-side theorem
  proved in `DiagUpperLim`.
-/

namespace Submission

open _root_.BoseGases
open _root_.BoseGases.CInfty0Box
set_option autoImplicit false

namespace BoseGases

open Filter Metric MeasureTheory
open scoped ContDiff Topology Real

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-! ## Generic liminf / limsup facts over `atTop` on `ℝ`

For `u : ℝ → ℝ` which is eventually bounded below by `0` and eventually
bounded above by `B`, the liminf and limsup lie between `0` and `B`, and
the liminf is monotone in pointwise order.  All proofs use the
characterizations `liminf_eq` / `limsup_eq` and the `csSup`/`csInf` API.
-/

/-- From two eventual pointwise inequalities on `atTop (ℝ)` one obtains the
corresponding inequality of the constants (`atTop` is not the trivial filter). -/
lemma atTop_le_of_eventually {u : ℝ → ℝ} {a b : ℝ} (ha : ∀ᶠ L : ℝ in atTop, a ≤ u L)
    (hb : ∀ᶠ L : ℝ in atTop, u L ≤ b) : a ≤ b := by
  have hle : ∀ᶠ L : ℝ in atTop, a ≤ b := by
    filter_upwards [ha, hb] with L hLa hLb
    exact le_trans hLa hLb
  rcases eventually_atTop.mp hle with ⟨N, hN⟩
  exact hN N (le_refl N)

/-- `a ≤ liminf u` from an eventual lower bound `a ≤ u`, provided `u` is
eventually bounded above. -/
lemma liminf_ge_of_eventually_ge {u : ℝ → ℝ} {a : ℝ}
    (h : ∀ᶠ L : ℝ in atTop, a ≤ u L)
    (hB : ∃ B : ℝ, ∀ᶠ L : ℝ in atTop, u L ≤ B) : a ≤ liminf u atTop := by
  rw [liminf_eq]
  apply le_csSup
  · rcases hB with ⟨B, hB⟩
    refine ⟨B, ?_⟩
    intro b hb
    exact atTop_le_of_eventually hb hB
  · simpa using h

/-- `liminf u ≤ B` from an eventual upper bound `u ≤ B`, provided `u` is
eventually bounded below by `0`. -/
lemma liminf_le_of_eventually_le {u : ℝ → ℝ} {B : ℝ}
    (h : ∀ᶠ L : ℝ in atTop, u L ≤ B)
    (h0 : ∀ᶠ L : ℝ in atTop, (0 : ℝ) ≤ u L) : liminf u atTop ≤ B := by
  rw [liminf_eq]
  apply csSup_le
  · refine ⟨0, ?_⟩
    simpa using h0
  · intro b hb
    exact atTop_le_of_eventually hb h

/-- `0 ≤ liminf u` from eventual nonnegativity, provided `u` is eventually
bounded above. -/
lemma liminf_nonneg_of_eventually_nonneg {u : ℝ → ℝ}
    (h : ∀ᶠ L : ℝ in atTop, 0 ≤ u L)
    (hB : ∃ B : ℝ, ∀ᶠ L : ℝ in atTop, u L ≤ B) : 0 ≤ liminf u atTop := by
  rw [liminf_eq]
  apply le_csSup
  · rcases hB with ⟨B, hB⟩
    refine ⟨B, ?_⟩
    intro a ha
    exact atTop_le_of_eventually ha hB
  · simpa using h

/-- `limsup u ≤ B` from an eventual upper bound `u ≤ B`, provided `u` is
eventually bounded below by `0`. -/
lemma limsup_le_of_eventually_le {u : ℝ → ℝ} {B : ℝ}
    (h : ∀ᶠ L : ℝ in atTop, u L ≤ B)
    (h0 : ∀ᶠ L : ℝ in atTop, (0 : ℝ) ≤ u L) : limsup u atTop ≤ B := by
  rw [limsup_eq]
  apply csInf_le
  · refine ⟨0, ?_⟩
    intro a ha
    exact atTop_le_of_eventually h0 ha
  · simpa using h

/-- `0 ≤ limsup u` from eventual nonnegativity, provided `u` is eventually
bounded above. -/
lemma limsup_nonneg_of_eventually_nonneg {u : ℝ → ℝ}
    (h : ∀ᶠ L : ℝ in atTop, 0 ≤ u L)
    (hB : ∃ B : ℝ, ∀ᶠ L : ℝ in atTop, u L ≤ B) : 0 ≤ limsup u atTop := by
  rw [limsup_eq]
  apply le_csInf
  · rcases hB with ⟨B, hB⟩
    refine ⟨B, ?_⟩
    simpa using hB
  · intro a ha
    exact atTop_le_of_eventually h ha

/-- `liminf u ≤ limsup u` for eventually two-sided bounded `u`. -/
lemma liminf_le_limsup_of_bounded {u : ℝ → ℝ}
    (h0 : ∀ᶠ L : ℝ in atTop, (0 : ℝ) ≤ u L)
    (hB : ∃ B : ℝ, ∀ᶠ L : ℝ in atTop, u L ≤ B) : liminf u atTop ≤ limsup u atTop := by
  rw [liminf_eq, limsup_eq]
  apply le_csInf
  · rcases hB with ⟨B, hB⟩
    refine ⟨B, ?_⟩
    simpa using hB
  · intro a ha
    apply csSup_le
    · refine ⟨0, ?_⟩
      simpa using h0
    · intro b hb
      exact atTop_le_of_eventually hb ha

/-- Pointwise eventual order passes to the liminf (upper bound needed on the
larger function). -/
lemma liminf_mono_of_eventually_le {u v : ℝ → ℝ}
    (h : ∀ᶠ L : ℝ in atTop, u L ≤ v L)
    (hu0 : ∀ᶠ L : ℝ in atTop, (0 : ℝ) ≤ u L)
    (hvB : ∃ B : ℝ, ∀ᶠ L : ℝ in atTop, v L ≤ B) : liminf u atTop ≤ liminf v atTop := by
  rw [liminf_eq, liminf_eq]
  apply csSup_le
  · refine ⟨0, ?_⟩
    simpa using hu0
  · intro a ha
    apply le_csSup
    · rcases hvB with ⟨B, hvB⟩
      refine ⟨B, ?_⟩
      intro b hb
      exact atTop_le_of_eventually hb hvB
    · have : ∀ᶠ L : ℝ in atTop, a ≤ v L := by
        filter_upwards [ha, h] with L hLa hLuv
        exact le_trans hLa hLuv
      simpa using this

/-! ## The diagonal: eventual boundedness, extremal limits, monotonicity -/

/-- Eventually (in `L`) the diagonal is nonnegative. -/
lemma diag_eventually_nonneg {v : ℝ³ → ℝ} {ρ : ℝ} (hv : 0 ≤ v) :
    ∀ᶠ L : ℝ in atTop, (0 : ℝ) ≤ diag v ρ L := by
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with L hL
  exact diag_nonneg hv (by linarith)

/-- Eventually the diagonal is bounded above by the density bound. -/
lemma diag_eventually_bdd_above {v : ℝ³ → ℝ} {ρ : ℝ} (hv1 : MemLp v 1) (hρ : 0 ≤ ρ) :
    ∃ B : ℝ, ∀ᶠ L : ℝ in atTop, diag v ρ L ≤ B := by
  rcases diag_le_density_bound hv1 with ⟨C, hCpos, hbd⟩
  refine ⟨C * (ρ ^ 2 * vL1 v + ρ), ?_⟩
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with L hL
  exact hbd hL hρ

/-- The liminf of the diagonal is nonnegative. -/
lemma diagLiminf_nonneg {v : ℝ³ → ℝ} {ρ : ℝ} (hv : 0 ≤ v)
    (hv1 : MemLp v 1) (hρ : 0 ≤ ρ) : 0 ≤ diagLiminf v ρ := by
  unfold diagLiminf
  exact liminf_nonneg_of_eventually_nonneg (diag_eventually_nonneg hv)
    (diag_eventually_bdd_above hv1 hρ)

/-- The liminf of the diagonal is bounded above by the density bound. -/
lemma diagLiminf_le_density_bound {v : ℝ³ → ℝ} {ρ : ℝ} (hv : 0 ≤ v)
    (hv1 : MemLp v 1) (hρ : 0 ≤ ρ) :
    ∃ C : ℝ, 0 < C ∧ diagLiminf v ρ ≤ C * (ρ ^ 2 * vL1 v + ρ) := by
  rcases diag_le_density_bound hv1 with ⟨C, hCpos, hbd⟩
  refine ⟨C, hCpos, ?_⟩
  unfold diagLiminf
  apply liminf_le_of_eventually_le
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with L hL
    exact hbd hL hρ
  · exact diag_eventually_nonneg hv

/-- The limsup of the diagonal is nonnegative. -/
lemma diagLimsup_nonneg {v : ℝ³ → ℝ} {ρ : ℝ} (hv : 0 ≤ v)
    (hv1 : MemLp v 1) (hρ : 0 ≤ ρ) : 0 ≤ diagLimsup v ρ := by
  unfold diagLimsup
  exact limsup_nonneg_of_eventually_nonneg (diag_eventually_nonneg hv)
    (diag_eventually_bdd_above hv1 hρ)

/-- The limsup of the diagonal is bounded above by the density bound. -/
lemma diagLimsup_le_density_bound {v : ℝ³ → ℝ} {ρ : ℝ} (hv : 0 ≤ v)
    (hv1 : MemLp v 1) (hρ : 0 ≤ ρ) :
    ∃ C : ℝ, 0 < C ∧ diagLimsup v ρ ≤ C * (ρ ^ 2 * vL1 v + ρ) := by
  rcases diag_le_density_bound hv1 with ⟨C, hCpos, hbd⟩
  refine ⟨C, hCpos, ?_⟩
  unfold diagLimsup
  apply limsup_le_of_eventually_le
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with L hL
    exact hbd hL hρ
  · exact diag_eventually_nonneg hv

/-- `liminf ≤ limsup` for the diagonal. -/
lemma diagLiminf_le_diagLimsup {v : ℝ³ → ℝ} {ρ : ℝ} (hv : 0 ≤ v)
    (hv1 : MemLp v 1) (hρ : 0 ≤ ρ) : diagLiminf v ρ ≤ diagLimsup v ρ := by
  unfold diagLiminf diagLimsup
  exact liminf_le_limsup_of_bounded (diag_eventually_nonneg hv)
    (diag_eventually_bdd_above hv1 hρ)

/-- The liminf of the diagonal is nondecreasing in the density. -/
lemma diagLiminf_mono {v : ℝ³ → ℝ} {ρ₁ ρ₂ : ℝ} (hv : 0 ≤ v) (hv1 : MemLp v 1)
    (hρ₁ : 0 ≤ ρ₁) (hρ : ρ₁ ≤ ρ₂) : diagLiminf v ρ₁ ≤ diagLiminf v ρ₂ := by
  have hρ₂ : 0 ≤ ρ₂ := le_trans hρ₁ hρ
  unfold diagLiminf
  apply liminf_mono_of_eventually_le
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with L hL
    exact diag_mono_ρ (v := v) (ρ₁ := ρ₁) (ρ₂ := ρ₂) (L := L) (by linarith) hv hv1 hρ
  · exact diag_eventually_nonneg (v := v) (ρ := ρ₁) hv
  · exact diag_eventually_bdd_above (v := v) (ρ := ρ₂) hv1 hρ₂

/-! ## Grid windows

Write `G_m := gridSide m ℓ R = mℓ + (m−1)R`.  For `ℓ > 0`, `R ≥ 0`:

- `G_{m+1} = G_m + (ℓ+R)` and `G_m = m(ℓ+R) − R`;
- `m ↦ G_m` is strictly increasing and `G_m > 0` for `m ≥ 1`;
- every `L ≥ G_1` belongs to an interval `[G_m, G_{m+1}]` with
  `m := ⌊(L+R)/(ℓ+R)⌋` (`gridWinIdx`), and `m ≥ M` once `L ≥ G_{M+1}`;
- the rescaling factor `(m/G_m)³ → (ℓ+R)^{-3}`.
-/

/-- The grid-window index of `L`: `m := ⌊(L+R)/(ℓ+R)⌋`, so that
`G_m ≤ L ≤ G_{m+1}` whenever `L ≥ G_1`. -/
noncomputable def gridWinIdx (ℓ R L : ℝ) : ℕ :=
  Nat.floor ((L + R) / (ℓ + R))

/-- `gridSide` is affine-linear in the grid index: `G_m = m(ℓ+R) − R`. -/
lemma gridSide_eq {m : ℕ} {ℓ R : ℝ} : gridSide m ℓ R = (m : ℝ) * (ℓ + R) - R := by
  unfold gridSide
  ring

/-- `G_1 = ℓ`. -/
lemma gridSide_one {ℓ R : ℝ} : gridSide 1 ℓ R = ℓ := by
  unfold gridSide
  ring

/-- Successor formula: `G_{m+1} = G_m + (ℓ + R)`. -/
lemma gridSide_succ {m : ℕ} {ℓ R : ℝ} :
    gridSide (m + 1) ℓ R = gridSide m ℓ R + (ℓ + R) := by
  unfold gridSide
  push_cast
  ring

/-- `G_m` is monotone in `m` (for `ℓ ≥ 0`, `R ≥ 0`). -/
lemma gridSide_mono {m n : ℕ} {ℓ R : ℝ} (hℓ : 0 ≤ ℓ) (hR : 0 ≤ R) (hmn : m ≤ n) :
    gridSide m ℓ R ≤ gridSide n ℓ R := by
  rw [gridSide_eq, gridSide_eq]
  have hm : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hmn
  have hpos : 0 ≤ ℓ + R := add_nonneg hℓ hR
  have hmul : (m : ℝ) * (ℓ + R) ≤ (n : ℝ) * (ℓ + R) :=
    mul_le_mul_of_nonneg_right hm hpos
  linarith

/-- `G_m` is strictly increasing (for `ℓ > 0`, `R ≥ 0`). -/
lemma gridSide_lt {m n : ℕ} {ℓ R : ℝ} (hℓ : 0 < ℓ) (hR : 0 ≤ R) (hmn : m < n) :
    gridSide m ℓ R < gridSide n ℓ R := by
  rw [gridSide_eq, gridSide_eq]
  have hm : (m : ℝ) < (n : ℝ) := by exact_mod_cast hmn
  have hpos : 0 < ℓ + R := by linarith
  have hmul : (m : ℝ) * (ℓ + R) < (n : ℝ) * (ℓ + R) :=
    mul_lt_mul_of_pos_right hm hpos
  linarith

/-- `G_m > 0` for `m ≥ 1` (with `ℓ > 0`, `R ≥ 0`). -/
lemma gridSide_pos {m : ℕ} {ℓ R : ℝ} (hm : 1 ≤ m) (hℓ : 0 < ℓ) (hR : 0 ≤ R) :
    0 < gridSide m ℓ R := by
  have hmr : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hpart : 0 ≤ ((m : ℝ) - 1) * R := mul_nonneg (by linarith) hR
  have hmain : 0 < (m : ℝ) * ℓ := mul_pos (by linarith) hℓ
  unfold gridSide
  nlinarith

/-- Lower window bound: `G_{m(L)} ≤ L` (for `L ≥ G_1`, i.e. `ℓ ≤ L`). -/
lemma gridWinIdx_lower {ℓ R L : ℝ} (hℓ : 0 < ℓ) (hR : 0 ≤ R) (hL : ℓ ≤ L) :
    gridSide (gridWinIdx ℓ R L) ℓ R ≤ L := by
  unfold gridWinIdx
  rw [gridSide_eq]
  have hden : 0 < ℓ + R := by linarith
  have hnum : 0 ≤ L + R := by nlinarith
  have hx0 : 0 ≤ (L + R) / (ℓ + R) := div_nonneg hnum hden.le
  have hfl : (Nat.floor ((L + R) / (ℓ + R)) : ℝ) ≤ (L + R) / (ℓ + R) := Nat.floor_le hx0
  have h1 : (Nat.floor ((L + R) / (ℓ + R)) : ℝ) * (ℓ + R) ≤ L + R := by
    rw [le_div_iff₀ hden] at hfl
    simpa [mul_comm, mul_left_comm, mul_assoc] using hfl
  nlinarith

/-- Upper window bound: `L ≤ G_{m(L)+1}`. -/
lemma gridWinIdx_upper {ℓ R L : ℝ} (hℓ : 0 < ℓ) (hR : 0 ≤ R) (hL : ℓ ≤ L) :
    L ≤ gridSide (gridWinIdx ℓ R L + 1) ℓ R := by
  unfold gridWinIdx
  rw [gridSide_eq]
  have hden : 0 < ℓ + R := by linarith
  have hnum : 0 ≤ L + R := by nlinarith
  have hx0 : 0 ≤ (L + R) / (ℓ + R) := div_nonneg hnum hden.le
  have hfl : (L + R) / (ℓ + R) < (Nat.floor ((L + R) / (ℓ + R)) : ℝ) + 1 :=
    Nat.lt_floor_add_one _
  have h2 : L + R ≤ ((Nat.floor ((L + R) / (ℓ + R)) : ℝ) + 1) * (ℓ + R) := by
    rw [div_lt_iff₀ hden] at hfl
    exact le_of_lt (by simpa [mul_comm, mul_left_comm, mul_assoc] using hfl)
  have hcast : ((Nat.floor ((L + R) / (ℓ + R)) + 1 : ℕ) : ℝ) =
      (Nat.floor ((L + R) / (ℓ + R)) : ℝ) + 1 := by
    rw [Nat.cast_add, Nat.cast_one]
  nlinarith

/-- The window index is at least `1` once `L ≥ G_1`. -/
lemma gridWinIdx_ge_one {ℓ R L : ℝ} (hℓ : 0 < ℓ) (hR : 0 ≤ R) (hL : ℓ ≤ L) :
    1 ≤ gridWinIdx ℓ R L := by
  unfold gridWinIdx
  have hden : 0 < ℓ + R := by linarith
  have hnum : 0 ≤ L + R := by nlinarith
  have hx0 : 0 ≤ (L + R) / (ℓ + R) := div_nonneg hnum hden.le
  have hone : (1 : ℝ) ≤ (L + R) / (ℓ + R) := by
    rw [le_div_iff₀ hden]
    nlinarith
  exact (Nat.le_floor_iff hx0).2 (by simpa using hone)

/-- The window index is large once the box is: `L ≥ G_{M+1}` implies
`gridWinIdx ℓ R L ≥ M + 1 ≥ M`. -/
lemma gridWinIdx_ge_of_gridSide {M : ℕ} {ℓ R L : ℝ} (hℓ : 0 < ℓ) (hR : 0 ≤ R)
    (hL : gridSide (M + 1) ℓ R ≤ L) : M + 1 ≤ gridWinIdx ℓ R L := by
  unfold gridWinIdx
  have hden : 0 < ℓ + R := by linarith
  have hL' : ((M + 1 : ℕ) : ℝ) * (ℓ + R) - R ≤ L := by
    rw [gridSide_eq] at hL
    simpa using hL
  have hnum : 0 ≤ L + R := by nlinarith
  have hx0 : 0 ≤ (L + R) / (ℓ + R) := div_nonneg hnum hden.le
  have hM : ((M + 1 : ℕ) : ℝ) ≤ (L + R) / (ℓ + R) := by
    have h1 : ((M + 1 : ℕ) : ℝ) * (ℓ + R) ≤ L + R := by nlinarith
    rw [le_div_iff₀ hden]
    simpa using h1
  exact (Nat.le_floor_iff hx0).2 hM

/-- The grid rescaling factor: `(m/G_m)³ → (ℓ+R)^{-3}` (for `ℓ > 0`, `R ≥ 0`). -/
lemma tendsto_grid_cube_inv {ℓ R : ℝ} (hℓ : 0 < ℓ) (hR : 0 ≤ R) :
    Tendsto (fun m : ℕ => (m : ℝ) ^ 3 / gridSide m ℓ R ^ 3) atTop
      (𝓝 ((ℓ + R) ^ 3)⁻¹) := by
  have hpos : 0 < ℓ + R := by linarith
  have hRdiv : Tendsto (fun m : ℕ => R / (m : ℝ)) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul R
  have hs : Tendsto (fun m : ℕ => (ℓ + R) - R / (m : ℝ)) atTop (𝓝 (ℓ + R)) := by
    simpa using (tendsto_const_nhds.sub hRdiv)
  have hsc : Tendsto (fun m : ℕ => ((ℓ + R) - R / (m : ℝ)) ^ 3) atTop (𝓝 ((ℓ + R) ^ 3)) := by
    simpa using hs.pow 3
  have hne : (ℓ + R) ^ 3 ≠ 0 := pow_ne_zero 3 (ne_of_gt hpos)
  have hscinv : Tendsto (fun m : ℕ => (((ℓ + R) - R / (m : ℝ)) ^ 3)⁻¹) atTop
      (𝓝 (((ℓ + R) ^ 3)⁻¹)) := by
    exact hsc.inv₀ hne
  apply hscinv.congr'
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with m hm
    have hmne : (m : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt (lt_of_lt_of_le (by norm_num) hm))
    have hG : gridSide m ℓ R ≠ 0 := ne_of_gt (gridSide_pos hm hℓ hR)
    have hsm : (ℓ + R) - R / (m : ℝ) = gridSide m ℓ R / (m : ℝ) := by
      unfold gridSide
      field_simp [hmne]
      ring
    rw [hsm, div_pow]
    field_simp [hmne, hG]

/-- Eventual upper bound on the rescaling factor: for every `δ > 0`, eventually
`(m/G_m)³ ≤ (1+δ)·(ℓ+R)^{-3}`. -/
lemma grid_cube_eventually_le {ℓ R : ℝ} (hℓ : 0 < ℓ) (hR : 0 ≤ R) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ m : ℕ in atTop,
      (m : ℝ) ^ 3 / gridSide m ℓ R ^ 3 ≤ (1 + δ) * ((ℓ + R) ^ 3)⁻¹ := by
  have hpos : 0 < ℓ + R := by linarith
  have hcp : 0 < ((ℓ + R) ^ 3)⁻¹ := inv_pos.mpr (pow_pos hpos 3)
  have htarget : ((ℓ + R) ^ 3)⁻¹ < (1 + δ) * ((ℓ + R) ^ 3)⁻¹ := by
    nlinarith
  have hev : ∀ᶠ m : ℕ in atTop,
      (m : ℝ) ^ 3 / gridSide m ℓ R ^ 3 < (1 + δ) * ((ℓ + R) ^ 3)⁻¹ :=
    (tendsto_grid_cube_inv hℓ hR).eventually (isOpen_Iio.mem_nhds htarget)
  exact hev.mono (fun m hm => le_of_lt hm)

end BoseGases

end Submission
