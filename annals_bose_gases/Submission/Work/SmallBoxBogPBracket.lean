import Mathlib.Order.CompletePartialOrder
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import ChallengeDeps
import Submission.Commons.Measure.FinFunction.integrableOn_exterior_inv_pow_six
import Submission.Work.SmallBoxBogLatticeFactor
import Submission.Work.SmallBoxBogLogLeaf
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Session-262 — the abstract `|p| > 2c` p-space bracket of lm:appbogolubov
(`SmallBoxBogPBracket.lean`)

FS `lm:appbogolubov`'s refined bound (eq:refinedaprioribog, final_v2.tex
ll.3820–3850) reduces, over the region `|p| > 2c` (`c := (dsℓ)⁻¹`), the
per-mode Bogoliubov error `ℬ(p)²/𝒜(p)` — with the diagonal coefficient
`𝒜(p) = (|B|/(n+1))·[|p|−c]₊² + 2K_s·a` and `|ℬ(p)| ≤ C₀·a`
(eq:WSestimate) — to

    ∫_{|p|>2c} ℬ²/𝒜  ≤  ((n+1)/|B|) · [ (1 + C·c·a)·∫_{ℝ³}F²/|p|²
                                          + C·(C₀a)²·c·ln((c·a)⁻¹) ]

i.e. the Newtonian value `∫F²/p²` times the `(1+C·c·a)`-factor plus the
log-divergent `|p| ∈ (2c, a⁻¹)`-shell contribution cut by
`|F| ≤ C₀·a`.  This module certifies the underlying abstract
real-analysis content for a generic real function `F : ℝ³ → ℝ` with
`|F p| ≤ C₀·a` pointwise (the `ℬ := Ŵ₁`-instance is attached at the
per-mode Fock assembly; `|Ŵ₁(p)| ≤ Ŵ₁(0) = ∫W₁ ≤ C₀·(av)` holds
POINTWISE since `Ŵ₁` is the Fourier transform of the nonnegative
`W₁`):

  * `ann_inv_cube_value` — `∫_{2c≤‖p‖≤a⁻¹}‖p‖⁻³ = 4π·ln((2ca)⁻¹)`
    (the log-leaf value with the `c`-factor cancelled);
  * `integrableOn_ann_inv_cube` — integrability of `‖p‖⁻³` on the
    annulus (bounded set, bounded function);
  * **`pBdd_annulus_sq_inv_cube_le`** — the bounded fold
    `∫_{2c≤‖p‖≤a⁻¹} F(p)²·‖p‖⁻³ ≤ (C₀a)²·4π·ln((2ca)⁻¹)`
    (the `|p| < a⁻¹`-shell part of the bracket);
  * **`pBracket_inv_sub_sq_le`** — the assembled bracket
    `∫_{‖p‖≥2c} F(p)²/(‖p‖−c)² ≤ (1+6ca)·∫_{ℝ³}F(p)²/‖p‖²
        + 24π·c·(C₀a)²·ln((2ca)⁻¹)`
    (split at `|p| = a⁻¹`; the `|p| ≥ a⁻¹`-part is the `6ca`-correction
    via `inv_sub_sq_le` (universal `6`), the shell part is the log
    fold); hypotheses: `0 < c`, `0 < a`, `0 ≤ C₀`, the dilute
    `2·c·a ≤ 1`, `F` measurable, `|F p| ≤ C₀·a` pointwise, and
    `F²/‖p‖²` integrable.
  * `ball_two_c_volume` / `exterior_pow_six_two_c` — the other two
    momentum leaves of the refined bracket at `R := 2c`:
    `∫_{‖p‖<2c}1 = (4π/3)(2c)³` (the `|p| < 2c`-piece via
    `momentum_ball_integral_one`) and
    `∫_{‖p‖≥2c}‖p‖⁻⁶ = (4π/3)(2c)⁻³` (the `ℬ⁴/𝒜³`-piece via the
    commons `eucl_ball_exterior_pow_six`);
  * `inv_sub_sq6_pointwise_le` — `(‖p‖−c)⁻⁶ ≤ 64·‖p‖⁻⁶` on
    `{2c ≤ ‖p‖}` (the `ℬ⁴/𝒜³` pointwise reduction);
  * **`pBdd_exterior_pow4_inv_sub_sq6_le`** — the `ℬ⁴/𝒜³` exterior fold
    `∫_{‖p‖ ≥ 2c} F(p)⁴·(‖p‖−c)⁻⁶ dp ≤ 64·(C₀a)⁴·(4π/3)·(2c)⁻³`
    (integrability of `‖p‖⁻⁶` on the exterior via the commons
    `integrableOn_exterior_inv_pow_six`, committed by the fleet).

All integrals are over the corpus `EuclideanSpace ℝ (Fin 3)` (`ℝ³`)
with the standard volume.  The module is self-contained (imports only
the corpus momentum/log leaves + the commons pow-six leaf); the D1-body
instantiation (`F := Ŵ₁`) and the `(n+1)/|B|`-mode-count factors attach
at the per-mode Fock assembly (design-note Session-260 parts 6–8).
-/

noncomputable section
open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal
namespace Submission
open _root_.BoseGases
namespace BoseGases
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false

/-- Integrability of `‖p‖⁻³` on the closed annulus `{2c ≤ ‖p‖ ≤ a⁻¹}`
(bounded set of finite measure, bounded function: `‖p‖ ≥ 2c > 0`). -/
lemma integrableOn_ann_inv_cube {c a : ℝ} (hc : 0 < c) :
    MeasureTheory.IntegrableOn (fun p : ℝ³ => (‖p‖ ^ 3)⁻¹)
      {p : ℝ³ | 2 * c ≤ ‖p‖ ∧ ‖p‖ ≤ a⁻¹} := by
  let s : Set ℝ³ := {p : ℝ³ | 2 * c ≤ ‖p‖ ∧ ‖p‖ ≤ a⁻¹}
  have hsmeas : MeasurableSet s := by
    dsimp [s]
    measurability
  have hsfin : (volume : Measure ℝ³) s < (∞ : ℝ≥0∞) := by
    have hsub : s ⊆ Metric.closedBall (0 : ℝ³) a⁻¹ := by
      intro p hp
      simp [Metric.mem_closedBall, dist_eq_norm]
      exact hp.2
    exact lt_of_le_of_lt (MeasureTheory.measure_mono hsub)
      (MeasureTheory.measure_closedBall_lt_top (μ := (volume : Measure ℝ³)))
  have hbdd : ∀ p ∈ s, ‖(fun p : ℝ³ => (‖p‖ ^ 3)⁻¹) p‖ ≤ ((2 * c) ^ 3)⁻¹ := by
    intro p hp
    dsimp [s] at hp
    have hp1 : 2 * c ≤ ‖p‖ := hp.1
    have hpos : 0 < ‖p‖ := lt_of_lt_of_le (by nlinarith : (0 : ℝ) < 2 * c) hp1
    have h2c : 0 < 2 * c := by nlinarith
    have hpow := pow_le_pow_left₀ (le_of_lt h2c) hp1 3
    have hpos3 : 0 < (2 * c) ^ 3 := pow_pos h2c 3
    have hposb : 0 < ‖p‖ ^ 3 := pow_pos hpos 3
    have hle : (‖p‖ ^ 3)⁻¹ ≤ ((2 * c) ^ 3)⁻¹ := (inv_le_inv₀ hposb hpos3).mpr hpow
    calc
      ‖(fun p : ℝ³ => (‖p‖ ^ 3)⁻¹) p‖ = ‖(‖p‖ ^ 3)⁻¹‖ := rfl
      _ = (‖p‖ ^ 3)⁻¹ := abs_of_nonneg (inv_nonneg.mpr (pow_nonneg (norm_nonneg p) 3))
      _ ≤ ((2 * c) ^ 3)⁻¹ := hle
  have hmeas : AEStronglyMeasurable (fun p : ℝ³ => (‖p‖ ^ 3)⁻¹) (volume.restrict s) := by
    exact (by measurability : Measurable (fun p : ℝ³ => (‖p‖ ^ 3)⁻¹)).aestronglyMeasurable
  have hfi : MeasureTheory.HasFiniteIntegral (fun p : ℝ³ => (‖p‖ ^ 3)⁻¹) (volume.restrict s) := by
    refine MeasureTheory.HasFiniteIntegral.restrict_of_bounded (C := ((2 * c) ^ 3)⁻¹) ?_ ?_
    · exact hsfin
    · filter_upwards [ae_restrict_mem hsmeas] with p hp
      have hb := hbdd p hp
      simpa using hb
  exact ⟨hmeas, hfi⟩

/-- The exact annulus value `∫_{2c ≤ ‖p‖ ≤ a⁻¹} ‖p‖⁻³ = 4π·ln((2·c·a)⁻¹)`
for `0 < c`, `0 < a`, `2·c·a ≤ 1` (from `momentum_shell_log_bound_ln`,
with the `c`-factor cancelled). -/
lemma ann_inv_cube_value {c a : ℝ} (hc : 0 < c) (ha : 0 < a) (hreg : 2 * c * a ≤ 1) :
    (∫ p : ℝ³ in {p : ℝ³ | 2 * c ≤ ‖p‖ ∧ ‖p‖ ≤ a⁻¹}, (‖p‖ ^ 3)⁻¹)
      = 4 * Real.pi * Real.log ((2 * c * a)⁻¹) := by
  let s : Set ℝ³ := {p : ℝ³ | 2 * c ≤ ‖p‖ ∧ ‖p‖ ≤ a⁻¹}
  have hleaf := momentum_shell_log_bound_ln c hc a ha hreg
  have hcn : c ≠ 0 := ne_of_gt hc
  have hcv : (∫ p : ℝ³ in s, c * (‖p‖ ^ 3)⁻¹) = c * (∫ p : ℝ³ in s, (‖p‖ ^ 3)⁻¹) := by
    simpa [s] using (MeasureTheory.integral_const_mul
      (μ := (volume : Measure ℝ³).restrict s) (r := c) (f := fun p : ℝ³ => (‖p‖ ^ 3)⁻¹))
  have hstep1 : (∫ p : ℝ³ in s, (‖p‖ ^ 3)⁻¹) = c⁻¹ * (c * (∫ p : ℝ³ in s, (‖p‖ ^ 3)⁻¹)) := by
    field_simp [hcn]
  have hstep2 : c⁻¹ * (∫ p : ℝ³ in s, c * (‖p‖ ^ 3)⁻¹) = 4 * Real.pi * Real.log ((2 * c * a)⁻¹) := by
    calc
      c⁻¹ * (∫ p : ℝ³ in s, c * (‖p‖ ^ 3)⁻¹) = c⁻¹ * (4 * Real.pi * c * Real.log ((2 * c * a)⁻¹)) :=
            congrArg (fun t : ℝ => c⁻¹ * t) (by simpa [s] using hleaf)
      _ = 4 * Real.pi * Real.log ((2 * c * a)⁻¹) := by field_simp [hcn]
  calc
    (∫ p : ℝ³ in s, (‖p‖ ^ 3)⁻¹) = c⁻¹ * (c * (∫ p : ℝ³ in s, (‖p‖ ^ 3)⁻¹)) := hstep1
    _ = c⁻¹ * (∫ p : ℝ³ in s, c * (‖p‖ ^ 3)⁻¹) := by rw [← hcv]
    _ = 4 * Real.pi * Real.log ((2 * c * a)⁻¹) := hstep2

/-- **the bounded fold over the log shell** (FS: the `|p| ∈ (2c, a⁻¹)`
part of `∫_{|p|>2c}ℬ²/𝒜`, cut by `|ℬ(p)| ≤ C₀·a`):

    ∫_{2c ≤ ‖p‖ ≤ a⁻¹} F(p)²·‖p‖⁻³ dp ≤ (C₀·a)²·4π·ln((2·c·a)⁻¹)

(`|F p| ≤ C₀·a` pointwise, `0 ≤ C₀`, `2·c·a ≤ 1`). -/
lemma pBdd_annulus_sq_inv_cube_le {c a C₀ : ℝ} (hc : 0 < c) (ha : 0 < a)
    (hC0 : 0 ≤ C₀) (hreg : 2 * c * a ≤ 1) {F : ℝ³ → ℝ}
    (hbdd : ∀ p, |F p| ≤ C₀ * a) :
    (∫ p : ℝ³ in {p : ℝ³ | 2 * c ≤ ‖p‖ ∧ ‖p‖ ≤ a⁻¹}, (F p) ^ 2 * (‖p‖ ^ 3)⁻¹)
      ≤ (C₀ * a) ^ 2 * (4 * Real.pi * Real.log ((2 * c * a)⁻¹)) := by
  let s : Set ℝ³ := {p : ℝ³ | 2 * c ≤ ‖p‖ ∧ ‖p‖ ≤ a⁻¹}
  have hC0a : 0 ≤ C₀ * a := mul_nonneg hC0 (le_of_lt ha)
  have hgint : MeasureTheory.IntegrableOn (fun p : ℝ³ => (‖p‖ ^ 3)⁻¹) s := by
    simpa [s] using (integrableOn_ann_inv_cube (c := c) (a := a) hc)
  have hmono : (∫ p : ℝ³ in s, (F p) ^ 2 * (‖p‖ ^ 3)⁻¹)
      ≤ ∫ p : ℝ³ in s, (C₀ * a) ^ 2 * (‖p‖ ^ 3)⁻¹ := by
    refine setIntegral_mono_of_nonneg (g := fun p : ℝ³ => (C₀ * a) ^ 2 * (‖p‖ ^ 3)⁻¹) ?_ ?_ ?_
    · intro p hp
      exact mul_nonneg (sq_nonneg (F p)) (inv_nonneg.mpr (pow_nonneg (norm_nonneg p) 3))
    · intro p hp
      have hsq : (F p) ^ 2 ≤ (C₀ * a) ^ 2 := by
        have hsq' : |F p| ≤ |C₀ * a| := by
          calc
            |F p| ≤ C₀ * a := hbdd p
            _ = |C₀ * a| := (abs_of_nonneg hC0a).symm
        exact sq_le_sq.mpr hsq'
      exact mul_le_mul_of_nonneg_right hsq (inv_nonneg.mpr (pow_nonneg (norm_nonneg p) 3))
    · change MeasureTheory.Integrable (fun p : ℝ³ => (C₀ * a) ^ 2 * (‖p‖ ^ 3)⁻¹)
          ((volume : Measure ℝ³).restrict s)
      exact hgint.const_mul ((C₀ * a) ^ 2)
  have hval := ann_inv_cube_value hc ha hreg
  calc
    (∫ p : ℝ³ in s, (F p) ^ 2 * (‖p‖ ^ 3)⁻¹) ≤ ∫ p : ℝ³ in s, (C₀ * a) ^ 2 * (‖p‖ ^ 3)⁻¹ := hmono
    _ = (C₀ * a) ^ 2 * (∫ p : ℝ³ in s, (‖p‖ ^ 3)⁻¹) := by
        simpa using (MeasureTheory.integral_const_mul
          (μ := (volume : Measure ℝ³).restrict s) (r := (C₀ * a) ^ 2) (f := fun p : ℝ³ => (‖p‖ ^ 3)⁻¹))
    _ = (C₀ * a) ^ 2 * (4 * Real.pi * Real.log ((2 * c * a)⁻¹)) := by rw [hval]

/-- Pointwise inverse-square refinement on the region `2c ≤ ‖p‖`:
`F(p)²/(‖p‖−c)² ≤ F(p)²/‖p‖² + 6c·F(p)²/‖p‖³` (from `inv_sub_sq_le`,
the universal-6 `1/(1−t)² ≤ 1+6t`-type bound at `t := c/‖p‖ ≤ 1/2`). -/
lemma psubc_sq_pointwise_le {c : ℝ} (hc : 0 < c) (F : ℝ³ → ℝ) (p : ℝ³)
    (hp : 2 * c ≤ ‖p‖) :
    (F p) ^ 2 / (‖p‖ - c) ^ 2 ≤ (F p) ^ 2 / ‖p‖ ^ 2 + 6 * c * (F p) ^ 2 / ‖p‖ ^ 3 := by
  have hc0 : 0 < ‖p‖ := lt_of_lt_of_le (by nlinarith : (0 : ℝ) < 2 * c) hp
  have hpc : ‖p‖ - c ≠ 0 := by
    have : 0 < ‖p‖ - c := by nlinarith
    exact ne_of_gt this
  have hpn : ‖p‖ ≠ 0 := ne_of_gt hc0
  have hsq : (‖p‖ - c)⁻¹ ^ 2 ≤ ‖p‖⁻¹ ^ 2 * (1 + 6 * c / ‖p‖) := inv_sub_sq_le hc hp
  have hpt : (F p) ^ 2 / (‖p‖ - c) ^ 2 = (F p) ^ 2 * (‖p‖ - c)⁻¹ ^ 2 := by
    field_simp [hpc]
  have hpt2 : (F p) ^ 2 / ‖p‖ ^ 2 + 6 * c * (F p) ^ 2 / ‖p‖ ^ 3
      = (F p) ^ 2 * (‖p‖⁻¹ ^ 2 * (1 + 6 * c / ‖p‖)) := by
    field_simp [hpn]
  calc
    (F p) ^ 2 / (‖p‖ - c) ^ 2 = (F p) ^ 2 * (‖p‖ - c)⁻¹ ^ 2 := hpt
    _ ≤ (F p) ^ 2 * (‖p‖⁻¹ ^ 2 * (1 + 6 * c / ‖p‖)) := by
        exact mul_le_mul_of_nonneg_left hsq (sq_nonneg (F p))
    _ = (F p) ^ 2 / ‖p‖ ^ 2 + 6 * c * (F p) ^ 2 / ‖p‖ ^ 3 := hpt2.symm

/-- On `{2c ≤ ‖p‖}`: `‖p‖⁻¹ ≤ (2c)⁻¹`. -/
lemma inv_norm_le_inv_two_c {c : ℝ} (hc : 0 < c) (p : ℝ³) (hp : 2 * c ≤ ‖p‖) :
    (‖p‖ : ℝ)⁻¹ ≤ (2 * c)⁻¹ := by
  have hpos : 0 < ‖p‖ := lt_of_lt_of_le (by nlinarith : (0 : ℝ) < 2 * c) hp
  have h2c : 0 < 2 * c := by nlinarith
  exact (inv_le_inv₀ hpos h2c).mpr (by nlinarith)

/-- The exterior region is the disjoint union of the log shell and the
far exterior: `{2c ≤ ‖p‖} = {2c ≤ ‖p‖ ≤ a⁻¹} ∪ {a⁻¹ < ‖p‖}` for
`2·c·a ≤ 1`, `0 < a`. -/
lemma split_set_union {c a : ℝ} (hreg : 2 * c * a ≤ 1) (ha : 0 < a) :
    {p : ℝ³ | 2 * c ≤ ‖p‖}
      = {p : ℝ³ | 2 * c ≤ ‖p‖ ∧ ‖p‖ ≤ a⁻¹} ∪ {p : ℝ³ | a⁻¹ < ‖p‖} := by
  have hle : 2 * c ≤ a⁻¹ := by
    simpa [one_div] using (le_div_iff₀ ha).mpr hreg
  ext p
  constructor
  · intro hp
    by_cases hsmall : ‖p‖ ≤ a⁻¹
    · exact Or.inl ⟨hp, hsmall⟩
    · exact Or.inr (lt_of_not_ge hsmall)
  · intro hp
    rcases hp with hpAnn | hpExt
    · exact hpAnn.1
    · have hp1 : a⁻¹ ≤ ‖p‖ := le_of_lt hpExt
      exact le_trans hle hp1

/-- **the abstract `|p| > 2c` p-space bracket** (FS eq:refinedaprioribog,
the `∫_{|p|>2c} ℬ²/𝒜 ≤ ((n+1)/|B|)·∫F²/(|p|−c)²`-content): for a real
`F : ℝ³ → ℝ` with `|F p| ≤ C₀·a` pointwise and `F²/‖p‖²` integrable,
with `0 < c`, `0 < a`, `0 ≤ C₀`, `2·c·a ≤ 1`,

    ∫_{‖p‖ ≥ 2c} F(p)²/(‖p‖−c)² dp
        ≤ (1 + 6·c·a)·∫_{ℝ³}F(p)²/‖p‖² dp + 6·c·(C₀·a)²·4π·ln((2·c·a)⁻¹)

(split at `|p| = a⁻¹`: the far-exterior `|p| ≥ a⁻¹`-part contributes the
`6ca`-correction of the Newtonian value via `inv_sub_sq_le`; the shell
`2c ≤ |p| ≤ a⁻¹`-part is the log fold `pBdd_annulus_sq_inv_cube_le`).
With `F := Ŵ₁`, `C₀ := 16π`, `c := (dsℓ)⁻¹` this is the |p|>2c error
content of `lm:appbogolubov`. -/
theorem pBracket_inv_sub_sq_le {c a C₀ : ℝ} (hc : 0 < c) (ha : 0 < a)
    (hC0 : 0 ≤ C₀) (hreg : 2 * c * a ≤ 1) {F : ℝ³ → ℝ}
    (hmeasF : Measurable F) (hbdd : ∀ p, |F p| ≤ C₀ * a)
    (hint : MeasureTheory.Integrable (fun p : ℝ³ => (F p) ^ 2 / ‖p‖ ^ 2)) :
    (∫ p : ℝ³ in {p : ℝ³ | 2 * c ≤ ‖p‖}, (F p) ^ 2 / (‖p‖ - c) ^ 2)
      ≤ (1 + 6 * c * a) * (∫ p : ℝ³, (F p) ^ 2 / ‖p‖ ^ 2)
        + 6 * c * (C₀ * a) ^ 2 * (4 * Real.pi * Real.log ((2 * c * a)⁻¹)) := by
  let S : Set ℝ³ := {p : ℝ³ | 2 * c ≤ ‖p‖}
  let Ann : Set ℝ³ := {p : ℝ³ | 2 * c ≤ ‖p‖ ∧ ‖p‖ ≤ a⁻¹}
  let Ext : Set ℝ³ := {p : ℝ³ | a⁻¹ < ‖p‖}
  let f1 : ℝ³ → ℝ := fun p => (F p) ^ 2 / (‖p‖ - c) ^ 2
  let f2 : ℝ³ → ℝ := fun p => (F p) ^ 2 / ‖p‖ ^ 2
  let f3 : ℝ³ → ℝ := fun p => (F p) ^ 2 / ‖p‖ ^ 3
  have hSmeas : MeasurableSet S := by
    dsimp [S]
    measurability
  have hExtmeas : MeasurableSet Ext := by
    dsimp [Ext]
    measurability
  have hdisj : Disjoint Ann Ext := by
    rw [Set.disjoint_left]
    intro p hp
    dsimp [Ann, Ext] at hp ⊢
    exact (not_lt_of_ge hp.2)
  have hsplit : S = Ann ∪ Ext := by
    dsimp [S, Ann, Ext]
    exact split_set_union hreg ha
  have hf2S : MeasureTheory.Integrable f2 ((volume : Measure ℝ³).restrict S) := by
    change MeasureTheory.Integrable (fun p : ℝ³ => (F p) ^ 2 / ‖p‖ ^ 2)
      ((volume : Measure ℝ³).restrict S)
    exact hint.integrableOn
  have hf3S : MeasureTheory.Integrable f3 ((volume : Measure ℝ³).restrict S) := by
    have hmeas3 : AEStronglyMeasurable f3 (volume.restrict S) := by
      exact (by measurability : Measurable f3).aestronglyMeasurable
    have hbd : ∀ᵐ p ∂(volume.restrict S), ‖f3 p‖ ≤ (2 * c)⁻¹ * f2 p := by
      filter_upwards [ae_restrict_mem hSmeas] with p hp
      have hpos : 0 < ‖p‖ := lt_of_lt_of_le (by nlinarith : (0 : ℝ) < 2 * c) hp
      have hle : (F p) ^ 2 / ‖p‖ ^ 3 ≤ (2 * c)⁻¹ * ((F p) ^ 2 / ‖p‖ ^ 2) := by
        calc
          (F p) ^ 2 / ‖p‖ ^ 3 = ((F p) ^ 2 / ‖p‖ ^ 2) * ‖p‖⁻¹ := by
                field_simp [ne_of_gt (pow_pos hpos 3), ne_of_gt (sq_pos_of_pos hpos)]
          _ ≤ ((F p) ^ 2 / ‖p‖ ^ 2) * (2 * c)⁻¹ := by
                exact mul_le_mul_of_nonneg_left (inv_norm_le_inv_two_c hc p hp)
                  (div_nonneg (sq_nonneg (F p)) (sq_nonneg ‖p‖))
          _ = (2 * c)⁻¹ * ((F p) ^ 2 / ‖p‖ ^ 2) := by ring
      have habs : ‖f3 p‖ = (F p) ^ 2 / ‖p‖ ^ 3 := by
        dsimp [f3]
        exact abs_of_nonneg (div_nonneg (sq_nonneg (F p)) (pow_nonneg (norm_nonneg p) 3))
      calc
        ‖f3 p‖ = (F p) ^ 2 / ‖p‖ ^ 3 := habs
        _ ≤ (2 * c)⁻¹ * ((F p) ^ 2 / ‖p‖ ^ 2) := hle
        _ = (2 * c)⁻¹ * f2 p := by dsimp [f2]
    exact MeasureTheory.Integrable.mono' (hg := (hf2S.const_mul ((2 * c)⁻¹))) hmeas3 hbd
  have hf1_le : (∫ p : ℝ³ in S, f1 p) ≤ ∫ p : ℝ³ in S, f2 p + 6 * c * f3 p := by
    refine setIntegral_mono_of_nonneg (g := fun p : ℝ³ => f2 p + 6 * c * f3 p) ?_ ?_ ?_
    · intro p hp
      dsimp [f1]
      exact div_nonneg (sq_nonneg (F p)) (sq_nonneg (‖p‖ - c))
    · intro p hp
      dsimp [f1, f2, f3]
      have hpt := psubc_sq_pointwise_le hc F p hp
      calc
        (F p) ^ 2 / (‖p‖ - c) ^ 2 ≤ (F p) ^ 2 / ‖p‖ ^ 2 + 6 * c * (F p) ^ 2 / ‖p‖ ^ 3 := hpt
        _ = (F p) ^ 2 / ‖p‖ ^ 2 + 6 * c * ((F p) ^ 2 / ‖p‖ ^ 3) := by ring
    · change MeasureTheory.Integrable (fun p : ℝ³ => f2 p + 6 * c * f3 p)
        ((volume : Measure ℝ³).restrict S)
      exact hf2S.add (hf3S.const_mul (6 * c))
  have hadd : (∫ p : ℝ³ in S, f2 p + 6 * c * f3 p)
      = (∫ p : ℝ³ in S, f2 p) + 6 * c * (∫ p : ℝ³ in S, f3 p) := by
    have h1 : (∫ p : ℝ³ in S, f2 p + 6 * c * f3 p)
        = (∫ p : ℝ³ in S, f2 p) + (∫ p : ℝ³ in S, 6 * c * f3 p) := by
      simpa using (integral_add (μ := (volume : Measure ℝ³).restrict S) (f := f2)
        (g := fun p : ℝ³ => 6 * c * f3 p) hf2S (hf3S.const_mul (6 * c)))
    have h2 : (∫ p : ℝ³ in S, 6 * c * f3 p) = 6 * c * (∫ p : ℝ³ in S, f3 p) := by
      simpa using (MeasureTheory.integral_const_mul
        (μ := (volume : Measure ℝ³).restrict S) (r := 6 * c) (f := f3))
    rw [h1, h2]
  have h2cle : 2 * c ≤ a⁻¹ := by
    simpa [one_div] using (le_div_iff₀ ha).mpr hreg
  have hunion : (∫ p : ℝ³ in S, f3 p) = (∫ p : ℝ³ in Ann, f3 p) + (∫ p : ℝ³ in Ext, f3 p) := by
    have hfs : MeasureTheory.IntegrableOn f3 S := by
      change MeasureTheory.Integrable f3 ((volume : Measure ℝ³).restrict S)
      exact hf3S
    have hfAnn : MeasureTheory.IntegrableOn f3 Ann := hfs.mono_set (by
      intro p hp
      exact hp.1)
    have hfExt : MeasureTheory.IntegrableOn f3 Ext := hfs.mono_set (by
      intro p hp
      have hp1 : a⁻¹ ≤ ‖p‖ := le_of_lt hp
      exact le_trans h2cle hp1)
    have hu := setIntegral_union (s := Ann) (t := Ext) (f := f3) (μ := (volume : Measure ℝ³))
      hdisj hExtmeas hfAnn hfExt
    rw [hsplit]
    exact hu
  have hannB : (∫ p : ℝ³ in Ann, f3 p) ≤ (C₀ * a) ^ 2 * (4 * Real.pi * Real.log ((2 * c * a)⁻¹)) := by
    dsimp [Ann, f3]
    exact pBdd_annulus_sq_inv_cube_le (c := c) (a := a) (C₀ := C₀) hc ha hC0 hreg hbdd
  have hExtB : (∫ p : ℝ³ in Ext, f3 p) ≤ a * (∫ p : ℝ³, f2 p) := by
    have hmono : (∫ p : ℝ³ in Ext, f3 p) ≤ ∫ p : ℝ³ in Ext, a * f2 p := by
      refine setIntegral_mono_of_nonneg (g := fun p : ℝ³ => a * f2 p) ?_ ?_ ?_
      · intro p hp
        dsimp [f3]
        exact div_nonneg (sq_nonneg (F p)) (pow_nonneg (norm_nonneg p) 3)
      · intro p hp
        have hpa : a⁻¹ ≤ ‖p‖ := le_of_lt hp
        have hpos : 0 < ‖p‖ := lt_of_lt_of_le (inv_pos.mpr ha) hpa
        have hmp : a * a⁻¹ ≤ a * ‖p‖ := mul_le_mul_of_nonneg_left hpa (le_of_lt ha)
        have hmain : ‖p‖⁻¹ ≤ a := (inv_le_iff_one_le_mul₀ hpos).2 (by
          simpa [mul_comm, mul_inv_cancel₀ (ne_of_gt ha)] using hmp)
        have hle : (F p) ^ 2 / ‖p‖ ^ 3 ≤ a * ((F p) ^ 2 / ‖p‖ ^ 2) := by
          calc
            (F p) ^ 2 / ‖p‖ ^ 3 = ((F p) ^ 2 / ‖p‖ ^ 2) * ‖p‖⁻¹ := by
                  field_simp [ne_of_gt (pow_pos hpos 3), ne_of_gt (sq_pos_of_pos hpos)]
            _ ≤ ((F p) ^ 2 / ‖p‖ ^ 2) * a := by
                  exact mul_le_mul_of_nonneg_left hmain (div_nonneg (sq_nonneg (F p)) (sq_nonneg ‖p‖))
            _ = a * ((F p) ^ 2 / ‖p‖ ^ 2) := by ring
        dsimp [f3, f2]
        exact hle
      · change MeasureTheory.Integrable (fun p : ℝ³ => a * f2 p) ((volume : Measure ℝ³).restrict Ext)
        have hintExt : MeasureTheory.Integrable f2 ((volume : Measure ℝ³).restrict Ext) := by
          change MeasureTheory.Integrable (fun p : ℝ³ => (F p) ^ 2 / ‖p‖ ^ 2) ((volume : Measure ℝ³).restrict Ext)
          exact hint.integrableOn
        exact hintExt.const_mul a
    have hconst : (∫ p : ℝ³ in Ext, a * f2 p) = a * (∫ p : ℝ³ in Ext, f2 p) := by
      simpa using (MeasureTheory.integral_const_mul
        (μ := (volume : Measure ℝ³).restrict Ext) (r := a) (f := f2))
    have hsub : (∫ p : ℝ³ in Ext, f2 p) ≤ (∫ p : ℝ³, f2 p) := by
      exact setIntegral_le_integral hint (by
        refine ae_of_all _ ?_
        intro p
        dsimp [f2]
        exact div_nonneg (sq_nonneg (F p)) (sq_nonneg ‖p‖))
    calc
      (∫ p : ℝ³ in Ext, f3 p) ≤ ∫ p : ℝ³ in Ext, a * f2 p := hmono
      _ = a * (∫ p : ℝ³ in Ext, f2 p) := hconst
      _ ≤ a * (∫ p : ℝ³, f2 p) := mul_le_mul_of_nonneg_left hsub (le_of_lt ha)
  have hmain_calc :
      (∫ p : ℝ³ in S, f2 p) + 6 * c * (∫ p : ℝ³ in S, f3 p)
        ≤ (∫ p : ℝ³, f2 p) + 6 * c * ((C₀ * a) ^ 2 * (4 * Real.pi * Real.log ((2 * c * a)⁻¹)) + a * (∫ p : ℝ³, f2 p)) := by
    have hstepA : (∫ p : ℝ³ in S, f2 p) ≤ (∫ p : ℝ³, f2 p) := by
      exact setIntegral_le_integral hint (by
        refine ae_of_all _ ?_
        intro p
        dsimp [f2]
        exact div_nonneg (sq_nonneg (F p)) (sq_nonneg ‖p‖))
    have hstepB : (∫ p : ℝ³ in S, f3 p) ≤ (C₀ * a) ^ 2 * (4 * Real.pi * Real.log ((2 * c * a)⁻¹)) + a * (∫ p : ℝ³, f2 p) := by
      calc
        (∫ p : ℝ³ in S, f3 p) = (∫ p : ℝ³ in Ann, f3 p) + (∫ p : ℝ³ in Ext, f3 p) := hunion
        _ ≤ (C₀ * a) ^ 2 * (4 * Real.pi * Real.log ((2 * c * a)⁻¹)) + a * (∫ p : ℝ³, f2 p) := add_le_add hannB hExtB
    exact add_le_add hstepA (mul_le_mul_of_nonneg_left hstepB (mul_nonneg (by norm_num : (0 : ℝ) ≤ 6) (le_of_lt hc)))
  calc
    (∫ p : ℝ³ in S, f1 p) ≤ ∫ p : ℝ³ in S, f2 p + 6 * c * f3 p := hf1_le
    _ = (∫ p : ℝ³ in S, f2 p) + 6 * c * (∫ p : ℝ³ in S, f3 p) := hadd
    _ ≤ (∫ p : ℝ³, f2 p) + 6 * c * ((C₀ * a) ^ 2 * (4 * Real.pi * Real.log ((2 * c * a)⁻¹)) + a * (∫ p : ℝ³, f2 p)) := hmain_calc
    _ = (1 + 6 * c * a) * (∫ p : ℝ³, f2 p) + 6 * c * (C₀ * a) ^ 2 * (4 * Real.pi * Real.log ((2 * c * a)⁻¹)) := by ring

/-- The `|p| < 2c`-ball volume leaf at the model threshold:
`∫_{‖p‖ < 2c} 1 dp = (4π/3)·(2c)³` (`momentum_ball_integral_one` at
`R := 2c`). -/
lemma ball_two_c_volume (c : ℝ) (hc : 0 < c) :
    (∫ p : ℝ³ in Metric.ball (0 : ℝ³) (2 * c), (1 : ℝ)) = (4 / 3 : ℝ) * Real.pi * (2 * c) ^ 3 := by
  exact momentum_ball_integral_one (2 * c) (by positivity)

/-- The `ℬ⁴/𝒜³`-exterior leaf at the model threshold:
`∫_{‖p‖ ≥ 2c} ‖p‖⁻⁶ dp = (4π/3)·(2c)⁻³` (the commons
`eucl_ball_exterior_pow_six` at `R := 2c`). -/
lemma exterior_pow_six_two_c (c : ℝ) (hc : 0 < c) :
    (∫ p : ℝ³ in {p : ℝ³ | 2 * c ≤ ‖p‖}, (‖p‖ ^ 6)⁻¹)
      = (4 / 3 : ℝ) * Real.pi * ((2 * c) ^ 3)⁻¹ := by
  exact Commons.Measure.FinFunction.eucl_ball_exterior_pow_six (2 * c) (by positivity)

/-- Pointwise inverse-sixth refinement on `{2c ≤ ‖p‖}`:
`(‖p‖−c)⁻⁶ ≤ 64·‖p‖⁻⁶` (from `‖p‖−c ≥ ‖p‖/2`). -/
lemma inv_sub_sq6_pointwise_le {c : ℝ} (hc : 0 < c) (p : ℝ³) (hp : 2 * c ≤ ‖p‖) :
    ((‖p‖ - c) ^ 6)⁻¹ ≤ 64 * (‖p‖ ^ 6)⁻¹ := by
  have hc0 : 0 < ‖p‖ := lt_of_lt_of_le (by nlinarith : (0 : ℝ) < 2 * c) hp
  have hpc : 0 < ‖p‖ - c := by nlinarith
  have hhalf : ‖p‖ / 2 ≤ ‖p‖ - c := by nlinarith
  have hpos1 : 0 < ‖p‖ / 2 := by positivity
  have hpowle : (‖p‖ / 2) ^ 6 ≤ (‖p‖ - c) ^ 6 :=
    pow_le_pow_left₀ (le_of_lt hpos1) hhalf 6
  have hinvle : ((‖p‖ - c) ^ 6)⁻¹ ≤ ((‖p‖ / 2) ^ 6)⁻¹ :=
    (inv_le_inv₀ (pow_pos hpc 6) (pow_pos hpos1 6)).mpr hpowle
  have hcalc : ((‖p‖ / 2) ^ 6)⁻¹ = 64 * (‖p‖ ^ 6)⁻¹ := by
    field_simp [ne_of_gt hc0]
    ring
  rw [← hcalc]
  exact hinvle

/-- **the `ℬ⁴/𝒜³` exterior fold** (FS eq:refinedaprioribog's
`∫_{|p|>2c}ℬ⁴/𝒜³ ≤ C·(C₀a)⁴·((n+1)/|B|)³·(2c)⁻³`-content): for
`|F p| ≤ C₀·a` pointwise,

    ∫_{‖p‖ ≥ 2c} F(p)⁴·(‖p‖−c)⁻⁶ dp ≤ 64·(C₀·a)⁴·(4π/3)·(2c)⁻³

(`F⁴ ≤ (C₀a)⁴` and `(‖p‖−c)⁻⁶ ≤ 64‖p‖⁻⁶` on the region; the exterior
`‖p‖⁻⁶`-integral via the commons `eucl_ball_exterior_pow_six` at
`R := 2c`, integrability via the commons
`integrableOn_exterior_inv_pow_six`). -/
lemma pBdd_exterior_pow4_inv_sub_sq6_le {c a C₀ : ℝ} (hc : 0 < c) (ha : 0 < a)
    (hC0 : 0 ≤ C₀) {F : ℝ³ → ℝ} (hbdd : ∀ p, |F p| ≤ C₀ * a) :
    (∫ p : ℝ³ in {p : ℝ³ | 2 * c ≤ ‖p‖}, (F p) ^ 4 * ((‖p‖ - c) ^ 6)⁻¹)
      ≤ 64 * (C₀ * a) ^ 4 * ((4 / 3 : ℝ) * Real.pi * ((2 * c) ^ 3)⁻¹) := by
  let s : Set ℝ³ := {p : ℝ³ | 2 * c ≤ ‖p‖}
  have hC0a : 0 ≤ C₀ * a := mul_nonneg hC0 (le_of_lt ha)
  have hgint : MeasureTheory.IntegrableOn (fun p : ℝ³ => 64 * (C₀ * a) ^ 4 * (‖p‖ ^ 6)⁻¹) s := by
    have hE := Commons.Measure.FinFunction.integrableOn_exterior_inv_pow_six (2 * c) (by positivity)
    have hE' : MeasureTheory.IntegrableOn (fun p : ℝ³ => (‖p‖ ^ 6)⁻¹) s := by
      simpa [s] using hE
    change MeasureTheory.Integrable (fun p : ℝ³ => 64 * (C₀ * a) ^ 4 * (‖p‖ ^ 6)⁻¹)
      ((volume : Measure ℝ³).restrict s)
    exact hE'.const_mul (64 * (C₀ * a) ^ 4)
  have hmono : (∫ p : ℝ³ in s, (F p) ^ 4 * ((‖p‖ - c) ^ 6)⁻¹)
      ≤ ∫ p : ℝ³ in s, 64 * (C₀ * a) ^ 4 * (‖p‖ ^ 6)⁻¹ := by
    refine setIntegral_mono_of_nonneg (g := fun p : ℝ³ => 64 * (C₀ * a) ^ 4 * (‖p‖ ^ 6)⁻¹) ?_ ?_ ?_
    · intro p hp
      exact mul_nonneg (by positivity : 0 ≤ (F p) ^ 4)
        (inv_nonneg.mpr (by positivity : 0 ≤ (‖p‖ - c) ^ 6))
    · intro p hp
      have hF4 : (F p) ^ 4 ≤ (C₀ * a) ^ 4 := by
        have hpw : |F p| ^ 4 ≤ (C₀ * a) ^ 4 :=
          pow_le_pow_left₀ (abs_nonneg (F p)) (hbdd p) 4
        calc
          (F p) ^ 4 = |F p| ^ 4 := by
                rw [← abs_pow (F p) 4]
                exact (abs_of_nonneg (by positivity : 0 ≤ (F p) ^ 4)).symm
          _ ≤ (C₀ * a) ^ 4 := hpw
      have hsix := inv_sub_sq6_pointwise_le hc p hp
      have hF0 : 0 ≤ (F p) ^ 4 := by positivity
      have hstep1 : (F p) ^ 4 * ((‖p‖ - c) ^ 6)⁻¹ ≤ (C₀ * a) ^ 4 * ((‖p‖ - c) ^ 6)⁻¹ := by
        exact mul_le_mul_of_nonneg_right hF4 (inv_nonneg.mpr (by positivity : 0 ≤ (‖p‖ - c) ^ 6))
      have hC04 : 0 ≤ (C₀ * a) ^ 4 := by positivity
      have hstep2 : (C₀ * a) ^ 4 * ((‖p‖ - c) ^ 6)⁻¹ ≤ (C₀ * a) ^ 4 * (64 * (‖p‖ ^ 6)⁻¹) := by
        exact mul_le_mul_of_nonneg_left hsix hC04
      calc
        (F p) ^ 4 * ((‖p‖ - c) ^ 6)⁻¹ ≤ (C₀ * a) ^ 4 * ((‖p‖ - c) ^ 6)⁻¹ := hstep1
        _ ≤ (C₀ * a) ^ 4 * (64 * (‖p‖ ^ 6)⁻¹) := hstep2
        _ = 64 * (C₀ * a) ^ 4 * (‖p‖ ^ 6)⁻¹ := by ring
    · exact hgint
  have hval := exterior_pow_six_two_c c hc
  calc
    (∫ p : ℝ³ in s, (F p) ^ 4 * ((‖p‖ - c) ^ 6)⁻¹)
        ≤ ∫ p : ℝ³ in s, 64 * (C₀ * a) ^ 4 * (‖p‖ ^ 6)⁻¹ := hmono
    _ = 64 * (C₀ * a) ^ 4 * (∫ p : ℝ³ in s, (‖p‖ ^ 6)⁻¹) := by
        simpa using (MeasureTheory.integral_const_mul
          (μ := (volume : Measure ℝ³).restrict s) (r := 64 * (C₀ * a) ^ 4) (f := fun p : ℝ³ => (‖p‖ ^ 6)⁻¹))
    _ = 64 * (C₀ * a) ^ 4 * ((4 / 3 : ℝ) * Real.pi * ((2 * c) ^ 3)⁻¹) :=
        congrArg (fun t : ℝ => 64 * (C₀ * a) ^ 4 * t) (by simpa [s] using hval)

end BoseGases
end Submission
