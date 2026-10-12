import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseFixB1.perBoxF_flat
import Submission.Work.BoseFixB1S.psiWeightVarianceFrowB1
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1.Up.FrowSharp` — **cycle-free copy of the sharp `F`-row** (`Fsharp`)

The sharp upper `F`-row of the flat branch,

    `flatFterm ≤ normB · F(flatTau) + (4μ²/(flatTau+μ)²) · flatVar`   (`Fsharp`)

is *proved* in the corpus as `Work.BoseFixB1B.flatFterm_sharp_row`
(`Submission/Work/BoseFixB1B/flatFterm_sharp_row.lean`, `#print axioms` clean) and
`Work.BoseFixB1S.F_weight_le_mean_add_var_sharpB1`.  **Both live in modules that (transitively)
import `Work.BoseFixB1.perBoxFWeight_holds`** — `flatFterm_sharp_row` through
`flatFrowTwoSidedB1` → `perBoxF_thick` → `perBoxF_localised`.  Consequently *no* module in the
import cone of `perBoxFWeight_holds` can import them (Lean rejects the import cycle), and in
particular the flat-branch residual `Up.flatFreeResidual` (whose file is imported by the target)
could not use them.

This module is a **verbatim, namespace-renamed copy** (`Work.BoseFixB1S`/`Work.BoseFixB1B` →
`Work.BoseFixB1.Up`) of exactly the declarations on that path, so that everything above the target
can cite the sharp `F`-row without the cycle.  Nothing is new mathematics: the proofs are the
corpus's.

* from `Submission/Work/BoseFixB1S/flatFrowTwoSidedB1.lean` (§§1–4): `psiWeight_one_eq_linear`,
  `psiWeight_one_taylor_le_sharp`, `psiWeight_one_window_sub`, `psiWeight_one_window_iff`,
  `integral_psiWeight_le_of_mean_sharp`, `integral_psiWeight_ge_of_mean`, `F_weight_ge_meanB1`,
  **`F_weight_le_mean_add_var_sharpB1`**;
* from `Submission/Work/BoseFixB1B/flatFterm_sharp_row.lean`: the box-continuity helpers,
  `integral_mul_sq_sub_mean`, `flatFterm_le_sharp_variance`, **`flatFterm_sharp_row`**.

The `flatVar`/`flatT2` vocabulary is the corpus's `Work.BoseFixB1B.{flatVar,flatT2}`
(imported, not copied).
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.BoseFixB1.Up

open _root_.BoseGases Submission.BoseGases Work.BoseBoxFix Work.BoseBox Work.UBB
open Work.SmallBoxSliding Work.BoseFixB1 Work.BoseFixB1S

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

/-! ## 0. The variance vocabulary (`flatT2`, `flatVar`)

Verbatim copies of `Work.BoseFixB1B.flatT2` / `Work.BoseFixB1B.flatVar`
(`Submission/Work/BoseFixB1B/flatBranchLedgerDefs.lean`), reproduced here so that this module's
import cone stays free of the target.  -/

/-- `∫Φ²·t²` at FS's parameters, `t := nCountB M ℓ d u / chiMass M ℓ d u`. -/
noncomputable def flatT2 (v : EuclideanSpace ℝ (Fin 3) → ℝ) (μ : ℝ) {n : ℕ}
    (Φ : Submission.BoseGases.X n → ℝ) (u : EuclideanSpace ℝ (Fin 3)) : ℝ :=
  ∫ x in Submission.BoseGases.abox n (Work.BoseFixB1.pL v μ), (Φ x) ^ 2 *
    (Work.BoseFixB1.nCountB (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
        (Work.BoseFixB1.pD v μ) u x
      / Work.SmallBoxSliding.chiMass (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
          (Work.BoseFixB1.pD v μ) u) ^ 2

/-- The state's smooth-density variance `V = ∫Φ²t² − τ²‖Φ‖²`. -/
noncomputable def flatVar (v : EuclideanSpace ℝ (Fin 3) → ℝ) (μ : ℝ) {n : ℕ}
    (Φ : Submission.BoseGases.X n → ℝ) (u : EuclideanSpace ℝ (Fin 3)) : ℝ :=
  flatT2 v μ Φ u
    - Work.BoseFixB1.flatTau (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
        (Work.BoseFixB1.pD v μ) u Φ ^ 2
      * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ)

/-! ## Part 1 (copied from `Work.BoseFixB1S.flatFrowTwoSidedB1` §§1–4) -/


/-! ## 1. The linear form of `F`, and the pointwise sharp Taylor bound -/

/-- **The linear form of FS's weight**: `F(t) = μt − 3μ² + 4μ³/(t+μ)` (`t ≥ 0`, `μ > 0`). -/
theorem psiWeight_one_eq_linear {μ t : ℝ} (hμ : 0 < μ) (ht : 0 ≤ t) :
    Work.SmallBoxSliding.psiWeight 1 μ t = μ * t - 3 * μ ^ 2 + 4 * μ ^ 3 / (t + μ) := by
  rw [psiWeight_one_eq' hμ ht]
  have h0 : t + μ ≠ 0 := by positivity
  field_simp
  ring

/-- **The sharpened pointwise Taylor bound**: the exact remainder of `psiWeight_one_taylor_exact`
is `≤ 4μ²(t−τ)²/(τ+μ)²` (since `t + μ ≥ μ`), so

    F(t) ≤ F(τ) + F'(τ)(t−τ) + 4μ²(t−τ)²/(τ+μ)²

for `t, τ ≥ 0`, `μ > 0`.  This improves `psiWeight_one_taylor_le`'s absolute coefficient `4` to
the one the *sharp* row needs: at the borderline `τ = μ` the quadratic coefficient becomes
`4μ²/(2μ)² = 1`. -/
theorem psiWeight_one_taylor_le_sharp {μ t τ : ℝ} (hμ : 0 < μ) (ht : 0 ≤ t) (hτ : 0 ≤ τ) :
    Work.SmallBoxSliding.psiWeight 1 μ t
      ≤ Work.SmallBoxSliding.psiWeight 1 μ τ
        + (μ * (τ - μ) * (τ + 3 * μ) / (τ + μ) ^ 2) * (t - τ)
        + (4 * μ ^ 2 / (τ + μ) ^ 2) * (t - τ) ^ 2 := by
  rw [psiWeight_one_taylor_exact hμ ht hτ]
  have hpos1 : 0 < (t + μ) * (τ + μ) ^ 2 := by positivity
  have hpos2 : 0 < (τ + μ) ^ 2 := by positivity
  have hle : 4 * μ ^ 3 / ((t + μ) * (τ + μ) ^ 2) ≤ 4 * μ ^ 2 / (τ + μ) ^ 2 := by
    rw [div_le_div_iff₀ hpos1 hpos2]
    have hfac : 4 * μ ^ 2 * ((t + μ) * (τ + μ) ^ 2) - 4 * μ ^ 3 * (τ + μ) ^ 2
        = 4 * μ ^ 2 * (τ + μ) ^ 2 * t := by ring
    nlinarith [hfac, mul_nonneg (mul_nonneg (by positivity) (sq_nonneg (τ + μ))) ht]
  have hkey : 4 * μ ^ 3 / ((t + μ) * (τ + μ) ^ 2) * (t - τ) ^ 2
      ≤ (4 * μ ^ 2 / (τ + μ) ^ 2) * (t - τ) ^ 2 :=
    mul_le_mul_of_nonneg_right hle (sq_nonneg _)
  rw [div_mul_eq_mul_div] at hkey
  linarith [hkey]

/-! ## 2. The window row is *equivalent* to the density window -/

/-- **The exact deficit of the window row**: for `t, T ≥ 0`, `μ > 0`,

    (μt + μ² − 4μ²t/(T+μ)) − F(t) = 4μ²t(T−t)/((t+μ)(T+μ)) . -/
theorem psiWeight_one_window_sub {μ T t : ℝ} (hμ : 0 < μ) (hT : 0 ≤ T) (ht : 0 ≤ t) :
    μ * t + μ ^ 2 - 4 * μ ^ 2 * t / (T + μ) - Work.SmallBoxSliding.psiWeight 1 μ t
      = 4 * μ ^ 2 * t * (T - t) / ((t + μ) * (T + μ)) := by
  rw [psiWeight_one_eq_linear hμ ht]
  have h1 : T + μ ≠ 0 := by positivity
  have h2 : t + μ ≠ 0 := by positivity
  field_simp
  ring

/-- **The window row holds *iff* the density is inside the window.**  For `t, T ≥ 0`, `μ > 0`,

    F(t) ≤ μt + μ² − 4μ²t/(T+μ)    ⟺    t ≤ T .

The deviation is `4μ²t(T−t)/((t+μ)(T+μ))`, so equality holds at `t = 0` and at `t = T`.  This is
the reason the linear `F`-row must be integrated as a *window* row: its window parameter `T` is
pinned from below by the pointwise density, and *no* choice of `T` makes the row hold outside its
window. -/
theorem psiWeight_one_window_iff {μ T t : ℝ} (hμ : 0 < μ) (hT : 0 ≤ T) (ht : 0 ≤ t) :
    (Work.SmallBoxSliding.psiWeight 1 μ t ≤ μ * t + μ ^ 2 - 4 * μ ^ 2 * t / (T + μ))
      ↔ t ≤ T := by
  have hid := psiWeight_one_window_sub (μ := μ) (T := T) (t := t) hμ hT ht
  have hden : 0 < (t + μ) * (T + μ) := by positivity
  have h4 : 0 < 4 * μ ^ 2 := by positivity
  have hnum : 0 ≤ 4 * μ ^ 2 * t := by positivity
  have hkey : (Work.SmallBoxSliding.psiWeight 1 μ t ≤ μ * t + μ ^ 2 - 4 * μ ^ 2 * t / (T + μ))
      ↔ 0 ≤ 4 * μ ^ 2 * t * (T - t) := by
    constructor
    · intro h
      have hpos : 0 ≤ μ * t + μ ^ 2 - 4 * μ ^ 2 * t / (T + μ)
          - Work.SmallBoxSliding.psiWeight 1 μ t := by linarith
      rw [hid] at hpos
      have hm := mul_le_mul_of_nonneg_right hpos (le_of_lt hden)
      simp only [zero_mul] at hm
      rwa [div_mul_cancel₀ _ (ne_of_gt hden)] at hm
    · intro h
      have hnonneg : 0 ≤ 4 * μ ^ 2 * t * (T - t) / ((t + μ) * (T + μ)) :=
        div_nonneg h (le_of_lt hden)
      rw [← hid] at hnonneg
      linarith
  rw [hkey]
  constructor
  · intro h
    by_cases ht0 : t = 0
    · rw [ht0]; exact hT
    · have htp : 0 < t := lt_of_le_of_ne ht (Ne.symm ht0)
      by_contra hcon
      push_neg at hcon
      have hneg : 4 * μ ^ 2 * t * (T - t) < 0 :=
        mul_neg_of_pos_of_neg (mul_pos h4 htp) (by linarith)
      linarith
  · intro h
    exact mul_nonneg hnum (by linarith)

/-! ## 3. The two-sided integral rows at a weighted mean -/

/-- **The sharpened upper row**: with the *exact* quadratic coefficient `4μ²/(τ+μ)²`,

    ∫ f·F(g) ≤ (∫f)·F(τ) + (4μ²/(τ+μ)²)·∫ f(g−τ)²

whenever `τ` is the `f`-weighted mean of `g` and `f, g ≥ 0` ae. -/
theorem integral_psiWeight_le_of_mean_sharp {α : Type*} [MeasurableSpace α] {μ : ℝ} (hμ : 0 < μ)
    {ν : Measure α} {f g : α → ℝ} {τ : ℝ} (hτ : 0 ≤ τ)
    (hf : Integrable f ν) (hfg : Integrable (fun x => f x * g x) ν)
    (hfg2 : Integrable (fun x => f x * g x ^ 2) ν)
    (hfψ : Integrable (fun x => f x * Work.SmallBoxSliding.psiWeight 1 μ (g x)) ν)
    (hmean : ∫ x, f x * (g x - τ) ∂ν = 0)
    (hf0 : 0 ≤ᵐ[ν] f) (hg0 : 0 ≤ᵐ[ν] g) :
    ∫ x, f x * Work.SmallBoxSliding.psiWeight 1 μ (g x) ∂ν
      ≤ (∫ x, f x ∂ν) * Work.SmallBoxSliding.psiWeight 1 μ τ
        + 4 * μ ^ 2 / (τ + μ) ^ 2 * ∫ x, f x * (g x - τ) ^ 2 ∂ν := by
  set c : ℝ := μ * (τ - μ) * (τ + 3 * μ) / (τ + μ) ^ 2 with hc
  set C : ℝ := 4 * μ ^ 2 / (τ + μ) ^ 2 with hC
  set A : α → ℝ := fun x => (Work.SmallBoxSliding.psiWeight 1 μ τ) * f x with hAdef
  set B : α → ℝ := fun x => c * (f x * (g x - τ)) with hBdef
  set D : α → ℝ := fun x => C * (f x * (g x - τ) ^ 2) with hDdef
  have hgτ : Integrable (fun x => f x * (g x - τ)) ν := by
    have h : (fun x => f x * (g x - τ)) = fun x => f x * g x - τ * f x := by
      funext x; ring
    rw [h]; exact hfg.sub (hf.const_mul τ)
  have hgτ2 : Integrable (fun x => f x * (g x - τ) ^ 2) ν := by
    have h : (fun x => f x * (g x - τ) ^ 2)
        = fun x => f x * g x ^ 2 - (2 * τ) * (f x * g x) + (τ ^ 2) * f x := by
      funext x; ring
    rw [h]
    exact (hfg2.sub (hfg.const_mul (2 * τ))).add (hf.const_mul (τ ^ 2))
  have hAi : Integrable A ν := by rw [hAdef]; exact hf.const_mul _
  have hBi : Integrable B ν := by rw [hBdef]; exact hgτ.const_mul c
  have hDi : Integrable D ν := by rw [hDdef]; exact hgτ2.const_mul C
  have hABi : Integrable (A + B) ν := hAi.add hBi
  have hABCi : Integrable (A + B + D) ν := hABi.add hDi
  have hpt : ∀ᵐ x ∂ν, f x * Work.SmallBoxSliding.psiWeight 1 μ (g x) ≤ (A + B + D) x := by
    filter_upwards [hf0, hg0] with x hfx hgx
    have h1 := psiWeight_one_taylor_le_sharp hμ hgx hτ
    rw [← hc, ← hC] at h1
    have hb := mul_le_mul_of_nonneg_left h1 hfx
    simp only [hAdef, hBdef, hDdef, Pi.add_apply]
    calc f x * Work.SmallBoxSliding.psiWeight 1 μ (g x)
        ≤ f x * (Work.SmallBoxSliding.psiWeight 1 μ τ + c * (g x - τ)
            + C * (g x - τ) ^ 2) := hb
      _ = Work.SmallBoxSliding.psiWeight 1 μ τ * f x + c * (f x * (g x - τ))
            + C * (f x * (g x - τ) ^ 2) := by ring
  have hmono : ∫ x, f x * Work.SmallBoxSliding.psiWeight 1 μ (g x) ∂ν
      ≤ ∫ x, (A + B + D) x ∂ν := integral_mono_ae hfψ hABCi hpt
  have e2 : ∫ x, (fun x => A x + B x) x + D x ∂ν
      = (∫ x, (fun x => A x + B x) x ∂ν) + (∫ x, D x ∂ν) := integral_add hABi hDi
  have e1 : ∫ x, A x + B x ∂ν = (∫ x, A x ∂ν) + (∫ x, B x ∂ν) := integral_add hAi hBi
  have i1 : ∫ x, A x ∂ν = (Work.SmallBoxSliding.psiWeight 1 μ τ) * (∫ x, f x ∂ν) := by
    rw [hAdef, integral_const_mul]
  have i2 : ∫ x, B x ∂ν = c * (∫ x, f x * (g x - τ) ∂ν) := by
    rw [hBdef, integral_const_mul]
  have i3 : ∫ x, D x ∂ν = C * (∫ x, f x * (g x - τ) ^ 2 ∂ν) := by
    rw [hDdef, integral_const_mul]
  have hv : ∫ x, (A + B + D) x ∂ν
      = (∫ x, f x ∂ν) * Work.SmallBoxSliding.psiWeight 1 μ τ
        + 4 * μ ^ 2 / (τ + μ) ^ 2 * ∫ x, f x * (g x - τ) ^ 2 ∂ν := by
    rw [show (∫ x, (A + B + D) x ∂ν) = ∫ x, (fun x => A x + B x) x + D x ∂ν from rfl,
      e2, e1, i1, i2, i3, hC, hc, hmean]
    simp only [mul_zero, add_zero]
    ring
  linarith [hmono, hv.le]

/-- **The lower row (= Jensen)**: since the exact expansion's remainder is positive,

    (∫f)·F(τ) ≤ ∫ f·F(g)

whenever `τ` is the `f`-weighted mean of `g` and `f, g ≥ 0` ae.  Together with
`integral_psiWeight_le_of_mean_sharp` this pins `∫f·F(g)` between the value at the mean and the
value at the mean plus the quadratic correction — the *two-sided sharp row*. -/
theorem integral_psiWeight_ge_of_mean {α : Type*} [MeasurableSpace α] {μ : ℝ} (hμ : 0 < μ)
    {ν : Measure α} {f g : α → ℝ} {τ : ℝ} (hτ : 0 ≤ τ)
    (hf : Integrable f ν) (hfg : Integrable (fun x => f x * g x) ν)
    (hfψ : Integrable (fun x => f x * Work.SmallBoxSliding.psiWeight 1 μ (g x)) ν)
    (hmean : ∫ x, f x * (g x - τ) ∂ν = 0)
    (hf0 : 0 ≤ᵐ[ν] f) (hg0 : 0 ≤ᵐ[ν] g) :
    (∫ x, f x ∂ν) * Work.SmallBoxSliding.psiWeight 1 μ τ
      ≤ ∫ x, f x * Work.SmallBoxSliding.psiWeight 1 μ (g x) ∂ν := by
  set c : ℝ := μ * (τ - μ) * (τ + 3 * μ) / (τ + μ) ^ 2 with hc
  set A : α → ℝ := fun x => (Work.SmallBoxSliding.psiWeight 1 μ τ) * f x with hAdef
  set B : α → ℝ := fun x => c * (f x * (g x - τ)) with hBdef
  have hgτ : Integrable (fun x => f x * (g x - τ)) ν := by
    have h : (fun x => f x * (g x - τ)) = fun x => f x * g x - τ * f x := by
      funext x; ring
    rw [h]; exact hfg.sub (hf.const_mul τ)
  have hAi : Integrable A ν := by rw [hAdef]; exact hf.const_mul _
  have hBi : Integrable B ν := by rw [hBdef]; exact hgτ.const_mul c
  have hABi : Integrable (A + B) ν := hAi.add hBi
  have hpt : ∀ᵐ x ∂ν, (A + B) x ≤ f x * Work.SmallBoxSliding.psiWeight 1 μ (g x) := by
    filter_upwards [hf0, hg0] with x hfx hgx
    simp only [Pi.zero_apply] at hfx hgx
    have h := psiWeight_one_taylor_exact hμ hgx hτ
    have hfr : (0 : ℝ) ≤ 4 * μ ^ 3 * (g x - τ) ^ 2 / ((g x + μ) * (τ + μ) ^ 2) := by
      have hden : 0 < (g x + μ) * (τ + μ) ^ 2 := by
        have h1 : 0 < g x + μ := by linarith
        have h2 : 0 < (τ + μ) ^ 2 := by positivity
        exact mul_pos h1 h2
      exact div_nonneg (mul_nonneg (by nlinarith [hμ, sq_nonneg μ] : (0:ℝ) ≤ 4 * μ ^ 3)
        (sq_nonneg _)) (le_of_lt hden)
    have hlow : Work.SmallBoxSliding.psiWeight 1 μ τ
        + (μ * (τ - μ) * (τ + 3 * μ) / (τ + μ) ^ 2) * (g x - τ)
        ≤ Work.SmallBoxSliding.psiWeight 1 μ (g x) := by
      rw [h]
      linarith [hfr]
    have hb := mul_le_mul_of_nonneg_left hlow hfx
    simp only [hAdef, hBdef, Pi.add_apply, hc]
    linarith [hb]
  have hmono : ∫ x, (A + B) x ∂ν ≤ ∫ x, f x * Work.SmallBoxSliding.psiWeight 1 μ (g x) ∂ν :=
    integral_mono_ae hABi hfψ hpt
  have e1 : ∫ x, A x + B x ∂ν = (∫ x, A x ∂ν) + (∫ x, B x ∂ν) := integral_add hAi hBi
  have i1 : ∫ x, A x ∂ν = (Work.SmallBoxSliding.psiWeight 1 μ τ) * (∫ x, f x ∂ν) := by
    rw [hAdef, integral_const_mul]
  have i2 : ∫ x, B x ∂ν = c * (∫ x, f x * (g x - τ) ∂ν) := by
    rw [hBdef, integral_const_mul]
  have hv : ∫ x, (A + B) x ∂ν = (∫ x, f x ∂ν) * Work.SmallBoxSliding.psiWeight 1 μ τ := by
    rw [show (∫ x, (A + B) x ∂ν) = ∫ x, A x + B x ∂ν from rfl, e1, i1, i2, hmean, mul_zero,
      add_zero]
    ring
  linarith [hmono, hv.le]

/-! ## 4. The two rows at the sliding box -/

/-- **The lower (`F`-)row at the sliding box**: `(∫Φ²)·F(τ) ≤ ∫Φ²·F(t)`. -/
theorem F_weight_ge_meanB1 {M : ℕ} (hM : 1 ≤ M) {ℓ d μ : ℝ} (hℓ : 0 < ℓ) (hμ : 0 < μ)
    (u : E3) {n : ℕ} {Φ : Submission.BoseGases.X n → ℝ} (hΦc : Continuous Φ)
    (hJ : 0 < ∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2) :
    (∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2)
        * Work.SmallBoxSliding.psiWeight 1 μ
            ((∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2 *
                (Work.BoseFixB1.nCountB M ℓ d u x / Work.SmallBoxSliding.chiMass M ℓ d u))
              / (∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2))
      ≤ ∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2 *
          Work.SmallBoxSliding.psiWeight 1 μ
            (Work.BoseFixB1.nCountB M ℓ d u x / Work.SmallBoxSliding.chiMass M ℓ d u) := by
  set κ : ℝ := Work.SmallBoxSliding.chiMass M ℓ d u with hκ
  set t : Submission.BoseGases.X n → ℝ := fun x => Work.BoseFixB1.nCountB M ℓ d u x / κ with ht
  set T : ℝ := (∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2 * t x)
      / (∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2) with hT
  have hκ0 : 0 ≤ κ := by rw [hκ]; exact Work.SmallBoxSliding.chiMass_nonneg M ℓ d u
  have hnc0 : ∀ x : Submission.BoseGases.X n, 0 ≤ Work.BoseFixB1.nCountB M ℓ d u x := by
    intro x; rw [Work.BoseFixB1.nCountB]
    exact Finset.sum_nonneg fun i _ => sq_nonneg _
  have ht0 : ∀ x, 0 ≤ t x := fun x => div_nonneg (hnc0 x) hκ0
  have hI2 : IntegrableOn (fun x => (Φ x) ^ 2)
      (Submission.BoseGases.abox n ℓ) volume :=
    ContinuousOn.integrableOn_compact (Submission.BoseGases.abox_compact n hℓ)
      ((hΦc.pow 2).continuousOn)
  have hnc : Continuous (fun x : Submission.BoseGases.X n => Work.BoseFixB1.nCountB M ℓ d u x) := by
    rw [show (fun x : Submission.BoseGases.X n => Work.BoseFixB1.nCountB M ℓ d u x)
        = (fun x : Submission.BoseGases.X n => ∑ i : Fin n,
            (Submission.BoseGases.chiSmallB M ℓ d u (x i)) ^ 2) from by
      funext x; rw [Work.BoseFixB1.nCountB]]
    refine continuous_finsetSum _ fun i _ => ?_
    have hc : Continuous (Submission.BoseGases.chiSmallB M ℓ d u) := by
      unfold Submission.BoseGases.chiSmallB
      exact (Submission.BoseGases.chiScale_continuous ℓ).mul
        ((Submission.BoseGases.chiSmall_continuous hM).comp (by fun_prop))
    exact (hc.comp (continuous_apply i)).pow 2
  have htc : Continuous t := hnc.div_const κ
  have hIt : IntegrableOn (fun x => (Φ x) ^ 2 * t x) (Submission.BoseGases.abox n ℓ) volume :=
    ContinuousOn.integrableOn_compact (Submission.BoseGases.abox_compact n hℓ)
      (((hΦc.pow 2).continuousOn).mul htc.continuousOn)
  have hIψ : IntegrableOn (fun x => (Φ x) ^ 2 * Work.SmallBoxSliding.psiWeight 1 μ (t x))
      (Submission.BoseGases.abox n ℓ) volume := by
    refine ContinuousOn.integrableOn_compact (Submission.BoseGases.abox_compact n hℓ) ?_
    rw [show (fun x : Submission.BoseGases.X n =>
          (Φ x) ^ 2 * Work.SmallBoxSliding.psiWeight 1 μ (t x))
        = fun x => (Φ x) ^ 2 * ((1 : ℝ) * (t x - μ) ^ 2 / (1 + t x * μ⁻¹)) from by
      funext x; rw [Work.SmallBoxSliding.psiWeight]]
    exact ((hΦc.pow 2).continuousOn).mul
      (ContinuousOn.div (by fun_prop) (by fun_prop) (fun x _ => by
        have hx := ht0 x
        have hinv : 0 ≤ μ⁻¹ := inv_nonneg.mpr hμ.le
        nlinarith [mul_nonneg hx hinv]))
  have hmean : ∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2 * (t x - T) = 0 := by
    have hsplit : ∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2 * (t x - T)
        = (∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2 * t x)
          - T * (∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2) := by
      rw [show (fun x : Submission.BoseGases.X n => (Φ x) ^ 2 * (t x - T))
          = fun x => (Φ x) ^ 2 * t x - T * (Φ x) ^ 2 from by funext x; ring]
      rw [integral_sub hIt (hI2.const_mul T), integral_const_mul]
    rw [hsplit, hT]
    field_simp
    ring
  have hT0 : 0 ≤ T := by
    rw [hT]
    exact div_nonneg (integral_nonneg fun x => mul_nonneg (sq_nonneg _) (ht0 x)) hJ.le
  have hmain := integral_psiWeight_ge_of_mean (ν := volume.restrict (Submission.BoseGases.abox n ℓ))
    hμ hT0 hI2 hIt hIψ hmean
    (Filter.Eventually.of_forall fun x => sq_nonneg _) (Filter.Eventually.of_forall ht0)
  simpa [ht, hκ, hT] using hmain

/-- **The sharpened upper `F`-row at the sliding box**: the quadratic correction carries the exact
coefficient `4μ²/(τ+μ)²` instead of the absolute `4` of `F_weight_le_mean_add_variance`. -/
theorem F_weight_le_mean_add_var_sharpB1 {M : ℕ} (hM : 1 ≤ M) {ℓ d μ : ℝ} (hℓ : 0 < ℓ)
    (hμ : 0 < μ) (u : E3) {n : ℕ} {Φ : Submission.BoseGases.X n → ℝ} (hΦc : Continuous Φ)
    (hJ : 0 < ∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2) :
    (∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2 *
        Work.SmallBoxSliding.psiWeight 1 μ
          (Work.BoseFixB1.nCountB M ℓ d u x / Work.SmallBoxSliding.chiMass M ℓ d u))
      ≤ (∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2)
          * Work.SmallBoxSliding.psiWeight 1 μ
              ((∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2 *
                  (Work.BoseFixB1.nCountB M ℓ d u x / Work.SmallBoxSliding.chiMass M ℓ d u))
                / (∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2))
        + 4 * μ ^ 2 / (((∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2 *
                    (Work.BoseFixB1.nCountB M ℓ d u x / Work.SmallBoxSliding.chiMass M ℓ d u))
                  / (∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2)) + μ) ^ 2
          * (∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2 *
              (Work.BoseFixB1.nCountB M ℓ d u x / Work.SmallBoxSliding.chiMass M ℓ d u
                - (∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2 *
                    (Work.BoseFixB1.nCountB M ℓ d u x / Work.SmallBoxSliding.chiMass M ℓ d u))
                  / (∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2)) ^ 2) := by
  set κ : ℝ := Work.SmallBoxSliding.chiMass M ℓ d u with hκ
  set t : Submission.BoseGases.X n → ℝ := fun x => Work.BoseFixB1.nCountB M ℓ d u x / κ with ht
  set T : ℝ := (∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2 * t x)
      / (∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2) with hT
  have hκ0 : 0 ≤ κ := by rw [hκ]; exact Work.SmallBoxSliding.chiMass_nonneg M ℓ d u
  have hnc0 : ∀ x : Submission.BoseGases.X n, 0 ≤ Work.BoseFixB1.nCountB M ℓ d u x := by
    intro x; rw [Work.BoseFixB1.nCountB]
    exact Finset.sum_nonneg fun i _ => sq_nonneg _
  have ht0 : ∀ x, 0 ≤ t x := fun x => div_nonneg (hnc0 x) hκ0
  have hI2 : IntegrableOn (fun x => (Φ x) ^ 2)
      (Submission.BoseGases.abox n ℓ) volume :=
    ContinuousOn.integrableOn_compact (Submission.BoseGases.abox_compact n hℓ)
      ((hΦc.pow 2).continuousOn)
  have hnc : Continuous (fun x : Submission.BoseGases.X n => Work.BoseFixB1.nCountB M ℓ d u x) := by
    rw [show (fun x : Submission.BoseGases.X n => Work.BoseFixB1.nCountB M ℓ d u x)
        = (fun x : Submission.BoseGases.X n => ∑ i : Fin n,
            (Submission.BoseGases.chiSmallB M ℓ d u (x i)) ^ 2) from by
      funext x; rw [Work.BoseFixB1.nCountB]]
    refine continuous_finsetSum _ fun i _ => ?_
    have hc : Continuous (Submission.BoseGases.chiSmallB M ℓ d u) := by
      unfold Submission.BoseGases.chiSmallB
      exact (Submission.BoseGases.chiScale_continuous ℓ).mul
        ((Submission.BoseGases.chiSmall_continuous hM).comp (by fun_prop))
    exact (hc.comp (continuous_apply i)).pow 2
  have htc : Continuous t := hnc.div_const κ
  have hIt : IntegrableOn (fun x => (Φ x) ^ 2 * t x) (Submission.BoseGases.abox n ℓ) volume :=
    ContinuousOn.integrableOn_compact (Submission.BoseGases.abox_compact n hℓ)
      (((hΦc.pow 2).continuousOn).mul htc.continuousOn)
  have hIt2 : IntegrableOn (fun x => (Φ x) ^ 2 * t x ^ 2) (Submission.BoseGases.abox n ℓ) volume :=
    ContinuousOn.integrableOn_compact (Submission.BoseGases.abox_compact n hℓ)
      (((hΦc.pow 2).continuousOn).mul (htc.pow 2).continuousOn)
  have hIψ : IntegrableOn (fun x => (Φ x) ^ 2 * Work.SmallBoxSliding.psiWeight 1 μ (t x))
      (Submission.BoseGases.abox n ℓ) volume := by
    refine ContinuousOn.integrableOn_compact (Submission.BoseGases.abox_compact n hℓ) ?_
    rw [show (fun x : Submission.BoseGases.X n =>
          (Φ x) ^ 2 * Work.SmallBoxSliding.psiWeight 1 μ (t x))
        = fun x => (Φ x) ^ 2 * ((1 : ℝ) * (t x - μ) ^ 2 / (1 + t x * μ⁻¹)) from by
      funext x; rw [Work.SmallBoxSliding.psiWeight]]
    exact ((hΦc.pow 2).continuousOn).mul
      (ContinuousOn.div (by fun_prop) (by fun_prop) (fun x _ => by
        have hx := ht0 x
        have hinv : 0 ≤ μ⁻¹ := inv_nonneg.mpr hμ.le
        nlinarith [mul_nonneg hx hinv]))
  have hmean : ∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2 * (t x - T) = 0 := by
    have hsplit : ∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2 * (t x - T)
        = (∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2 * t x)
          - T * (∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2) := by
      rw [show (fun x : Submission.BoseGases.X n => (Φ x) ^ 2 * (t x - T))
          = fun x => (Φ x) ^ 2 * t x - T * (Φ x) ^ 2 from by funext x; ring]
      rw [integral_sub hIt (hI2.const_mul T), integral_const_mul]
    rw [hsplit, hT]
    field_simp
    ring
  have hT0 : 0 ≤ T := by
    rw [hT]
    exact div_nonneg (integral_nonneg fun x => mul_nonneg (sq_nonneg _) (ht0 x)) hJ.le
  have hmain := integral_psiWeight_le_of_mean_sharp
    (ν := volume.restrict (Submission.BoseGases.abox n ℓ))
    hμ hT0 hI2 hIt hIt2 hIψ hmean
    (Filter.Eventually.of_forall fun x => sq_nonneg _) (Filter.Eventually.of_forall ht0)
  simpa [ht, hκ, hT] using hmain


/-! ## Part 2 (copied from `Work.BoseFixB1B.flatFterm_sharp_row`)
-/

/-! ## 1. Elementary facts about the (possibly degenerate) box

`abox n ℓ` is compact for **every** real `ℓ` (it is empty for `ℓ < 0`, a point for `ℓ = 0`) and
`chiSmallB`/`nCountB` are continuous for **every** `M` (at `M = 0` the cutoff is constant), so no
hypothesis on the parameters is needed.  (These are the same facts as in
`Submission/Work/BoseFixB1/flatFterm_le_tau_add_variance.lean`, reproduced locally to keep this
module's import cone light.) -/

private lemma acube_compact_all (ℓ : ℝ) : IsCompact (Submission.BoseGases.acube ℓ) := by
  by_cases h : 0 ≤ ℓ
  · exact (Metric.isCompact_iff_isClosed_bounded).mpr
      ⟨Submission.BoseGases.acube_isClosed ℓ, Submission.BoseGases.acube_isBounded ℓ h⟩
  · have hempty : Submission.BoseGases.acube ℓ = ∅ := by
      ext y
      constructor
      · intro hy
        simp only [Set.mem_empty_iff_false]
        rw [Submission.BoseGases.mem_acube_iff] at hy
        have h1 := hy 0
        linarith [h1.1, h1.2, not_le.mp h]
      · intro hy; exact absurd hy (Set.notMem_empty y)
    rw [hempty]; exact isCompact_empty

private lemma abox_compact_all (n : ℕ) (ℓ : ℝ) :
    IsCompact (Submission.BoseGases.abox n ℓ) := by
  rw [Submission.BoseGases.abox_eq_pi_acube]
  exact isCompact_univ_pi fun _ => acube_compact_all ℓ

private lemma chiSmall_continuous_all (M : ℕ) :
    Continuous (fun z : E3 => Submission.BoseGases.chiSmall M z) := by
  unfold Submission.BoseGases.chiSmall
  exact (Submission.BoseGases.chiSmallBase_continuous M).div_const _

private lemma chiSmallB_continuous_all (M : ℕ) (ℓ d : ℝ) (u : E3) :
    Continuous (fun x : E3 => Submission.BoseGases.chiSmallB M ℓ d u x) := by
  unfold Submission.BoseGases.chiSmallB
  exact (Submission.BoseGases.chiScale_continuous ℓ).mul
    ((chiSmall_continuous_all M).comp
      ((continuous_id.const_smul ((ℓ * d)⁻¹)).sub continuous_const))

private lemma nCountB_continuous_all (M : ℕ) (ℓ d : ℝ) (u : E3) {n : ℕ} :
    Continuous (fun x : Submission.BoseGases.X n => Work.BoseFixB1.nCountB M ℓ d u x) := by
  rw [show (fun x : Submission.BoseGases.X n => Work.BoseFixB1.nCountB M ℓ d u x)
      = fun x => ∑ i : Fin n, (Submission.BoseGases.chiSmallB M ℓ d u (x i)) ^ 2 from by
    funext x; rw [Work.BoseFixB1.nCountB]]
  exact continuous_finsetSum _ fun i _ =>
    ((chiSmallB_continuous_all M ℓ d u).comp (continuous_apply i)).pow 2

private lemma nCountB_nonneg_all (M : ℕ) (ℓ d : ℝ) (u : E3) {n : ℕ}
    (x : Submission.BoseGases.X n) : 0 ≤ Work.BoseFixB1.nCountB M ℓ d u x := by
  rw [Work.BoseFixB1.nCountB]
  exact Finset.sum_nonneg fun i _ => sq_nonneg _

private lemma integrableOn_abox_all {n : ℕ} {ℓ : ℝ} {F : Submission.BoseGases.X n → ℝ}
    (hF : Continuous F) : IntegrableOn F (Submission.BoseGases.abox n ℓ) volume :=
  ContinuousOn.integrableOn_compact (abox_compact_all n ℓ) hF.continuousOn

/-! ## 2. The abstract mean–variance identity -/

/-- **The variance identity at a weighted mean.**  If `τ` is the `f`-weighted mean of `g`
(`τ·∫f = ∫ f g`) then

    ∫ f (g − τ)² = ∫ f g² − τ² ∫ f .

No positivity of `f` or `g` is needed — the identity is purely the expansion of the square (the
hypothesis `τ·∫f = ∫fg` is what makes the two cross terms cancel). -/
lemma integral_mul_sq_sub_mean {α : Type*} [MeasurableSpace α] {ν : Measure α}
    {f g : α → ℝ} {τ : ℝ} (hf : Integrable f ν)
    (hfg : Integrable (fun x => f x * g x) ν) (hfg2 : Integrable (fun x => f x * g x ^ 2) ν)
    (hτ : τ * ∫ x, f x ∂ν = ∫ x, f x * g x ∂ν) :
    ∫ x, f x * (g x - τ) ^ 2 ∂ν = (∫ x, f x * g x ^ 2 ∂ν) - τ ^ 2 * ∫ x, f x ∂ν := by
  set A : α → ℝ := fun x => f x * g x ^ 2 with hAdef
  set B : α → ℝ := fun x => (2 * τ) * (f x * g x) with hBdef
  set C : α → ℝ := fun x => τ ^ 2 * f x with hCdef
  have hA : Integrable A ν := by rw [hAdef]; exact hfg2
  have hB : Integrable B ν := by rw [hBdef]; exact hfg.const_mul _
  have hC : Integrable C ν := by rw [hCdef]; exact hf.const_mul _
  have hAB : ∫ x, (A x - B x) ∂ν = (∫ x, A x ∂ν) - (∫ x, B x ∂ν) :=
    MeasureTheory.integral_sub hA hB
  have hABC : ∫ x, (A x - B x + C x) ∂ν = (∫ x, (A x - B x) ∂ν) + (∫ x, C x ∂ν) :=
    MeasureTheory.integral_add (hA.sub hB) hC
  have hfun : (fun x => f x * (g x - τ) ^ 2) = fun x => A x - B x + C x := by
    funext x; simp only [hAdef, hBdef, hCdef]; ring
  have hAval : (∫ x, A x ∂ν) = ∫ x, f x * g x ^ 2 ∂ν := by rw [hAdef]
  have hBval : (∫ x, B x ∂ν) = (2 * τ) * ∫ x, f x * g x ∂ν := by
    rw [hBdef, MeasureTheory.integral_const_mul]
  have hCval : (∫ x, C x ∂ν) = τ ^ 2 * ∫ x, f x ∂ν := by
    rw [hCdef, MeasureTheory.integral_const_mul]
  rw [hfun, hABC, hAB, hAval, hBval, hCval, ← hτ]
  ring

/-! ## 3. The sharp `F`-row in the raw vocabulary -/

/-- **The sharp `F`-row at arbitrary parameters** (= `(Fsharp)` of the flat ledger, un-normalised).
With `t := nCountB M ℓ d u / chiMass M ℓ d u` the smooth local density, `N := ∫Φ²`,
`τ := flatTau M ℓ d u Φ` its `Φ²`-weighted mean and `T2 := ∫Φ²t²`,

    flatFterm M ℓ d μ u Φ ≤ N·(μ(τ−μ)²/(τ+μ)) + (4μ²/(τ+μ)²)·(T2 − τ²N) .

The right-hand side's bracket is the state's **count variance** `∫Φ²(t−τ)²`; the row follows from
the sharp Taylor expansion `psiWeight_one_taylor_le_sharp` integrated at the weighted mean
(`Work.BoseFixB1.Up.integral_psiWeight_le_of_mean_sharp`), whose quadratic coefficient
`4μ²/(τ+μ)²` is *exactly* the one appearing here.

Nothing is assumed about `M`, `ℓ`, `d`, `chiMass` or the state's mass: the degenerate cases
(`∫Φ² = 0` makes `Φ²` vanish a.e. on the compact box, so both sides vanish; `chiMass = 0` makes
`t ≡ 0` and `τ = 0`, again both sides vanishing) are handled explicitly below. -/
theorem flatFterm_le_sharp_variance {μ : ℝ} (hμ : 0 < μ) {M : ℕ} {ℓ d : ℝ} {u : E3} {n : ℕ}
    {Φ : Submission.BoseGases.X n → ℝ} (hΦc : Continuous Φ) :
    Work.BoseFixB1.flatFterm M ℓ d μ u Φ
      ≤ (∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2)
          * (μ * (Work.BoseFixB1.flatTau M ℓ d u Φ - μ) ^ 2
              / (Work.BoseFixB1.flatTau M ℓ d u Φ + μ))
        + 4 * μ ^ 2 / (Work.BoseFixB1.flatTau M ℓ d u Φ + μ) ^ 2
          * ((∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2 *
                (Work.BoseFixB1.nCountB M ℓ d u x / Work.SmallBoxSliding.chiMass M ℓ d u) ^ 2)
              - Work.BoseFixB1.flatTau M ℓ d u Φ ^ 2
                  * (∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2)) := by
  classical
  set N : ℝ := ∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2 with hNdef
  set τ : ℝ := Work.BoseFixB1.flatTau M ℓ d u Φ with hτdef
  set T2 : ℝ := ∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2 *
      (Work.BoseFixB1.nCountB M ℓ d u x / Work.SmallBoxSliding.chiMass M ℓ d u) ^ 2 with hT2def
  have hΦ2 : Continuous (fun x : Submission.BoseGases.X n => (Φ x) ^ 2) := hΦc.pow 2
  have hnc : Continuous (fun x : Submission.BoseGases.X n => Work.BoseFixB1.nCountB M ℓ d u x) :=
    nCountB_continuous_all M ℓ d u
  have hnc0 : ∀ x : Submission.BoseGases.X n, 0 ≤ Work.BoseFixB1.nCountB M ℓ d u x :=
    fun x => nCountB_nonneg_all M ℓ d u x
  have hκ0 : 0 ≤ Work.SmallBoxSliding.chiMass M ℓ d u :=
    Work.SmallBoxSliding.chiMass_nonneg M ℓ d u
  have hf_int : Integrable (fun x : Submission.BoseGases.X n => (Φ x) ^ 2)
      ((volume : Measure (Submission.BoseGases.X n)).restrict (Submission.BoseGases.abox n ℓ)) :=
    integrableOn_abox_all hΦ2
  have hfg_int : Integrable (fun x : Submission.BoseGases.X n => (Φ x) ^ 2 *
      (Work.BoseFixB1.nCountB M ℓ d u x / Work.SmallBoxSliding.chiMass M ℓ d u))
      ((volume : Measure (Submission.BoseGases.X n)).restrict (Submission.BoseGases.abox n ℓ)) :=
    integrableOn_abox_all (hΦ2.mul (hnc.div_const _))
  have hfg2_int : Integrable (fun x : Submission.BoseGases.X n => (Φ x) ^ 2 *
      (Work.BoseFixB1.nCountB M ℓ d u x / Work.SmallBoxSliding.chiMass M ℓ d u) ^ 2)
      ((volume : Measure (Submission.BoseGases.X n)).restrict (Submission.BoseGases.abox n ℓ)) :=
    integrableOn_abox_all (hΦ2.mul ((hnc.div_const _).pow 2))
  have hfψ_int : Integrable (fun x : Submission.BoseGases.X n => (Φ x) ^ 2 *
      Work.SmallBoxSliding.psiWeight 1 μ
        (Work.BoseFixB1.nCountB M ℓ d u x / Work.SmallBoxSliding.chiMass M ℓ d u))
      ((volume : Measure (Submission.BoseGases.X n)).restrict (Submission.BoseGases.abox n ℓ)) := by
    refine integrableOn_abox_all ?_
    rw [show (fun x : Submission.BoseGases.X n => (Φ x) ^ 2 * Work.SmallBoxSliding.psiWeight 1 μ
          (Work.BoseFixB1.nCountB M ℓ d u x / Work.SmallBoxSliding.chiMass M ℓ d u))
        = fun x : Submission.BoseGases.X n => (Φ x) ^ 2 *
            ((1 : ℝ) * (Work.BoseFixB1.nCountB M ℓ d u x / Work.SmallBoxSliding.chiMass M ℓ d u
                - μ) ^ 2
              / (1 + (Work.BoseFixB1.nCountB M ℓ d u x / Work.SmallBoxSliding.chiMass M ℓ d u)
                  * μ⁻¹)) from by
      funext x; rw [Work.SmallBoxSliding.psiWeight]]
    exact hΦ2.mul (Continuous.div (continuous_const.mul (((hnc.div_const _).sub
        continuous_const).pow 2))
      (continuous_const.add ((hnc.div_const _).mul continuous_const)) (fun x => by
        have hx : 0 ≤ Work.BoseFixB1.nCountB M ℓ d u x / Work.SmallBoxSliding.chiMass M ℓ d u :=
          div_nonneg (hnc0 x) hκ0
        have hinv : 0 ≤ μ⁻¹ := inv_nonneg.mpr hμ.le
        have h2 : 0 ≤ Work.BoseFixB1.nCountB M ℓ d u x / Work.SmallBoxSliding.chiMass M ℓ d u
            * μ⁻¹ := mul_nonneg hx hinv
        linarith))
  have hN0 : 0 ≤ N := by
    rw [hNdef]
    exact integral_nonneg fun x => sq_nonneg _
  rcases eq_or_lt_of_le hN0 with hNz | hNpos
  · -- ## degenerate case `∫Φ² = 0`: `Φ²` vanishes a.e. on the box, hence so do all integrals
    have hzint : (∫ x, (Φ x) ^ 2
        ∂((volume : Measure (Submission.BoseGases.X n)).restrict
          (Submission.BoseGases.abox n ℓ))) = 0 := by
      rw [← hNdef]; exact hNz.symm
    have hae : (fun x : Submission.BoseGases.X n => (Φ x) ^ 2) =ᵐ[
        ((volume : Measure (Submission.BoseGases.X n)).restrict
          (Submission.BoseGases.abox n ℓ))] 0 :=
      (MeasureTheory.integral_eq_zero_iff_of_nonneg (fun x => sq_nonneg (Φ x)) hf_int).mp hzint
    have hL : Work.BoseFixB1.flatFterm M ℓ d μ u Φ = 0 := by
      rw [Work.BoseFixB1.flatFterm]
      have hae2 : (fun x : Submission.BoseGases.X n => (Φ x) ^ 2 *
          Work.SmallBoxSliding.psiWeight 1 μ
            (Work.BoseFixB1.nCountB M ℓ d u x / Work.SmallBoxSliding.chiMass M ℓ d u)) =ᵐ[
          ((volume : Measure (Submission.BoseGases.X n)).restrict
            (Submission.BoseGases.abox n ℓ))] 0 := by
        filter_upwards [hae] with x hx
        simp only [Pi.zero_apply] at hx ⊢
        rw [hx]; ring
      rw [MeasureTheory.integral_congr_ae hae2]
      simp
    have hT2z : T2 = 0 := by
      rw [hT2def]
      have hae3 : (fun x : Submission.BoseGases.X n => (Φ x) ^ 2 *
          (Work.BoseFixB1.nCountB M ℓ d u x / Work.SmallBoxSliding.chiMass M ℓ d u) ^ 2) =ᵐ[
          ((volume : Measure (Submission.BoseGases.X n)).restrict
            (Submission.BoseGases.abox n ℓ))] 0 := by
        filter_upwards [hae] with x hx
        simp only [Pi.zero_apply] at hx ⊢
        rw [hx]; ring
      rw [MeasureTheory.integral_congr_ae hae3]
      simp
    have hτz : τ = 0 := by
      rw [hτdef, Work.BoseFixB1.flatTau,
        show Work.BoseFixB1.flatMass ℓ Φ = N from by rw [hNdef]; rfl, hNz.symm]
      simp
    rw [hL, hτz, hT2z, hNz.symm]
    norm_num
  · -- ## main case `∫Φ² > 0`
    have hS0 : 0 ≤ Work.BoseFixB1.flatScountB M ℓ d u Φ := by
      rw [Work.BoseFixB1.flatScountB]
      exact integral_nonneg fun x => mul_nonneg (sq_nonneg _) (hnc0 x)
    have hτval : τ = Work.BoseFixB1.flatScountB M ℓ d u Φ
        / (Work.SmallBoxSliding.chiMass M ℓ d u * N) := by
      rw [hτdef, Work.BoseFixB1.flatTau,
        show Work.BoseFixB1.flatMass ℓ Φ = N from by rw [hNdef]; rfl]
    have hτ0 : 0 ≤ τ := by
      rw [hτval]
      exact div_nonneg hS0 (mul_nonneg hκ0 hNpos.le)
    -- the mean density `∫Φ²t`
    have hmidB : (∫ x, (Φ x) ^ 2 * (Work.BoseFixB1.nCountB M ℓ d u x
          / Work.SmallBoxSliding.chiMass M ℓ d u)
        ∂((volume : Measure (Submission.BoseGases.X n)).restrict
          (Submission.BoseGases.abox n ℓ)))
        = Work.BoseFixB1.flatScountB M ℓ d u Φ / Work.SmallBoxSliding.chiMass M ℓ d u := by
      rw [show (fun x : Submission.BoseGases.X n => (Φ x) ^ 2 *
            (Work.BoseFixB1.nCountB M ℓ d u x / Work.SmallBoxSliding.chiMass M ℓ d u))
          = fun x : Submission.BoseGases.X n =>
              ((Φ x) ^ 2 * Work.BoseFixB1.nCountB M ℓ d u x)
                * (Work.SmallBoxSliding.chiMass M ℓ d u)⁻¹ from by
        funext x; ring]
      rw [MeasureTheory.integral_mul_const, Work.BoseFixB1.flatScountB, div_eq_mul_inv]
    -- `τ` is the `Φ²`-weighted mean of `t`
    have hmean : ∫ x, (Φ x) ^ 2 * (Work.BoseFixB1.nCountB M ℓ d u x
          / Work.SmallBoxSliding.chiMass M ℓ d u - τ)
        ∂((volume : Measure (Submission.BoseGases.X n)).restrict
          (Submission.BoseGases.abox n ℓ)) = 0 := by
      have hsplit : ∫ x, (Φ x) ^ 2 * (Work.BoseFixB1.nCountB M ℓ d u x
              / Work.SmallBoxSliding.chiMass M ℓ d u - τ)
            ∂((volume : Measure (Submission.BoseGases.X n)).restrict
              (Submission.BoseGases.abox n ℓ))
          = (∫ x, (Φ x) ^ 2 * (Work.BoseFixB1.nCountB M ℓ d u x
                / Work.SmallBoxSliding.chiMass M ℓ d u)
              ∂((volume : Measure (Submission.BoseGases.X n)).restrict
                (Submission.BoseGases.abox n ℓ)))
            - τ * (∫ x, (Φ x) ^ 2
                ∂((volume : Measure (Submission.BoseGases.X n)).restrict
                  (Submission.BoseGases.abox n ℓ))) := by
        rw [show (fun x : Submission.BoseGases.X n => (Φ x) ^ 2 *
              (Work.BoseFixB1.nCountB M ℓ d u x / Work.SmallBoxSliding.chiMass M ℓ d u - τ))
            = fun x : Submission.BoseGases.X n => (Φ x) ^ 2 *
                (Work.BoseFixB1.nCountB M ℓ d u x / Work.SmallBoxSliding.chiMass M ℓ d u)
              - τ * (Φ x) ^ 2 from by
          funext x; ring]
        rw [MeasureTheory.integral_sub hfg_int (hf_int.const_mul τ),
          MeasureTheory.integral_const_mul]
      rw [hsplit, hmidB, ← hNdef, hτval]
      have hNn : N ≠ 0 := ne_of_gt hNpos
      rw [div_mul_eq_mul_div, mul_div_mul_right _ _ hNn, sub_self]
    -- the sharp `F`-row at the weighted mean
    have hrow := Work.BoseFixB1.Up.integral_psiWeight_le_of_mean_sharp (μ := μ)
      (ν := (volume : Measure (Submission.BoseGases.X n)).restrict
        (Submission.BoseGases.abox n ℓ))
      (f := fun x : Submission.BoseGases.X n => (Φ x) ^ 2)
      (g := fun x : Submission.BoseGases.X n => Work.BoseFixB1.nCountB M ℓ d u x
        / Work.SmallBoxSliding.chiMass M ℓ d u)
      (τ := τ) hμ hτ0 hf_int hfg_int hfg2_int hfψ_int hmean
      (Filter.Eventually.of_forall fun x => sq_nonneg (Φ x))
      (Filter.Eventually.of_forall fun x => div_nonneg (hnc0 x) hκ0)
    -- the quadratic correction is the variance `T2 − τ²N`
    have hτN : τ * N = Work.BoseFixB1.flatScountB M ℓ d u Φ
        / Work.SmallBoxSliding.chiMass M ℓ d u := by
      rw [hτval, div_mul_eq_mul_div]
      exact mul_div_mul_right _ _ (ne_of_gt hNpos)
    have hτint : τ * (∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2)
        = ∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2 *
            (Work.BoseFixB1.nCountB M ℓ d u x / Work.SmallBoxSliding.chiMass M ℓ d u) := by
      rw [← hNdef, hmidB, ← hτN]
    have hexp : (∫ x, (Φ x) ^ 2 * (Work.BoseFixB1.nCountB M ℓ d u x
          / Work.SmallBoxSliding.chiMass M ℓ d u - τ) ^ 2
        ∂((volume : Measure (Submission.BoseGases.X n)).restrict
          (Submission.BoseGases.abox n ℓ))) = T2 - τ ^ 2 * N := by
      have h := integral_mul_sq_sub_mean
        (ν := (volume : Measure (Submission.BoseGases.X n)).restrict
          (Submission.BoseGases.abox n ℓ))
        (f := fun x : Submission.BoseGases.X n => (Φ x) ^ 2)
        (g := fun x : Submission.BoseGases.X n => Work.BoseFixB1.nCountB M ℓ d u x
          / Work.SmallBoxSliding.chiMass M ℓ d u)
        (τ := τ) hf_int hfg_int hfg2_int hτint
      rw [hT2def, hNdef]
      exact h
    rw [hexp] at hrow
    rw [Work.BoseFixB1S.psiWeight_one_eq' hμ hτ0] at hrow
    rw [← hNdef] at hrow
    rw [← Work.BoseFixB1.flatFterm] at hrow
    exact hrow

/-! ## 4. The requested row at FS's parameters -/

/-- **The sharp `F`-row `(Fsharp)` of the flat ledger at FS's parameters** (`Work.BoseFixB1.Up.flatFterm_sharp_row`):

    flatFterm ≤ ‖Φ‖²·(μ(τ−μ)²/(τ+μ)) + (4μ²/(τ+μ)²)·flatVar ,

with `τ = flatTau` the state's mean smooth density and `flatVar = ∫Φ²t² − τ²‖Φ‖²` its count
variance.  This is `flatFterm_le_sharp_variance` with the parameter block `pM/pL/pD` and the
identifications `normB = ∫_{abox n ℓ}Φ² = flatMass` and `flatVar = ∫Φ²(t−τ)²`.

No hypothesis on `Work.BoseBoxFix.Adm` is used beyond `0 < μ` and the state's smoothness, so the
row holds uniformly in every parameter regime (in particular without `0 < a v`, which `Adm` and
`Work.UBB.ScatSol v` do not provide). -/
theorem flatFterm_sharp_row {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    {ε₀ μ : ℝ} (hAdm : Work.BoseBoxFix.Adm v ε₀ μ)
    {n : ℕ} (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))
    (u : EuclideanSpace ℝ (Fin 3)) :
    Work.BoseFixB1.flatFterm (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
        (Work.BoseFixB1.pD v μ) μ u (Φ : Submission.BoseGases.X n → ℝ)
      ≤ Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ)
          * (μ * (Work.BoseFixB1.flatTau (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
                  (Work.BoseFixB1.pD v μ) u (Φ : Submission.BoseGases.X n → ℝ) - μ) ^ 2
              / (Work.BoseFixB1.flatTau (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
                  (Work.BoseFixB1.pD v μ) u (Φ : Submission.BoseGases.X n → ℝ) + μ))
        + 4 * μ ^ 2 / (Work.BoseFixB1.flatTau (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
              (Work.BoseFixB1.pD v μ) u (Φ : Submission.BoseGases.X n → ℝ) + μ) ^ 2
          * Work.BoseFixB1.Up.flatVar v μ (Φ : Submission.BoseGases.X n → ℝ) u := by
  have hμ : 0 < μ := hAdm.1
  have hΦc : Continuous (Φ : Submission.BoseGases.X n → ℝ) := Φ.contDiff.continuous
  have hkey := flatFterm_le_sharp_variance (μ := μ) (M := Work.BoseFixB1.pM v μ)
    (ℓ := Work.BoseFixB1.pL v μ) (d := Work.BoseFixB1.pD v μ) (u := u) (n := n)
    (Φ := (Φ : Submission.BoseGases.X n → ℝ)) hμ hΦc
  simpa only [Work.BoseFixB1.Up.flatVar, Work.BoseFixB1.Up.flatT2, Work.BoseBoxFix.normB,
    Work.BoseKinLoc.sqNormB] using hkey

end Work.BoseFixB1.Up
