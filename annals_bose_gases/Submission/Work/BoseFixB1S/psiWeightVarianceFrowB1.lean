import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1.AprioriPieces
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseFixB1S.psiWeightVarianceFrowB1` — the **sharp `F`-row** of `PerBoxF`

FS's weight is `F(t) = psiWeight 1 μ t = μ(t−μ)²/(t+μ)` (the corpus's
`Work.SmallBoxSliding.psiWeight 1 μ`).  Every route to the flat branch of `PerBoxF`
(`Submission/Work/BoseFixB1/AprioriPieces.lean`) consumes a *sharpening* of the crude
pointwise bound `F(t) ≤ μ(t+μ)` (`Work.BoseFixB1.perBoxF_pieces.psiWeight_le_mu_mul_add`)
at the borderline density `t = μ`; the corpus had only the crude form.

This module supplies the sharpening, in the **exact** form in which it is sharp, and the
integral ("F-row") consequence:

* `psiWeight_one_taylor_exact` — the **exact identity**
  `F(t) = F(τ) + F'(τ)(t−τ) + 4·μ³(t−τ)²/((t+μ)(τ+μ)²)`, `F'(τ) = μ(τ−μ)(τ+3μ)/(τ+μ)²`
  (proved by clearing denominators);
* `psiWeight_one_taylor_le` — the consequence `F(t) ≤ F(τ) + F'(τ)(t−τ) + 4(t−τ)²`
  (the remainder `4μ³(t−τ)²/((t+μ)(τ+μ)²)` is `≤ 4(t−τ)²` because `t,τ ≥ 0`);
* `integral_psiWeight_le_of_mean` — the **`F`-row at the weighted mean**: if `τ` is the
  `f`-weighted mean count (i.e. `∫f(g−τ) = 0`), then
  `∫ f·F(g) ≤ (∫f)·F(τ) + 4·∫ f (g−τ)²`, i.e. the crude row `(∫f)·F(τ) + O(f·Var)` — the
  linear term `F'(τ)∫f(g−τ)` vanishes *identically* and the **exact** square
  `∫f(g−τ)²` (the count variance) is what is left;
* `F_weight_le_mean_add_variance` — the same in the frozen corpus vocabulary at the sliding
  box `B(u)`: with `t := nCountB M ℓ d u x / chiMass M ℓ d u` and
  `τ := (∫Φ²t)/(∫Φ²)`,
  `∫Φ²F(t) ≤ (∫Φ²)·F(τ) + 4·∫Φ²(t−τ)²`.

## Why this is the right sharpening (and the constant is `4`, not `1/2`)

`F''(t) = 8μ³/(t+μ)³ ≤ 8` on `t ≥ 0`, so the Taylor remainder at `τ` is at most
`½·8·(t−τ)² = 4(t−τ)²`; the exact form above reaches it.  The `−3μ²`/`+4μ³/(t+μ)`
decomposition of `flatBranchAlt.psiWeight_one_decomp` loses exactly this square term, and the
crude `F ≤ μ(t+μ)` (whose loss is `4μ²∫Φ²t/(t+μ)`) is what makes the borderline density
`τ ≈ μ` fail: at `τ = μ` one has `F(τ) = 0 = F'(τ)`, so the *whole* demand of the row is the
square term `4∫Φ²(t−τ)²` — quadratic in the density fluctuation, not linear.

## Consequence for the flat branch, and the **refutation** of the `n`-free variance route

With `N := ∫Φ²`, `κ := chiMass`, `scountB := ∫Φ²·nCountB`, `τ = scountB/(κN)`:

    ∫Φ²F(nCountB/κ) ≤ N·F(τ) + 4·Var(t),     Var(t) := ∫Φ²(t − τ)².

The *crude* variance bound is elementary and **true** (and now delegated as
`Work.BoseFixB1S.flatVarCrudeB1`): if `χ_B² ≤ Cs` pointwise and `κ > 0` then
`t = nCountB/κ ∈ [0, nCs/κ]`, so
`∫Φ²(t−τ)² ≤ sup(t)·∫Φ²t = Cs·n·scountB/κ²`.

**The hoped-for `n`-free sharpening is FALSE**, and this is *the* structural obstruction of the
flat branch (two independent reviews of the statement
`∫Φ²(t−τ)² ≤ C·Cs·scountB/κ²` under the flat hypothesis `n₊ < γnN` produced the same
counterexample).  Take the **Bernoulli mixture**

    Φ = √w·Π f(x_i) + √(1−w)·Π g(x_i),     f ≈ const on the box B(u),  g ≈ const OUTSIDE it,

with weight `w < γ`.  Then

* `n₊ = Σ_i‖Q_iΦ‖² ≈ w·n·δ²` with `δ² = ‖f − ⨍_B f‖²` small (on the outside component every
  coordinate has `1_B(x_i) = 0`, so `Q_i` annihilates it), so the flat gate holds for `w < γ`;
* but `t ≈ nχ_B²/κ` on the `f`-component and `t ≈ 0` on the `g`-component, so
  `τ ≈ w·nχ_B²/κ` and `Var(t) ≈ w(1−w)(nχ_B²/κ)²`, while `scountB ≈ w·n·χ_B²`, giving
  `Var/scountB ≈ (1−w)nχ_B²/κ → ∞` as `n → ∞`.

So the flat gate bounds only the **weight** of the excited component, never its **concentration**:
`n₊ < γnN` does *not* make `Φ` spread, and `Var(t)` can be `n²`-sized.  Consequences:

1. the `τ`-Taylor F-row (`F_weight_le_mean_add_variance` above) is *lossy* on such states: on the
   mixture it gives `N·F(τ) + 4Var(t) ≈ 4wρ²N` with `ρ = nχ_B²/κ`, while the *true* row is
   `w·F(ρ)N + (1−w)μ²N` — and the crude bound `N(μ² + μτ)` is *better* there;
2. hence the flat branch's F-row must be handled by a **case split on the local density**
   (`t ≈ μ` borderline: the sharp Taylor row; `t ≫ μ`: the crude row, whose `μt` term is paid by
   the pair term) — exactly FS's own split — and *not* by a single `n`-free variance estimate;
3. equivalently, any residual stated with the *only* hypothesis `n₊ < γnN` and an `n`-free
   variance/Var-target cannot be closed; a **density-window** hypothesis on the smooth count
   (e.g. `t ≤ Kμ` on the band, cf. `Work.BoseFixB1B.FlatArmBand`'s hypotheses) is what makes the
   variance `μκ`-sized.

**The product-state computation** (for the record): for `Φ = Π f(x_i)` with `N = 1`,
`x := ∫χ²f²`, `y := ∫χ⁴f²`, one has `Var(t) = n(y − x²)/κ²`, and the sharp bound
`Var ≤ C·Cs·scountB/κ² = Cn x Cs/κ²` reduces to `y − x² ≤ C Cs x` — **true** (since `χ² ≤ Cs`).
So the product states are fine; the obstruction is genuinely the *mixture/concentration*. -/

noncomputable section

open MeasureTheory

namespace Work.BoseFixB1S

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ## 1. The exact second-order Taylor identity for FS's weight -/

/-- FS's weight in the rational (`c = 1`) form: `F(t) = μ(t−μ)²/(t+μ)`. -/
theorem psiWeight_one_eq' {μ t : ℝ} (hμ : 0 < μ) (ht : 0 ≤ t) :
    Work.SmallBoxSliding.psiWeight 1 μ t = μ * (t - μ) ^ 2 / (t + μ) := by
  rw [Work.SmallBoxSliding.psiWeight]
  have hden : 1 + t * μ⁻¹ ≠ 0 := by
    have : 0 ≤ t * μ⁻¹ := mul_nonneg ht (le_of_lt (inv_pos.mpr hμ))
    linarith
  field_simp
  ring

/-- **The exact second-order expansion of `F` at `τ`**: with
`F'(τ) = μ(τ−μ)(τ+3μ)/(τ+μ)²`,

    F(t) = F(τ) + F'(τ)(t−τ) + 4·μ³(t−τ)²/((t+μ)(τ+μ)²) .

The remainder is *positive* (so `F` is convex, with `F''(t) = 8μ³/(t+μ)³`) and
`≤ 4(t−τ)²` on `t, τ ≥ 0` (`psiWeight_one_taylor_le`). -/
theorem psiWeight_one_taylor_exact {μ t τ : ℝ} (hμ : 0 < μ) (ht : 0 ≤ t) (hτ : 0 ≤ τ) :
    Work.SmallBoxSliding.psiWeight 1 μ t
      = Work.SmallBoxSliding.psiWeight 1 μ τ
        + (μ * (τ - μ) * (τ + 3 * μ) / (τ + μ) ^ 2) * (t - τ)
        + 4 * μ ^ 3 * (t - τ) ^ 2 / ((t + μ) * (τ + μ) ^ 2) := by
  rw [psiWeight_one_eq' hμ ht, psiWeight_one_eq' hμ hτ]
  have ht0 : t + μ ≠ 0 := by positivity
  have hτ0 : τ + μ ≠ 0 := by positivity
  field_simp
  ring

/-- **The sharpened pointwise bound** `F(t) ≤ F(τ) + F'(τ)(t−τ) + 4(t−τ)²`
for `t, τ ≥ 0`, `μ > 0`.  (This is the missing upgrade of the corpus's crude
`F(t) ≤ μ(t+μ)`: at the borderline `τ = μ` both `F(τ)` and `F'(τ)` vanish, so the
whole remainder is the square.) -/
theorem psiWeight_one_taylor_le {μ t τ : ℝ} (hμ : 0 < μ) (ht : 0 ≤ t) (hτ : 0 ≤ τ) :
    Work.SmallBoxSliding.psiWeight 1 μ t
      ≤ Work.SmallBoxSliding.psiWeight 1 μ τ
        + (μ * (τ - μ) * (τ + 3 * μ) / (τ + μ) ^ 2) * (t - τ)
        + 4 * (t - τ) ^ 2 := by
  rw [psiWeight_one_taylor_exact hμ ht hτ]
  have hA : μ ≤ t + μ := by linarith
  have hB : μ ≤ τ + μ := by linarith
  have hB2 : μ ^ 2 ≤ (τ + μ) ^ 2 := by nlinarith
  have hle : μ ^ 3 ≤ (t + μ) * (τ + μ) ^ 2 := by
    have := mul_le_mul hA hB2 (by positivity) (by linarith)
    nlinarith [this]
  have hpos : 0 < (t + μ) * (τ + μ) ^ 2 := by positivity
  have hstep : 4 * μ ^ 3 * (t - τ) ^ 2 ≤ 4 * ((t + μ) * (τ + μ) ^ 2) * (t - τ) ^ 2 :=
    mul_le_mul_of_nonneg_right (by linarith [hle]) (sq_nonneg _)
  have key : 4 * μ ^ 3 * (t - τ) ^ 2 / ((t + μ) * (τ + μ) ^ 2) ≤ 4 * (t - τ) ^ 2 := by
    rw [div_le_iff₀ hpos]
    nlinarith [hstep]
  linarith [key]

/-! ## 2. The `F`-row at the weighted mean -/

/-- **The sharp `F`-row.**  If `τ` is the `f`-weighted mean of `g`
(`∫ f·(g − τ) = 0`) and `f, g ≥ 0`, then the linear term of the Taylor expansion integrates to
zero and only the **count variance** survives:

    ∫ f·F(g) ≤ (∫f)·F(τ) + 4·∫ f (g − τ)² .

This is the statement the flat branch of `PerBoxF` needs in place of the crude
`F(t) ≤ μ(t+μ)`. -/
theorem integral_psiWeight_le_of_mean {α : Type*} [MeasurableSpace α] {μ : ℝ} (hμ : 0 < μ)
    {ν : Measure α} {f g : α → ℝ} {τ : ℝ} (hτ : 0 ≤ τ)
    (hf : Integrable f ν) (hfg : Integrable (fun x => f x * g x) ν)
    (hfg2 : Integrable (fun x => f x * g x ^ 2) ν)
    (hfψ : Integrable (fun x => f x * Work.SmallBoxSliding.psiWeight 1 μ (g x)) ν)
    (hmean : ∫ x, f x * (g x - τ) ∂ν = 0)
    (hf0 : 0 ≤ᵐ[ν] f) (hg0 : 0 ≤ᵐ[ν] g) :
    ∫ x, f x * Work.SmallBoxSliding.psiWeight 1 μ (g x) ∂ν
      ≤ (∫ x, f x ∂ν) * Work.SmallBoxSliding.psiWeight 1 μ τ
        + 4 * ∫ x, f x * (g x - τ) ^ 2 ∂ν := by
  set c : ℝ := μ * (τ - μ) * (τ + 3 * μ) / (τ + μ) ^ 2 with hc
  set A : α → ℝ := fun x => (Work.SmallBoxSliding.psiWeight 1 μ τ) * f x with hAdef
  set B : α → ℝ := fun x => c * (f x * (g x - τ)) with hBdef
  set C : α → ℝ := fun x => 4 * (f x * (g x - τ) ^ 2) with hCdef
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
  have hCi : Integrable C ν := by rw [hCdef]; exact hgτ2.const_mul 4
  have hABi : Integrable (A + B) ν := hAi.add hBi
  have hABCi : Integrable (A + B + C) ν := hABi.add hCi
  have hpt : ∀ᵐ x ∂ν, f x * Work.SmallBoxSliding.psiWeight 1 μ (g x) ≤ (A + B + C) x := by
    filter_upwards [hf0, hg0] with x hfx hgx
    have h := psiWeight_one_taylor_le hμ hgx hτ
    have hb := mul_le_mul_of_nonneg_left h hfx
    simp only [hAdef, hBdef, hCdef, Pi.add_apply, hc]
    nlinarith [hb]
  have hmono : ∫ x, f x * Work.SmallBoxSliding.psiWeight 1 μ (g x) ∂ν
      ≤ ∫ x, (A + B + C) x ∂ν := integral_mono_ae hfψ hABCi hpt
  have e2 : ∫ x, (fun x => A x + B x) x + C x ∂ν
      = (∫ x, (fun x => A x + B x) x ∂ν) + (∫ x, C x ∂ν) := integral_add hABi hCi
  have e1 : ∫ x, A x + B x ∂ν = (∫ x, A x ∂ν) + (∫ x, B x ∂ν) := integral_add hAi hBi
  have i1 : ∫ x, A x ∂ν = (Work.SmallBoxSliding.psiWeight 1 μ τ) * (∫ x, f x ∂ν) := by
    rw [hAdef, integral_const_mul]
  have i2 : ∫ x, B x ∂ν = c * (∫ x, f x * (g x - τ) ∂ν) := by
    rw [hBdef, integral_const_mul]
  have i3 : ∫ x, C x ∂ν = 4 * (∫ x, f x * (g x - τ) ^ 2 ∂ν) := by
    rw [hCdef, integral_const_mul]
  have hv : ∫ x, (A + B + C) x ∂ν
      = (Work.SmallBoxSliding.psiWeight 1 μ τ) * (∫ x, f x ∂ν)
        + c * (∫ x, f x * (g x - τ) ∂ν) + 4 * (∫ x, f x * (g x - τ) ^ 2 ∂ν) := by
    rw [show (∫ x, (A + B + C) x ∂ν) = ∫ x, (fun x => A x + B x) x + C x ∂ν from rfl,
      e2, e1, i1, i2, i3]
  rw [hv, hmean] at hmono
  linarith [hmono]

/-! ## 3. The `F`-row at the sliding box, in the frozen vocabulary -/

/-- **The sharp `F`-row of `PerBoxF`, at the box `B(u)`.**  With
`t := nCountB M ℓ d u x / chiMass M ℓ d u` (the smooth local density) and
`τ := (∫Φ²·t)/(∫Φ²)` its state mean,

    ∫Φ²·F(t) ≤ (∫Φ²)·F(τ) + 4·∫Φ²·(t − τ)² .

The RHS's first term is the crude row at the *mean* density and the second is the **count
variance**; this is the form the flat branch of `PerBoxF` must consume (the corpus's
`Work.BoseFixB1.perBoxF_pieces.psiWeight_le_mu_mul_add`, `F ≤ μ(t+μ)`, replaces the exact
square by the *linear* loss and is what fails at the borderline density `τ ≈ μ`).

`hJ : 0 < ∫Φ²` is the only non-degeneracy condition; the degenerate case is handled by
`Work.BoseKinLoc.Sector.eq_zero_on_abox_of_sqNormB_eq_zero` (the state vanishes pointwise). -/
theorem F_weight_le_mean_add_variance {M : ℕ} (hM : 1 ≤ M) {ℓ d μ : ℝ} (hℓ : 0 < ℓ) (hμ : 0 < μ)
    (u : E3) {n : ℕ} {Φ : Submission.BoseGases.X n → ℝ} (hΦc : Continuous Φ)
    (hJ : 0 < ∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2) :
    (∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2 *
        Work.SmallBoxSliding.psiWeight 1 μ
          (Work.BoseFixB1.nCountB M ℓ d u x / Work.SmallBoxSliding.chiMass M ℓ d u))
      ≤ (∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2)
          * Work.SmallBoxSliding.psiWeight 1 μ
              ((∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2 *
                  (Work.BoseFixB1.nCountB M ℓ d u x / Work.SmallBoxSliding.chiMass M ℓ d u))
                / (∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2))
        + 4 * (∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2 *
              (Work.BoseFixB1.nCountB M ℓ d u x / Work.SmallBoxSliding.chiMass M ℓ d u
                - (∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2 *
                    (Work.BoseFixB1.nCountB M ℓ d u x / Work.SmallBoxSliding.chiMass M ℓ d u))
                  / (∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2)) ^ 2) := by
  set κ : ℝ := Work.SmallBoxSliding.chiMass M ℓ d u with hκ
  set t : Submission.BoseGases.X n → ℝ :=
    fun x => Work.BoseFixB1.nCountB M ℓ d u x / κ with ht
  set T : ℝ := (∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2 * t x)
      / (∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2) with hT
  have hκ0 : 0 ≤ κ := by rw [hκ]; exact Work.SmallBoxSliding.chiMass_nonneg M ℓ d u
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
  have hnc0 : ∀ x : Submission.BoseGases.X n, 0 ≤ Work.BoseFixB1.nCountB M ℓ d u x := by
    intro x; rw [Work.BoseFixB1.nCountB]
    exact Finset.sum_nonneg fun i _ => sq_nonneg _
  have ht0 : ∀ x, 0 ≤ t x := fun x => div_nonneg (hnc0 x) hκ0
  have htc : Continuous t := hnc.div_const κ
  have hI2 : IntegrableOn (fun x => (Φ x) ^ 2)
      (Submission.BoseGases.abox n ℓ) volume :=
    ContinuousOn.integrableOn_compact (Submission.BoseGases.abox_compact n hℓ)
      ((hΦc.pow 2).continuousOn)
  have hIt : IntegrableOn (fun x => (Φ x) ^ 2 * t x)
      (Submission.BoseGases.abox n ℓ) volume :=
    ContinuousOn.integrableOn_compact (Submission.BoseGases.abox_compact n hℓ)
      (((hΦc.pow 2).continuousOn).mul htc.continuousOn)
  have hIt2 : IntegrableOn (fun x => (Φ x) ^ 2 * t x ^ 2)
      (Submission.BoseGases.abox n ℓ) volume :=
    ContinuousOn.integrableOn_compact (Submission.BoseGases.abox_compact n hℓ)
      (((hΦc.pow 2).continuousOn).mul (htc.pow 2).continuousOn)
  have hIψ : IntegrableOn (fun x => (Φ x) ^ 2 * Work.SmallBoxSliding.psiWeight 1 μ (t x))
      (Submission.BoseGases.abox n ℓ) volume := by
    refine ContinuousOn.integrableOn_compact (Submission.BoseGases.abox_compact n hℓ) ?_
    rw [show (fun x : Submission.BoseGases.X n => (Φ x) ^ 2 * Work.SmallBoxSliding.psiWeight 1 μ (t x))
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
  have hmain := integral_psiWeight_le_of_mean hμ hT0 hI2 hIt hIt2 hIψ hmean
    (Filter.Eventually.of_forall fun x => sq_nonneg _) (Filter.Eventually.of_forall ht0)
  simpa [ht, hκ, hT] using hmain

end Work.BoseFixB1S
