import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBox.potAmbAux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBox.abs_potBracketG_le` — the pointwise bound for the bracket of `potAmb`

The bracket of the (full-space) localised potential

`potBracketG N ℓ μ v (g₀ v h) u x
   = −μ·Σ_{i< N} ∫_y w_{1,u}(x_i,y) dy + (1/2)·Σ_{p∈pairSet N} w_u(x_{p.1},x_{p.2})`

is bounded pointwise by the un-localised data

`|μ|·N·(2·chiSup²·∫|g₀|) + chiSup²·Σ_{p∈pairSet N}|v(x_{p.1}−x_{p.2})|`.

The proof is elementary and completely pointwise/integrational:

* the one-body fibre integrand factors as
  `wLoc ℓ g u a y = χ_u(a)·wScaled ℓ g (a−y)·χ_u(y)`, so with `|χ_u| ≤ chiSup`
  (`abs_chiU_le_chiSup`) and `|wScaled ℓ g z| ≤ 2|g z|` (`abs_wScaled_le`, valid in
  FS's regime `R ≤ ℓ·r₀` plus the pointwise support of the numerator) the fibre obeys
  `|wLoc …| ≤ 2·chiSup²·|g(a−y)|`; this is `abs_wLoc_le`.
* hence the fibre is integrable (`integrable_wLoc_fibre`: `Integrable.mono'` against
  `2·chiSup²·|g(a−·)|`, whose integrability is translation invariance,
  `km_integrable_comp_sub_left`) and
  `|∫_y wLoc …| ≤ 2·chiSup²·∫|g|` (`abs_wLoc_integral_le`).
* instantiating `g := g₀ v h` gives `abs_potBr_le`, and the same pointwise bound
  gives `abs_wLoc_pair_le` for the pair terms (with numerator `v`).
* the assembly is `abs_add_le` + `abs_mul` + `Finset.abs_sum_le_sum_abs` +
  `Finset.sum_le_sum` + `mul_le_mul_of_nonneg_left`.
-/

noncomputable section

open MeasureTheory Metric
open scoped Real BigOperators

namespace Work.BoseBox


open Submission.BoseGases
open Work.UBB

set_option autoImplicit false
set_option linter.unusedVariables false

/-- `|χ_u(z)| ≤ chiSup` pointwise (the window factor is bounded by `chiSup`). -/
lemma abs_chiU_le_chiSup (ℓ : ℝ) (u z : ℝ³) : |chiU ℓ u z| ≤ chiSup := by
  simpa [chiU] using abs_chi_le_chiSup ((ℓ⁻¹) • z - u)

/-- **Pointwise bound of the localised kernel.** In FS's regime (`0 < ℓ`, `R ≤ ℓ·r₀`,
`(χ⋆χ)(·/ℓ) ≥ 1/2` on `‖z‖ ≤ r₀`) and with the numerator `h` vanishing for `‖z‖ ≥ R`,

`|wLoc ℓ h u a b| ≤ 2·chiSup²·|h (a − b)|`. -/
lemma abs_wLoc_le {h : ℝ³ → ℝ} {ℓ R r₀ : ℝ} (hℓ : 0 < ℓ)
    (hhsupp : ∀ z : ℝ³, R ≤ ‖z‖ → h z = 0) (hRℓ : R ≤ ℓ * r₀)
    (hC : ∀ z : ℝ³, ‖z‖ ≤ r₀ → 1 / 2 ≤ conv3 chi chi z) (u a b : ℝ³) :
    |wLoc ℓ h u a b| ≤ 2 * chiSup ^ 2 * |h (a - b)| := by
  have hw := abs_wScaled_le hℓ hhsupp hRℓ hC (a - b)
  have hS : 0 ≤ chiSup := le_of_lt chiSup_pos
  have hb2 : 0 ≤ 2 * |h (a - b)| := mul_nonneg (by norm_num) (abs_nonneg _)
  have h1 : |chiU ℓ u a| * |wScaled ℓ h (a - b)| ≤ chiSup * (2 * |h (a - b)|) :=
    mul_le_mul (abs_chiU_le_chiSup ℓ u a) hw (abs_nonneg _) hS
  have h2 : |chiU ℓ u a| * |wScaled ℓ h (a - b)| * |chiU ℓ u b|
      ≤ (chiSup * (2 * |h (a - b)|)) * chiSup :=
    mul_le_mul h1 (abs_chiU_le_chiSup ℓ u b) (abs_nonneg _) (mul_nonneg hS hb2)
  calc |wLoc ℓ h u a b| = |chiU ℓ u a| * |wScaled ℓ h (a - b)| * |chiU ℓ u b| := by
        simp [wLoc, abs_mul]
    _ ≤ _ := h2
    _ = 2 * chiSup ^ 2 * |h (a - b)| := by ring

/-- The `y`-fibre of the localised kernel is a.e. strongly measurable whenever the
numerator is. -/
lemma aestronglyMeasurable_wLoc_fibre {h : ℝ³ → ℝ} {ℓ : ℝ}
    (hh : AEStronglyMeasurable h volume) (u a : ℝ³) :
    AEStronglyMeasurable (fun y : ℝ³ => wLoc ℓ h u a y) volume := by
  have h1 : AEStronglyMeasurable (fun y : ℝ³ => h (a - y)) volume :=
    km_aestronglyMeasurable_comp_sub_left hh a
  have hcs : Continuous (fun y : ℝ³ => convScale ℓ (a - y)) :=
    (convScale_continuous ℓ).comp (by fun_prop)
  have h2 : AEStronglyMeasurable (fun y : ℝ³ => wScaled ℓ h (a - y)) volume := by
    have hEq : (fun y : ℝ³ => wScaled ℓ h (a - y))
        = fun y : ℝ³ => h (a - y) * (convScale ℓ (a - y))⁻¹ := by
      funext y; dsimp [wScaled]; rw [div_eq_mul_inv]
    rw [hEq]
    have hinv : Measurable (fun t : ℝ => t⁻¹) := by fun_prop
    exact h1.mul ((hinv.comp hcs.measurable).aestronglyMeasurable)
  have h3 : AEStronglyMeasurable (fun y : ℝ³ => chiU ℓ u y) volume := by
    have hc : Continuous (fun y : ℝ³ => chiU ℓ u y) := by
      rw [show (fun y : ℝ³ => chiU ℓ u y) = fun y : ℝ³ => chi (u - ℓ⁻¹ • y) from
        funext (fun y => chiU_eq_chi_sub ℓ u y)]
      exact chi_continuous.comp (by fun_prop)
    exact hc.aestronglyMeasurable
  have hEq : (fun y : ℝ³ => wLoc ℓ h u a y)
      = fun y => chiU ℓ u a * (wScaled ℓ h (a - y) * chiU ℓ u y) := by
    funext y; simp [wLoc, mul_assoc]
  rw [hEq]
  exact (h2.mul h3).const_mul _

/-- The `y`-fibre of the localised kernel is integrable under FS's regime. -/
lemma integrable_wLoc_fibre {h : ℝ³ → ℝ} {ℓ R r₀ : ℝ} (hℓ : 0 < ℓ)
    (hi : Integrable h) (hhsupp : ∀ z : ℝ³, R ≤ ‖z‖ → h z = 0) (hRℓ : R ≤ ℓ * r₀)
    (hC : ∀ z : ℝ³, ‖z‖ ≤ r₀ → 1 / 2 ≤ conv3 chi chi z) (u a : ℝ³) :
    Integrable (fun y : ℝ³ => wLoc ℓ h u a y) := by
  have hdom : Integrable (fun y : ℝ³ => 2 * chiSup ^ 2 * |h (a - y)|) :=
    (km_integrable_comp_sub_left hi.abs a).const_mul (2 * chiSup ^ 2)
  refine Integrable.mono' hdom (aestronglyMeasurable_wLoc_fibre hi.aestronglyMeasurable u a) ?_
  filter_upwards with y
  rw [Real.norm_eq_abs]
  exact abs_wLoc_le hℓ hhsupp hRℓ hC u a y

/-- **Fibre bound.** `|∫_y wLoc ℓ h u a y| ≤ 2·chiSup²·∫|h|` under FS's regime. -/
lemma abs_wLoc_integral_le {h : ℝ³ → ℝ} {ℓ R r₀ : ℝ} (hℓ : 0 < ℓ)
    (hi : Integrable h) (hhsupp : ∀ z : ℝ³, R ≤ ‖z‖ → h z = 0) (hRℓ : R ≤ ℓ * r₀)
    (hC : ∀ z : ℝ³, ‖z‖ ≤ r₀ → 1 / 2 ≤ conv3 chi chi z) (u a : ℝ³) :
    |∫ y : ℝ³, wLoc ℓ h u a y| ≤ 2 * chiSup ^ 2 * (∫ z : ℝ³, |h z|) := by
  have hfi : Integrable (fun y : ℝ³ => wLoc ℓ h u a y) :=
    integrable_wLoc_fibre hℓ hi hhsupp hRℓ hC u a
  have hg : Integrable (fun y : ℝ³ => 2 * chiSup ^ 2 * |h (a - y)|) :=
    (km_integrable_comp_sub_left hi.abs a).const_mul (2 * chiSup ^ 2)
  calc |∫ y : ℝ³, wLoc ℓ h u a y| ≤ ∫ y : ℝ³, |wLoc ℓ h u a y| :=
        abs_integral_le_integral_abs
    _ ≤ ∫ y : ℝ³, 2 * chiSup ^ 2 * |h (a - y)| :=
        integral_mono hfi.abs hg (fun y => abs_wLoc_le hℓ hhsupp hRℓ hC u a y)
    _ = 2 * chiSup ^ 2 * (∫ y : ℝ³, |h (a - y)|) := integral_const_mul _ _
    _ = 2 * chiSup ^ 2 * (∫ z : ℝ³, |h z|) := by
        congr 1
        exact integral_comp_sub_left (fun z : ℝ³ => |h z|) a

/-- Pointwise form of the support hypothesis: `tsupport v ⊆ ball 0 R` means `v`
vanishes for `‖z‖ ≥ R`. -/
lemma v_zero_of_tsupport {v : ℝ³ → ℝ} {R : ℝ}
    (hv_supp : tsupport v ⊆ Metric.ball (0 : ℝ³) R) :
    ∀ z : ℝ³, R ≤ ‖z‖ → v z = 0 := by
  intro z hz
  by_contra hne
  have hzball : z ∈ Metric.ball (0 : ℝ³) R := hv_supp (subset_tsupport v hne)
  rw [Metric.mem_ball, dist_zero_right] at hzball
  exact absurd hzball (not_lt.mpr hz)

/-- **The one-body fibre integral is bounded by `2·chiSup²·∫|g₀|`.** -/
lemma abs_potBr_le {v : ℝ³ → ℝ} {R r₀ : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : ℝ³) R)
    (hC : ∀ z : ℝ³, ‖z‖ ≤ r₀ → 1 / 2 ≤ conv3 chi chi z)
    {ℓ : ℝ} (hℓ : 0 < ℓ) (hRℓ : R ≤ ℓ * r₀)
    {h : ScatSol v} (u a : ℝ³) :
    |potBr ℓ (g0 v h) u a| ≤ 2 * chiSup ^ 2 * g0mass v h := by
  have hb := abs_wLoc_integral_le (h := g0 v h) (ℓ := ℓ) (R := R) (r₀ := r₀) hℓ
    (g0_integrable hR hv_supp h) (fun z hz => g0_zero_of_norm_ge hv_supp hz h) hRℓ hC u a
  simpa [potBr, g0mass] using hb

/-- **Pointwise bound of the pair kernel.** -/
lemma abs_wLoc_pair_le {v : ℝ³ → ℝ} {R r₀ ℓ : ℝ}
    (hv_supp : tsupport v ⊆ Metric.ball (0 : ℝ³) R)
    (hC : ∀ z : ℝ³, ‖z‖ ≤ r₀ → 1 / 2 ≤ conv3 chi chi z)
    (hℓ : 0 < ℓ) (hRℓ : R ≤ ℓ * r₀) (u a b : ℝ³) :
    |wLoc ℓ v u a b| ≤ chiSup ^ 2 * (2 * |v (a - b)|) := by
  have hvsupp := v_zero_of_tsupport hv_supp
  calc |wLoc ℓ v u a b| ≤ 2 * chiSup ^ 2 * |v (a - b)| :=
        abs_wLoc_le hℓ hvsupp hRℓ hC u a b
    _ = chiSup ^ 2 * (2 * |v (a - b)|) := by ring

/-- **Pointwise bound for the potential bracket.** Under FS's potential regime the bracket `potBracketG N ℓ μ v (g₀ v h) u x` is bounded by `|μ|·N·(2·chiSup²·∫|g₀|) + chiSup²·Σ_{p∈pairSet N}|v(x_{p.1}−x_{p.2})|`.

Route: for each `i`, `potBr ℓ (g₀ v h) u (x i) = ∫_y wLoc ℓ g₀ u (x i) y`; the integrand is bounded by `chiSup·(2|g₀(x i − y)|)·chiSup` using `Submission.BoseGases.abs_chi_le` (via `Work.BoseBox.abs_chi_le_chiSup`) and `Submission.BoseGases.abs_wScaled_le` (with the pointwise support of `g₀` from `Submission.BoseGases.g0_zero_of_norm_ge`, the hypothesis `hRℓ` and `hC`), so that integrand is integrable (`Integrable.mono'` against the integrable `y ↦ 2·chiSup²·|g₀(x i − y)|`; a.e. strong measurability from `g₀`'s a.e. measurability composed with the measure-preserving `y ↦ x i − y` and the continuous `convScale`); `norm_integral_le_integral_norm` and `integral_mono` give `|potBr| ≤ 2·chiSup²·∫_y |g₀(x i − y)| = 2·chiSup²·g0mass v h` (translation invariance). The pair terms are bounded directly by `|wLoc ℓ v u (x_{p.1}) (x_{p.2})| ≤ chiSup²·2|v(x_{p.1}−x_{p.2})|` (same two lemmas, plus `Submission.BoseGases.convScale_ge_half_of_hnz` inside `abs_wScaled_le`). Sum, multiply by `|μ|` resp. `1/2`, and use `Finset.sum_le_sum` / `abs_mul` / `abs_le` and the elementary bound `‖∑ …‖ ≤ ∑ …` (`norm_sum_le`). -/
theorem abs_potBracketG_le {v : EuclideanSpace ℝ (Fin 3) → ℝ} {R r₀ : ℝ} (hR : 0 < R) (hr₀ : 0 < r₀)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hC : ∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ ≤ r₀ →
      1 / 2 ≤ Submission.BoseGases.conv3 Submission.BoseGases.chi Submission.BoseGases.chi x)
    {ℓ μ : ℝ} (hℓ : 0 < ℓ) (hRℓ : R ≤ ℓ * r₀)
    {N : ℕ} {h : Work.UBB.ScatSol v}
    (u : EuclideanSpace ℝ (Fin 3)) (x : Submission.BoseGases.X N) :
    |Work.BoseBox.potBracketG N ℓ μ v (Submission.BoseGases.g0 v h) u x|
      ≤ |μ| * (N : ℝ) * (2 * Work.BoseBox.chiSup ^ 2 * Work.BoseBox.g0mass v h)
        + Work.BoseBox.chiSup ^ 2 *
            ∑ p ∈ Submission.BoseGases.pairSet N, |v (x p.1 - x p.2)| := by
  -- the per-particle fibre bounds, then the sum over `Fin N`.
  have hBr : ∀ i : Fin N, |potBr ℓ (g0 v h) u (x i)| ≤ 2 * chiSup ^ 2 * g0mass v h :=
    fun i => abs_potBr_le hR hv_supp hC hℓ hRℓ u (x i)
  have hSum1 : |∑ i : Fin N, potBr ℓ (g0 v h) u (x i)|
      ≤ (N : ℝ) * (2 * chiSup ^ 2 * g0mass v h) := by
    calc |∑ i : Fin N, potBr ℓ (g0 v h) u (x i)|
        ≤ ∑ i : Fin N, |potBr ℓ (g0 v h) u (x i)| :=
          Finset.abs_sum_le_sum_abs (fun i : Fin N => potBr ℓ (g0 v h) u (x i)) Finset.univ
      _ ≤ ∑ _i : Fin N, (2 * chiSup ^ 2 * g0mass v h) :=
          Finset.sum_le_sum (fun i _ => hBr i)
      _ = (N : ℝ) * (2 * chiSup ^ 2 * g0mass v h) := by
          simp [Finset.sum_const, nsmul_eq_mul]
  -- the per-pair bounds, then the sum over `pairSet N`.
  have hPair : |∑ p ∈ pairSet N, wLoc ℓ v u (x p.1) (x p.2)|
      ≤ ∑ p ∈ pairSet N, chiSup ^ 2 * (2 * |v (x p.1 - x p.2)|) :=
    le_trans
      (Finset.abs_sum_le_sum_abs
        (fun p : Fin N × Fin N => wLoc ℓ v u (x p.1) (x p.2)) (pairSet N))
      (Finset.sum_le_sum
        (fun p _ => abs_wLoc_pair_le hv_supp hC hℓ hRℓ u (x p.1) (x p.2)))
  have hPair2 : |(1 / 2) * (∑ p ∈ pairSet N, wLoc ℓ v u (x p.1) (x p.2))|
      ≤ chiSup ^ 2 * ∑ p ∈ pairSet N, |v (x p.1 - x p.2)| := by
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    calc (1 / 2) * |∑ p ∈ pairSet N, wLoc ℓ v u (x p.1) (x p.2)|
        ≤ (1 / 2) * (∑ p ∈ pairSet N, chiSup ^ 2 * (2 * |v (x p.1 - x p.2)|)) :=
          mul_le_mul_of_nonneg_left hPair (by norm_num)
      _ = chiSup ^ 2 * ∑ p ∈ pairSet N, |v (x p.1 - x p.2)| := by
          rw [← Finset.mul_sum, ← Finset.mul_sum]
          ring
  -- unfold the bracket and combine.
  have hbrk : potBracketG N ℓ μ v (g0 v h) u x
      = - μ * (∑ i : Fin N, potBr ℓ (g0 v h) u (x i))
        + (1 / 2) * (∑ p ∈ pairSet N, wLoc ℓ v u (x p.1) (x p.2)) := rfl
  rw [hbrk]
  calc |(-μ) * (∑ i : Fin N, potBr ℓ (g0 v h) u (x i))
          + (1 / 2) * (∑ p ∈ pairSet N, wLoc ℓ v u (x p.1) (x p.2))|
      ≤ |(-μ) * (∑ i : Fin N, potBr ℓ (g0 v h) u (x i))|
          + |(1 / 2) * (∑ p ∈ pairSet N, wLoc ℓ v u (x p.1) (x p.2))| := abs_add_le _ _
    _ = |μ| * |∑ i : Fin N, potBr ℓ (g0 v h) u (x i)|
          + |(1 / 2) * (∑ p ∈ pairSet N, wLoc ℓ v u (x p.1) (x p.2))| := by
          rw [abs_mul, abs_neg]
    _ ≤ |μ| * ((N : ℝ) * (2 * chiSup ^ 2 * g0mass v h))
          + chiSup ^ 2 * ∑ p ∈ pairSet N, |v (x p.1 - x p.2)| :=
          add_le_add (mul_le_mul_of_nonneg_left hSum1 (abs_nonneg μ)) hPair2
    _ = |μ| * (N : ℝ) * (2 * chiSup ^ 2 * g0mass v h)
          + chiSup ^ 2 * ∑ p ∈ pairSet N, |v (x p.1 - x p.2)| := by ring

end Work.BoseBox
