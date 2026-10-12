import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Order.Group.Lattice
import Submission.Work.BoseBoxFock.PCFU.chBimg_Kchi_sup
import Submission.Work.BoseBoxFock.PCFU.chDimgFibreSharp
import Submission.Work.BoseBoxFock.PCFU.chiScale_imageSum_lowKer_le
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.PCFU.chDimg_fibre_le` — the `(D)`-slot image sum against the state

Holder of the target `Work.BoseBoxFock.PCFU.chDimg_fibre_le`.

The `(D)`-channel lattice-image slot is

    chDimg = ∫_x Θ(x) · ∫_w χ(w)·ΚχfrU(w) · ∫_{u ∈ acube ℓ} Σ_d(u,w)·Ψ(x[j↦u]) ,

where `ℓ = ellH v μ`, `χ = chiScale ℓ`, `Σ_d(u,w) = Σ'_{d≠0} lowKer fc κ (u + w + ℓ•latVec d)`
(the `d ≠ 0` images of the low cut-off kernel, `κ = chKappa v μ`) and `Ψ = Q_j P_i Θ` the two slot
projections of the state `Θ = boxRestrictR ℓ Φ`.

The target bounds it by `ℓ³·A·(∫W)·∫_{abox n ℓ}Φ²` from the *two pointwise data*

* `hA` : `‖ΚχfrU w‖ ≤ A` (uniform in `w`), and
* `hpt`: `χ(w)·‖Σ_d(u,w)‖ ≤ W w` uniformly in `u ∈ acube ℓ` (`W` integrable),

and the **sharp** state-level fibre Cauchy–Schwarz `Work.BoseBoxFock.PCFU.chDimgFibreSharp`:
with `Θ`, `Ψ` as above,

    ∫_x |Θ x| · (∫_{u ∈ acube ℓ} |Ψ (x[j↦u])|)  ≤  ℓ³ ∫_{abox n ℓ} Φ² .

## The assembly

For fixed `x`, with `II w = ∫_{u ∈ acube ℓ} Σ_d(u,w)·Ψ(x[j↦u])`:

* `χ(w)·‖II w‖ ≤ ∫_{u ∈ acube ℓ} χ(w)‖Σ_d(u,w)‖·|Ψ(x[j↦u])| ≤ ∫_{u ∈ acube ℓ} W w·|Ψ(x[j↦u])|
  = W w·F x` where `F x = ∫_u |Ψ(x[j↦u])|` (Cauchy–Schwarz for the Bochner integral, the
  positivity of `χ`, and `hpt`);
* hence `‖∫_w χ(w)ΚχfrU(w)·II w‖ ≤ ∫_w χ(w)‖ΚχfrU(w)‖·‖II w‖ ≤ ∫_w A·(W w·F x) = A(∫W)·F x`
  (by `hA`);
* the `x`-integral of `|Θ x|·‖·‖` is then dominated by `A(∫W)·∫_x |Θ x| F x`, which is
  `≤ ℓ³·A·(∫W)·∫_{abox n ℓ}Φ²` by the sharp fibre bound.

The only regularity needed on `Φ` is measurability plus the global bound `B`, which is the state
class in which the slot dictionary is used.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

set_option maxHeartbeats 1000000

namespace Work.BoseBoxFock.PCFU

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- The lattice-image sum of the low cut-off kernel:
`Σ'_{d ≠ 0} lowKer fc κ (u + w + ℓ • latVec d)`, as a complex number (the form in which `chDimg`
integrates it against the state). -/
noncomputable def chDimgImgSum (fc : Work.BoseBoxFix.LowCut) (κ ℓ : ℝ) (u w : E3) : ℂ :=
  ∑' d : Fin 3 → ℤ, if d = 0 then (0 : ℂ) else
    ((lowKer fc κ (u + w + ℓ • Work.BoseBoxFock.latVec d) : ℝ) : ℂ)

/-- **The `w`-integral at a fixed configuration.**  For a state `Θ` (measurable, bounded by `C`),
the `w`-integral of `chDimg` against the image sum is dominated by `A·(∫W)·F x`, where
`F x = ∫_{u ∈ acube ℓ} |aQ ℓ j (aP ℓ i Θ) (x[j↦u])|`.

This is where the pointwise hypothesis `hpt` (`χ·‖image sum‖ ≤ W`) is consumed: after multiplying
by `χ(w) ≥ 0` and applying Cauchy–Schwarz for the Bochner integral in `u`, the integrand is
`≤ W w·|Ψ(x[j↦u])|` pointwise. -/
private theorem chDimg_wint_le {v : E3 → ℝ} {h : Work.UBB.ScatSol v}
    {fc fu : Work.BoseBoxFix.LowCut} {μ : ℝ} {N n : ℕ} (i j : Fin n) {ℓ : ℝ} (hℓ : 0 < ℓ)
    {W : E3 → ℝ} (hWint : MeasureTheory.Integrable W)
    {A : ℝ} (hA0 : 0 ≤ A) (hA : ∀ w, ‖KχfrU v h μ fu N w‖ ≤ A)
    {Θ : Submission.BoseGases.X n → ℝ} (hΘm : Measurable Θ) {C : ℝ} (hC0 : 0 ≤ C)
    (hΘb : ∀ x, |Θ x| ≤ C)
    (hpt : ∀ w (u : E3), u ∈ Submission.BoseGases.acube ℓ →
        Submission.BoseGases.chiScale ℓ w * ‖chDimgImgSum fc (chKappa v μ) ℓ u w‖ ≤ W w)
    (x : Submission.BoseGases.X n) :
    ‖∫ w : E3, ((Work.BoseK15.corpusBox.chiLam ℓ w : ℝ) : ℂ) * KχfrU v h μ fu N w *
        (∫ u in Submission.BoseGases.acube ℓ,
          chDimgImgSum fc (chKappa v μ) ℓ u w *
            ((Submission.BoseGases.aQ ℓ j (Submission.BoseGases.aP ℓ i Θ)
              (Function.update x j u) : ℝ) : ℂ))‖
      ≤ A * (∫ w, W w) *
          (∫ u in Submission.BoseGases.acube ℓ,
            |Submission.BoseGases.aQ ℓ j (Submission.BoseGases.aP ℓ i Θ)
              (Function.update x j u)|) := by
  classical
  set II : E3 → ℂ := fun w => ∫ u in Submission.BoseGases.acube ℓ,
          chDimgImgSum fc (chKappa v μ) ℓ u w *
            ((Submission.BoseGases.aQ ℓ j (Submission.BoseGases.aP ℓ i Θ)
              (Function.update x j u) : ℝ) : ℂ) with hIIdef
  haveI hcube : IsFiniteMeasure ((volume : Measure E3).restrict (Submission.BoseGases.acube ℓ)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact Submission.BoseGases.acube_lt_top ℓ hℓ.le⟩
  -- the fibre of the state over the cube is integrable (measurability + the bound `2C`)
  have hfib_int : Integrable (fun u : E3 =>
      |Submission.BoseGases.aQ ℓ j (Submission.BoseGases.aP ℓ i Θ) (Function.update x j u)|)
      ((volume : Measure E3).restrict (Submission.BoseGases.acube ℓ)) := by
    refine Integrable.of_bound ?_ (2 * C) (Filter.Eventually.of_forall fun u => ?_)
    · exact (((Work.BoseBoxFock.Weak.aQ_measurable j
          (Work.BoseBoxFock.Weak.aP_measurable i hΘm)).comp
        (by fun_prop : Measurable fun u : E3 => Function.update x j u))).abs.aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_abs]
      exact Work.BoseBoxFock.Weak.aQ_abs_le hℓ j (by linarith)
        (Work.BoseBoxFock.Weak.aP_abs_le hℓ i hC0 hΘb) (Function.update x j u)
  have hχ0 : ∀ w : E3, (0 : ℝ) ≤ Work.BoseK15.corpusBox.chiLam ℓ w :=
    fun w => Submission.BoseGases.chiScale_nonneg ℓ w
  -- ## the pointwise (in `w`) step: `χ w · ‖II w‖ ≤ W w · F x`
  have h2b : ∀ w : E3, (Work.BoseK15.corpusBox.chiLam ℓ w) * ‖II w‖ ≤ W w *
      (∫ u in Submission.BoseGases.acube ℓ,
        |Submission.BoseGases.aQ ℓ j (Submission.BoseGases.aP ℓ i Θ) (Function.update x j u)|) := by
    intro w
    have hcs : ‖II w‖ ≤ ∫ u in Submission.BoseGases.acube ℓ,
        ‖chDimgImgSum fc (chKappa v μ) ℓ u w‖ *
          |Submission.BoseGases.aQ ℓ j (Submission.BoseGases.aP ℓ i Θ) (Function.update x j u)| := by
      rw [hIIdef]
      refine (norm_integral_le_integral_norm _).trans_eq ?_
      refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    calc (Work.BoseK15.corpusBox.chiLam ℓ w) * ‖II w‖
        ≤ (Work.BoseK15.corpusBox.chiLam ℓ w) * (∫ u in Submission.BoseGases.acube ℓ,
            ‖chDimgImgSum fc (chKappa v μ) ℓ u w‖ *
              |Submission.BoseGases.aQ ℓ j (Submission.BoseGases.aP ℓ i Θ)
                (Function.update x j u)|) :=
          mul_le_mul_of_nonneg_left hcs (hχ0 w)
      _ = ∫ u in Submission.BoseGases.acube ℓ,
            (Work.BoseK15.corpusBox.chiLam ℓ w) *
              (‖chDimgImgSum fc (chKappa v μ) ℓ u w‖ *
                |Submission.BoseGases.aQ ℓ j (Submission.BoseGases.aP ℓ i Θ)
                  (Function.update x j u)|) := by
          rw [MeasureTheory.integral_const_mul]
      _ ≤ ∫ u in Submission.BoseGases.acube ℓ,
            W w * |Submission.BoseGases.aQ ℓ j (Submission.BoseGases.aP ℓ i Θ)
              (Function.update x j u)| := by
          refine MeasureTheory.integral_mono_of_nonneg (Filter.Eventually.of_forall fun u => ?_)
            ?_ ?_
          · have h1 : (0 : ℝ) ≤ Work.BoseK15.corpusBox.chiLam ℓ w := hχ0 w
            positivity
          · exact hfib_int.const_mul (W w)
          · filter_upwards [MeasureTheory.ae_restrict_mem (Submission.BoseGases.acube_measurable ℓ)]
              with u hu
            have h1 : Submission.BoseGases.chiScale ℓ w * ‖chDimgImgSum fc (chKappa v μ) ℓ u w‖
                ≤ W w := hpt w u hu
            calc (Work.BoseK15.corpusBox.chiLam ℓ w) *
                  (‖chDimgImgSum fc (chKappa v μ) ℓ u w‖ *
                    |Submission.BoseGases.aQ ℓ j (Submission.BoseGases.aP ℓ i Θ)
                      (Function.update x j u)|)
                = ((Work.BoseK15.corpusBox.chiLam ℓ w) *
                    ‖chDimgImgSum fc (chKappa v μ) ℓ u w‖) *
                    |Submission.BoseGases.aQ ℓ j (Submission.BoseGases.aP ℓ i Θ)
                      (Function.update x j u)| := by
                  ring
              _ ≤ W w * |Submission.BoseGases.aQ ℓ j (Submission.BoseGases.aP ℓ i Θ)
                    (Function.update x j u)| :=
                  mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
      _ = W w * (∫ u in Submission.BoseGases.acube ℓ,
            |Submission.BoseGases.aQ ℓ j (Submission.BoseGases.aP ℓ i Θ)
              (Function.update x j u)|) := by
          rw [MeasureTheory.integral_const_mul]
  -- ## the `w`-integral of the norm
  have h2a : ‖∫ w : E3, ((Work.BoseK15.corpusBox.chiLam ℓ w : ℝ) : ℂ) *
        KχfrU v h μ fu N w * II w‖
      ≤ ∫ w : E3, (Work.BoseK15.corpusBox.chiLam ℓ w) * ‖KχfrU v h μ fu N w‖ * ‖II w‖ := by
    refine (norm_integral_le_integral_norm _).trans_eq ?_
    refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hχ0 w)]
  have h2c : ∫ w : E3, (Work.BoseK15.corpusBox.chiLam ℓ w) * ‖KχfrU v h μ fu N w‖ * ‖II w‖
      ≤ ∫ w : E3, A * (W w * (∫ u in Submission.BoseGases.acube ℓ,
            |Submission.BoseGases.aQ ℓ j (Submission.BoseGases.aP ℓ i Θ)
              (Function.update x j u)|)) := by
    refine MeasureTheory.integral_mono_of_nonneg (Filter.Eventually.of_forall fun w => ?_) ?_
      (Filter.Eventually.of_forall fun w => ?_)
    · have h1 : (0 : ℝ) ≤ Work.BoseK15.corpusBox.chiLam ℓ w := hχ0 w
      positivity
    · simpa only [mul_assoc] using (hWint.const_mul A).mul_const
        (∫ u in Submission.BoseGases.acube ℓ,
            |Submission.BoseGases.aQ ℓ j (Submission.BoseGases.aP ℓ i Θ)
              (Function.update x j u)|)
    · calc (Work.BoseK15.corpusBox.chiLam ℓ w) * ‖KχfrU v h μ fu N w‖ * ‖II w‖
          = ‖KχfrU v h μ fu N w‖ *
              ((Work.BoseK15.corpusBox.chiLam ℓ w) * ‖II w‖) := by ring
        _ ≤ A * (W w * (∫ u in Submission.BoseGases.acube ℓ,
              |Submission.BoseGases.aQ ℓ j (Submission.BoseGases.aP ℓ i Θ)
                (Function.update x j u)|)) :=
            mul_le_mul (hA w) (h2b w) (mul_nonneg (hχ0 w) (norm_nonneg _)) hA0
  have h2d : ∫ w : E3, A * (W w * (∫ u in Submission.BoseGases.acube ℓ,
          |Submission.BoseGases.aQ ℓ j (Submission.BoseGases.aP ℓ i Θ)
            (Function.update x j u)|))
      = A * (∫ w, W w) * (∫ u in Submission.BoseGases.acube ℓ,
          |Submission.BoseGases.aQ ℓ j (Submission.BoseGases.aP ℓ i Θ)
            (Function.update x j u)|) := by
    rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_mul_const]
    ring
  have hgoal : ‖∫ w : E3, ((Work.BoseK15.corpusBox.chiLam ℓ w : ℝ) : ℂ) *
        KχfrU v h μ fu N w * II w‖
      ≤ A * (∫ w, W w) * (∫ u in Submission.BoseGases.acube ℓ,
          |Submission.BoseGases.aQ ℓ j (Submission.BoseGases.aP ℓ i Θ)
            (Function.update x j u)|) :=
    le_trans h2a (le_trans h2c (le_of_eq h2d))
  simpa only [hIIdef] using hgoal

theorem chDimg_fibre_le {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v}
    {fc fu : Work.BoseBoxFix.LowCut} {μ : ℝ} {N n : ℕ} (i j : Fin n) (hij : i ≠ j)
    (hℓH : 0 < Work.BoseBoxFock.ellH v μ)
    {Φ : Submission.BoseGases.X n → ℝ} (hΦm : Measurable Φ)
    {B : ℝ} (hΦb : ∀ x, |Φ x| ≤ B)
    {W : EuclideanSpace ℝ (Fin 3) → ℝ} (hW0 : ∀ w, 0 ≤ W w) (hWint : MeasureTheory.Integrable W)
    {A : ℝ} (hA0 : 0 ≤ A) (hA : ∀ w, ‖Work.BoseBoxFock.PCFU.KχfrU v h μ fu N w‖ ≤ A)
    (hpt : ∀ w (u : EuclideanSpace ℝ (Fin 3)), u ∈ Submission.BoseGases.acube (Work.BoseBoxFock.ellH v μ) →
        Submission.BoseGases.chiScale (Work.BoseBoxFock.ellH v μ) w *
          ‖(∑' d : Fin 3 → ℤ, if d = 0 then (0 : ℂ) else
            ((Work.BoseBoxFock.PCFU.lowKer fc (Work.BoseBoxFock.PCFU.chKappa v μ)
              (u + w + (Work.BoseBoxFock.ellH v μ) • Work.BoseBoxFock.latVec d) : ℝ) : ℂ))‖ ≤ W w) :
    ‖Work.BoseBoxFock.PCFU.chDimg v h fc fu μ N i j
        (Work.BoseBoxFock.boxRestrictR (Work.BoseBoxFock.ellH v μ) Φ)‖
      ≤ (Work.BoseBoxFock.ellH v μ) ^ 3 * A * (∫ w, W w)
          * (∫ x in Submission.BoseGases.abox n (Work.BoseBoxFock.ellH v μ), (Φ x) ^ 2) := by
  classical
  set ℓ := Work.BoseBoxFock.ellH v μ with hℓdef
  have hℓ : 0 < ℓ := hℓH
  have hB0 : 0 ≤ B := le_trans (abs_nonneg (Φ 0)) (hΦb 0)
  set Θ : Submission.BoseGases.X n → ℝ := Work.BoseBoxFock.boxRestrictR ℓ Φ with hΘdef
  have hΘm : Measurable Θ := by
    rw [hΘdef]
    unfold Work.BoseBoxFock.boxRestrictR
    exact hΦm.mul (measurable_const.indicator (Submission.BoseGases.abox_measurable n ℓ))
  have hΘb : ∀ x, |Θ x| ≤ B := by
    intro x
    rw [hΘdef]
    unfold Work.BoseBoxFock.boxRestrictR
    by_cases hx : x ∈ Submission.BoseGases.abox n ℓ
    · rw [Set.indicator_of_mem hx, mul_one]; exact hΦb x
    · rw [Set.indicator_of_notMem hx, mul_zero, abs_zero]; exact hB0
  set Ψ : Submission.BoseGases.X n → ℝ :=
    Submission.BoseGases.aQ ℓ j (Submission.BoseGases.aP ℓ i Θ) with hΨdef
  set F : Submission.BoseGases.X n → ℝ :=
    fun x => ∫ u in Submission.BoseGases.acube ℓ, |Ψ (Function.update x j u)| with hFdef
  -- the sharp state-level fibre Cauchy–Schwarz
  obtain ⟨hFib_int, hFib_le⟩ := chDimgFibreSharp (ℓ := ℓ) hℓ i j hij hΦm hB0 hΦb
  have hFint : MeasureTheory.Integrable (fun x : Submission.BoseGases.X n => |Θ x| * F x) := by
    simpa only [hΘdef, hΨdef, hFdef] using hFib_int
  have hFle : ∫ x : Submission.BoseGases.X n, |Θ x| * F x
      ≤ ℓ ^ 3 * ∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2 := by
    simpa only [hΘdef, hΨdef, hFdef] using hFib_le
  -- the unfolded integrand, at a fixed `x`
  set Gfun : Submission.BoseGases.X n → ℂ := fun x => ∫ w : E3,
      ((Work.BoseK15.corpusBox.chiLam ℓ w : ℝ) : ℂ) * KχfrU v h μ fu N w *
        (∫ u in Submission.BoseGases.acube ℓ,
          chDimgImgSum fc (chKappa v μ) ℓ u w * ((Ψ (Function.update x j u) : ℝ) : ℂ)) with hGdef
  have hunf : chDimg v h fc fu μ N i j Θ
      = ∫ x : Submission.BoseGases.X n, ((Θ x : ℝ) : ℂ) * Gfun x := by
    simp only [chDimg, chDimgImgSum, hΨdef, hGdef]
    rw [← hℓdef]
  -- ## step 1: the `x`-integral of the norm
  have hstep1 : ‖chDimg v h fc fu μ N i j Θ‖
      ≤ ∫ x : Submission.BoseGases.X n, |Θ x| * ‖Gfun x‖ := by
    rw [hunf]
    refine (norm_integral_le_integral_norm _).trans_eq ?_
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  -- ## step 2: the pointwise bound on the `w`-integral
  have hG : ∀ x : Submission.BoseGases.X n, ‖Gfun x‖ ≤ A * (∫ w, W w) * F x := by
    intro x
    have hh := chDimg_wint_le (i := i) (j := j) (ℓ := ℓ) hℓ hWint hA0 hA hΘm hB0 hΘb
      (fun w u hu => by simpa only [chDimgImgSum] using hpt w u hu) x
    simpa only [hGdef, hΨdef, hFdef] using hh
  set C₀ : ℝ := A * (∫ w, W w) with hC₀def
  have hC0 : 0 ≤ C₀ := by
    rw [hC₀def]; exact mul_nonneg hA0 (integral_nonneg hW0)
  have hstep2 : ∫ x : Submission.BoseGases.X n, |Θ x| * ‖Gfun x‖
      ≤ ∫ x : Submission.BoseGases.X n, C₀ * (|Θ x| * F x) := by
    refine MeasureTheory.integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => ?_)
      ?_ (Filter.Eventually.of_forall fun x => ?_)
    · positivity
    · exact hFint.const_mul C₀
    · calc |Θ x| * ‖Gfun x‖ ≤ |Θ x| * (C₀ * F x) :=
            mul_le_mul_of_nonneg_left (hG x) (abs_nonneg _)
        _ = C₀ * (|Θ x| * F x) := by ring
  have hstep3 : ∫ x : Submission.BoseGases.X n, C₀ * (|Θ x| * F x)
      = C₀ * ∫ x : Submission.BoseGases.X n, |Θ x| * F x := by
    rw [MeasureTheory.integral_const_mul]
  -- ## step 3: assemble
  calc ‖chDimg v h fc fu μ N i j Θ‖
      ≤ ∫ x : Submission.BoseGases.X n, |Θ x| * ‖Gfun x‖ := hstep1
    _ ≤ ∫ x : Submission.BoseGases.X n, C₀ * (|Θ x| * F x) := hstep2
    _ = C₀ * ∫ x : Submission.BoseGases.X n, |Θ x| * F x := hstep3
    _ ≤ C₀ * (ℓ ^ 3 * ∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2) :=
        mul_le_mul_of_nonneg_left hFle hC0
    _ = ℓ ^ 3 * A * (∫ w, W w) * (∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2) := by
        rw [hC₀def]; ring

end Work.BoseBoxFock.PCFU
