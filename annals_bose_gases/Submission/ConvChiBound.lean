import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.Unique
import ChallengeDeps
import Submission.KernelIds
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Layer 5, brick B3 — bounds on the renormalized kernel (eq:W1-g)

With `χ` from `Submission.CubicChi` (even, `0 ≤ χ`, `∫χ² = 1`,
`CubicChi.conv3_at_zero : (χ⋆χ)(0) = 1`) and `C_ℓ(x) := (χ⋆χ)(x/ℓ) =
convScale ℓ x` (`Submission.KernelIds`), this module proves the three facts
needed for the FS kernel sandwich `eq:W1-g`

    g(x) ≤ W₁(x) := g(x)/C_ℓ(x) ≤ g(x)·(1 + C(R/ℓ)²)      (final_v2.tex line ~834)

for `g ≥ 0` with `supp g ⊆ ball 0 R` and `0 < ℓ` with `R/ℓ` small:

1. `conv3chi_le_one` — `(χ⋆χ)(x) ≤ 1` for all `x`.  Route: `χ ≥ 0` and
   `2ab ≤ a²+b²` gives `(χ⋆χ)(x) = ∫_y χ(y)χ(x−y) dy ≤ (1/2)∫χ(y)² dy +
   (1/2)∫χ(x−y)² dy = 1` (`∫χ² = 1` and translation-invariance
   `∫_y χ(x−y)² dy = ∫χ²`, via `KernelIds.integral_comp_sub_left`).
   (Together with `KernelIds.conv3chi_nonneg`: `0 ≤ (χ⋆χ) ≤ 1`.)

2. `conv3chi_second_order_bound` — since `χ⋆χ` is C^∞ (`CubicChi.conv_contDiff`),
   even (`KernelIds.conv3chi_even`), and equals `1` at `0`, its gradient
   vanishes at `0` and is Lipschitz near `0`, so a second-order Taylor bound
   holds: `∃ C ≥ 0, ∃ r₁ > 0, ∀ x, ‖x‖ ≤ r₁ → |(χ⋆χ)(x) − 1| ≤ C·‖x‖²`.
   Route: `f := χ⋆χ` is `C²` at `0`, hence `D := fderiv f` is `C¹` at `0`
   (`ContDiffAt.fderiv_right_succ`), so `D` is Lipschitz on a ball
   (`ContDiffAt.exists_lipschitzOnWith`).  Evenness forces `D 0 = 0`
   (`fderiv` of `f ∘ (-id) = f`), so `‖D z‖ ≤ K·‖z‖` on that ball.  Then the
   mean-value theorem on the convex set `closedBall 0 ‖x‖` applied to `f`
   (whose derivative `D z` is bounded by `K·‖x‖` there) gives
   `|f(x) − f(0)| ≤ (K·‖x‖)·‖x‖ = K‖x‖²`, and `f(0) = 1`.

3. `wScaled_sandwich` — instantiate on `C_ℓ(x) := convScale ℓ x`: under the
   regime conditions (`‖x/ℓ‖ ≤ r₁` on the support of `g`, i.e. `R/ℓ ≤ r₁`,
   and `C(R/ℓ)² ≤ 1/2` so that `1/2 ≤ C_ℓ(x)` and `1/(1−u) ≤ 1+2u` for
   `u := C(R/ℓ)²`), for every `x`:

       g x ≤ wScaled ℓ g x ∧ wScaled ℓ g x ≤ g x · (1 + 2C(R/ℓ)²).

   Case `g x = 0`: both sides are `0` (division by zero returns `0`).
   Case `g x > 0` (`0 ≤ g`): then `‖x‖ < R`, `|C_ℓ(x) − 1| ≤ C(R/ℓ)²`, and
   `1/2 ≤ C_ℓ(x) ≤ 1` (part 1 gives `≤ 1`); the field laws for division give
   the bounds.
-/

noncomputable section

open MeasureTheory
open scoped ContDiff Topology Real Convolution

namespace Submission.BoseGases

set_option autoImplicit false
set_option linter.unusedVariables false

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

-- ======================================================================
-- smoothness infrastructure for `f(x) := (χ⋆χ)(x)`
-- ======================================================================

/-- `χ⋆χ` is `C¹` at every point. -/
lemma conv3chi_contDiffAt_one (y : ℝ³) :
    ContDiffAt ℝ (1 : ℕ∞ω) (fun x : ℝ³ => conv3 chi chi x) y := by
  have hca : ContDiffAt ℝ ∞ (fun x : ℝ³ => conv3 chi chi x) y :=
    (contDiff_iff_contDiffAt.mp conv_contDiff) y
  exact ContDiffAt.of_le (m := 1) (n := ∞) hca (by norm_num)

/-- `χ⋆χ` is `C²` at `0`. -/
lemma conv3chi_contDiffAt_two_zero :
    ContDiffAt ℝ (2 : ℕ∞ω) (fun x : ℝ³ => conv3 chi chi x) 0 := by
  have hca : ContDiffAt ℝ ∞ (fun x : ℝ³ => conv3 chi chi x) 0 :=
    (contDiff_iff_contDiffAt.mp conv_contDiff) 0
  have hmn : (2 : ℕ∞ω) ≤ (∞ : ℕ∞ω) := by
    exact (WithTop.coe_le_coe.mpr le_top : (2 : ℕ∞ω) ≤ (∞ : ℕ∞ω))
  exact ContDiffAt.of_le (m := 2) (n := ∞) hca hmn

/-- The derivative of `χ⋆χ` is `C¹` at `0`. -/
lemma conv3chi_contDiffAt_fderiv_one :
    ContDiffAt ℝ (1 : ℕ∞ω) (fderiv ℝ (fun x : ℝ³ => conv3 chi chi x)) 0 := by
  exact ContDiffAt.fderiv_right_succ conv3chi_contDiffAt_two_zero

/-- Evenness of `χ⋆χ` forces its derivative at `0` to vanish. -/
lemma conv3chi_fderiv_zero : fderiv ℝ (fun x : ℝ³ => conv3 chi chi x) 0 = 0 := by
  let f : ℝ³ → ℝ := fun x => conv3 chi chi x
  let N : ℝ³ →L[ℝ] ℝ³ := -ContinuousLinearMap.id ℝ ℝ³
  have hfD0 : DifferentiableAt ℝ f 0 := by
    exact (conv3chi_contDiffAt_one 0).differentiableAt (by norm_num)
  have hfDN : DifferentiableAt ℝ f (N 0) := by
    simpa [N] using hfD0
  have hcomp : fderiv ℝ (f ∘ ⇑N) 0 = (fderiv ℝ f (N 0)).comp (fderiv ℝ (⇑N) 0) :=
    fderiv_comp 0 hfDN (ContinuousLinearMap.differentiableAt N)
  have hNeven : f ∘ ⇑N = f := by
    funext x
    dsimp [f, N]
    exact conv3chi_even x
  have hDmain : fderiv ℝ f 0 = (fderiv ℝ f 0).comp N := by
    calc
      fderiv ℝ f 0 = fderiv ℝ (f ∘ ⇑N) 0 := by
        congr 1
        exact hNeven.symm
      _ = (fderiv ℝ f (N 0)).comp (fderiv ℝ (⇑N) 0) := hcomp
      _ = (fderiv ℝ f 0).comp N := by
        congr 1
        · congr 1
          simp [N]
        · exact ContinuousLinearMap.fderiv N
  have hneg : (fderiv ℝ f 0).comp N = -(fderiv ℝ f 0) := by
    apply ContinuousLinearMap.ext
    intro v
    change (fderiv ℝ f 0) (-v) = -((fderiv ℝ f 0) v)
    rw [map_neg]
  have hsymm : fderiv ℝ f 0 = -(fderiv ℝ f 0) := hDmain.trans hneg
  have hD0 : fderiv ℝ f 0 = 0 := by
    apply ContinuousLinearMap.ext
    intro v
    have hv : (fderiv ℝ f 0) v = -((fderiv ℝ f 0) v) :=
      congrArg (fun L : ℝ³ →L[ℝ] ℝ => L v) hsymm
    change (fderiv ℝ f 0) v = 0
    linarith
  simpa [f] using hD0

/-- `‖t • x‖ = t * ‖x‖` for `0 ≤ t`. -/
lemma norm_smul_of_nonneg {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (t : ℝ)
    (ht : 0 ≤ t) (x : E) : ‖t • x‖ = t * ‖x‖ := by
  rw [norm_smul]
  congr 1
  exact abs_of_nonneg ht

-- ======================================================================
-- 1. the upper bound `(χ⋆χ)(x) ≤ 1`
-- ======================================================================

lemma chi_sq_continuous : Continuous (fun x : ℝ³ => (chi x) ^ 2) := by
  exact chi_continuous.pow 2

lemma chi_sq_hasCompactSupport : HasCompactSupport (fun x : ℝ³ => (chi x) ^ 2) := by
  refine HasCompactSupport.mono chi_hasCompactSupport ?_
  intro x hx
  exact fun hb => hx (by simp [hb])

lemma integrable_chi_sq : Integrable (fun x : ℝ³ => (chi x) ^ 2) := by
  exact Continuous.integrable_of_hasCompactSupport chi_sq_continuous chi_sq_hasCompactSupport

lemma integrable_chi_sq_sub (x : ℝ³) : Integrable (fun y : ℝ³ => (chi (x - y)) ^ 2) := by
  have hp : MeasurePreserving (fun y : ℝ³ => x - y) volume volume := by
    have hpneg : MeasurePreserving (fun y : ℝ³ => -y) volume volume :=
      Measure.measurePreserving_neg (volume : Measure ℝ³)
    have hptrans : MeasurePreserving (fun y : ℝ³ => x + y) volume volume :=
      measurePreserving_add_left (volume : Measure ℝ³) x
    simpa [Function.comp_def, sub_eq_add_neg] using (hptrans.comp hpneg)
  have hg : AEStronglyMeasurable (fun z : ℝ³ => (chi z) ^ 2) volume :=
    chi_sq_continuous.aestronglyMeasurable
  exact (hp.integrable_comp hg).mpr integrable_chi_sq

/-- `(χ⋆χ)(x) ≤ 1` pointwise (with `0 ≤ (χ⋆χ)` from
`KernelIds.conv3chi_nonneg`, this is the upper half of `0 ≤ χ⋆χ ≤ 1`). -/
theorem conv3chi_le_one (x : ℝ³) : conv3 chi chi x ≤ 1 := by
  unfold conv3
  let g : ℝ³ → ℝ := fun y : ℝ³ => (1 / 2) * ((chi y) ^ 2 + (chi (x - y)) ^ 2)
  have hg_int : Integrable g := by
    dsimp [g]
    exact (Integrable.const_mul (Integrable.add integrable_chi_sq (integrable_chi_sq_sub x))
      (1 / 2))
  have hpt : ∀ y : ℝ³,
      chi y * chi (x - y) ≤ (1 / 2) * ((chi y) ^ 2 + (chi (x - y)) ^ 2) := by
    intro y
    nlinarith [sq_nonneg (chi y - chi (x - y))]
  have hf_int : Integrable (fun y : ℝ³ => chi y * chi (x - y)) := by
    refine Integrable.mono' (g := g) hg_int ?_ ?_
    · have hc1 : AEStronglyMeasurable (fun y : ℝ³ => chi y) volume :=
        chi_continuous.aestronglyMeasurable
      have hc2 : AEStronglyMeasurable (fun y : ℝ³ => chi (x - y)) volume :=
        (chi_continuous.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
      exact hc1.mul hc2
    · apply ae_of_all
      intro y
      dsimp [g]
      have hnon : 0 ≤ chi y * chi (x - y) := mul_nonneg (chi_nonneg y) (chi_nonneg (x - y))
      calc
        ‖chi y * chi (x - y)‖ = |chi y * chi (x - y)| := by rfl
        _ = chi y * chi (x - y) := abs_of_nonneg hnon
        _ ≤ (1 / 2) * ((chi y) ^ 2 + (chi (x - y)) ^ 2) := hpt y
  have hfg : (fun y : ℝ³ => chi y * chi (x - y)) ≤ᵐ[volume] g := by
    apply ae_of_all
    intro y
    dsimp [g]
    exact hpt y
  have hmono : (∫ y : ℝ³, chi y * chi (x - y)) ≤ ∫ y : ℝ³, g y :=
    integral_mono_ae hf_int hg_int hfg
  calc
    (∫ y : ℝ³, chi y * chi (x - y)) ≤ ∫ y : ℝ³, g y := hmono
    _ = ∫ y : ℝ³, (1 / 2) * ((chi y) ^ 2 + (chi (x - y)) ^ 2) := by
      apply integral_congr_ae
      exact ae_of_all _ (by intro y; dsimp [g])
    _ = (1 / 2) * (∫ y : ℝ³, (chi y) ^ 2 + (chi (x - y)) ^ 2) := by
      rw [integral_const_mul]
    _ = (1 / 2) * ((∫ y : ℝ³, (chi y) ^ 2) + (∫ y : ℝ³, (chi (x - y)) ^ 2)) := by
      rw [integral_add integrable_chi_sq (integrable_chi_sq_sub x)]
    _ = (1 / 2) * (1 + 1) := by
      congr 1
      rw [integral_comp_sub_left (fun z : ℝ³ => (chi z) ^ 2) x]
      rw [chi_L2]
    _ = 1 := by norm_num

-- ======================================================================
-- 2. the second-order Taylor bound at the origin
-- ======================================================================

/-- Second-order Taylor bound for the even smooth function `χ⋆χ` at the
origin (value `1` there): `|(χ⋆χ)(x) − 1| ≤ C·‖x‖²` near `0`. -/
theorem conv3chi_second_order_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ r₁ : ℝ, 0 < r₁ ∧
      ∀ x : ℝ³, ‖x‖ ≤ r₁ → |conv3 chi chi x - 1| ≤ C * ‖x‖ ^ 2 := by
  let fc : ℝ³ → ℝ := fun x => conv3 chi chi x
  have hcd1 : ContDiffAt ℝ (1 : ℕ∞ω) (fderiv ℝ fc) 0 := by
    simpa [fc] using conv3chi_contDiffAt_fderiv_one
  rcases ContDiffAt.exists_lipschitzOnWith hcd1 with ⟨K, s0, hsnhds, hlip⟩
  rcases (Metric.mem_nhds_iff.mp hsnhds) with ⟨ε, hεpos, hball0⟩
  refine ⟨(K : ℝ), K.2, ε / 2, by positivity, ?_⟩
  intro x hx
  have hxε : ‖x‖ < ε := by
    exact lt_of_le_of_lt hx (half_lt_self hεpos)
  have hD0 : fderiv ℝ fc 0 = 0 := by
    simpa [fc] using conv3chi_fderiv_zero
  have hlipz : ∀ z : ℝ³, ‖z‖ < ε → ‖fderiv ℝ fc z‖ ≤ (K : ℝ) * ‖z‖ := by
    intro z hzε
    have hzball : z ∈ Metric.ball (0 : ℝ³) ε := by
      simpa [Metric.mem_ball, dist_eq_norm] using hzε
    have h0ball : (0 : ℝ³) ∈ Metric.ball (0 : ℝ³) ε := by
      simpa [Metric.mem_ball] using hεpos
    have hd := (LipschitzOnWith.dist_le_mul hlip) z (hball0 hzball) (0 : ℝ³) (hball0 h0ball)
    simpa [dist_eq_norm, hD0] using hd
  have hmain : ‖fc x - fc 0‖ ≤ (K : ℝ) * ‖x‖ ^ 2 := by
    let s : Set ℝ³ := Metric.closedBall (0 : ℝ³) ‖x‖
    have hconv : Convex ℝ s := by
      dsimp [s]
      exact (convex_closedBall (a := (0 : ℝ³)) (r := ‖x‖))
    have h0s : (0 : ℝ³) ∈ s := by
      dsimp [s]
      simp [Metric.mem_closedBall]
    have hxs : x ∈ s := by
      dsimp [s]
      simp [Metric.mem_closedBall]
    have hfd : ∀ z : ℝ³, z ∈ s → HasFDerivWithinAt fc (fderiv ℝ fc z) s z := by
      intro z hz
      have hdiff : DifferentiableAt ℝ fc z := by
        simpa [fc] using (conv3chi_contDiffAt_one z).differentiableAt (by norm_num)
      exact hdiff.hasFDerivAt.hasFDerivWithinAt
    have hbnd : ∀ z : ℝ³, z ∈ s → ‖fderiv ℝ fc z‖ ≤ (K : ℝ) * ‖x‖ := by
      intro z hz
      have hzn : ‖z‖ ≤ ‖x‖ := by
        simpa [s, Metric.mem_closedBall, dist_eq_norm] using hz
      have hzε : ‖z‖ < ε := lt_of_le_of_lt hzn hxε
      exact le_trans (hlipz z hzε) (mul_le_mul_of_nonneg_left hzn (show 0 ≤ (K : ℝ) from K.2))
    have hmvt := hconv.norm_image_sub_le_of_norm_hasFDerivWithin_le
      (f := fc) (f' := fun z : ℝ³ => fderiv ℝ fc z) hfd hbnd h0s hxs
    -- hmvt : ‖fc x - fc 0‖ ≤ (↑K * ‖x‖) * ‖x - 0‖
    rw [sub_zero] at hmvt
    calc
      ‖fc x - fc 0‖ ≤ ↑K * ‖x‖ * ‖x‖ := by
        simpa [mul_assoc] using hmvt
      _ = (K : ℝ) * ‖x‖ ^ 2 := by ring
  have hgoal : |conv3 chi chi x - 1| ≤ (K : ℝ) * ‖x‖ ^ 2 := by
    have hu1 : fc x = conv3 chi chi x := by
      dsimp [fc]
    have hu0 : fc 0 = 1 := by
      dsimp [fc]
      exact conv3_at_zero
    rw [hu1, hu0] at hmain
    simpa using hmain
  simpa using hgoal

-- ======================================================================
-- 3. the FS kernel sandwich
-- ======================================================================

/-- The kernel sandwich (eq:W1-g): for `g ≥ 0` supported inside `ball 0 R`
and a `0 < ℓ` with `R/ℓ` small enough that the second-order bound applies on
the support (`R/ℓ ≤ r₁`) and `C(R/ℓ)² ≤ 1/2`, the renormalized kernel
`W₁(x) := g x / (χ⋆χ)(x/ℓ)` satisfies `g(x) ≤ W₁(x) ≤ g(x)·(1+2C(R/ℓ)²)`
pointwise in `x`. -/
theorem wScaled_sandwich {g : ℝ³ → ℝ} {ℓ R r₁ C : ℝ} (hℓ : 0 < ℓ)
    (hC : 0 ≤ C) (hr₁ : 0 < r₁)
    (hT : ∀ x : ℝ³, ‖x‖ ≤ r₁ → |conv3 chi chi x - 1| ≤ C * ‖x‖ ^ 2)
    (hg : 0 ≤ g) (hgsupp : ∀ x : ℝ³, R ≤ ‖x‖ → g x = 0)
    (hR : 0 ≤ R) (hreg : R / ℓ ≤ r₁) (hcond : C * (R / ℓ) ^ 2 ≤ 1 / 2) :
    ∀ x : ℝ³, g x ≤ wScaled ℓ g x ∧
      wScaled ℓ g x ≤ g x * (1 + 2 * C * (R / ℓ) ^ 2) := by
  intro x
  by_cases hx0 : g x = 0
  · simp [wScaled, hx0]
  · have hgpos : 0 < g x := lt_of_le_of_ne (hg x) (Ne.symm hx0)
    have hxRlt : ‖x‖ < R := by
      by_contra hn
      have hRle : R ≤ ‖x‖ := le_of_not_gt hn
      exact (hgpos.ne' (hgsupp x hRle))
    let y : ℝ³ := (ℓ⁻¹) • x
    let u : ℝ := C * (R / ℓ) ^ 2
    have hℓi : 0 < (ℓ⁻¹) := inv_pos.mpr hℓ
    have hu0 : 0 ≤ u := by
      dsimp [u]
      exact mul_nonneg hC (sq_nonneg (R / ℓ))
    have hcondU : u ≤ 1 / 2 := by
      simpa [u] using hcond
    have hyRlt : ‖y‖ < R / ℓ := by
      dsimp [y]
      calc
        ‖(ℓ⁻¹) • x‖ = (ℓ⁻¹) * ‖x‖ := norm_smul_of_nonneg (ℓ⁻¹) (le_of_lt hℓi) x
        _ < (ℓ⁻¹) * R := mul_lt_mul_of_pos_left hxRlt hℓi
        _ = R / ℓ := by ring
    have hyle : ‖y‖ ≤ r₁ := by
      exact le_of_lt (lt_of_lt_of_le hyRlt hreg)
    have hT' := hT y hyle
    have hbnd : C * ‖y‖ ^ 2 ≤ u := by
      dsimp [u]
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (norm_nonneg y) (le_of_lt hyRlt) 2) hC
    have hCu : |conv3 chi chi y - 1| ≤ u := le_trans hT' hbnd
    have hCu' := (abs_le.mp hCu)
    have hcge : 1 - u ≤ conv3 chi chi y := by linarith
    have hcup : conv3 chi chi y ≤ 1 + u := by linarith
    have hcpos : 0 < conv3 chi chi y := by
      have hcone : 0 < 1 - u := by linarith
      exact lt_of_lt_of_le hcone hcge
    have hconvle1 : convScale ℓ x ≤ 1 := by
      dsimp [convScale, y]
      exact conv3chi_le_one ((ℓ⁻¹) • x)
    have hconvge : 1 - u ≤ convScale ℓ x := by
      dsimp [convScale, y]
      exact hcge
    have hconvpos : 0 < convScale ℓ x := by
      dsimp [convScale, y]
      exact hcpos
    -- left inequality: `g x ≤ g x / C_ℓ(x)`
    have hleft : g x ≤ wScaled ℓ g x := by
      dsimp [wScaled]
      rw [le_div_iff₀ hconvpos]
      have hprod : 0 ≤ g x * (1 - convScale ℓ x) :=
        mul_nonneg (hg x) (sub_nonneg.mpr hconvle1)
      nlinarith
    -- right inequality: `g x / C_ℓ(x) ≤ g x (1 + 2u)`, using `1 ≤ (1+2u)C_ℓ(x)`
    have h1p2u : 0 ≤ 1 + 2 * u := by nlinarith
    have hprodpos : 0 ≤ u * (1 - 2 * u) :=
      mul_nonneg hu0 (sub_nonneg.mpr (by linarith))
    have hpoly1 : 1 ≤ (1 - u) * (1 + 2 * u) := by
      nlinarith [hprodpos]
    have hstep : (1 - u) * (1 + 2 * u) ≤ convScale ℓ x * (1 + 2 * u) := by
      exact mul_le_mul_of_nonneg_right hconvge h1p2u
    have hcbig : 1 ≤ (1 + 2 * u) * convScale ℓ x := by
      calc
        1 ≤ convScale ℓ x * (1 + 2 * u) := le_trans hpoly1 hstep
        _ = (1 + 2 * u) * convScale ℓ x := by ring
    have hright : wScaled ℓ g x ≤ g x * (1 + 2 * u) := by
      dsimp [wScaled]
      rw [div_le_iff₀ hconvpos]
      have hprod2 : 0 ≤ g x * ((1 + 2 * u) * convScale ℓ x - 1) :=
        mul_nonneg (hg x) (sub_nonneg.mpr hcbig)
      nlinarith
    constructor
    · exact hleft
    · dsimp [u] at hright
      convert hright using 1
      ring

end BoseGases

end Submission
