import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.FDeriv.Const
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseB1Cube.autocorr_sub_le
import Submission.Work.BoseB1Cube.chiSmallB_lipschitz_le
import Submission.Work.BoseB1Cube.w1MassB_ge_chiMass_plateau
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Fréchet-derivative bounds for the two-factor sliding cutoff `chiSmallB`

The window of the sliding small-box word is

    chiSmallB M ℓ d u x = chiScale ℓ x · chiSmall M ((ℓ d)⁻¹ • x − u) ,

the product of the corpus ball bump at the big-box scale `ℓ` and the cosine-`M`-th-power bump
`chiSmall M` at the small-box scale `ℓ d`.  This file proves that its Fréchet derivative is
controlled by the two scales, pointwise and in `L¹`:

* **pointwise**: `‖fderiv ℝ (chiSmallB M ℓ d u) x‖ ≤ C · chiSupAbs · (1/ℓ + 1/(ℓd))`;
* **`L¹`**: the same bound times the volume `(ℓ d)³` of the small box, which is exactly the
  volume of the support.

The route is a *Lipschitz* (first-difference) bound rather than a chain rule, because the
cosine bump `chiSmall M` is only `C¹` for `M ≥ 2` and merely Lipschitz at `M = 1`
(`zeta1d` has a kink at `±1/2`); a `LipschitzWith` bound survives at non-differentiable points
(`‖fderiv f x‖ = 0` there), so the estimate holds for every `M ≥ 1`.

The two Lipschitz constants are taken from the corpus:

* `Work.BoseFixB1B.exists_lipschitz_chi` — the corpus bump `chi` is `Cchi`-Lipschitz;
* `Work.BoseFixB1S.chiSmall_lipschitz` — `chiSmall M` is `L`-Lipschitz for `M ≥ 1`
  (through `zeta1d` being `π`-Lipschitz and `x ↦ x^M` being `M`-Lipschitz on `[0,1]`).

The product rule for differences `A(y)B(y) − A(x)B(x) = (A(y)−A(x))·B(y) + A(x)·(B(y)−B(x))`
then gives the two-scale constant `Cchi·chiSmallNormFactor M + chiSupAbs·L` — the two scales
enter *separately*, which is what makes the estimate uniform in `d` (no `d ≤ 1`).

For the `L¹` bound we integrate against the indicator of the translated cube
`(ℓd)•u + acube (ℓd)` of volume exactly `(ℓd)³`, which contains the support: the support of
`chiSmallB M ℓ d u` lies in `dlBox ℓ d u ⊆ (ℓd)•u + acube (ℓd)`, a closed set, so off it the
function vanishes in a neighbourhood of every point and its Fréchet derivative vanishes there.
-/

namespace Work.BoseB1Cube

open MeasureTheory Metric Filter
open scoped Real Topology

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false

/-! ## 1. The sup of the small-box factor -/

/-- **Sup bound of the `ℓd`-scale cosine-`M`-th-power factor.**
`chiSmall M = chiSmallBase M · chiSmallNormFactor M` with `|chiSmallBase M| ≤ 1` (each cosine
factor of `ζζζ` lies in `[0,1]`). -/
theorem chiSmall_abs_le_normFactor (M : ℕ) (z : E3) :
    |Submission.BoseGases.chiSmall M z| ≤ Submission.BoseGases.chiSmallNormFactor M := by
  have hnf : 0 ≤ Submission.BoseGases.chiSmallNormFactor M :=
    Submission.BoseGases.chiSmallNormFactor_nonneg M
  rw [Work.BoseFixB1S.chiLip_chiSmall_eq_factor M z, abs_mul, abs_of_nonneg hnf]
  calc |Submission.BoseGases.chiSmallBase M z| * Submission.BoseGases.chiSmallNormFactor M
      ≤ 1 * Submission.BoseGases.chiSmallNormFactor M :=
        mul_le_mul_of_nonneg_right (chiSmallBase_abs_le_one M z) hnf
    _ = Submission.BoseGases.chiSmallNormFactor M := one_mul _

/-! ## 2. The two-scale Lipschitz bound -/

/-- **The two-scale first-difference bound for `chiSmallB`.**  There is a constant `A ≥ 0` with

    |chiSmallB M ℓ d u y − chiSmallB M ℓ d u x| ≤ A · (1/ℓ + 1/(ℓd)) · ‖y − x‖

for all `0 < ℓ`, `0 < d`, `u`, `x`, `y` and every `M ≥ 1` — the two scales enter *separately*,
so no hypothesis comparing `d` with `1` is needed. -/
theorem chiSmallB_abs_sub_le {M : ℕ} (hM : 1 ≤ M) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (ℓ d : ℝ) (hℓ : 0 < ℓ) (hd : 0 < d) (u x y : E3),
      |Submission.BoseGases.chiSmallB M ℓ d u y - Submission.BoseGases.chiSmallB M ℓ d u x|
        ≤ A * (ℓ⁻¹ + (ℓ * d)⁻¹) * ‖y - x‖ := by
  obtain ⟨Cchi, hCchi0, hCchi⟩ := Work.BoseFixB1B.exists_lipschitz_chi
  obtain ⟨L, hL0, hL⟩ := Work.BoseFixB1S.chiSmall_lipschitz hM
  have hnf : 0 ≤ Submission.BoseGases.chiSmallNormFactor M :=
    Submission.BoseGases.chiSmallNormFactor_nonneg M
  have hsup : 0 ≤ Submission.BoseGases.chiSupAbs := Submission.BoseGases.chiSupAbs_nonneg
  refine ⟨Cchi * Submission.BoseGases.chiSmallNormFactor M
      + Submission.BoseGases.chiSupAbs * L,
    add_nonneg (mul_nonneg hCchi0 hnf) (mul_nonneg hsup hL0), ?_⟩
  intro ℓ d hℓ hd u x y
  have hℓd : 0 < ℓ * d := mul_pos hℓ hd
  have hl : 0 ≤ ℓ⁻¹ := le_of_lt (inv_pos.mpr hℓ)
  have hli : 0 ≤ (ℓ * d)⁻¹ := le_of_lt (inv_pos.mpr hℓd)
  -- the `ℓ`-scale factor: Lipschitz
  have hA : |Submission.BoseGases.chiScale ℓ y - Submission.BoseGases.chiScale ℓ x|
      ≤ Cchi * ℓ⁻¹ * ‖y - x‖ :=
    Work.BoseFixB1.SectorAux.chiScale_lipschitz (C := Cchi) hCchi hℓ y x
  -- the `ℓd`-scale factor: sup and Lipschitz
  have hBsup : |Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • y - u)|
      ≤ Submission.BoseGases.chiSmallNormFactor M := chiSmall_abs_le_normFactor M _
  have hAsup : |Submission.BoseGases.chiScale ℓ x| ≤ Submission.BoseGases.chiSupAbs :=
    Submission.BoseGases.chiScale_abs_le_sup ℓ x
  have hBlip : |Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • y - u)
      - Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • x - u)|
      ≤ L * ((ℓ * d)⁻¹ * ‖y - x‖) := by
    have h := hL ((ℓ * d)⁻¹ • y - u) ((ℓ * d)⁻¹ • y - u - ((ℓ * d)⁻¹ • x - u))
    have hsub : (ℓ * d)⁻¹ • y - u - ((ℓ * d)⁻¹ • y - u - ((ℓ * d)⁻¹ • x - u))
        = (ℓ * d)⁻¹ • x - u := by abel
    rw [hsub] at h
    have hvec : (ℓ * d)⁻¹ • y - u - ((ℓ * d)⁻¹ • x - u) = (ℓ * d)⁻¹ • (y - x) := by
      rw [smul_sub]
      abel
    rw [hvec] at h
    have hnorm : ‖(ℓ * d)⁻¹ • (y - x)‖ = (ℓ * d)⁻¹ * ‖y - x‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hli]
    rwa [hnorm] at h
  have hkey : Submission.BoseGases.chiSmallB M ℓ d u y - Submission.BoseGases.chiSmallB M ℓ d u x
      = (Submission.BoseGases.chiScale ℓ y - Submission.BoseGases.chiScale ℓ x)
          * Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • y - u)
        + Submission.BoseGases.chiScale ℓ x
          * (Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • y - u)
              - Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • x - u)) := by
    simp only [Submission.BoseGases.chiSmallB]
    ring
  rw [hkey]
  have hb1 : |(Submission.BoseGases.chiScale ℓ y - Submission.BoseGases.chiScale ℓ x)
        * Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • y - u)|
      ≤ (Cchi * ℓ⁻¹ * ‖y - x‖) * Submission.BoseGases.chiSmallNormFactor M := by
    rw [abs_mul]
    exact mul_le_mul hA hBsup (abs_nonneg _)
      (mul_nonneg (mul_nonneg hCchi0 hl) (norm_nonneg _))
  have hb2 : |Submission.BoseGases.chiScale ℓ x
        * (Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • y - u)
            - Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • x - u))|
      ≤ Submission.BoseGases.chiSupAbs * (L * ((ℓ * d)⁻¹ * ‖y - x‖)) := by
    rw [abs_mul]
    exact mul_le_mul hAsup hBlip (abs_nonneg _) hsup
  -- the two-scale arithmetic
  have hcoef : Cchi * Submission.BoseGases.chiSmallNormFactor M * ℓ⁻¹
        + Submission.BoseGases.chiSupAbs * L * (ℓ * d)⁻¹
      ≤ (Cchi * Submission.BoseGases.chiSmallNormFactor M
          + Submission.BoseGases.chiSupAbs * L) * (ℓ⁻¹ + (ℓ * d)⁻¹) := by
    have h1 : Cchi * Submission.BoseGases.chiSmallNormFactor M * ℓ⁻¹
        ≤ (Cchi * Submission.BoseGases.chiSmallNormFactor M) * (ℓ⁻¹ + (ℓ * d)⁻¹) := by
      have hle : ℓ⁻¹ ≤ ℓ⁻¹ + (ℓ * d)⁻¹ := le_add_of_nonneg_right hli
      exact mul_le_mul_of_nonneg_left hle (mul_nonneg hCchi0 hnf)
    have h2 : Submission.BoseGases.chiSupAbs * L * (ℓ * d)⁻¹
        ≤ (Submission.BoseGases.chiSupAbs * L) * (ℓ⁻¹ + (ℓ * d)⁻¹) := by
      have hle : (ℓ * d)⁻¹ ≤ ℓ⁻¹ + (ℓ * d)⁻¹ := le_add_of_nonneg_left hl
      exact mul_le_mul_of_nonneg_left hle (mul_nonneg hsup hL0)
    linarith
  calc |(Submission.BoseGases.chiScale ℓ y - Submission.BoseGases.chiScale ℓ x)
          * Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • y - u)
        + Submission.BoseGases.chiScale ℓ x
          * (Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • y - u)
              - Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • x - u))|
      ≤ |(Submission.BoseGases.chiScale ℓ y - Submission.BoseGases.chiScale ℓ x)
            * Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • y - u)|
        + |Submission.BoseGases.chiScale ℓ x
            * (Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • y - u)
                - Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • x - u))| := abs_add_le _ _
    _ ≤ (Cchi * ℓ⁻¹ * ‖y - x‖) * Submission.BoseGases.chiSmallNormFactor M
        + Submission.BoseGases.chiSupAbs * (L * ((ℓ * d)⁻¹ * ‖y - x‖)) := add_le_add hb1 hb2
    _ = (Cchi * Submission.BoseGases.chiSmallNormFactor M * ℓ⁻¹
          + Submission.BoseGases.chiSupAbs * L * (ℓ * d)⁻¹) * ‖y - x‖ := by ring
    _ ≤ (Cchi * Submission.BoseGases.chiSmallNormFactor M
          + Submission.BoseGases.chiSupAbs * L) * (ℓ⁻¹ + (ℓ * d)⁻¹) * ‖y - x‖ :=
        mul_le_mul_of_nonneg_right hcoef (norm_nonneg _)

/-! ## 3. The `L¹` bound -/

/-- **The `L¹` bound for the derivative of `chiSmallB`.**

If the Fréchet derivative of `chiSmallB M ℓ d u` is pointwise bounded by `c ≥ 0`, then its
integral is at most `c · (ℓd)³`: the support of `chiSmallB M ℓ d u` is contained in
`dlBox ℓ d u ⊆ (ℓd)•u + acube (ℓd)`, a closed set of volume `(ℓd)³` (the translate of the
centred cube `acube (ℓd)`), and off it the function vanishes in a neighbourhood of every point,
hence its Fréchet derivative vanishes. -/
theorem chiSmallB_integral_bound {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (u : E3) {c : ℝ} (hc0 : 0 ≤ c)
    (hc : ∀ x : E3, ‖fderiv ℝ (Submission.BoseGases.chiSmallB M ℓ d u) x‖ ≤ c) :
    (∫ x : E3, ‖fderiv ℝ (Submission.BoseGases.chiSmallB M ℓ d u) x‖)
      ≤ c * (ℓ * d) ^ 3 := by
  have hℓd : 0 < ℓ * d := mul_pos hℓ hd
  have hγ0 : 0 ≤ ℓ * d := le_of_lt hℓd
  set f := Submission.BoseGases.chiSmallB M ℓ d u with hf
  -- the translated cube containing the support
  set S : Set E3 := (fun h : E3 => h - (ℓ * d) • u) ⁻¹' Submission.BoseGases.acube (ℓ * d)
    with hSdef
  have hacube_closed : IsClosed (Submission.BoseGases.acube (ℓ * d)) := by
    rw [show Submission.BoseGases.acube (ℓ * d)
        = ⋂ m : Fin 3,
            {y : E3 | y.ofLp m ∈ Set.Icc (-(ℓ * d) / 2) ((ℓ * d) / 2)} by
      ext y
      simp [Submission.BoseGases.mem_acube_iff]]
    exact isClosed_iInter (fun m => isClosed_Icc.preimage
      (PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) m))
  have hSclosed : IsClosed S := by
    rw [hSdef]
    exact IsClosed.preimage (continuous_id.sub continuous_const) hacube_closed
  have hsupp : Function.support f ⊆ S := by
    intro y hy
    rw [hf] at hy
    have hdl := Work.SlotWord.chiSmallB_support_mem_dlBox hM hℓ hd hy
    rw [hSdef]
    exact ((Submission.BoseGases.mem_dlBox_iff ℓ d u y).mp hdl).2
  have htsupp : tsupport f ⊆ S := closure_minimal hsupp hSclosed
  have hmeas : MeasurableSet S := by
    rw [hSdef]
    exact (Submission.BoseGases.acube_measurable (ℓ * d)).preimage
      (continuous_id.sub continuous_const).measurable
  -- the volume of the cube
  have hvolS : (volume : Measure E3) S = ENNReal.ofReal ((ℓ * d) ^ 3) := by
    rw [hSdef]
    have hshift : (fun h : E3 => h - (ℓ * d) • u)
        = (fun h : E3 => -((ℓ * d) • u) + h) := by
      funext h
      rw [sub_eq_add_neg, add_comm]
    rw [hshift, measure_preimage_add (volume : Measure E3) (-((ℓ * d) • u))
      (Submission.BoseGases.acube (ℓ * d))]
    exact Submission.BoseGases.acube_volume (ℓ * d) hγ0
  -- off the support's closure the function vanishes on a neighbourhood, so the derivative is `0`
  have hzero : ∀ x : E3, x ∉ tsupport f → fderiv ℝ f x = 0 := by
    intro x hx
    have hvan : f =ᶠ[𝓝 x] (fun _ : E3 => (0 : ℝ)) := by
      obtain ⟨ε, hε, hsub⟩ := Metric.isOpen_iff.mp isClosed_closure.isOpen_compl x hx
      filter_upwards [Metric.ball_mem_nhds x hε] with y hy
      by_contra hfy
      exact hsub (Metric.mem_ball.mpr hy)
        (subset_tsupport f (Function.mem_support.mpr hfy))
    rw [hvan.fderiv_eq]
    exact congrFun (fderiv_const (𝕜 := ℝ) (c := (0 : ℝ))) x
  -- the pointwise bound against the indicator of the cube
  have hpt : ∀ x : E3, ‖fderiv ℝ f x‖ ≤ c * S.indicator (fun _ => (1 : ℝ)) x := by
    intro x
    by_cases hx : x ∈ S
    · rw [Set.indicator_of_mem hx, mul_one]
      exact hc x
    · have hxt : x ∉ tsupport f := fun h => hx (htsupp h)
      rw [Set.indicator_of_notMem hx, mul_zero, hzero x hxt, norm_zero]
  have hIntg : Integrable (fun x : E3 => c * S.indicator (fun _ => (1 : ℝ)) x) := by
    have hfin : (volume : Measure E3) S ≠ ⊤ := by
      rw [hvolS]
      exact ENNReal.ofReal_ne_top
    exact ((integrable_indicator_iff hmeas).mpr (integrableOn_const hfin (by simp))).const_mul c
  have hmono := integral_mono_of_nonneg (ae_of_all _ (fun x => norm_nonneg _)) hIntg
    (ae_of_all _ hpt)
  calc ∫ x : E3, ‖fderiv ℝ f x‖
      ≤ ∫ x : E3, c * S.indicator (fun _ => (1 : ℝ)) x := hmono
    _ = c * ∫ x : E3, S.indicator (fun _ => (1 : ℝ)) x := integral_const_mul c _
    _ = c * (volume S).toReal := by
        rw [integral_indicator hmeas, setIntegral_const, Measure.real_def]
        simp [smul_eq_mul]
    _ = c * (ℓ * d) ^ 3 := by
        rw [hvolS, ENNReal.toReal_ofReal (by positivity)]

/-! ## 4. The target -/

theorem chiSmallB_fderiv_bounds {M : ℕ} (hM : 1 ≤ M) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ℓ d : ℝ) (hℓ : 0 < ℓ) (hd : 0 < d) (u : EuclideanSpace ℝ (Fin 3)),
      (∀ x : EuclideanSpace ℝ (Fin 3),
          ‖fderiv ℝ (Submission.BoseGases.chiSmallB M ℓ d u) x‖
            ≤ C * Submission.BoseGases.chiSupAbs * (1 / ℓ + 1 / (ℓ * d))) ∧
      (∫ x : EuclideanSpace ℝ (Fin 3),
          ‖fderiv ℝ (Submission.BoseGases.chiSmallB M ℓ d u) x‖
        ≤ C * Submission.BoseGases.chiSupAbs * (1 / ℓ + 1 / (ℓ * d)) * (ℓ * d) ^ 3) := by
  obtain ⟨A, hA0, hA⟩ := chiSmallB_abs_sub_le hM
  -- the corpus sup is positive (`chi 0 > 0` and `|chi 0| ≤ chiSupAbs`)
  have hsup_pos : 0 < Submission.BoseGases.chiSupAbs := by
    have h0 : 0 < Submission.BoseGases.chi 0 := by
      rw [Submission.BoseGases.chi, Submission.BoseGases.chiBase_zero]
      exact div_pos one_pos (Real.sqrt_pos.mpr Submission.BoseGases.chiNormSq_pos)
    have h1 : Submission.BoseGases.chi 0 ≤ Submission.BoseGases.chiSupAbs := by
      have := Submission.BoseGases.chi_abs_le_sup 0
      rwa [abs_of_pos h0] at this
    linarith
  refine ⟨max 1 (A / Submission.BoseGases.chiSupAbs), lt_max_of_lt_left one_pos, ?_⟩
  have hAle : A ≤ max 1 (A / Submission.BoseGases.chiSupAbs) * Submission.BoseGases.chiSupAbs := by
    rcases le_or_gt (A / Submission.BoseGases.chiSupAbs) 1 with h | h
    · rw [max_eq_left h]
      rw [div_le_one hsup_pos] at h
      simpa using h
    · rw [max_eq_right (le_of_lt h), div_mul_cancel₀ _ (ne_of_gt hsup_pos)]
  intro ℓ d hℓ hd u
  have hℓd : 0 < ℓ * d := mul_pos hℓ hd
  have hli : 0 ≤ ℓ⁻¹ + (ℓ * d)⁻¹ := add_nonneg (le_of_lt (inv_pos.mpr hℓ))
    (le_of_lt (inv_pos.mpr hℓd))
  -- the Lipschitz constant of `chiSmallB M ℓ d u`
  have hfd : ∀ x : E3, ‖fderiv ℝ (Submission.BoseGases.chiSmallB M ℓ d u) x‖
      ≤ A * (ℓ⁻¹ + (ℓ * d)⁻¹) := by
    intro x
    refine norm_fderiv_le_of_lip' ℝ (by positivity) ?_
    filter_upwards with y
    have h := hA ℓ d hℓ hd u x y
    simpa [Real.norm_eq_abs] using h
  have hscale : ℓ⁻¹ + (ℓ * d)⁻¹ = 1 / ℓ + 1 / (ℓ * d) := by
    rw [one_div, one_div]
  have hli : 0 ≤ (1 : ℝ) / ℓ + 1 / (ℓ * d) :=
    le_of_lt (add_pos (one_div_pos.mpr hℓ) (one_div_pos.mpr hℓd))
  constructor
  · intro x
    calc ‖fderiv ℝ (Submission.BoseGases.chiSmallB M ℓ d u) x‖
        ≤ A * (ℓ⁻¹ + (ℓ * d)⁻¹) := hfd x
      _ = A * (1 / ℓ + 1 / (ℓ * d)) := by rw [hscale]
      _ ≤ max 1 (A / Submission.BoseGases.chiSupAbs) * Submission.BoseGases.chiSupAbs
            * (1 / ℓ + 1 / (ℓ * d)) := mul_le_mul_of_nonneg_right hAle hli
  · have hInt := chiSmallB_integral_bound hM hℓ hd u (c := A * (ℓ⁻¹ + (ℓ * d)⁻¹))
      (by positivity) hfd
    have h3 : (0 : ℝ) ≤ (ℓ * d) ^ 3 := by positivity
    calc (∫ x : E3, ‖fderiv ℝ (Submission.BoseGases.chiSmallB M ℓ d u) x‖)
        ≤ (A * (ℓ⁻¹ + (ℓ * d)⁻¹)) * (ℓ * d) ^ 3 := hInt
      _ = A * (1 / ℓ + 1 / (ℓ * d)) * (ℓ * d) ^ 3 := by rw [hscale]
      _ ≤ max 1 (A / Submission.BoseGases.chiSupAbs) * Submission.BoseGases.chiSupAbs
            * (1 / ℓ + 1 / (ℓ * d)) * (ℓ * d) ^ 3 :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hAle hli) h3

end Work.BoseB1Cube
