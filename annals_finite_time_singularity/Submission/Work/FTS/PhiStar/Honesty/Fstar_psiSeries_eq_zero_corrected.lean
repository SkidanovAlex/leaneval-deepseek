/-
# The moment of `psiSeries`: the honest (corrected) statements

## Why a correction is needed

The requested lemma

```lean
theorem Fstar_psiSeries_eq_zero {α : ℝ} {F : ℝ → ℝ → ℝ} {z : ℝ}
    (hsum : Summable (fun m : ℕ => ((m : ℝ) + 1) * |acoeff α m F z|))
    (hF : ∀ t : ℝ, 0 < t → Fstar F t = 0) :
    Fstar (psiSeries α F) z = 0
```

is **false**: the source moment `Fstar F` is constrained only on `t > 0`, whereas

  `psiSeries α F z θ = ∑'_m (acoeff α m F z) · e_m(θ)`,   `acoeff α 0 F z = radGreen α 0 (cmode 0 F) z`,

and `radGreen α 0 c z` is an integral of `c = cmode 0 F` over `(z,∞)` — for `z < 0` this includes
`(z,0)`, where `cmode 0 F` is *not* touched by `hF`.  Since the `m ≥ 1` modes contribute nothing to
`Fstar` (they are orthogonal to `sin θ cos²θ = e_0 cos θ/3` in the weight `cos θ dθ`), the value of
`Fstar (psiSeries α F) z` is exactly

  `acoeff α 0 F z · 3 ∫_0^{π/2} sin²θ cos³θ dθ`,

so the conclusion holds **iff** the mode-`0` coefficient vanishes.

Explicit counterexample (see `../../PhiStar/Honesty/NOTES_Fstar_psiSeries_eq_zero.md`):
take `α = 1`, `ψ := 1_{(-1,-1/2)}`, `F(t,θ) := ψ(t)·e_0(θ)`, `z = -1`.  Then `cmode 0 F = ψ`,
`cmode m F ≡ 0` for `m ≥ 1`, `Fstar F ≡ 0` on `(0,∞)`, `acoeff α m F z = 0` for `m ≥ 1`, and

  `acoeff α 0 F (-1) = (1/5)·(31/160 - log 2) ≠ 0`,  so  `Fstar (psiSeries α F) (-1) ≠ 0`.

## What *is* true (this file)

Everything the chain needs is true once the mode-`0` coefficient is known to vanish — which is
exactly what `acoeff_zero_of_fstar` provides on the positive half-line:

* `Fstar_psiSeries_eq_zero_of_acoeff_zero` — the general form, **for every `z : ℝ`**:
  `acoeff α 0 F z = 0` together with the summability of `∑ (m+1)|acoeff α m F z|` forces the moment
  to vanish.  The proof is a dominated-convergence interchange of `tsum` and `∫_θ` (dominator
  `3(m+1)|a_m|`, using `eFam_sup_le`) followed by the orthogonality `eFam_orthogonal m 0`.
* `Fstar_psiSeries_eq_zero_of_pos` — the form matching the source hypothesis `hF` on `(0,∞)`,
  valid for `0 < z` (this is the only correction needed for the positive half-line).
* `Fstar_psiSeries_eq_zero_of_moment_all` — if the source moment vanishes on **all** of `ℝ`
  (e.g. the compactly supported sources of the stability route), the conclusion holds for every
  `z`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Submission.Work.FTS.PhiStar.Series.acoeff_zero_of_fstar
import Submission.Work.FTS.PhiStar.Gegenbauer.eFam_orthogonal
import Submission.Work.FTS.PhiStar.Series.eFam_sup_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology BigOperators
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.Honesty

set_option autoImplicit false

/-! ## Elementary facts about the angular weight `sinCos2` -/

/-- The Dirichlet eigenfunctions `eFam m` are continuous. -/
lemma continuous_eFam (m : ℕ) : Continuous (Work.FTS.PhiStar.Gegenbauer.eFam m) := by
  unfold Work.FTS.PhiStar.Gegenbauer.eFam
  exact Real.continuous_cos.mul
    ((Work.FTS.PhiStar.Gegenbauer.contDiff_gC (2 * m + 1)).continuous.comp
      Real.continuous_sin)

/-- `sinCos2 θ = sin θ cos²θ` is continuous. -/
lemma continuous_sinCos2 : Continuous Work.Elliptic.sinCos2 := by
  unfold Work.Elliptic.sinCos2
  exact Real.continuous_sin.mul (Real.continuous_cos.pow 2)

/-- `sinCos2 θ ≥ 0` on `Iθ = [0,π/2]`. -/
lemma sinCos2_nonneg_of_mem_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ Work.Elliptic.sinCos2 θ := by
  rw [Work.Spaces.Iθ] at hθ
  obtain ⟨h0, h1⟩ := hθ
  unfold Work.Elliptic.sinCos2
  exact mul_nonneg (Real.sin_nonneg_of_mem_Icc ⟨h0, by linarith [h1, Real.pi_pos]⟩)
    (sq_nonneg _)

/-- `sinCos2 θ ≤ 1` on `Iθ = [0,π/2]`. -/
lemma sinCos2_le_one_of_mem_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Elliptic.sinCos2 θ ≤ 1 := by
  rw [Work.Spaces.Iθ] at hθ
  obtain ⟨h0, h1⟩ := hθ
  have hcos2 : Real.cos θ ^ 2 ≤ 1 := by
    have := Real.cos_sq_le_one θ
    linarith
  unfold Work.Elliptic.sinCos2
  simpa using mul_le_mul (Real.sin_le_one θ) hcos2 (sq_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)

/-- **Every `m ≠ 0` mode is orthogonal to `sinCos2` in the moment pairing**:
`∫_θ e_m(θ) sin θ cos²θ dθ = 0`.  This is `eFam_orthogonal m 0` together with
`e_0 cos θ = 3 sin θ cos²θ`. -/
lemma integral_eFam_mul_sinCos2_eq_zero {n : ℕ} (hn : n ≠ 0) :
    (∫ θ in Work.Spaces.Iθ,
      Work.FTS.PhiStar.Gegenbauer.eFam n θ * Work.Elliptic.sinCos2 θ) = 0 := by
  have hpt : Work.Elliptic.sinCos2 = fun θ =>
      (1 / 3) * (Work.FTS.PhiStar.Gegenbauer.eFam 0 θ * Real.cos θ) := by
    funext θ
    rw [Work.FTS.PhiStar.Series.eFam_zero_apply]
    unfold Work.Elliptic.sinCos2
    ring
  calc (∫ θ in Work.Spaces.Iθ,
        Work.FTS.PhiStar.Gegenbauer.eFam n θ * Work.Elliptic.sinCos2 θ)
      = ∫ θ in Work.Spaces.Iθ, (1 / 3) * (Work.FTS.PhiStar.Gegenbauer.eFam n θ
          * Work.FTS.PhiStar.Gegenbauer.eFam 0 θ * Real.cos θ) := by
        apply MeasureTheory.setIntegral_congr_fun measurableSet_Icc
        intro θ _
        rw [hpt]
        ring
    _ = (1 / 3) * ∫ θ in Work.Spaces.Iθ, Work.FTS.PhiStar.Gegenbauer.eFam n θ
          * Work.FTS.PhiStar.Gegenbauer.eFam 0 θ * Real.cos θ := by
        rw [MeasureTheory.integral_const_mul]
    _ = 0 := by
        have hsub : (∫ θ in Work.Spaces.Iθ, Work.FTS.PhiStar.Gegenbauer.eFam n θ
              * Work.FTS.PhiStar.Gegenbauer.eFam 0 θ * Real.cos θ)
            = ∫ θ in (0 : ℝ)..(Real.pi / 2), Work.FTS.PhiStar.Gegenbauer.eFam n θ
              * Work.FTS.PhiStar.Gegenbauer.eFam 0 θ * Real.cos θ := by
          rw [Work.Spaces.Iθ, MeasureTheory.integral_Icc_eq_integral_Ioc,
            intervalIntegral.integral_of_le (by linarith [Real.pi_pos])]
        rw [hsub, Work.FTS.PhiStar.Gegenbauer.eFam_orthogonal n 0 hn, mul_zero]

/-! ## The moment of `psiSeries` as a mode sum -/

/-- **The `tsum`/`∫_θ` interchange**: the moment of the mode series is the sum of the moments of its
modes.  `Fstar` is the `θ`-integral against `sinCos2` and `psiSeries` is the mode series, so
dominated convergence (dominator `3(m+1)|acoeff α m F z|`, finite measure `Iθ`, uniform bound
`|eFam m θ| ≤ 3(m+1)` from `eFam_sup_le`) exchanges the sum and the integral. -/
theorem Fstar_psiSeries_eq_tsum {α : ℝ} {F : ℝ → ℝ → ℝ} {z : ℝ}
    (hsum : Summable (fun m : ℕ => ((m : ℝ) + 1) * |Work.FTS.PhiStar.Series.acoeff α m F z|)) :
    Work.Elliptic.Fstar (Work.FTS.PhiStar.Series.psiSeries α F) z
      = ∑' m : ℕ, Work.FTS.PhiStar.Series.acoeff α m F z *
          ∫ θ in Work.Spaces.Iθ,
            Work.FTS.PhiStar.Gegenbauer.eFam m θ * Work.Elliptic.sinCos2 θ := by
  have hfin : IsFiniteMeasure (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    rw [MeasureTheory.isFiniteMeasure_restrict, Work.Spaces.Iθ, Real.volume_Icc]
    exact ENNReal.ofReal_ne_top
  have hsum3 : Summable (fun n : ℕ =>
      3 * ((n : ℝ) + 1) * |Work.FTS.PhiStar.Series.acoeff α n F z|) := by
    have h := hsum.mul_left 3
    refine h.congr fun n => ?_
    ring
  have hmeas : ∀ n : ℕ, AEStronglyMeasurable (fun θ : ℝ =>
      Work.FTS.PhiStar.Series.acoeff α n F z
        * (Work.FTS.PhiStar.Gegenbauer.eFam n θ * Work.Elliptic.sinCos2 θ))
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    fun n => (continuous_const.mul ((continuous_eFam n).mul continuous_sinCos2))
      |>.aestronglyMeasurable
  have hbound : ∀ n : ℕ, ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      ‖Work.FTS.PhiStar.Series.acoeff α n F z
        * (Work.FTS.PhiStar.Gegenbauer.eFam n θ * Work.Elliptic.sinCos2 θ)‖
      ≤ 3 * ((n : ℝ) + 1) * |Work.FTS.PhiStar.Series.acoeff α n F z| := by
    intro n
    rw [MeasureTheory.ae_restrict_iff' (by rw [Work.Spaces.Iθ]; exact measurableSet_Icc)]
    refine Filter.Eventually.of_forall fun θ hθ => ?_
    have hb := sinCos2_le_one_of_mem_Iθ hθ
    have hb0 := sinCos2_nonneg_of_mem_Iθ hθ
    have he := Work.FTS.PhiStar.Series.abs_eFam_le_sqrt_Npsi n hθ
    have he3 := Work.FTS.PhiStar.Series.sqrt_Npsi_le_three n
    rw [Real.norm_eq_abs, abs_mul, abs_mul]
    have h1 : |Work.FTS.PhiStar.Series.acoeff α n F z|
          * (|Work.FTS.PhiStar.Gegenbauer.eFam n θ| * |Work.Elliptic.sinCos2 θ|)
        ≤ |Work.FTS.PhiStar.Series.acoeff α n F z| * ((3 * ((n : ℝ) + 1)) * 1) := by
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      apply mul_le_mul
      · exact le_trans he he3
      · rw [abs_of_nonneg hb0]; exact hb
      · norm_num
      · positivity
    exact le_trans h1 (le_of_eq (by ring))
  have hbs : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      Summable (fun n : ℕ => 3 * ((n : ℝ) + 1)
        * |Work.FTS.PhiStar.Series.acoeff α n F z|) :=
    Filter.Eventually.of_forall fun _ => hsum3
  have hint : Integrable (fun _ : ℝ => ∑' n : ℕ,
      3 * ((n : ℝ) + 1) * |Work.FTS.PhiStar.Series.acoeff α n F z|)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    MeasureTheory.integrable_const_iff.mpr (Or.inr hfin)
  have hlim : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      HasSum (fun n : ℕ => Work.FTS.PhiStar.Series.acoeff α n F z
        * (Work.FTS.PhiStar.Gegenbauer.eFam n θ * Work.Elliptic.sinCos2 θ))
        (Work.FTS.PhiStar.Series.psiSeries α F z θ * Work.Elliptic.sinCos2 θ) := by
    rw [MeasureTheory.ae_restrict_iff' (by rw [Work.Spaces.Iθ]; exact measurableSet_Icc)]
    refine Filter.Eventually.of_forall fun θ hθ => ?_
    have hb : ∀ m : ℕ, ‖Work.FTS.PhiStar.Series.acoeff α m F z
          * Work.FTS.PhiStar.Gegenbauer.eFam m θ‖
        ≤ 3 * ((m : ℝ) + 1) * |Work.FTS.PhiStar.Series.acoeff α m F z| := by
      intro m
      have he := Work.FTS.PhiStar.Series.abs_eFam_le_sqrt_Npsi m hθ
      have he3 := Work.FTS.PhiStar.Series.sqrt_Npsi_le_three m
      rw [Real.norm_eq_abs, abs_mul]
      calc |Work.FTS.PhiStar.Series.acoeff α m F z|
            * |Work.FTS.PhiStar.Gegenbauer.eFam m θ|
          ≤ |Work.FTS.PhiStar.Series.acoeff α m F z| * (3 * ((m : ℝ) + 1)) :=
            mul_le_mul_of_nonneg_left (le_trans he he3) (abs_nonneg _)
        _ = 3 * ((m : ℝ) + 1) * |Work.FTS.PhiStar.Series.acoeff α m F z| := by ring
    have hsumm : Summable (fun m : ℕ => Work.FTS.PhiStar.Series.acoeff α m F z
        * Work.FTS.PhiStar.Gegenbauer.eFam m θ) :=
      Summable.of_norm_bounded hsum3 hb
    have hh := hsumm.hasSum.mul_right (Work.Elliptic.sinCos2 θ)
    rw [show (fun m : ℕ => (Work.FTS.PhiStar.Series.acoeff α m F z
          * Work.FTS.PhiStar.Gegenbauer.eFam m θ) * Work.Elliptic.sinCos2 θ)
        = (fun m : ℕ => Work.FTS.PhiStar.Series.acoeff α m F z
          * (Work.FTS.PhiStar.Gegenbauer.eFam m θ * Work.Elliptic.sinCos2 θ))
        from funext fun m => by ring] at hh
    simpa [Work.FTS.PhiStar.Series.psiSeries] using hh
  have key := MeasureTheory.hasSum_integral_of_dominated_convergence
    (μ := MeasureTheory.volume.restrict Work.Spaces.Iθ)
    (F := fun n : ℕ => fun θ : ℝ => Work.FTS.PhiStar.Series.acoeff α n F z
        * (Work.FTS.PhiStar.Gegenbauer.eFam n θ * Work.Elliptic.sinCos2 θ))
    (f := fun θ : ℝ => Work.FTS.PhiStar.Series.psiSeries α F z θ
        * Work.Elliptic.sinCos2 θ)
    (bound := fun n : ℕ => fun _ : ℝ => 3 * ((n : ℝ) + 1)
        * |Work.FTS.PhiStar.Series.acoeff α n F z|)
    hmeas hbound hbs hint hlim
  have hterm : ∀ n : ℕ, (∫ θ, Work.FTS.PhiStar.Series.acoeff α n F z
        * (Work.FTS.PhiStar.Gegenbauer.eFam n θ * Work.Elliptic.sinCos2 θ)
          ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
      = Work.FTS.PhiStar.Series.acoeff α n F z *
        ∫ θ in Work.Spaces.Iθ,
          Work.FTS.PhiStar.Gegenbauer.eFam n θ * Work.Elliptic.sinCos2 θ :=
    fun n => by rw [MeasureTheory.integral_const_mul]
  have hkey : HasSum (fun n : ℕ => Work.FTS.PhiStar.Series.acoeff α n F z *
        ∫ θ in Work.Spaces.Iθ,
          Work.FTS.PhiStar.Gegenbauer.eFam n θ * Work.Elliptic.sinCos2 θ)
      (Work.Elliptic.Fstar (Work.FTS.PhiStar.Series.psiSeries α F) z) := by
    have hval : (∫ θ, Work.FTS.PhiStar.Series.psiSeries α F z θ * Work.Elliptic.sinCos2 θ
        ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
        = Work.Elliptic.Fstar (Work.FTS.PhiStar.Series.psiSeries α F) z := rfl
    rw [← hval]
    rw [show (fun n : ℕ => ∫ θ, Work.FTS.PhiStar.Series.acoeff α n F z
          * (Work.FTS.PhiStar.Gegenbauer.eFam n θ * Work.Elliptic.sinCos2 θ)
          ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
        = (fun n : ℕ => Work.FTS.PhiStar.Series.acoeff α n F z *
          ∫ θ in Work.Spaces.Iθ,
            Work.FTS.PhiStar.Gegenbauer.eFam n θ * Work.Elliptic.sinCos2 θ)
        from funext hterm] at key
    exact key
  exact hkey.tsum_eq.symm

/-- **`Fstar (psiSeries α F) z = 0` for every `z`, as soon as the mode-`0` radial coefficient
`acoeff α 0 F z` vanishes** (and the mode coefficients are summable in the weighted `ℓ¹` sense).

Immediate from `Fstar_psiSeries_eq_tsum`: every summand is `0`, since for `m = 0` the coefficient
vanishes by hypothesis (`cmode 0 F` and hence `acoeff α 0 F z` encode the source moment, cf.
`eFam_zero_moment`, `acoeff_zero_of_fstar`) and for `m ≥ 1` the mode is orthogonal to `sinCos2`
(`integral_eFam_mul_sinCos2_eq_zero`, i.e. `eFam_orthogonal`). -/
theorem Fstar_psiSeries_eq_zero_of_acoeff_zero {α : ℝ} {F : ℝ → ℝ → ℝ} {z : ℝ}
    (hsum : Summable (fun m : ℕ => ((m : ℝ) + 1) * |Work.FTS.PhiStar.Series.acoeff α m F z|))
    (h0 : Work.FTS.PhiStar.Series.acoeff α 0 F z = 0) :
    Work.Elliptic.Fstar (Work.FTS.PhiStar.Series.psiSeries α F) z = 0 := by
  rw [Fstar_psiSeries_eq_tsum hsum]
  have hzero : (fun n : ℕ => Work.FTS.PhiStar.Series.acoeff α n F z *
        ∫ θ in Work.Spaces.Iθ,
          Work.FTS.PhiStar.Gegenbauer.eFam n θ * Work.Elliptic.sinCos2 θ)
      = fun _ => 0 := by
    funext n
    rcases eq_or_ne n 0 with h | h
    · subst h
      rw [h0, zero_mul]
    · rw [integral_eFam_mul_sinCos2_eq_zero h, mul_zero]
  rw [hzero, tsum_zero]

/-! ## The two specialisations matching the source hypothesis -/

/-- **The corrected form of the requested lemma**: with the source moment vanishing on the
positive half-line (`hF`), and `z > 0`, the moment of `psiSeries α F` at `z` vanishes.  This is the
only correction the requested statement needs (`0 < z`). -/
theorem Fstar_psiSeries_eq_zero_of_pos {α : ℝ} {F : ℝ → ℝ → ℝ} {z : ℝ} (hz : 0 < z)
    (hsum : Summable (fun m : ℕ => ((m : ℝ) + 1) * |Work.FTS.PhiStar.Series.acoeff α m F z|))
    (hF : ∀ t : ℝ, 0 < t → Work.Elliptic.Fstar F t = 0) :
    Work.Elliptic.Fstar (Work.FTS.PhiStar.Series.psiSeries α F) z = 0 :=
  Fstar_psiSeries_eq_zero_of_acoeff_zero hsum
    (Work.FTS.PhiStar.Series.acoeff_zero_of_fstar α F hF z hz)

/-- **If the source moment vanishes on all of `ℝ`** (for instance a source supported in `z > 0`),
then the moment of `psiSeries α F` vanishes at *every* `z : ℝ`. -/
theorem Fstar_psiSeries_eq_zero_of_moment_all {α : ℝ} {F : ℝ → ℝ → ℝ} {z : ℝ}
    (hsum : Summable (fun m : ℕ => ((m : ℝ) + 1) * |Work.FTS.PhiStar.Series.acoeff α m F z|))
    (hF : ∀ t : ℝ, Work.Elliptic.Fstar F t = 0) :
    Work.Elliptic.Fstar (Work.FTS.PhiStar.Series.psiSeries α F) z = 0 := by
  refine Fstar_psiSeries_eq_zero_of_acoeff_zero hsum ?_
  have hcm : (fun t => Work.FTS.PhiStar.Series.cmode 0 F t) = fun _ => 0 := by
    funext t
    exact Work.FTS.PhiStar.Series.eFam_zero_moment F (hF t)
  rw [Work.FTS.PhiStar.Series.acoeff, hcm]
  exact Work.FTS.PhiStar.Series.radGreen_zero α 0 z

/-- **The all-`z` form for sources vanishing on the closed left half-plane in `z`** (in particular
for every source with `support ⊆ (0,∞) × ℝ`, the compactly supported sources of the stability
route).  The source moment hypothesis is then automatically `equiv` to its restriction to
`z > 0`, and the conclusion holds for every `z : ℝ`. -/
theorem Fstar_psiSeries_eq_zero_of_left_support {α : ℝ} {F : ℝ → ℝ → ℝ} {z : ℝ}
    (hsum : Summable (fun m : ℕ => ((m : ℝ) + 1) * |Work.FTS.PhiStar.Series.acoeff α m F z|))
    (hF : ∀ t : ℝ, 0 < t → Work.Elliptic.Fstar F t = 0)
    (hsupp : ∀ t : ℝ, t ≤ 0 → ∀ θ : ℝ, F t θ = 0) :
    Work.Elliptic.Fstar (Work.FTS.PhiStar.Series.psiSeries α F) z = 0 := by
  refine Fstar_psiSeries_eq_zero_of_moment_all hsum fun t => ?_
  rcases lt_trichotomy 0 t with h | h | h
  · exact hF t h
  · subst h
    rw [Work.Elliptic.Fstar]
    trans ∫ θ in Work.Spaces.Iθ, (0 : ℝ)
    · apply MeasureTheory.setIntegral_congr_fun measurableSet_Icc
      intro θ _
      beta_reduce
      rw [hsupp 0 le_rfl θ, zero_mul]
    · simp
  · rw [Work.Elliptic.Fstar]
    trans ∫ θ in Work.Spaces.Iθ, (0 : ℝ)
    · apply MeasureTheory.setIntegral_congr_fun measurableSet_Icc
      intro θ _
      beta_reduce
      rw [hsupp t (le_of_lt h) θ, zero_mul]
    · simp

end Work.FTS.PhiStar.Honesty
