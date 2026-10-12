import ChallengeDeps
import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm
import Submission.ProfileConvex
import Submission.ProfileFormula
import Submission.ScatProfileReg
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Regularity package for the canonical scattering profile (assigned sub-lemma)

Prove the single theorem `Submission.BoseGases.canonicalProfile_reg` below
(it is supplied with a placeholder proof at present).  This is a *standalone, self-contained* task: everything
needed is in the imported modules (read `Submission/ProfileFormula.lean`,
`Submission/ScatProfileReg.lean`, `Submission/ScatProfileODE.lean`,
`Submission/ScatProfileGlue.lean` for idiom and facts) plus Mathlib.

## Statement, unpacked

Let `U := canonicalProfile v w R : ℝ → ℝ`.  For a radial weak scattering
solution `w` of a radial `v` with `tsupport v ⊆ ball 0 R` (`R > 0`):

  (1) `U 0 = 0` (definitional: the `Ioc 0 0` integral is over an empty set);
  (2) `ContinuousOn U (Icc 0 R)`;
  (3) `∀ r ∈ (0,R), DifferentiableAt ℝ U r`;
  (4) for `0 < a ≤ b ≤ R`: `AbsolutelyContinuousOnInterval (deriv U) a b`;
  (5) for `0 < a ≤ b ≤ R`: `∀ᵐ x, x ∈ Set.uIcc a b → HasDerivAt (deriv U)
      ((radialProfile v x / 2) * (U x - x)) x`.

## Known facts (from the imports; study ProfileFormula's proofs for idiom)

Let `g : ℝ³ → ℝ := fun y => v y * (1 - w y)`, `gprof : ℝ → ℝ := radialProfile g`,
`f1 s := s * gprof s`, `f2 s := s ^ 2 * gprof s`.  Then by definition

    U r = (1/2) * ((∫ s in Set.Ioc (0:ℝ) r, f2 s) + r * (∫ s in Set.Ioi r, f1 s)).

Facts you may re-derive locally (copy the standard blocks from ProfileFormula):

  * `hg : MeasureTheory.Integrable g` from `scatG_integrable`;
  * `hgrad : IsRadial g`;
  * `gprof s = 0` for `s ≥ R` (support);
  * `Integrable (fun s => s^2 * |gprof s|) (volume.restrict (Set.Ioi 0))`
    from `shell_profile_integrable`;
  * `AEStronglyMeasurable gprof (volume.restrict (Set.Ioi 0))`
    from `shell_gprof_ae_strong`;
  * for any `0 < y`: `IntegrableOn f1 (Set.Ioc y R) volume` and
    `IntegrableOn f2 (Set.Ioc 0 R) volume` (the second from the first:
    `|s^2 gprof| = s^2 |gprof|`).

## Route

(1) is trivial.

For (2) and (3): show U is *continuous* on `(0,R)` and *differentiable* at
each `r0 ∈ (0,R)`.  RECOMMENDED: prove HasDerivAt at every `r0 ∈ (0,R)` with
the derivative `(1/2)·∫ s in Ioi r0, f1 s`, via the one-sided slope limits
(`hasDerivAt_iff_tendsto_slope_left_right`).  For `y > r0` (both in `(0,R)`,
use a small right-neighbourhood) show the set-integral identity

    U y - U r0 = (1/2)·((y - r0)·T0 + ∫ s in Set.Ioc r0 y, (f2 s - y·f1 s))

with `T0 := ∫ s in Set.Ioi r0, f1 s` — prove it from the definition of U by
the set-integral splits
`Set.Ioc 0 y = Set.Ioc 0 r0 ∪ Set.Ioc r0 y` and
`Set.Ioi r0 = Set.Ioi y ∪ Set.Ioc r0 y` (use `integral_union_eq_left_of_forall`
as in ProfileFormula's `hBformula`/`hAdiff`, or `setIntegral_sdiff`).  For
`y < r0` get the mirror identity.  Then the slope error term is bounded:

    |(U y - U r0)/(y - r0) - (1/2)·T0| ≤ (1/2)·∫ s in Set.Ioc (min r0 y) (max r0 y), s·|gprof s|

and the right-hand side tends to 0 as `y → r0` from the relevant side
(dominated convergence, following ProfileFormula's `hJ` pattern, or
`continuousOn_primitive_interval` from
`Mathlib.MeasureTheory.Integral.DominatedConvergence`).  Conclude
`HasDerivAt U ((1/2)·T0) r0`; this gives (3) and continuity on `(0,R)`.
At `R`: `ContinuousAt U R` from
`ProfileFormula.canonicalProfile_hasDerivAt_R` (`HasDerivAt` implies
`ContinuousAt`).  At `0`: `U 0 = 0` and
`ProfileFormula.canonicalProfile_tendsto_zero` give the right-limit;
assemble `ContinuousOn U (Icc 0 R)` with `ContinuousWithinAt` at 0
(use that for `R > 0` the within-filter `𝓝[Icc 0 R] 0` and `𝓝[Ioi 0] 0`
differ only by the point `0`, so `continuousWithinAt` at 0 follows from the
tendsto at `0⁺` together with `U 0 = 0`; mathlib: `nhdsWithin_insert`,
`nhdsWithin_Icc_eq_nhdsGE`, `Filter.Tendsto` lemmas).

For (4) and (5): since `deriv U r = (1/2)·∫ s in Set.Ioi r, f1 s` for
`r ∈ (0,R)` (from HasDerivAt.deriv), and `f1 s = 0` for `s ≥ R`, for
`r ∈ (a,b) ⊆ (0,R)` write (set-integral splits, then interval integrals via
`intervalIntegral.integral_of_le`):
`∫ s in Ioi r, f1 s = ∫ t in a..b, ... `-style decompositions so that

    deriv U r = C - (1/2)·(∫ t in a..r, f1 t)   (r ∈ (a,b))

with `C` constant.  Then (4): `AbsolutelyContinuousOnInterval (deriv U) a b`
follows from
`IntervalIntegrable.absolutelyContinuousOnInterval_intervalIntegral`
(applied to `f1`, `c := a`) together with an AC-congruence lemma: if
`g x = h x` for all `x ∈ uIcc a b` and `h` is AC on `uIcc a b`, then `g` is
AC (the AC property only samples values at points of `uIcc a b`; prove by
`rw [absolutelyContinuousOnInterval_iff]` or a direct filter argument).
Do NOT forget the endpoint handling: extend the equality
`deriv U r = C - (1/2)∫t in a..r f1` from the open interval `(a,b)` to all of
`uIcc a b` using continuity at the endpoints (deriv U is continuous on
`(0,R)`; also `deriv U a = (1/2)∫_{Ioi a} f1` etc.).  Easier: prove AC for
each `[a,b]` with `0 < a ≤ b < R` first and extend to `b = R` by using
`AbsolutelyContinuousOnInterval.mono` (AC on `[a,b']` for `b' < R` arbitrarily
close to `R` does NOT give AC on `[a,R]` — instead handle `[a,R]` directly:
on `(a,R)` use the primitive representation, and at `R` use `deriv U R = 0`
from `canonicalProfile_hasDerivAt_R`, showing the primitive has the same
continuous extension to `R`).

(5): on `(a,∞)` the function `U` is a.e. equal to the C¹ representative of
`ScatProfileReg.scat_profile_reg_Ioi` (both are a.e. equal to
`r·radialProfile w r` — `ProfileFormula.canonicalProfile_eq_profile` and
reg's first conjunct), so they agree everywhere on `(a,∞)` (both continuous
there; prove a small lemma: two continuous functions equal a.e. on an open
interval are equal everywhere).  Then use reg's third conjunct
(`∀ᵐ r, a < r → HasDerivAt (deriv U₀) (scatH v w r) r`) together with the
pointwise identities
`scatH v w r = -(1/2)·r·gprof r` (`ScatProfileGlue.scatH_eq` plus
`ScatProfileGlue.radialProfile_mul_one_sub`, pointwise) and
`(radialProfile v r / 2)·(U r - r) = -(1/2)·(r·gprof r)` a.e.
(reproduce `canonicalProfile_ae_source_eq` below or prove it yourself) to
obtain, on every `uIcc a b ⊆ (0,R)`, the a.e.-statement of (5).  ALTERNATIVE
(avoiding the transfer): derive (5) directly from the primitive formula of
`deriv U` using `IntervalIntegrable.ae_hasDerivAt_integral`
(`Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm`):
`∀ᵐ x ∈ uIcc a b, HasDerivAt (fun t => ∫ in a..t, f1) (f1 x) x`, hence
`HasDerivAt (deriv U) (-(1/2)·(x·gprof x)) x` a.e. on `uIcc a b`; rewrite
`-(1/2)·(x·gprof x) = (radialProfile v x/2)·(U x - x)` a.e. on `(0,R)`
(needs `ProfileFormula.canonicalProfile_eq_profile`).
This direct route also gives (4).

Good luck; the key model files are ProfileFormula.lean (set-integral idiom,
dominated convergence) and the module doc of T3Bounds.
-/

noncomputable section

open _root_.BoseGases
set_option autoImplicit false

namespace Submission.BoseGases

open Filter Metric MeasureTheory Laplacian Set
open scoped ContDiff Topology Real Interval

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- The a.e. source identity used to rewrite the a.e. second derivative of the
canonical profile into Carathéodory form: for a.e. `r ∈ (0,R)`,
`(radialProfile v / 2)·(U − id) = −(1/2)·r·gprof r` where
`gprof := radialProfile (v·(1−w))`. -/
lemma canonicalProfile_ae_source_eq {v w : ℝ³ → ℝ} {R : ℝ} (hR : 0 < R)
    (hvrad : IsRadial v) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (hrad : IsRadial w) (hw : IsScatteringSolution w v) :
    ∀ᵐ r : ℝ, 0 < r → r < R →
      (radialProfile v r / 2) * (canonicalProfile v w R r - r) =
        -((1 / 2) * (r * radialProfile (fun x : ℝ³ => v x * (1 - w x)) r)) := by
  filter_upwards [canonicalProfile_eq_profile (v := v) (w := w) (R := R) hR hvrad hv_supp hrad hw]
    with r hr hrpos hrR
  have hU : canonicalProfile v w R r = r * radialProfile w r := hr hrpos
  have hgprof : radialProfile (fun x : ℝ³ => v x * (1 - w x)) r =
      radialProfile v r * (1 - radialProfile w r) := by
    rw [← radialProfile_mul_one_sub v w r]
  rw [hU, hgprof]
  ring

/-- **Interior derivative.**  For `0 < r0 < R` the canonical profile is
differentiable at `r0` with derivative `(1/2)·∫_{s>r0} s·gprof(s)`. -/
theorem canonicalProfile_hasDerivAt_Ioo {v w : ℝ³ → ℝ} {R r0 : ℝ} (hR : 0 < R)
    (hvrad : IsRadial v) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (hrad : IsRadial w) (hw : IsScatteringSolution w v) (hr0 : 0 < r0) (hr0R : r0 < R) :
    HasDerivAt (canonicalProfile v w R)
      ((1 / 2) * (∫ s in Set.Ioi r0, s * radialProfile (fun x : ℝ³ => v x * (1 - w x)) s)) r0 := by
  let g : ℝ³ → ℝ := fun y => v y * (1 - w y)
  let gprof : ℝ → ℝ := radialProfile g
  let u : ℝ → ℝ := canonicalProfile v w R
  let μ0 : Measure ℝ := volume.restrict (Set.Ioi (0 : ℝ))
  have hg : MeasureTheory.Integrable g := by
    simpa [g] using (scatG_integrable (v := v) (w := w) hv_supp hw)
  have hgrad : IsRadial g := by
    intro x y hxy
    dsimp [g]
    rw [hvrad x y hxy, hrad x y hxy]
  have hgsupp : ∀ y : ℝ³, R ≤ ‖y‖ → g y = 0 := by
    intro y hy
    have hv0 : v y = 0 := v_eq_zero_of_norm_ge hv_supp hy
    dsimp [g]
    simp [hv0]
  have hgprof_geR : ∀ s : ℝ, R ≤ s → gprof s = 0 := by
    intro s hs
    dsimp [gprof]
    have hnorm : R ≤ ‖s • radU0‖ := by
      rw [norm_smul_radU0]
      rw [abs_of_nonneg (le_trans hR.le hs)]
      exact hs
    exact hgsupp (s • radU0) hnorm
  have hcan (r : ℝ) : u r =
      (1 / 2 : ℝ) * ((∫ s in Set.Ioc (0 : ℝ) r, s ^ 2 * gprof s) +
        r * (∫ s in Set.Ioi r, s * gprof s)) := by
    dsimp [u, canonicalProfile, gprof, g]
  have hprof0 : Integrable (fun s : ℝ => s ^ 2 * |gprof s|) μ0 := by
    dsimp [μ0]
    exact (shell_profile_integrable (g := g) hg hgrad)
  have hgprofAE0 : AEStronglyMeasurable gprof μ0 := by
    simpa [gprof, μ0] using shell_gprof_ae_strong (g := g) hg hgrad
  have hf2AE0 : AEStronglyMeasurable (fun s : ℝ => s ^ 2 * gprof s) μ0 := by
    have hsq : AEStronglyMeasurable (fun s : ℝ => s ^ 2) μ0 :=
      (by fun_prop : Measurable (fun s : ℝ => s ^ 2)).aestronglyMeasurable
    exact hsq.mul hgprofAE0
  let f2 : ℝ → ℝ := fun s => s ^ 2 * gprof s
  let f1 : ℝ → ℝ := fun s => s * gprof s
  have hf2_int_R : IntegrableOn f2 (Set.Ioc (0 : ℝ) R) volume := by
    change Integrable (fun s : ℝ => s ^ 2 * gprof s) (volume.restrict (Set.Ioc (0 : ℝ) R))
    constructor
    · exact (hf2AE0.mono_set (s := Set.Ioc (0 : ℝ) R) (t := Set.Ioi (0 : ℝ)) Set.Ioc_subset_Ioi_self)
    · have hb : HasFiniteIntegral (fun s : ℝ => s ^ 2 * |gprof s|)
          (volume.restrict (Set.Ioc (0 : ℝ) R)) := by
        exact hprof0.2.mono_measure (Measure.restrict_mono Set.Ioc_subset_Ioi_self le_rfl)
      refine hb.mono ?_
      filter_upwards [] with s
      simp [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg s)]
  have hBformula (t : ℝ) (htR : t ≤ R) :
      (∫ s in Set.Ioi t, s * gprof s) = (∫ s in Set.Ioc t R, s * gprof s) := by
    have hsplit : Set.Ioi t = Set.Ioc t R ∪ Set.Ioi R := by
      ext s
      constructor
      · intro hts
        by_cases hsR : s ≤ R
        · left
          exact ⟨hts, hsR⟩
        · right
          exact lt_of_not_ge hsR
      · intro hs
        rcases hs with h1 | h2
        · exact h1.1
        · exact lt_of_le_of_lt htR h2
    calc
      (∫ s in Set.Ioi t, s * gprof s)
          = ∫ s in Set.Ioc t R ∪ Set.Ioi R, s * gprof s := by rw [hsplit]
      _ = ∫ s in Set.Ioc t R, s * gprof s := by
          refine integral_union_eq_left_of_forall (s := Set.Ioc t R) (t := Set.Ioi R)
            (f := fun s : ℝ => s * gprof s) (μ := (volume : Measure ℝ))
            (measurableSet_Ioi) ?_
          intro x hx
          have hg0 : gprof x = 0 := hgprof_geR x (le_of_lt hx)
          simp [hg0]
  have hf1_int_D (y : ℝ) (hy0 : 0 < y) : IntegrableOn f1 (Set.Ioc y R) volume := by
    have hy0le : 0 ≤ y := hy0.le
    have hyIoi : Set.Ioc y R ⊆ Set.Ioi (0 : ℝ) := by
      intro s hs
      exact lt_of_le_of_lt hy0le hs.1
    change Integrable (fun s : ℝ => s * gprof s) (volume.restrict (Set.Ioc y R))
    constructor
    · have hgAEy : AEStronglyMeasurable gprof (volume.restrict (Set.Ioc y R)) := by
        exact hgprofAE0.mono_set (s := Set.Ioc y R) (t := Set.Ioi (0 : ℝ)) hyIoi
      have hsAEy : AEStronglyMeasurable (fun s : ℝ => s) (volume.restrict (Set.Ioc y R)) :=
        (measurable_id : Measurable (fun s : ℝ => s)).aestronglyMeasurable
      exact hsAEy.mul hgAEy
    · have hb2' : HasFiniteIntegral (fun s : ℝ => (1 / y) * (s ^ 2 * |gprof s|))
          (volume.restrict (Set.Ioc y R)) := by
        have hb0 : HasFiniteIntegral (fun s : ℝ => s ^ 2 * |gprof s|)
            (volume.restrict (Set.Ioc y R)) := by
          exact hprof0.2.mono_measure (Measure.restrict_mono hyIoi le_rfl)
        exact hb0.const_mul (1 / y)
      refine hb2'.mono ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
      have hsy : y < s := hs.1
      have hspos : 0 < s := lt_trans hy0 hsy
      have hgpos : 0 ≤ |gprof s| := abs_nonneg (gprof s)
      have hsydiv : 1 ≤ s / y := by
        rw [one_le_div hy0]
        exact hsy.le
      have hle : s ≤ (1 / y) * s ^ 2 := by
        calc
          s = s * 1 := by ring
          _ ≤ s * (s / y) := by
            exact mul_le_mul_of_nonneg_left hsydiv (le_of_lt hspos)
          _ = (1 / y) * s ^ 2 := by ring
      calc
        |s * gprof s| = s * |gprof s| := by rw [abs_mul, abs_of_nonneg (le_of_lt hspos)]
        _ ≤ (1 / y) * s ^ 2 * |gprof s| := by
          exact mul_le_mul_of_nonneg_right hle hgpos
        _ = |(1 / y) * (s ^ 2 * |gprof s|)| := by
          rw [abs_of_nonneg (mul_nonneg (one_div_nonneg.mpr hy0.le)
            (mul_nonneg (sq_nonneg s) (abs_nonneg (gprof s))))]
          ring
  let S0 : ℝ := ∫ s in Set.Ioc r0 R, s * gprof s
  have hS0 : (∫ s in Set.Ioi r0, s * gprof s) = S0 := hBformula r0 hr0R.le
  -- integrability of |gprof|-weighted quantities on closed intervals with positive lower end
  have hsg_int (c d : ℝ) (hc : 0 < c) (hcd : c ≤ d) (hdR : d ≤ R) :
      IntegrableOn (fun s : ℝ => s * |gprof s|) (Set.Icc c d) volume := by
    have hcIoi : Set.Icc c d ⊆ Set.Ioi (0 : ℝ) := by
      intro s hs
      exact lt_of_lt_of_le hc hs.1
    change Integrable (fun s : ℝ => s * |gprof s|) (volume.restrict (Set.Icc c d))
    constructor
    · have hgAE : AEStronglyMeasurable gprof (volume.restrict (Set.Icc c d)) := by
        exact hgprofAE0.mono_set (s := Set.Icc c d) (t := Set.Ioi (0 : ℝ)) hcIoi
      have hsAE : AEStronglyMeasurable (fun s : ℝ => s) (volume.restrict (Set.Icc c d)) :=
        (measurable_id : Measurable (fun s : ℝ => s)).aestronglyMeasurable
      exact hsAE.mul hgAE.norm
    · have hb : HasFiniteIntegral (fun s : ℝ => s ^ 2 * |gprof s|)
          (volume.restrict (Set.Icc c d)) := by
        exact hprof0.2.mono_measure (Measure.restrict_mono hcIoi le_rfl)
      refine hb.const_mul (1 / c) |>.mono' ?_
      filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
      have hsc : c ≤ s := hs.1
      have hspos : 0 < s := lt_of_lt_of_le hc hsc
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (le_of_lt hspos) (abs_nonneg (gprof s)))]
      have hle : s ≤ (1 / c) * s ^ 2 := by
        calc
          s = s * 1 := by ring
          _ ≤ s * (s / c) := by
            exact mul_le_mul_of_nonneg_left (by rw [one_le_div hc]; exact hsc) (le_of_lt hspos)
          _ = (1 / c) * s ^ 2 := by ring
      calc
        s * |gprof s| ≤ (1 / c) * s ^ 2 * |gprof s| := by
          exact mul_le_mul_of_nonneg_right hle (abs_nonneg (gprof s))
        _ = (1 / c) * (s ^ 2 * |gprof s|) := by ring
  have hE : ∃ ε : ℝ, 0 < ε ∧ r0 + ε < R := ⟨(R - r0) / 2, by linarith, by linarith⟩
  let mid : ℝ := r0 / 2
  have hmid0 : 0 < mid := by dsimp [mid]; positivity
  have hmidR : mid < r0 := by dsimp [mid]; linarith
  have hmidR' : mid ≤ R := le_of_lt (lt_trans hmidR hr0R)
  let h : ℝ → ℝ := fun s => s * |gprof s|
  -- right primitive continuity
  have hprimR : ContinuousOn (fun x : ℝ => ∫ s in Set.Ioc r0 x, h s) (Set.Icc r0 R) := by
    exact intervalIntegral.continuousOn_primitive (a := r0) (b := R) (f := h)
      (by simpa [h] using hsg_int r0 R hr0 hr0R.le le_rfl)
  have hJR0 : (∫ s in Set.Ioc r0 r0, h s) = 0 := by simp [h]
  have hJright : Tendsto (fun x : ℝ => ∫ s in Set.Ioc r0 x, h s) (𝓝[>] r0) (𝓝 0) := by
    have hcw : ContinuousWithinAt (fun x : ℝ => ∫ s in Set.Ioc r0 x, h s) (Set.Icc r0 R) r0 :=
      hprimR.continuousWithinAt (by exact ⟨le_rfl, hr0R.le⟩)
    have hlim : Tendsto (fun x : ℝ => ∫ s in Set.Ioc r0 x, h s) (𝓝[≥] r0) (𝓝 0) := by
      rw [← nhdsWithin_Icc_eq_nhdsGE hr0R]
      simpa [hJR0, ContinuousWithinAt] using hcw
    exact hlim.mono_left (nhdsWithin_mono r0 (by intro x hx; exact le_of_lt (by simpa using hx)))
  -- left primitive continuity
  have hprimL : ContinuousOn (fun x : ℝ => ∫ s in x..r0, h s) (Set.Icc mid r0) := by
    have hint : IntegrableOn h (Set.Icc mid r0) volume := by
      simpa [h] using hsg_int mid r0 hmid0 hmidR.le hr0R.le
    simpa [Set.uIcc_of_le hmidR.le] using
      intervalIntegral.continuousOn_primitive_interval_left (a := mid) (b := r0)
        (by simpa [Set.uIcc_of_le hmidR.le] using hint)
  have hKL0 : (∫ s in r0..r0, h s) = 0 := by simp [h]
  have hKleft : Tendsto (fun x : ℝ => ∫ s in x..r0, h s) (𝓝[<] r0) (𝓝 0) := by
    have hcw : ContinuousWithinAt (fun x : ℝ => ∫ s in x..r0, h s) (Set.Icc mid r0) r0 :=
      hprimL.continuousWithinAt (by exact ⟨hmidR.le, le_rfl⟩)
    have hlim : Tendsto (fun x : ℝ => ∫ s in x..r0, h s) (𝓝[≤] r0) (𝓝 0) := by
      rw [← nhdsWithin_Icc_eq_nhdsLE hmidR]
      simpa [hKL0, ContinuousWithinAt] using hcw
    exact hlim.mono_left (nhdsWithin_mono r0 (by intro x hx; exact le_of_lt (by simpa using hx)))
  -- generic set-integral splitting over Ioc with lower endpoint 0
  have hAsplit (p : ℝ → ℝ) (hp : IntegrableOn p (Set.Ioc (0 : ℝ) R) volume)
      (a b : ℝ) (ha0 : 0 ≤ a) (hab : a ≤ b) (hbR : b ≤ R) :
      (∫ s in Set.Ioc (0 : ℝ) b, p s) - (∫ s in Set.Ioc (0 : ℝ) a, p s) =
        (∫ s in Set.Ioc a b, p s) := by
    have hsub : Set.Ioc (0 : ℝ) a ⊆ Set.Ioc (0 : ℝ) b := by
      intro s hs
      exact ⟨hs.1, le_trans hs.2 hab⟩
    have hsdiff : Set.Ioc (0 : ℝ) b \ Set.Ioc (0 : ℝ) a = Set.Ioc a b := by
      ext s
      constructor
      · intro hs
        rcases hs with ⟨⟨hs0, hsb⟩, hsa⟩
        refine ⟨?_, hsb⟩
        by_contra hnot
        have hsle : s ≤ a := le_of_not_gt hnot
        exact hsa ⟨hs0, hsle⟩
      · intro hs
        have hs0' : 0 < s := lt_of_le_of_lt ha0 hs.1
        constructor
        · exact ⟨hs0', hs.2⟩
        · intro hmem
          exact (not_lt_of_ge hmem.2) hs.1
    have hpb : IntegrableOn p (Set.Ioc (0 : ℝ) b) volume :=
      hp.mono_set (s := Set.Ioc (0 : ℝ) b) (by intro s hs; exact ⟨hs.1, le_trans hs.2 hbR⟩)
    calc
      (∫ s in Set.Ioc (0 : ℝ) b, p s) - (∫ s in Set.Ioc (0 : ℝ) a, p s)
          = ∫ s in Set.Ioc (0 : ℝ) b \ Set.Ioc (0 : ℝ) a, p s := by
            exact (setIntegral_sdiff (t := Set.Ioc (0 : ℝ) a) (f := p)
              (μ := (volume : Measure ℝ)) (measurableSet_Ioc) hpb hsub).symm
      _ = ∫ s in Set.Ioc a b, p s := by rw [hsdiff]
  -- generic tail-splitting over Ioc with upper endpoint R
  have hTailSplit (p : ℝ → ℝ) (hp : IntegrableOn p (Set.Ioc r0 R) volume)
      (y : ℝ) (hr0y : r0 ≤ y) (hyR : y ≤ R) :
      (∫ s in Set.Ioc r0 R, p s) = (∫ s in Set.Ioc r0 y, p s) + (∫ s in Set.Ioc y R, p s) := by
    have hsub1 : Set.Ioc r0 y ⊆ Set.Ioc r0 R := by
      intro s hs
      exact ⟨hs.1, le_trans hs.2 hyR⟩
    have hsub2 : Set.Ioc y R ⊆ Set.Ioc r0 R := by
      intro s hs
      exact ⟨lt_of_le_of_lt hr0y hs.1, hs.2⟩
    have hunion : Set.Ioc r0 y ∪ Set.Ioc y R = Set.Ioc r0 R := by
      ext s
      constructor
      · intro hs
        rcases hs with h1 | h2
        · exact ⟨h1.1, le_trans h1.2 hyR⟩
        · exact ⟨lt_of_le_of_lt hr0y h2.1, h2.2⟩
      · intro hs
        rcases hs with ⟨hr0s, hsR⟩
        by_cases hsy : s ≤ y
        · left
          exact ⟨hr0s, hsy⟩
        · right
          exact ⟨lt_of_not_ge hsy, hsR⟩
    calc
      (∫ s in Set.Ioc r0 R, p s) = ∫ s in Set.Ioc r0 y ∪ Set.Ioc y R, p s := by rw [hunion]
      _ = (∫ s in Set.Ioc r0 y, p s) + (∫ s in Set.Ioc y R, p s) := by
        exact setIntegral_union (s := Set.Ioc r0 y) (t := Set.Ioc y R) (f := p)
          (μ := (volume : Measure ℝ))
          (disjoint_left.2 (fun s hs1 hs2 => (not_lt_of_ge hs1.2) hs2.1))
          measurableSet_Ioc (hp.mono_set hsub1) (hp.mono_set hsub2)
  -- integrability of head/tail integrands over the intermediate interval
  have hf2y_int (y : ℝ) (hr0y : r0 ≤ y) (hyR : y ≤ R) :
      IntegrableOn (fun s : ℝ => s ^ 2 * gprof s) (Set.Ioc r0 y) volume := by
    simpa [f2] using (hf2_int_R.mono_set (s := Set.Ioc r0 y) (by
      intro s hs
      exact ⟨lt_of_le_of_lt hr0.le hs.1, le_trans hs.2 hyR⟩))
  have hf1y_int (y : ℝ) (hr0y : r0 ≤ y) (hyR : y ≤ R) :
      IntegrableOn (fun s : ℝ => s * gprof s) (Set.Ioc r0 y) volume := by
    simpa [f1] using ((hf1_int_D r0 hr0).mono_set (s := Set.Ioc r0 y) (by
      intro s hs
      exact ⟨hs.1, le_trans hs.2 hyR⟩))
  -- right difference identity
  have hdiffR (y : ℝ) (hr0y : r0 ≤ y) (hyR : y ≤ R) :
      u y - u r0 = (1 / 2 : ℝ) * ((y - r0) * S0 +
        (∫ s in Set.Ioc r0 y, (s ^ 2 - y * s) * gprof s)) := by
    have hA : (∫ s in Set.Ioc (0 : ℝ) y, s ^ 2 * gprof s) -
          (∫ s in Set.Ioc (0 : ℝ) r0, s ^ 2 * gprof s) =
          ∫ s in Set.Ioc r0 y, s ^ 2 * gprof s := by
      simpa [f2] using hAsplit f2 hf2_int_R r0 y hr0.le hr0y hyR
    have hTail : (∫ s in Set.Ioc y R, s * gprof s) =
          S0 - (∫ s in Set.Ioc r0 y, s * gprof s) := by
      have hS := hTailSplit (fun s : ℝ => s * gprof s) (by simpa [f1] using hf1_int_D r0 hr0) y hr0y hyR
      have hSdef : (∫ s in Set.Ioc r0 R, s * gprof s) = S0 := rfl
      rw [hSdef] at hS
      linarith
    have hI1 := hf2y_int y hr0y hyR
    have hI2 := hf1y_int y hr0y hyR
    have hI2y : IntegrableOn (fun s : ℝ => y * (s * gprof s)) (Set.Ioc r0 y) volume := hI2.const_mul y
    have hsumInt : (∫ s in Set.Ioc r0 y, (s ^ 2 - y * s) * gprof s) =
        (∫ s in Set.Ioc r0 y, s ^ 2 * gprof s) - y * (∫ s in Set.Ioc r0 y, s * gprof s) := by
      have hpt : (fun s : ℝ => s ^ 2 * gprof s - y * (s * gprof s)) =ᵐ[(volume.restrict (Set.Ioc r0 y))]
          (fun s : ℝ => (s ^ 2 - y * s) * gprof s) := by
        filter_upwards [] with s
        ring
      have hcm : (∫ s in Set.Ioc r0 y, y * (s * gprof s)) =
          y * (∫ s in Set.Ioc r0 y, s * gprof s) := by
        rw [← MeasureTheory.integral_const_mul y (fun s : ℝ => s * gprof s)]
      calc
        (∫ s in Set.Ioc r0 y, (s ^ 2 - y * s) * gprof s)
            = ∫ s in Set.Ioc r0 y, (s ^ 2 * gprof s - y * (s * gprof s)) := by
              rw [integral_congr_ae hpt]
        _ = (∫ s in Set.Ioc r0 y, s ^ 2 * gprof s) -
              (∫ s in Set.Ioc r0 y, y * (s * gprof s)) := by
              exact MeasureTheory.integral_sub hI1 hI2y
        _ = (∫ s in Set.Ioc r0 y, s ^ 2 * gprof s) - y * (∫ s in Set.Ioc r0 y, s * gprof s) := by
              rw [hcm]
    calc
      u y - u r0
          = (1 / 2 : ℝ) * ((∫ s in Set.Ioc (0 : ℝ) y, s ^ 2 * gprof s) +
              y * (∫ s in Set.Ioi y, s * gprof s)) -
              (1 / 2 : ℝ) * ((∫ s in Set.Ioc (0 : ℝ) r0, s ^ 2 * gprof s) +
              r0 * (∫ s in Set.Ioi r0, s * gprof s)) := by
            rw [hcan y, hcan r0]
      _ = (1 / 2 : ℝ) * ((∫ s in Set.Ioc (0 : ℝ) y, s ^ 2 * gprof s) -
              (∫ s in Set.Ioc (0 : ℝ) r0, s ^ 2 * gprof s) +
              y * (∫ s in Set.Ioc y R, s * gprof s) - r0 * S0) := by
            rw [hBformula y hyR, hBformula r0 hr0R.le]
            ring
      _ = (1 / 2 : ℝ) * ((∫ s in Set.Ioc r0 y, s ^ 2 * gprof s) +
              y * (S0 - (∫ s in Set.Ioc r0 y, s * gprof s)) - r0 * S0) := by
            rw [hA, hTail]
      _ = (1 / 2 : ℝ) * ((y - r0) * S0 +
              (∫ s in Set.Ioc r0 y, s ^ 2 * gprof s) -
              y * (∫ s in Set.Ioc r0 y, s * gprof s)) := by ring
      _ = (1 / 2 : ℝ) * ((y - r0) * S0 +
              (∫ s in Set.Ioc r0 y, (s ^ 2 - y * s) * gprof s)) := by
            have hrewrite : ((y - r0) * S0 + (∫ s in Set.Ioc r0 y, s ^ 2 * gprof s)) -
                  y * (∫ s in Set.Ioc r0 y, s * gprof s) =
                  (y - r0) * S0 + (∫ s in Set.Ioc r0 y, (s ^ 2 - y * s) * gprof s) := by
              rw [hsumInt]
              ring
            rw [hrewrite]

  -- pointwise |(s² − y·s)·gprof| = s·(y−s)·|gprof| on (r0, y)
  have habsR (y : ℝ) (hr0y : r0 ≤ y) :
      (fun s : ℝ => |(s ^ 2 - y * s) * gprof s|) =ᵐ[(volume.restrict (Set.Ioc r0 y))]
        (fun s : ℝ => s * (y - s) * |gprof s|) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    have hspos : 0 < s := lt_trans hr0 hs.1
    have hsy : s ≤ y := hs.2
    have hnonneg : 0 ≤ s * (y - s) := mul_nonneg hspos.le (sub_nonneg.mpr hsy)
    calc
      |(s ^ 2 - y * s) * gprof s| = |-(s * (y - s) * gprof s)| := by
        congr 1
        ring
      _ = |s * (y - s) * gprof s| := by rw [abs_neg]
      _ = s * (y - s) * |gprof s| := by
        rw [abs_mul, abs_of_nonneg hnonneg]
  -- |gprof| is strongly measurable on (r0, y)
  have hgAEy (y : ℝ) (hr0y : r0 ≤ y) (hyR : y ≤ R) :
      AEStronglyMeasurable (fun s : ℝ => |gprof s|) (volume.restrict (Set.Ioc r0 y)) := by
    have hg : AEStronglyMeasurable gprof (volume.restrict (Set.Ioc r0 y)) := by
      exact hgprofAE0.mono_set (s := Set.Ioc r0 y) (t := Set.Ioi (0 : ℝ))
        (by intro s hs; exact lt_of_le_of_lt hr0.le hs.1)
    exact hg.norm
  -- h := s·|gprof| integrable on (r0, y)
  have hh_int (y : ℝ) (hr0y : r0 ≤ y) (hyR : y ≤ R) :
      IntegrableOn h (Set.Ioc r0 y) volume := by
    exact (hsg_int r0 y hr0 hr0y hyR).mono_set (s := Set.Ioc r0 y) (by
      intro s hs
      exact ⟨le_of_lt hs.1, hs.2⟩)
  -- integrability of the (y−r0)-weighted copy
  have hg2_int (y : ℝ) (hr0y : r0 < y) (hyR : y ≤ R) :
      IntegrableOn (fun s : ℝ => (y - r0) * h s) (Set.Ioc r0 y) volume :=
    (hh_int y (le_of_lt hr0y) hyR).const_mul (y - r0)
  -- integrability of s·(y−s)·|gprof| on (r0, y)
  have hg1_int (y : ℝ) (hr0y : r0 < y) (hyR : y ≤ R) :
      IntegrableOn (fun s : ℝ => s * (y - s) * |gprof s|) (Set.Ioc r0 y) volume := by
    change Integrable (fun s : ℝ => s * (y - s) * |gprof s|) (volume.restrict (Set.Ioc r0 y))
    constructor
    · have hmeas : Measurable (fun s : ℝ => s * (y - s)) := by fun_prop
      exact hmeas.aestronglyMeasurable.mul (hgAEy y (le_of_lt hr0y) hyR)
    · have hb : HasFiniteIntegral (fun s : ℝ => (y - r0) * h s)
          (volume.restrict (Set.Ioc r0 y)) := (hg2_int y hr0y hyR).2
      refine hb.mono' ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
      have hsr0 : r0 < s := hs.1
      have hsy : s ≤ y := hs.2
      have hspos : 0 < s := lt_trans hr0 hsr0
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg
        (mul_nonneg hspos.le (sub_nonneg.mpr hsy)) (abs_nonneg (gprof s)))]
      calc
        s * (y - s) * |gprof s| ≤ s * (y - r0) * |gprof s| := by
          have h1 : s * (y - s) ≤ s * (y - r0) := by
            exact mul_le_mul_of_nonneg_left (by linarith) hspos.le
          exact mul_le_mul_of_nonneg_right h1 (abs_nonneg (gprof s))
        _ = (y - r0) * (s * |gprof s|) := by ring
  -- bound |∫ (s²−ys)gprof| ≤ (y−r0)·∫ h over (r0,y)
  have hdiff_abs_le (y : ℝ) (hr0y : r0 < y) (hyR : y ≤ R) :
      |∫ s in Set.Ioc r0 y, (s ^ 2 - y * s) * gprof s| ≤
        (y - r0) * (∫ s in Set.Ioc r0 y, h s) := by
    have hle2 : (∫ s in Set.Ioc r0 y, s * (y - s) * |gprof s|) ≤
        ∫ s in Set.Ioc r0 y, (y - r0) * h s := by
      refine setIntegral_mono_on (s := Set.Ioc r0 y) (μ := (volume : Measure ℝ))
        (hg1_int y hr0y hyR) (hg2_int y hr0y hyR) measurableSet_Ioc ?_
      intro x hx
      have hx1 : r0 < x := hx.1
      have hx2 : x ≤ y := hx.2
      have hxpos : 0 < x := lt_trans hr0 hx1
      calc
        x * (y - x) * |gprof x| ≤ x * (y - r0) * |gprof x| := by
          have h1 : x * (y - x) ≤ x * (y - r0) := by
            exact mul_le_mul_of_nonneg_left (by linarith) hxpos.le
          exact mul_le_mul_of_nonneg_right h1 (abs_nonneg (gprof x))
        _ = (y - r0) * (x * |gprof x|) := by ring
    calc
      |∫ s in Set.Ioc r0 y, (s ^ 2 - y * s) * gprof s|
          ≤ ∫ s in Set.Ioc r0 y, |(s ^ 2 - y * s) * gprof s| := by
            exact abs_integral_le_integral_abs
      _ = ∫ s in Set.Ioc r0 y, s * (y - s) * |gprof s| := by
            rw [integral_congr_ae (habsR y (le_of_lt hr0y))]
      _ ≤ ∫ s in Set.Ioc r0 y, (y - r0) * h s := hle2
      _ = (y - r0) * (∫ s in Set.Ioc r0 y, h s) := by
            rw [← MeasureTheory.integral_const_mul (y - r0) h]

  -- right slope bound
  have hslope_boundR (y : ℝ) (hr0y : r0 < y) (hyR : y ≤ R) :
      |slope u r0 y - (1 / 2 : ℝ) * S0| ≤ (1 / 2) * (∫ s in Set.Ioc r0 y, h s) := by
    have hyr0ne : y - r0 ≠ 0 := sub_ne_zero.mpr (ne_of_gt hr0y)
    have hId : slope u r0 y - (1 / 2 : ℝ) * S0 =
        (1 / 2) * (∫ s in Set.Ioc r0 y, (s ^ 2 - y * s) * gprof s) / (y - r0) := by
      rw [slope_def_field]
      rw [hdiffR y (le_of_lt hr0y) hyR]
      field_simp [hyr0ne]
      ring
    have habs := hdiff_abs_le y hr0y hyR
    calc
      |slope u r0 y - (1 / 2 : ℝ) * S0|
          = |(1 / 2) * (∫ s in Set.Ioc r0 y, (s ^ 2 - y * s) * gprof s) / (y - r0)| := by rw [hId]
      _ = (1 / 2) * |∫ s in Set.Ioc r0 y, (s ^ 2 - y * s) * gprof s| / (y - r0) := by
            rw [abs_div, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
            rw [abs_of_pos (sub_pos.mpr hr0y)]
      _ ≤ (1 / 2) * ((y - r0) * (∫ s in Set.Ioc r0 y, h s)) / (y - r0) := by
            exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left habs (by norm_num : (0 : ℝ) ≤ 1 / 2))
              (sub_pos.mpr hr0y).le
      _ = (1 / 2) * (∫ s in Set.Ioc r0 y, h s) := by
            field_simp [hyr0ne]
  -- one-sided right limit of the slope
  have hslopeR : Tendsto (fun y : ℝ => slope u r0 y) (𝓝[>] r0) (𝓝 ((1 / 2 : ℝ) * S0)) := by
    have hJm : Tendsto (fun y : ℝ => (1 / 2) * (∫ s in Set.Ioc r0 y, h s)) (𝓝[>] r0) (𝓝 0) := by
      simpa using hJright.const_mul (1 / 2 : ℝ)
    have hnonneg : ∀ᶠ y in 𝓝[>] r0, 0 ≤ |slope u r0 y - (1 / 2 : ℝ) * S0| :=
      Eventually.of_forall (fun y => abs_nonneg _)
    have hle : ∀ᶠ y in 𝓝[>] r0,
        |slope u r0 y - (1 / 2 : ℝ) * S0| ≤ (1 / 2) * (∫ s in Set.Ioc r0 y, h s) := by
      filter_upwards [self_mem_nhdsWithin (s := Set.Ioi r0),
        (mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hr0R) : Set.Iio R ∈ 𝓝[>] r0)] with y hy hr
      exact hslope_boundR y hy (le_of_lt hr)
    have hmain : Tendsto (fun y : ℝ => |slope u r0 y - (1 / 2 : ℝ) * S0|) (𝓝[>] r0) (𝓝 0) :=
      squeeze_zero' hnonneg hle hJm
    exact tendsto_iff_norm_sub_tendsto_zero.2 (by simpa [Real.norm_eq_abs] using hmain)

  -- generic tail-splitting over Ioc for the left side: c ≤ d ≤ R
  have hTailSplitL (p : ℝ → ℝ) (c d : ℝ) (hp : IntegrableOn p (Set.Ioc c R) volume)
      (hcd : c ≤ d) (hdR : d ≤ R) :
      (∫ s in Set.Ioc c R, p s) - (∫ s in Set.Ioc d R, p s) = (∫ s in Set.Ioc c d, p s) := by
    have hsub : Set.Ioc d R ⊆ Set.Ioc c R := by
      intro s hs
      exact ⟨lt_of_le_of_lt hcd hs.1, hs.2⟩
    have hsdiff : Set.Ioc c R \ Set.Ioc d R = Set.Ioc c d := by
      ext s
      constructor
      · intro hs
        rcases hs with ⟨⟨hcs, hsR⟩, hd⟩
        refine ⟨hcs, ?_⟩
        by_contra hnot
        have hsd : d < s := lt_of_not_ge hnot
        exact hd ⟨hsd, hsR⟩
      · intro hs
        constructor
        · exact ⟨hs.1, le_trans hs.2 hdR⟩
        · intro hmem
          exact (not_lt_of_ge hs.2) hmem.1
    calc
      (∫ s in Set.Ioc c R, p s) - (∫ s in Set.Ioc d R, p s)
          = ∫ s in Set.Ioc c R \ Set.Ioc d R, p s := by
            exact (setIntegral_sdiff (t := Set.Ioc d R) (f := p)
              (μ := (volume : Measure ℝ)) (measurableSet_Ioc) hp hsub).symm
      _ = ∫ s in Set.Ioc c d, p s := by rw [hsdiff]
  -- integrability over (y, r0] for y ≤ r0
  have hf2lr_int (y : ℝ) (hy0 : 0 ≤ y) (hyr0 : y ≤ r0) :
      IntegrableOn (fun s : ℝ => s ^ 2 * gprof s) (Set.Ioc y r0) volume := by
    simpa [f2] using (hf2_int_R.mono_set (s := Set.Ioc y r0) (by
      intro s hs
      exact ⟨lt_of_le_of_lt hy0 hs.1, le_trans hs.2 hr0R.le⟩))
  have hf1lr_int (y : ℝ) (hy0 : 0 < y) (hyr0 : y ≤ r0) :
      IntegrableOn (fun s : ℝ => s * gprof s) (Set.Ioc y r0) volume := by
    simpa [f1] using ((hf1_int_D y hy0).mono_set (s := Set.Ioc y r0) (by
      intro s hs
      exact ⟨hs.1, le_trans hs.2 hr0R.le⟩))
  -- left difference identity
  have hdiffL (y : ℝ) (hy0 : 0 < y) (hyr0 : y ≤ r0) :
      u r0 - u y = (1 / 2 : ℝ) * ((r0 - y) * S0 +
        (∫ s in Set.Ioc y r0, (s ^ 2 - y * s) * gprof s)) := by
    have hA : (∫ s in Set.Ioc (0 : ℝ) r0, s ^ 2 * gprof s) -
          (∫ s in Set.Ioc (0 : ℝ) y, s ^ 2 * gprof s) =
          ∫ s in Set.Ioc y r0, s ^ 2 * gprof s := by
      simpa [f2] using hAsplit f2 hf2_int_R y r0 hy0.le hyr0 hr0R.le
    have hTail : (∫ s in Set.Ioc y R, s * gprof s) =
          S0 + (∫ s in Set.Ioc y r0, s * gprof s) := by
      have hS := hTailSplitL (fun s : ℝ => s * gprof s) y r0 (by simpa [f1] using hf1_int_D y hy0) hyr0 hr0R.le
      have hSdef : (∫ s in Set.Ioc r0 R, s * gprof s) = S0 := rfl
      rw [hSdef] at hS
      linarith
    have hI1 := hf2lr_int y hy0.le hyr0
    have hI2 := hf1lr_int y hy0 hyr0
    have hI2y : IntegrableOn (fun s : ℝ => y * (s * gprof s)) (Set.Ioc y r0) volume := hI2.const_mul y
    have hsumInt : (∫ s in Set.Ioc y r0, (s ^ 2 - y * s) * gprof s) =
        (∫ s in Set.Ioc y r0, s ^ 2 * gprof s) - y * (∫ s in Set.Ioc y r0, s * gprof s) := by
      have hpt : (fun s : ℝ => s ^ 2 * gprof s - y * (s * gprof s)) =ᵐ[(volume.restrict (Set.Ioc y r0))]
          (fun s : ℝ => (s ^ 2 - y * s) * gprof s) := by
        filter_upwards [] with s
        ring
      have hcm : (∫ s in Set.Ioc y r0, y * (s * gprof s)) =
          y * (∫ s in Set.Ioc y r0, s * gprof s) := by
        rw [← MeasureTheory.integral_const_mul y (fun s : ℝ => s * gprof s)]
      calc
        (∫ s in Set.Ioc y r0, (s ^ 2 - y * s) * gprof s)
            = ∫ s in Set.Ioc y r0, (s ^ 2 * gprof s - y * (s * gprof s)) := by
              rw [integral_congr_ae hpt]
        _ = (∫ s in Set.Ioc y r0, s ^ 2 * gprof s) -
              (∫ s in Set.Ioc y r0, y * (s * gprof s)) := by
              exact MeasureTheory.integral_sub hI1 hI2y
        _ = (∫ s in Set.Ioc y r0, s ^ 2 * gprof s) - y * (∫ s in Set.Ioc y r0, s * gprof s) := by
              rw [hcm]
    calc
      u r0 - u y
          = (1 / 2 : ℝ) * ((∫ s in Set.Ioc (0 : ℝ) r0, s ^ 2 * gprof s) +
              r0 * (∫ s in Set.Ioi r0, s * gprof s)) -
              (1 / 2 : ℝ) * ((∫ s in Set.Ioc (0 : ℝ) y, s ^ 2 * gprof s) +
              y * (∫ s in Set.Ioi y, s * gprof s)) := by
            rw [hcan r0, hcan y]
      _ = (1 / 2 : ℝ) * ((∫ s in Set.Ioc (0 : ℝ) r0, s ^ 2 * gprof s) -
              (∫ s in Set.Ioc (0 : ℝ) y, s ^ 2 * gprof s) +
              r0 * S0 - y * (∫ s in Set.Ioc y R, s * gprof s)) := by
            rw [hS0, hBformula y (le_trans hyr0 hr0R.le)]
            ring
      _ = (1 / 2 : ℝ) * (∫ s in Set.Ioc y r0, s ^ 2 * gprof s) +
              (1 / 2 : ℝ) * ((r0 - y) * S0 - y * (∫ s in Set.Ioc y r0, s * gprof s)) := by
            rw [hA, hTail]
            ring
      _ = (1 / 2 : ℝ) * ((r0 - y) * S0 +
              ((∫ s in Set.Ioc y r0, s ^ 2 * gprof s) -
              y * (∫ s in Set.Ioc y r0, s * gprof s))) := by ring
      _ = (1 / 2 : ℝ) * ((r0 - y) * S0 +
              (∫ s in Set.Ioc y r0, (s ^ 2 - y * s) * gprof s)) := by
            have hrewrite : (r0 - y) * S0 +
                  ((∫ s in Set.Ioc y r0, s ^ 2 * gprof s) - y * (∫ s in Set.Ioc y r0, s * gprof s)) =
                  (r0 - y) * S0 + (∫ s in Set.Ioc y r0, (s ^ 2 - y * s) * gprof s) := by
              rw [hsumInt]
            rw [hrewrite]

  -- pointwise |(s² − y·s)·gprof| = s·(s−y)·|gprof| on (y, r0)
  have habsL (y : ℝ) (hy0 : 0 < y) (hyr0 : y < r0) :
      (fun s : ℝ => |(s ^ 2 - y * s) * gprof s|) =ᵐ[(volume.restrict (Set.Ioc y r0))]
        (fun s : ℝ => s * (s - y) * |gprof s|) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    have hsy : y < s := hs.1
    have hsr0 : s ≤ r0 := hs.2
    have hspos : 0 < s := lt_trans hy0 hsy
    have hnonneg : 0 ≤ s * (s - y) := mul_nonneg hspos.le (sub_nonneg.mpr hsy.le)
    calc
      |(s ^ 2 - y * s) * gprof s| = |s * (s - y) * gprof s| := by
        congr 1
        ring
      _ = s * (s - y) * |gprof s| := by
        rw [abs_mul, abs_of_nonneg hnonneg]
  have hgAEz (y : ℝ) (hy0 : 0 < y) (hyr0 : y ≤ r0) :
      AEStronglyMeasurable (fun s : ℝ => |gprof s|) (volume.restrict (Set.Ioc y r0)) := by
    have hg : AEStronglyMeasurable gprof (volume.restrict (Set.Ioc y r0)) := by
      exact hgprofAE0.mono_set (s := Set.Ioc y r0) (t := Set.Ioi (0 : ℝ))
        (by intro s hs; exact lt_trans hy0 hs.1)
    exact hg.norm
  have hh_int2 (y : ℝ) (hy0 : 0 < y) (hyr0 : y < r0) :
      IntegrableOn h (Set.Ioc y r0) volume := by
    exact (hsg_int y r0 hy0 hyr0.le hr0R.le).mono_set (s := Set.Ioc y r0) (by
      intro s hs
      exact ⟨le_of_lt hs.1, hs.2⟩)
  have hg2b_int (y : ℝ) (hy0 : 0 < y) (hyr0 : y < r0) :
      IntegrableOn (fun s : ℝ => (r0 - y) * h s) (Set.Ioc y r0) volume :=
    (hh_int2 y hy0 hyr0).const_mul (r0 - y)
  have hg1b_int (y : ℝ) (hy0 : 0 < y) (hyr0 : y < r0) :
      IntegrableOn (fun s : ℝ => s * (s - y) * |gprof s|) (Set.Ioc y r0) volume := by
    change Integrable (fun s : ℝ => s * (s - y) * |gprof s|) (volume.restrict (Set.Ioc y r0))
    constructor
    · have hmeas : Measurable (fun s : ℝ => s * (s - y)) := by fun_prop
      exact hmeas.aestronglyMeasurable.mul (hgAEz y hy0 hyr0.le)
    · have hb : HasFiniteIntegral (fun s : ℝ => (r0 - y) * h s)
          (volume.restrict (Set.Ioc y r0)) := (hg2b_int y hy0 hyr0).2
      refine hb.mono' ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
      have hsy : y < s := hs.1
      have hspos : 0 < s := lt_trans hy0 hsy
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg
        (mul_nonneg hspos.le (sub_nonneg.mpr hsy.le)) (abs_nonneg (gprof s)))]
      calc
        s * (s - y) * |gprof s| ≤ s * (r0 - y) * |gprof s| := by
          have h1 : s * (s - y) ≤ s * (r0 - y) := by
            exact mul_le_mul_of_nonneg_left (sub_le_sub_right hs.2 y) hspos.le
          exact mul_le_mul_of_nonneg_right h1 (abs_nonneg (gprof s))
        _ = (r0 - y) * (s * |gprof s|) := by ring
  have hdiff_abs_leL (y : ℝ) (hy0 : 0 < y) (hyr0 : y < r0) :
      |∫ s in Set.Ioc y r0, (s ^ 2 - y * s) * gprof s| ≤
        (r0 - y) * (∫ s in Set.Ioc y r0, h s) := by
    have hle2 : (∫ s in Set.Ioc y r0, s * (s - y) * |gprof s|) ≤
        ∫ s in Set.Ioc y r0, (r0 - y) * h s := by
      refine setIntegral_mono_on (s := Set.Ioc y r0) (μ := (volume : Measure ℝ))
        (hg1b_int y hy0 hyr0) (hg2b_int y hy0 hyr0) measurableSet_Ioc ?_
      intro x hx
      have hx1 : y < x := hx.1
      have hx2 : x ≤ r0 := hx.2
      have hxpos : 0 < x := lt_trans hy0 hx1
      calc
        x * (x - y) * |gprof x| ≤ x * (r0 - y) * |gprof x| := by
          have h1 : x * (x - y) ≤ x * (r0 - y) := by
            exact mul_le_mul_of_nonneg_left (sub_le_sub_right hx2 y) hxpos.le
          exact mul_le_mul_of_nonneg_right h1 (abs_nonneg (gprof x))
        _ = (r0 - y) * (x * |gprof x|) := by ring
    calc
      |∫ s in Set.Ioc y r0, (s ^ 2 - y * s) * gprof s|
          ≤ ∫ s in Set.Ioc y r0, |(s ^ 2 - y * s) * gprof s| := by
            exact abs_integral_le_integral_abs
      _ = ∫ s in Set.Ioc y r0, s * (s - y) * |gprof s| := by
            rw [integral_congr_ae (habsL y hy0 hyr0)]
      _ ≤ ∫ s in Set.Ioc y r0, (r0 - y) * h s := hle2
      _ = (r0 - y) * (∫ s in Set.Ioc y r0, h s) := by
            rw [← MeasureTheory.integral_const_mul (r0 - y) h]

  -- left slope bound
  have hslope_boundL (y : ℝ) (hy0 : 0 < y) (hyr0 : y < r0) :
      |slope u r0 y - (1 / 2 : ℝ) * S0| ≤ (1 / 2) * (∫ s in Set.Ioc y r0, h s) := by
    have hd := hdiffL y hy0 hyr0.le
    have hr0yne : r0 - y ≠ 0 := sub_ne_zero.mpr (ne_of_gt hyr0)
    have hyrne : y - r0 ≠ 0 := sub_ne_zero.mpr (ne_of_lt hyr0)
    have hId : slope u r0 y - (1 / 2 : ℝ) * S0 =
        (1 / 2) * (∫ s in Set.Ioc y r0, (s ^ 2 - y * s) * gprof s) / (r0 - y) := by
      rw [slope_def_field]
      calc
        (u y - u r0) / (y - r0) - (1 / 2 : ℝ) * S0
            = (u r0 - u y) / (r0 - y) - (1 / 2) * S0 := by
              field_simp [hr0yne, hyrne]
              ring
        _ = ((1 / 2 : ℝ) * ((r0 - y) * S0 +
              (∫ s in Set.Ioc y r0, (s ^ 2 - y * s) * gprof s))) / (r0 - y) -
              (1 / 2) * S0 := by rw [hd]
        _ = (1 / 2) * (∫ s in Set.Ioc y r0, (s ^ 2 - y * s) * gprof s) / (r0 - y) := by
              field_simp [hr0yne]
              ring
    have habs := hdiff_abs_leL y hy0 hyr0
    calc
      |slope u r0 y - (1 / 2 : ℝ) * S0|
          = |(1 / 2) * (∫ s in Set.Ioc y r0, (s ^ 2 - y * s) * gprof s) / (r0 - y)| := by rw [hId]
      _ = (1 / 2) * |∫ s in Set.Ioc y r0, (s ^ 2 - y * s) * gprof s| / (r0 - y) := by
            rw [abs_div, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
            rw [abs_of_pos (sub_pos.mpr hyr0)]
      _ ≤ (1 / 2) * ((r0 - y) * (∫ s in Set.Ioc y r0, h s)) / (r0 - y) := by
            exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left habs (by norm_num : (0 : ℝ) ≤ 1 / 2))
              (sub_pos.mpr hyr0).le
      _ = (1 / 2) * (∫ s in Set.Ioc y r0, h s) := by
            field_simp [hr0yne]
  -- the left error integral tends to 0 (interval version ≡ set version on x ≤ r0)
  have hL0 : Tendsto (fun x : ℝ => ∫ s in Set.Ioc x r0, h s) (𝓝[<] r0) (𝓝 0) := by
    have hl : (fun x : ℝ => ∫ s in x..r0, h s) =ᶠ[𝓝[<] r0]
        (fun x : ℝ => ∫ s in Set.Ioc x r0, h s) := by
      filter_upwards [self_mem_nhdsWithin (s := Set.Iio r0)] with x hx
      rw [intervalIntegral.integral_of_le hx.le]
    exact hKleft.congr' hl
  -- one-sided left limit of the slope
  have hslopeL : Tendsto (fun y : ℝ => slope u r0 y) (𝓝[<] r0) (𝓝 ((1 / 2 : ℝ) * S0)) := by
    have hJm : Tendsto (fun y : ℝ => (1 / 2) * (∫ s in Set.Ioc y r0, h s)) (𝓝[<] r0) (𝓝 0) := by
      simpa using hL0.const_mul (1 / 2 : ℝ)
    have hnonneg : ∀ᶠ y in 𝓝[<] r0, 0 ≤ |slope u r0 y - (1 / 2 : ℝ) * S0| :=
      Eventually.of_forall (fun y => abs_nonneg _)
    have hle : ∀ᶠ y in 𝓝[<] r0,
        |slope u r0 y - (1 / 2 : ℝ) * S0| ≤ (1 / 2) * (∫ s in Set.Ioc y r0, h s) := by
      filter_upwards [self_mem_nhdsWithin (s := Set.Iio r0),
        (mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds hmidR) : Set.Ioi mid ∈ 𝓝[<] r0)] with y hy hr
      exact hslope_boundL y (lt_trans hmid0 hr) hy
    have hmain : Tendsto (fun y : ℝ => |slope u r0 y - (1 / 2 : ℝ) * S0|) (𝓝[<] r0) (𝓝 0) :=
      squeeze_zero' hnonneg hle hJm
    exact tendsto_iff_norm_sub_tendsto_zero.2 (by simpa [Real.norm_eq_abs] using hmain)
  -- assemble: HasDerivAt with value (1/2)·S0
  have hder : HasDerivAt u ((1 / 2 : ℝ) * S0) r0 := by
    rw [hasDerivAt_iff_tendsto_slope_left_right]
    exact ⟨hslopeL, hslopeR⟩
  have hS0eq : (∫ s in Set.Ioi r0, s * radialProfile (fun x : ℝ³ => v x * (1 - w x)) s) = S0 := by
    simpa [gprof, g] using hS0
  simpa [u, hS0eq] using hder

/-- `canonicalProfile v w R 0 = 0`. -/
lemma canonicalProfile_zero (v w : ℝ³ → ℝ) (R : ℝ) : canonicalProfile v w R 0 = 0 := by
  dsimp [canonicalProfile]
  simp

/-- Interior derivative formula: `deriv U r = (1/2)·∫_{s>r} s·gprof(s)` for
`0 < r < R`. -/
lemma canonicalProfile_deriv_Ioo {v w : ℝ³ → ℝ} {R r : ℝ} (hR : 0 < R)
    (hvrad : IsRadial v) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (hrad : IsRadial w) (hw : IsScatteringSolution w v) (hr0 : 0 < r) (hrR : r < R) :
    deriv (canonicalProfile v w R) r =
      (1 / 2) * (∫ s in Set.Ioi r, s * radialProfile (fun x : ℝ³ => v x * (1 - w x)) s) := by
  exact (canonicalProfile_hasDerivAt_Ioo (v := v) (w := w) (R := R) hR hvrad hv_supp hrad hw hr0 hrR).deriv

/-- **Continuity on `[0,R]`.**  The canonical profile is continuous on the whole
closed interval (origin datum from `canonicalProfile_tendsto_zero`, interior
continuity from the derivative theorem, and right-endpoint continuity from
`canonicalProfile_hasDerivAt_R`). -/
theorem canonicalProfile_continuousOn_Icc {v w : ℝ³ → ℝ} {R : ℝ} (hR : 0 < R)
    (hvrad : IsRadial v) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (hrad : IsRadial w) (hw : IsScatteringSolution w v) :
    ContinuousOn (canonicalProfile v w R) (Set.Icc (0 : ℝ) R) := by
  intro x hx
  rcases hx with ⟨hx0, hxR⟩
  by_cases hx0' : x = 0
  · -- continuity at the origin: right limit + value at 0
    subst x
    rw [ContinuousWithinAt]
    have hU0 : canonicalProfile v w R 0 = 0 := canonicalProfile_zero v w R
    have hT0 : Tendsto (canonicalProfile v w R) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
      canonicalProfile_tendsto_zero (v := v) (w := w) (R := R) hR hvrad hv_supp hrad hw
    have hge : 𝓝[Icc (0 : ℝ) R] 0 = 𝓝[≥] (0 : ℝ) := by
      simpa using (nhdsWithin_Icc_eq_nhdsGE hR : 𝓝[Icc (0:ℝ) R] 0 = 𝓝[Ici (0:ℝ)] 0)
    rw [hge]
    have hIci : Set.Ici (0 : ℝ) = insert (0 : ℝ) (Set.Ioi (0 : ℝ)) := by
      ext y
      simp [le_iff_lt_or_eq]
    rw [hIci]
    rw [nhdsWithin_insert]
    rw [tendsto_sup]
    constructor
    · simpa [hU0] using tendsto_pure_nhds (canonicalProfile v w R) (0 : ℝ)
    · simpa [hU0] using hT0
  · -- interior or right endpoint
    have hxpos : 0 < x := lt_of_le_of_ne hx0 (Ne.symm hx0')
    rcases lt_or_eq_of_le hxR with hxRlt | hxReq
    · exact (canonicalProfile_hasDerivAt_Ioo (v := v) (w := w) (R := R) hR hvrad hv_supp hrad hw
        hxpos hxRlt).continuousAt.continuousWithinAt
    · subst x
      exact (canonicalProfile_hasDerivAt_R (v := v) (w := w) (R := R) hR hvrad hv_supp hrad hw)
        |>.continuousAt.continuousWithinAt

/-- If two functions agree on `uIcc a b` and one is absolutely continuous
there, then so is the other. -/
lemma absolutelyContinuousOnInterval_of_eqOn {a b : ℝ} {f g : ℝ → ℝ}
    (hg : AbsolutelyContinuousOnInterval g a b) (hfg : Set.EqOn f g (Set.uIcc a b)) :
    AbsolutelyContinuousOnInterval f a b := by
  rw [absolutelyContinuousOnInterval_iff] at hg ⊢
  intro ε hε
  rcases hg ε hε with ⟨δ, hδ, hδ'⟩
  refine ⟨δ, hδ, ?_⟩
  intro E hE hlen
  have hsum : (∑ i ∈ Finset.range E.1, dist (f (E.2 i).1) (f (E.2 i).2)) =
      ∑ i ∈ Finset.range E.1, dist (g (E.2 i).1) (g (E.2 i).2) := by
    refine Finset.sum_congr rfl ?_
    intro i hi
    have hmem := hE.1 i hi
    rw [hfg hmem.1, hfg hmem.2]
  simpa [hsum] using (hδ' E hE hlen : (∑ i ∈ Finset.range E.1, dist (g (E.2 i).1) (g (E.2 i).2)) < ε)


/-- **Interval regularity of the canonical profile.**  For `0 < a ≤ b ≤ R` the
derivative of the canonical profile is absolutely continuous on `[a,b]` and has
the a.e. Carathéodory second derivative `(radialProfile v / 2)·(U − id)`
there.  The proof: on `[a,b]` the derivative is represented pointwise as
`deriv U x = C − (1/2)·∫_{a..x} f1` (a tail split of the explicit derivative
`(1/2)∫_{>x} f1` from `canonicalProfile_deriv_Ioo`), so it is absolutely
continuous with `f1 := r ↦ r·gprof(r)` as its Radon–Nikodym derivative;
differentiating that primitive a.e. (Lebesgue differentiation) and rewriting
`−f1/2 = (v/2)(U − id)` a.e. (the source identity) gives the Carathéodory
second derivative. -/
theorem canonicalProfile_reg_interval {v w : ℝ³ → ℝ} {R a b : ℝ} (hR : 0 < R)
    (hvrad : IsRadial v) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (hrad : IsRadial w) (hw : IsScatteringSolution w v) (ha0 : 0 < a) (hab : a ≤ b)
    (hbR : b ≤ R) :
    AbsolutelyContinuousOnInterval (deriv (canonicalProfile v w R)) a b ∧
      (∀ᵐ x : ℝ, x ∈ Set.uIcc a b → HasDerivAt (deriv (canonicalProfile v w R))
        ((radialProfile v x / 2) * (canonicalProfile v w R x - x)) x) := by
  let g : ℝ³ → ℝ := fun y => v y * (1 - w y)
  let gprof : ℝ → ℝ := radialProfile g
  let f1 : ℝ → ℝ := fun s => s * gprof s
  let u : ℝ → ℝ := canonicalProfile v w R
  have hg : MeasureTheory.Integrable g := by
    simpa [g] using (scatG_integrable (v := v) (w := w) hv_supp hw)
  have hgrad : IsRadial g := by
    intro x y hxy
    dsimp [g]
    rw [hvrad x y hxy, hrad x y hxy]
  have hgsupp : ∀ y : ℝ³, R ≤ ‖y‖ → g y = 0 := by
    intro y hy
    have hv0 : v y = 0 := v_eq_zero_of_norm_ge hv_supp hy
    dsimp [g]
    simp [hv0]
  have hgprof_geR : ∀ s : ℝ, R ≤ s → gprof s = 0 := by
    intro s hs
    dsimp [gprof]
    have hnorm : R ≤ ‖s • radU0‖ := by
      rw [norm_smul_radU0]
      rw [abs_of_nonneg (le_trans hR.le hs)]
      exact hs
    exact hgsupp (s • radU0) hnorm
  have hprof0 : Integrable (fun s : ℝ => s ^ 2 * |gprof s|) (volume.restrict (Set.Ioi (0 : ℝ))) := by
    exact (shell_profile_integrable (g := g) hg hgrad)
  have hgprofAE0 : AEStronglyMeasurable gprof (volume.restrict (Set.Ioi (0 : ℝ))) := by
    simpa [gprof] using shell_gprof_ae_strong (g := g) hg hgrad
  -- integrability of the tail profile f1 on (y, R] for 0 < y ≤ R
  have hf1_int_D (y : ℝ) (hy0 : 0 < y) : IntegrableOn f1 (Set.Ioc y R) volume := by
    have hy0le : 0 ≤ y := hy0.le
    have hyIoi : Set.Ioc y R ⊆ Set.Ioi (0 : ℝ) := by
      intro s hs
      exact lt_of_le_of_lt hy0le hs.1
    change Integrable (fun s : ℝ => s * gprof s) (volume.restrict (Set.Ioc y R))
    constructor
    · have hgAEy : AEStronglyMeasurable gprof (volume.restrict (Set.Ioc y R)) := by
        exact hgprofAE0.mono_set (s := Set.Ioc y R) (t := Set.Ioi (0 : ℝ)) hyIoi
      have hsAEy : AEStronglyMeasurable (fun s : ℝ => s) (volume.restrict (Set.Ioc y R)) :=
        (measurable_id : Measurable (fun s : ℝ => s)).aestronglyMeasurable
      exact hsAEy.mul hgAEy
    · have hb2' : HasFiniteIntegral (fun s : ℝ => (1 / y) * (s ^ 2 * |gprof s|))
          (volume.restrict (Set.Ioc y R)) := by
        have hb0 : HasFiniteIntegral (fun s : ℝ => s ^ 2 * |gprof s|)
            (volume.restrict (Set.Ioc y R)) := by
          exact hprof0.2.mono_measure (Measure.restrict_mono hyIoi le_rfl)
        exact hb0.const_mul (1 / y)
      refine hb2'.mono ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
      have hsy : y < s := hs.1
      have hspos : 0 < s := lt_trans hy0 hsy
      have hgpos : 0 ≤ |gprof s| := abs_nonneg (gprof s)
      have hsydiv : 1 ≤ s / y := by
        rw [one_le_div hy0]
        exact hsy.le
      have hle : s ≤ (1 / y) * s ^ 2 := by
        calc
          s = s * 1 := by ring
          _ ≤ s * (s / y) := by
            exact mul_le_mul_of_nonneg_left hsydiv (le_of_lt hspos)
          _ = (1 / y) * s ^ 2 := by ring
      calc
        |s * gprof s| = s * |gprof s| := by rw [abs_mul, abs_of_nonneg (le_of_lt hspos)]
        _ ≤ (1 / y) * s ^ 2 * |gprof s| := by
          exact mul_le_mul_of_nonneg_right hle hgpos
        _ = |(1 / y) * (s ^ 2 * |gprof s|)| := by
          rw [abs_of_nonneg (mul_nonneg (one_div_nonneg.mpr hy0.le)
            (mul_nonneg (sq_nonneg s) (abs_nonneg (gprof s))))]
          ring
  -- tail integral restricted to (r, R]
  have hBformula (r : ℝ) (hrR : r ≤ R) :
      (∫ s in Set.Ioi r, s * gprof s) = (∫ s in Set.Ioc r R, s * gprof s) := by
    have hsplit : Set.Ioi r = Set.Ioc r R ∪ Set.Ioi R := by
      ext s
      constructor
      · intro hs
        by_cases hsR : s ≤ R
        · left
          exact ⟨hs, hsR⟩
        · right
          exact lt_of_not_ge hsR
      · intro hs
        rcases hs with h1 | h2
        · exact h1.1
        · exact lt_of_le_of_lt hrR h2
    calc
      (∫ s in Set.Ioi r, s * gprof s)
          = ∫ s in Set.Ioc r R ∪ Set.Ioi R, s * gprof s := by rw [hsplit]
      _ = ∫ s in Set.Ioc r R, s * gprof s := by
          refine integral_union_eq_left_of_forall (s := Set.Ioc r R) (t := Set.Ioi R)
            (f := fun s : ℝ => s * gprof s) (μ := (volume : Measure ℝ))
            (measurableSet_Ioi) ?_
          intro x hx
          have hg0 : gprof x = 0 := hgprof_geR x (le_of_lt hx)
          simp [hg0]
  -- interior derivative formula (with the local names)
  have hder (r : ℝ) (hr0 : 0 < r) (hrR : r < R) :
      deriv u r = (1 / 2) * (∫ s in Set.Ioi r, s * gprof s) := by
    simpa [u, gprof, g] using
      (canonicalProfile_deriv_Ioo (v := v) (w := w) (R := R) hR hvrad hv_supp hrad hw hr0 hrR)
  -- tail-split: (a,R] = (a,x] ∪ (x,R] for a ≤ x ≤ R
  have htail_split (x : ℝ) (hax : a ≤ x) (hxR : x ≤ R) :
      (∫ s in Set.Ioc a R, f1 s) = (∫ s in Set.Ioc a x, f1 s) + (∫ s in Set.Ioc x R, f1 s) := by
    have hsub1 : Set.Ioc a x ⊆ Set.Ioc a R := by
      intro s hs
      exact ⟨hs.1, le_trans hs.2 hxR⟩
    have hsub2 : Set.Ioc x R ⊆ Set.Ioc a R := by
      intro s hs
      exact ⟨lt_of_le_of_lt hax hs.1, hs.2⟩
    have hunion : Set.Ioc a x ∪ Set.Ioc x R = Set.Ioc a R := by
      ext s
      constructor
      · intro hs
        rcases hs with h1 | h2
        · exact ⟨h1.1, le_trans h1.2 hxR⟩
        · exact ⟨lt_of_le_of_lt hax h2.1, h2.2⟩
      · intro hs
        rcases hs with ⟨has, hsR⟩
        by_cases hsx : s ≤ x
        · left
          exact ⟨has, hsx⟩
        · right
          exact ⟨lt_of_not_ge hsx, hsR⟩
    calc
      (∫ s in Set.Ioc a R, f1 s) = ∫ s in Set.Ioc a x ∪ Set.Ioc x R, f1 s := by rw [hunion]
      _ = (∫ s in Set.Ioc a x, f1 s) + (∫ s in Set.Ioc x R, f1 s) := by
        exact setIntegral_union (s := Set.Ioc a x) (t := Set.Ioc x R) (f := f1)
          (μ := (volume : Measure ℝ))
          (disjoint_left.2 (fun s hs1 hs2 => (not_lt_of_ge hs1.2) hs2.1))
          measurableSet_Ioc
          ((hf1_int_D a ha0).mono_set hsub1) ((hf1_int_D a ha0).mono_set hsub2)
  -- base constant C := (1/2)·∫_{Ioc a R} f1
  let C : ℝ := (1 / 2) * (∫ s in Set.Ioc a R, f1 s)
  let P : ℝ → ℝ := fun x => C - (1 / 2) * (∫ t in a..x, f1 t)
  -- pointwise representation of deriv u on [a, b]
  have hEqP : Set.EqOn (deriv u) P (Set.uIcc a b) := by
    intro x hx
    have hxab : x ∈ Set.Icc a b := by
      rw [Set.uIcc_of_le hab] at hx
      exact hx
    have hxa : a ≤ x := hxab.1
    have hxb : x ≤ b := hxab.2
    have hxR : x ≤ R := le_trans hxb hbR
    have hx0 : 0 < x := lt_of_lt_of_le ha0 hxa
    have hBx : (∫ s in Set.Ioi x, s * gprof s) = ∫ s in Set.Ioc x R, s * gprof s := hBformula x hxR
    by_cases hxRlt : x < R
    · have hdx : deriv u x = (1 / 2) * (∫ s in Set.Ioi x, s * gprof s) := hder x hx0 hxRlt
      have hdx' : deriv u x = (1 / 2) * (∫ s in Set.Ioc x R, s * gprof s) := by
        rw [hdx, hBx]
      have htail := htail_split x hxa hxR
      have hival : (∫ t in a..x, f1 t) = ∫ s in Set.Ioc a x, f1 s :=
        intervalIntegral.integral_of_le hxa
      have hdx'' : deriv u x = (1 / 2) * (∫ s in Set.Ioc x R, f1 s) := by
        simpa [f1] using hdx'
      calc
        deriv u x = (1 / 2) * (∫ s in Set.Ioc x R, f1 s) := hdx''
        _ = (1 / 2) * ((∫ s in Set.Ioc a R, f1 s) - (∫ s in Set.Ioc a x, f1 s)) := by
              rw [htail]
              ring
        _ = (1 / 2) * (∫ s in Set.Ioc a R, f1 s) - (1 / 2) * (∫ s in Set.Ioc a x, f1 s) := by ring
        _ = C - (1 / 2) * (∫ t in a..x, f1 t) := by
              rw [hival]
    · -- x = R
      have hxeq : x = R := le_antisymm hxR (le_of_not_gt hxRlt)
      have hdR : deriv u R = 0 := by
        simpa [u] using (canonicalProfile_hasDerivAt_R (v := v) (w := w) (R := R) hR hvrad hv_supp hrad hw).deriv
      have hPx : P R = 0 := by
        dsimp [P, C]
        have hivalR : (∫ t in a..R, f1 t) = ∫ s in Set.Ioc a R, f1 s :=
          intervalIntegral.integral_of_le (le_trans hab hbR)
        rw [hivalR]
        ring
      rw [hxeq]
      rw [hPx]
      exact hdR


  -- interval integrability of f1 on a..b
  have hf1II : IntervalIntegrable f1 volume a b := by
    constructor
    · simpa [f1] using (hf1_int_D a ha0).mono_set (s := Set.Ioc a b) (by
        intro s hs
        exact ⟨hs.1, le_trans hs.2 hbR⟩)
    · have : Set.Ioc b a = ∅ := by
        ext s
        simp [hab]
      rw [this]
      exact integrableOn_empty
  -- absolute continuity from the primitive representation
  have hAC : AbsolutelyContinuousOnInterval (deriv u) a b := by
    have hPrim : AbsolutelyContinuousOnInterval (fun x : ℝ => ∫ t in a..x, f1 t) a b :=
      hf1II.absolutelyContinuousOnInterval_intervalIntegral left_mem_uIcc
    have hneg : AbsolutelyContinuousOnInterval (fun x : ℝ => (-(1 / 2 : ℝ)) * (∫ t in a..x, f1 t)) a b :=
      hPrim.const_mul (-(1 / 2 : ℝ))
    have hcst : AbsolutelyContinuousOnInterval (fun _ : ℝ => C) a b := by
      apply LipschitzOnWith.absolutelyContinuousOnInterval (K := 0)
      intro x hx y hy
      simp
    have hcomb : AbsolutelyContinuousOnInterval (fun x : ℝ => C + (-(1 / 2 : ℝ)) * (∫ t in a..x, f1 t)) a b :=
      hcst.add hneg
    have hPac : AbsolutelyContinuousOnInterval P a b := by
      convert hcomb using 1
      funext x
      dsimp [P]
      ring
    exact absolutelyContinuousOnInterval_of_eqOn hPac hEqP
  -- a.e. Carathéodory second derivative
  have hsrc : ∀ᵐ r : ℝ, 0 < r → r < R →
      (radialProfile v r / 2) * (canonicalProfile v w R r - r) =
        -((1 / 2) * (r * radialProfile (fun x : ℝ³ => v x * (1 - w x)) r)) := by
    exact canonicalProfile_ae_source_eq (v := v) (w := w) (R := R) hR hvrad hv_supp hrad hw
  have hae : ∀ᵐ x : ℝ, x ∈ Set.Ioo a b → HasDerivAt (deriv u)
      ((radialProfile v x / 2) * (u x - x)) x := by
    have hLDT := hf1II.ae_hasDerivAt_integral (f := f1)
    filter_upwards [hLDT, hsrc] with x hxL hxsrc
    intro hxIoo
    have hxIcc : x ∈ Set.uIcc a b := by
      exact Set.mem_uIcc.mpr (Or.inl ⟨le_of_lt hxIoo.1, le_of_lt hxIoo.2⟩)
    have hxR : x < R := lt_of_lt_of_le hxIoo.2 hbR
    have hxpos : 0 < x := lt_trans ha0 hxIoo.1
    have hDerF : HasDerivAt (fun x : ℝ => ∫ t in a..x, f1 t) (f1 x) x :=
      hxL hxIcc a left_mem_uIcc
    have hDerP : HasDerivAt P (-(1 / 2) * f1 x) x := by
      have hneg : HasDerivAt (fun x : ℝ => (-(1 / 2 : ℝ)) * (∫ t in a..x, f1 t))
          (-(1 / 2) * f1 x) x := hDerF.const_mul (-(1 / 2))
      have hCadd : HasDerivAt (fun x : ℝ => C + (-(1 / 2 : ℝ)) * (∫ t in a..x, f1 t))
          (-(1 / 2) * f1 x) x := by
        simpa using (hneg.const_add C)
      have hPdef : P = fun x : ℝ => C + (-(1 / 2 : ℝ)) * (∫ t in a..x, f1 t) := by
        funext x
        dsimp [P]
        ring
      rwa [hPdef]
    have hEqOn_ab : Set.EqOn (deriv u) P (Set.Ioo a b) := by
      intro y hy
      exact hEqP (Set.mem_uIcc.mpr (Or.inl ⟨le_of_lt hy.1, le_of_lt hy.2⟩))
    have hloc : (fun y : ℝ => deriv u y) =ᶠ[𝓝 x] P :=
      hEqOn_ab.eventuallyEq_of_mem (isOpen_Ioo.mem_nhds hxIoo)
    have hDerU : HasDerivAt (deriv u) (-(1 / 2) * f1 x) x := by
      exact HasDerivAt.congr_of_eventuallyEq (f := P) (f₁ := deriv u) hDerP hloc
    have hsrcx : (radialProfile v x / 2) * (u x - x) =
        -((1 / 2) * (x * radialProfile (fun x : ℝ³ => v x * (1 - w x)) x)) := by
      simpa [u] using (hxsrc hxpos hxR)
    have hval : (radialProfile v x / 2) * (u x - x) = -(1 / 2) * f1 x := by
      dsimp [f1, gprof, g] at hsrcx ⊢
      convert hsrcx using 1
      ring
    simpa [hval] using hDerU
  -- convert the open-interval a.e. statement to the uIcc statement (endpoints are null)
  have haeIcc : ∀ᵐ x : ℝ, x ∈ Set.uIcc a b → HasDerivAt (deriv u)
      ((radialProfile v x / 2) * (u x - x)) x := by
    let Q : ℝ → Prop := fun x => HasDerivAt (deriv u) ((radialProfile v x / 2) * (u x - x)) x
    have hbad_open : (volume : Measure ℝ) {x : ℝ | x ∈ Set.Ioo a b ∧ ¬Q x} = 0 := by
      simpa [Q, Set.mem_Ioo, and_assoc] using (MeasureTheory.ae_iff.mp hae)
    have hcover : {x : ℝ | x ∈ Set.uIcc a b ∧ ¬Q x} ⊆
        {x : ℝ | x ∈ Set.Ioo a b ∧ ¬Q x} ∪ {a, b} := by
      intro x hx
      have hxi : x ∈ Set.uIcc a b := hx.1
      have hxab : x ∈ Set.Icc a b := by
        rw [Set.uIcc_of_le hab] at hxi
        exact hxi
      by_cases hxab' : a < x ∧ x < b
      · exact Or.inl ⟨hxab', hx.2⟩
      · right
        by_cases hxa' : x = a
        · simp [hxa']
        · by_cases hxb' : x = b
          · simp [hxb']
          · have hxa2 : a < x := lt_of_le_of_ne hxab.1 (Ne.symm hxa')
            have hxb2 : x < b := lt_of_le_of_ne hxab.2 hxb'
            exact False.elim (hxab' ⟨hxa2, hxb2⟩)
    have habs0 : (volume : Measure ℝ) ({a, b} : Set ℝ) = 0 := by
      rw [show ({a, b} : Set ℝ) = {a} ∪ {b} by aesop]
      exact measure_union_null (by simp) (by simp)
    have hunion0 : (volume : Measure ℝ) ({x : ℝ | x ∈ Set.Ioo a b ∧ ¬Q x} ∪ {a, b}) = 0 := by
      apply le_antisymm
      · calc
          (volume : Measure ℝ) ({x : ℝ | x ∈ Set.Ioo a b ∧ ¬Q x} ∪ {a, b})
              ≤ (volume : Measure ℝ) {x : ℝ | x ∈ Set.Ioo a b ∧ ¬Q x} + volume ({a, b} : Set ℝ) := by
                exact measure_union_le _ _
          _ = 0 := by rw [hbad_open, habs0]; simp
      · exact bot_le
    have hbad : (volume : Measure ℝ) {x : ℝ | x ∈ Set.uIcc a b ∧ ¬Q x} = 0 :=
      measure_mono_null hcover hunion0
    have hbad' : (volume : Measure ℝ) {x : ℝ | ¬(x ∈ Set.uIcc a b → Q x)} = 0 := by
      have hEq : {x : ℝ | ¬(x ∈ Set.uIcc a b → Q x)} = {x : ℝ | x ∈ Set.uIcc a b ∧ ¬Q x} := by
        ext x
        constructor
        · intro h
          by_cases hx : x ∈ Set.uIcc a b
          · exact ⟨hx, fun hQ => h (fun _ => hQ)⟩
          · exact False.elim (h (fun hx' => False.elim (hx hx')))
        · rintro ⟨hx, hQ⟩ h'
          exact hQ (h' hx)
      rwa [hEq]
    exact (MeasureTheory.ae_iff.mpr hbad')
  constructor
  · simpa [u] using hAC
  · simpa [u] using haeIcc

/-- **Regularity package.**  See the module doc above. -/
theorem canonicalProfile_reg {v w : ℝ³ → ℝ} {R : ℝ} (hR : 0 < R)
    (hvrad : IsRadial v) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (hrad : IsRadial w) (hw : IsScatteringSolution w v) :
    (canonicalProfile v w R 0 = 0) ∧
    (ContinuousOn (canonicalProfile v w R) (Set.Icc (0 : ℝ) R)) ∧
    (∀ r : ℝ, 0 < r → r < R → DifferentiableAt ℝ (canonicalProfile v w R) r) ∧
    (∀ ⦃a b : ℝ⦄, 0 < a → a ≤ b → b ≤ R →
      AbsolutelyContinuousOnInterval (deriv (canonicalProfile v w R)) a b) ∧
    (∀ ⦃a b : ℝ⦄, 0 < a → a ≤ b → b ≤ R → ∀ᵐ x : ℝ, x ∈ Set.uIcc a b →
      HasDerivAt (deriv (canonicalProfile v w R))
        ((radialProfile v x / 2) * (canonicalProfile v w R x - x)) x) := by
  have h0 : canonicalProfile v w R 0 = 0 := canonicalProfile_zero v w R
  have hcont : ContinuousOn (canonicalProfile v w R) (Set.Icc (0 : ℝ) R) :=
    canonicalProfile_continuousOn_Icc (v := v) (w := w) (R := R) hR hvrad hv_supp hrad hw
  refine ⟨h0, hcont, ?_, ?_, ?_⟩
  · intro r hr0 hrR
    exact (canonicalProfile_hasDerivAt_Ioo (v := v) (w := w) (R := R) hR hvrad hv_supp hrad hw
      hr0 hrR).differentiableAt
  · intro a b ha0 hab hbR
    exact (canonicalProfile_reg_interval (v := v) (w := w) (R := R) hR hvrad hv_supp hrad hw
      ha0 hab hbR).1
  · intro a b ha0 hab hbR
    exact (canonicalProfile_reg_interval (v := v) (w := w) (R := R) hR hvrad hv_supp hrad hw
      ha0 hab hbR).2

end Submission.BoseGases
