/-
# `StrongEps/L12_Jeps_sub_le4_proof.lean` — the zero-mode mollifier error at level 4

For every admissible smooth kernel `ρ` there is a universal constant `C` with

  `|L₁₂(J_ε f)(0) - L₁₂(f)(0)| ≤ C ε ‖f‖_{ℋ⁴}`

for all `α ∈ (0,1]`, all `f` smooth on the open quadrant with honest `ℋ⁴`-membership, and all
`ε ∈ (0,1]`.

The proof does **not** go through an `ℋ⁴`-estimate for `J_ε f - f` (which is false: the mollifier
error loses one derivative, so only `‖J_ε f - f‖_{ℋ⁴} ≲ ε ‖f‖_{ℋ⁵}` holds).  Instead it uses that
`L₁₂(·)(0)` is *one linear functional* whose kernel, in the log coordinates
`(s,ζ) = (log z, log tan θ)`, is **independent of `s`**:

  `L₁₂(h)(0) = ∫_s ∫_ζ Glw ζ · h (e^s) (arctan (e^ζ))`,   `Glw ζ = κ(ζ) K(arctan (e^ζ))`

(`Work.FTS.StrongEps.L12Sub4.L12ZeroLog`).  The mollifier is the convolution with
`Jker ρ ε = ε⁻¹^2 ρ(ε⁻¹ ·)` in these coordinates, so the whole `s`-dependence of the kernel
integrates out and the error is a *difference of two weights in `ζ`*,

  `L₁₂(J_ε f)(0) - L₁₂(f)(0) = ∫_x (∫_p Jker ρ ε p (Glw (x.2+p.2) - Glw x.2)) f̃(x)`,

with `|∫_p Jker ρ ε p (Glw (ζ+p.2) - Glw ζ)| ≤ 8 e^8 ε Glw ζ`: on the support of the kernel
`|p.2| ≤ ε`, and `Glw` oscillates by at most `8 e^8 |q| Glw` on the unit interval.  The remaining
factor satisfies `∫_x Glw x.2 |f̃ x| ≤ 4 ‖f‖_{ℋ⁴}`
(`Work.FTS.StrongEps.L12Sub4.QuadAbsLintegral`, the weighted `L¹` Cauchy–Schwarz bound with an
`α`-independent constant).

The pieces used here (all proved in `Submission/Work/FTS/StrongEps/L12Sub4/`):

* `Defs` — `Glw`, `logF`, `Khat`, `L12_zero_eq_double`;
* `GlwFacts` — continuity, positivity and the oscillation bounds for `Glw`;
* `L12ZeroLog` — the log-coordinate form of `L₁₂(·)(0)`;
* `LogSubstLintegral` — the same substitution in `lintegral` form;
* `QuadAbsLintegral` — `∫⁻∫⁻ K(θ)|f|/z ≤ ofReal (4 ‖f‖_{ℋ⁴})`;
* `KernelWeightSub`, `ConvDiffBound` — the `ε`-error of the kernel against a `ζ`-weight;
* `ConvAdjDiff` — the (Fubini + translation invariance) adjointness identity.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.StrongEps.Basic
import Submission.Work.FTS.StrongEps.Kernel
import Submission.Work.FTS.StrongEps.L12Sub4.Defs
import Submission.Work.FTS.StrongEps.L12Sub4.GlwFacts
import Submission.Work.FTS.StrongEps.L12Sub4.L12ZeroLog
import Submission.Work.FTS.StrongEps.L12Sub4.LogSubstLintegral
import Submission.Work.FTS.StrongEps.L12Sub4.KernelWeightSub
import Submission.Work.FTS.StrongEps.L12Sub4.QuadAbsLintegral
import Submission.Work.FTS.StrongEps.L12Sub4.ConvAdjDiff
import Submission.Work.FTS.StrongEps.L12Sub4.ConvDiffBound
import Submission.Work.FTS.StrongEps.L12_Jeps_sub_le
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.Construction.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option maxHeartbeats 4000000

/-! ## Elementary helpers -/

/-- The log-coordinate pull-back `(s,ζ) ↦ h (e^s) (arctan (e^ζ))` of a profile which is smooth on
the open quadrant is continuous on the plane. -/
lemma continuous_logF_uncurry {h : Fn} (hh : Work.FTS.EllipticEst.SmoothOpen h) :
    Continuous (fun x : ℝ × ℝ => L12Sub4.logF h x.1 x.2) := by
  have h1 : ContinuousOn (Function.uncurry h) Work.FTS.EllipticEst.Q0 := hh.continuousOn
  have h2 : Continuous fun x : ℝ × ℝ => (Real.exp x.1, Real.arctan (Real.exp x.2)) :=
    Continuous.prodMk (Real.continuous_exp.comp continuous_fst)
      (Real.continuous_arctan.comp (Real.continuous_exp.comp continuous_snd))
  have h3 := h1.comp_continuous h2 (fun x => ⟨Real.exp_pos x.1,
    Real.arctan_pos.2 (Real.exp_pos x.2), Real.arctan_lt_pi_div_two _⟩)
  exact h3.congr fun x => rfl

/-- `L₁₂(·)(0)` in log coordinates, in the `logF` shape used below. -/
lemma L12_zero_eq_logF (h : ℝ → ℝ → ℝ) :
    Work.Construction.L12 h 0
      = ∫ s, ∫ ζ, L12Sub4.Glw ζ * L12Sub4.logF h s ζ :=
  L12Sub4.L12ZeroLog h

/-- **The mollifier in the log coordinates**: for *every* `(s,ζ) ∈ ℝ²`,
`J_ε f (e^s) (arctan (e^ζ)) = ∫ p, Jker ρ ε p · f̃(s-p₁, ζ-p₂)`. -/
lemma logF_Jeps (ρ : ℝ × ℝ → ℝ) (ε : ℝ) (f : Fn) (s ζ : ℝ) :
    L12Sub4.logF (Jeps ρ ε f) s ζ
      = ∫ p : ℝ × ℝ, Jker ρ ε p * L12Sub4.logF f (s - p.1) (ζ - p.2) := by
  have hz : 0 < Real.exp s := Real.exp_pos s
  have hθ : Real.arctan (Real.exp ζ) ∈ Set.Ioo 0 (π / 2) :=
    ⟨Real.arctan_pos.2 (Real.exp_pos ζ), Real.arctan_lt_pi_div_two _⟩
  rw [L12Sub4.logF, Jeps_eq_integral ρ ε f hz hθ]
  refine integral_congr_ae (Eventually.of_forall fun p => ?_)
  simp only [L12Sub4.logF, zShift, thShift, Real.tan_arctan, ← Real.exp_add, sub_eq_add_neg]

/-- **The weighted `L¹`-size of the log pull-back.**  For `α ∈ (0,1]` and `h` smooth on the open
quadrant with `HkMem α 4 h`, the function `x ↦ Glw x.2 · |h̃ x|` is integrable on the plane and its
integral is at most `4 ‖h‖_{ℋ⁴}` (with an `α`-independent constant). -/
lemma Glw_logF_integrable {α : ℝ} (hα : α ∈ Set.Ioc 0 1) {h : Fn}
    (hso : Work.FTS.EllipticEst.SmoothOpen h) (hm : Work.Spaces.HkMem α 4 h) :
    MeasureTheory.Integrable (fun x : ℝ × ℝ => L12Sub4.Glw x.2 * |L12Sub4.logF h x.1 x.2|)
      ∧ (∫ x : ℝ × ℝ, L12Sub4.Glw x.2 * |L12Sub4.logF h x.1 x.2|)
          ≤ 4 * Work.Spaces.HkNorm α 4 h := by
  have hGcont : Continuous L12Sub4.Glw := L12Sub4.GlwFacts.1
  have hGpos : ∀ ζ : ℝ, 0 < L12Sub4.Glw ζ := L12Sub4.GlwFacts.2.1
  have hlog : Continuous fun x : ℝ × ℝ => L12Sub4.logF h x.1 x.2 := continuous_logF_uncurry hso
  have hnn : ∀ x : ℝ × ℝ, 0 ≤ L12Sub4.Glw x.2 * |L12Sub4.logF h x.1 x.2| :=
    fun x => mul_nonneg (hGpos x.2).le (abs_nonneg _)
  have haesm : AEStronglyMeasurable
      (fun x : ℝ × ℝ => L12Sub4.Glw x.2 * |L12Sub4.logF h x.1 x.2|) volume :=
    ((hGcont.comp continuous_snd).mul hlog.abs).aestronglyMeasurable
  have hmeasE : AEMeasurable
      (fun x : ℝ × ℝ => ENNReal.ofReal (L12Sub4.Glw x.2 * |L12Sub4.logF h x.1 x.2|))
      (volume.prod volume) :=
    (ENNReal.continuous_ofReal.comp
      ((hGcont.comp continuous_snd).mul hlog.abs)).aemeasurable
  -- the `lintegral` identity (angular + radial substitution)
  have hlin : (∫⁻ s, ∫⁻ ζ, ENNReal.ofReal (L12Sub4.Glw ζ * |L12Sub4.logF h s ζ|))
      = ∫⁻ z in Set.Ioi 0, ∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal (Work.Spaces.K θ * |h z θ| / z) :=
    L12Sub4.LogSubstLintegral (fun z θ => |h z θ|) (fun z θ => abs_nonneg _)
  have hquad := L12Sub4.QuadAbsLintegral hα hso hm
  have hprod : (∫⁻ x : ℝ × ℝ, ENNReal.ofReal (L12Sub4.Glw x.2 * |L12Sub4.logF h x.1 x.2|))
      = ∫⁻ s, ∫⁻ ζ, ENNReal.ofReal (L12Sub4.Glw ζ * |L12Sub4.logF h s ζ|) :=
    MeasureTheory.lintegral_prod _ hmeasE
  have hfin : (∫⁻ x : ℝ × ℝ, ENNReal.ofReal (L12Sub4.Glw x.2 * |L12Sub4.logF h x.1 x.2|))
      ≠ ⊤ := by
    rw [hprod, hlin]
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hquad
  have hint : MeasureTheory.Integrable
      (fun x : ℝ × ℝ => L12Sub4.Glw x.2 * |L12Sub4.logF h x.1 x.2|) :=
    (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable haesm
      (Eventually.of_forall hnn)).mp hfin
  refine ⟨hint, ?_⟩
  have hof : ENNReal.ofReal (∫ x : ℝ × ℝ, L12Sub4.Glw x.2 * |L12Sub4.logF h x.1 x.2|)
      = ∫⁻ x : ℝ × ℝ, ENNReal.ofReal (L12Sub4.Glw x.2 * |L12Sub4.logF h x.1 x.2|) :=
    MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall hnn)
  have hmain : ENNReal.ofReal (∫ x : ℝ × ℝ, L12Sub4.Glw x.2 * |L12Sub4.logF h x.1 x.2|)
      ≤ ENNReal.ofReal (4 * Work.Spaces.HkNorm α 4 h) := by
    rw [hof, hprod, hlin]
    exact hquad
  exact (ENNReal.ofReal_le_ofReal_iff
    (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))).mp hmain

/-- **The pointwise-in-`ζ` kernel error.**  For an admissible mollifier kernel and `ε ∈ (0,1]`,
`|∫ p, Jker ρ ε p · (Glw (ζ+p.2) - Glw ζ)| ≤ 8 e^8 ε Glw ζ` for every `ζ`. -/
lemma Khat_abs_sub_le {ρ : ℝ × ℝ → ℝ} (hρ : IsMollKernel ρ) {ε : ℝ} (hε0 : 0 < ε)
    (hε1 : ε ≤ 1) : ∀ ζ : ℝ,
    |∫ p : ℝ × ℝ, Jker ρ ε p * (L12Sub4.Glw (ζ + p.2) - L12Sub4.Glw ζ)|
      ≤ 8 * Real.exp 8 * ε * L12Sub4.Glw ζ := by
  have hGcont : Continuous L12Sub4.Glw := L12Sub4.GlwFacts.1
  have hGpos : ∀ ζ : ℝ, 0 < L12Sub4.Glw ζ := L12Sub4.GlwFacts.2.1
  have hGr : ∀ ζ q : ℝ, L12Sub4.Glw (ζ + q) ≤ Real.exp (8 * |q|) * L12Sub4.Glw ζ :=
    L12Sub4.GlwFacts.2.2.1
  have hGd : ∀ ζ q : ℝ, |q| ≤ 1 → |L12Sub4.Glw (ζ + q) - L12Sub4.Glw ζ|
      ≤ 8 * Real.exp 8 * |q| * L12Sub4.Glw ζ := L12Sub4.GlwFacts.2.2.2
  have hknn : ∀ p : ℝ × ℝ, 0 ≤ Jker ρ ε p := HkSqAux.Jker_nonneg ρ hρ ε
  have hki : Integrable (Jker ρ ε) := Jker_integrable hρ hε0
  have hktot : ∫ p : ℝ × ℝ, Jker ρ ε p = 1 := Jker_integral_eq_one ρ hρ hε0
  have hJc : Continuous (Jker ρ ε) := Jker_continuous hρ ε
  have hksuppε : ∀ p : ℝ × ℝ, Jker ρ ε p ≠ 0 → |p.2| ≤ ε := by
    intro p hp
    have h := Jker_ne_zero_support (ε := ε) hρ hε0 hp
    have h1 : p.2 ^ 2 ≤ ε ^ 2 := by nlinarith [sq_nonneg p.1, h]
    have h2 : |p.2| ≤ |ε| := sq_le_sq.mp h1
    rwa [abs_of_pos hε0] at h2
  have hksupp1 : ∀ p : ℝ × ℝ, Jker ρ ε p ≠ 0 → |p.2| ≤ 1 := fun p hp =>
    le_trans (hksuppε p hp) hε1
  have hKW := L12Sub4.KernelWeightSub (Jker ρ ε) L12Sub4.Glw (ε := ε) (B := 8 * Real.exp 8)
    hknn hki hktot hksuppε hGcont (by positivity) hGd hε0 hε1
  intro ζ
  -- integrability against the shifted weight, using `Glw (ζ+p.2) ≤ e^8 Glw ζ`
  have hA : Integrable (fun p : ℝ × ℝ => Jker ρ ε p * L12Sub4.Glw (ζ + p.2)) := by
    refine MeasureTheory.Integrable.mono' (hki.const_mul (Real.exp 8 * L12Sub4.Glw ζ)) ?_ ?_
    · have : AEStronglyMeasurable
          (fun p : ℝ × ℝ => Jker ρ ε p * L12Sub4.Glw (ζ + p.2)) volume :=
        ((hJc.aemeasurable.mul (hGcont.comp (continuous_const.add continuous_snd)).aemeasurable)).aestronglyMeasurable
      exact this
    · filter_upwards with p
      by_cases hp : Jker ρ ε p = 0
      · simp [hp]
      · have hp2 : |p.2| ≤ 1 := hksupp1 p hp
        have hle : L12Sub4.Glw (ζ + p.2) ≤ Real.exp 8 * L12Sub4.Glw ζ := by
          refine (hGr ζ p.2).trans (mul_le_mul_of_nonneg_right ?_ (hGpos ζ).le)
          exact Real.exp_le_exp.mpr (by linarith [abs_nonneg p.2])
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hknn p), abs_of_pos (hGpos _)]
        calc Jker ρ ε p * L12Sub4.Glw (ζ + p.2)
            ≤ Jker ρ ε p * (Real.exp 8 * L12Sub4.Glw ζ) :=
              mul_le_mul_of_nonneg_left hle (hknn p)
          _ = (Real.exp 8 * L12Sub4.Glw ζ) * Jker ρ ε p := by ring
  have hrew : (∫ p : ℝ × ℝ, Jker ρ ε p * (L12Sub4.Glw (ζ + p.2) - L12Sub4.Glw ζ))
      = (∫ p : ℝ × ℝ, Jker ρ ε p * L12Sub4.Glw (ζ + p.2)) - L12Sub4.Glw ζ := by
    have h1 : (fun p : ℝ × ℝ => Jker ρ ε p * (L12Sub4.Glw (ζ + p.2) - L12Sub4.Glw ζ))
        = fun p : ℝ × ℝ =>
            Jker ρ ε p * L12Sub4.Glw (ζ + p.2) - Jker ρ ε p * L12Sub4.Glw ζ :=
      funext fun p => by ring
    rw [h1, MeasureTheory.integral_sub hA (hki.mul_const _), MeasureTheory.integral_mul_const,
      hktot, one_mul]
  rw [hrew]
  exact hKW ζ

/-- **The zero-mode mollifier error at level `4`.**  For every admissible *smooth* kernel `ρ` there
is a universal constant `C` such that `|L₁₂(J_ε f)(0) - L₁₂(f)(0)| ≤ C ε ‖f‖_{ℋ⁴}` for every
`α ∈ (0,1]`, every `f` smooth on the open quadrant with `HkMem α 4 f`, and every `ε ∈ (0,1]`. -/
theorem L12_Jeps_sub_le4_proof (ρ : ℝ × ℝ → ℝ) (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ), α ∈ Set.Ioc 0 1 → ∀ (f : Work.FTS.Galerkin.Fn),
      Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 4 f →
      ∀ ε : ℝ, ε ∈ Set.Ioc 0 1 →
        |Work.Construction.L12 (Work.FTS.StrongEps.Jeps ρ ε f) 0 - Work.Construction.L12 f 0|
          ≤ C * ε * Work.Spaces.HkNorm α 4 f := by
  refine ⟨32 * Real.exp 8, by positivity, ?_⟩
  intro α hα f hf hmem ε hε
  have hε0 : 0 < ε := hε.1
  have hε1 : ε ≤ 1 := hε.2
  have hGcont : Continuous L12Sub4.Glw := L12Sub4.GlwFacts.1
  have hGpos : ∀ ζ : ℝ, 0 < L12Sub4.Glw ζ := L12Sub4.GlwFacts.2.1
  have hGnn : ∀ ζ : ℝ, 0 ≤ L12Sub4.Glw ζ := fun ζ => (hGpos ζ).le
  have hGr : ∀ ζ q : ℝ, L12Sub4.Glw (ζ + q) ≤ Real.exp (8 * |q|) * L12Sub4.Glw ζ :=
    L12Sub4.GlwFacts.2.2.1
  have hGsuble : ∀ ζ q : ℝ, |q| ≤ 1 → |L12Sub4.Glw (ζ + q) - L12Sub4.Glw ζ|
      ≤ 8 * Real.exp 8 * |q| * L12Sub4.Glw ζ := L12Sub4.GlwFacts.2.2.2
  -- smoothness certificates
  have hfQ0 : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f) Work.FTS.EllipticEst.Q0 :=
    (Work.FTS.EllipticEst.smoothOpen_iff_forall f).mp hf
  have hfQuad : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f) Quad := by
    intro n
    simpa only [Quad, Work.FTS.EllipticEst.Q0] using hfQ0 n
  have hJso : Work.FTS.EllipticEst.SmoothOpen (Jeps ρ ε f) :=
    smoothOpen_Jeps ρ hρ hε0 hfQuad
  have hmemJ : Work.Spaces.HkMem α 4 (Jeps ρ ε f) :=
    HkMem_Jeps hρ.moll hα hε0 hfQuad hmem
  -- the kernel data
  have hknn : ∀ p : ℝ × ℝ, 0 ≤ Jker ρ ε p := HkSqAux.Jker_nonneg ρ hρ.moll ε
  have hki : Integrable (Jker ρ ε) := Jker_integrable hρ.moll hε0
  have hk1 : ∫ p : ℝ × ℝ, Jker ρ ε p = 1 := Jker_integral_eq_one ρ hρ.moll hε0
  have hksuppε : ∀ p : ℝ × ℝ, Jker ρ ε p ≠ 0 → |p.2| ≤ ε := by
    intro p hp
    have h := Jker_ne_zero_support (ε := ε) hρ.moll hε0 hp
    have h1 : p.2 ^ 2 ≤ ε ^ 2 := by nlinarith [sq_nonneg p.1, h]
    have h2 : |p.2| ≤ |ε| := sq_le_sq.mp h1
    rwa [abs_of_pos hε0] at h2
  have hksupp1 : ∀ p : ℝ × ℝ, Jker ρ ε p ≠ 0 → |p.2| ≤ 1 := fun p hp =>
    le_trans (hksuppε p hp) hε1
  -- the weighted `L¹` bounds for `f` and `J_ε f`
  obtain ⟨hFabs, hFbd⟩ := Glw_logF_integrable (h := f) hα hf hmem
  obtain ⟨hJFabs, _⟩ := Glw_logF_integrable (h := Jeps ρ ε f) hα hJso hmemJ
  have hFcont : Continuous fun x : ℝ × ℝ => L12Sub4.logF f x.1 x.2 := continuous_logF_uncurry hf
  have hJFcont : Continuous fun x : ℝ × ℝ => L12Sub4.logF (Jeps ρ ε f) x.1 x.2 :=
    continuous_logF_uncurry hJso
  have hFsgn : MeasureTheory.Integrable
      (fun x : ℝ × ℝ => L12Sub4.Glw x.2 * L12Sub4.logF f x.1 x.2) := by
    refine MeasureTheory.Integrable.mono' hFabs
      ((hGcont.comp continuous_snd).mul hFcont).aestronglyMeasurable ?_
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hGnn x.2)]
  have hJFsgn : MeasureTheory.Integrable
      (fun x : ℝ × ℝ => L12Sub4.Glw x.2 * L12Sub4.logF (Jeps ρ ε f) x.1 x.2) := by
    refine MeasureTheory.Integrable.mono' hJFabs
      ((hGcont.comp continuous_snd).mul hJFcont).aestronglyMeasurable ?_
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hGnn x.2)]
  -- (1) the identity, in iterated form, by adjointness of the mollifier
  have hdiff_iter : Work.Construction.L12 (Jeps ρ ε f) 0 - Work.Construction.L12 f 0
      = ∫ s, ∫ ζ, (∫ p : ℝ × ℝ, Jker ρ ε p * (L12Sub4.Glw (ζ + p.2) - L12Sub4.Glw ζ))
          * L12Sub4.logF f s ζ := by
    rw [L12_zero_eq_logF (Jeps ρ ε f), L12_zero_eq_logF f]
    rw [← MeasureTheory.integral_integral_sub
      (f := fun z : ℝ × ℝ => L12Sub4.Glw z.2 * L12Sub4.logF (Jeps ρ ε f) z.1 z.2)
      (g := fun z : ℝ × ℝ => L12Sub4.Glw z.2 * L12Sub4.logF f z.1 z.2) hJFsgn hFsgn]
    have hcong : (∫ x : ℝ, ∫ y : ℝ, (L12Sub4.Glw y * L12Sub4.logF (Jeps ρ ε f) x y
          - L12Sub4.Glw y * L12Sub4.logF f x y))
        = ∫ x : ℝ, ∫ y : ℝ, L12Sub4.Glw y *
            ((∫ p : ℝ × ℝ, Jker ρ ε p * L12Sub4.logF f (x - p.1) (y - p.2))
              - L12Sub4.logF f x y) := by
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      refine integral_congr_ae (Eventually.of_forall fun y => ?_)
      dsimp only
      rw [logF_Jeps ρ ε f]
      ring
    exact hcong.trans (L12Sub4.ConvAdjDiff (Jker ρ ε) L12Sub4.Glw (L12Sub4.logF f) hknn hki hk1
      hksupp1 hGcont hGnn (fun ζ q _ => hGr ζ q) hFcont.aestronglyMeasurable hFabs)
  -- (2) the same value as a plane integral
  have hconv_sm : StronglyMeasurable fun ζ : ℝ =>
      ∫ p : ℝ × ℝ, Jker ρ ε p * (L12Sub4.Glw (ζ + p.2) - L12Sub4.Glw ζ) := by
    have hf' : StronglyMeasurable (fun q : (ℝ × ℝ) × ℝ =>
        Jker ρ ε q.1 * (L12Sub4.Glw (q.2 + q.1.2) - L12Sub4.Glw q.2)) :=
      (((Jker_continuous hρ.moll ε).comp continuous_fst).mul
        ((hGcont.comp (continuous_snd.add continuous_fst.snd)).sub
          (hGcont.comp continuous_snd))).stronglyMeasurable
    simpa only using MeasureTheory.StronglyMeasurable.integral_prod_left' (μ := volume) hf'
  have hconv_aesm : AEStronglyMeasurable (fun x : ℝ × ℝ =>
      (∫ p : ℝ × ℝ, Jker ρ ε p * (L12Sub4.Glw (x.2 + p.2) - L12Sub4.Glw x.2))) volume :=
    (hconv_sm.comp_measurable measurable_snd).aestronglyMeasurable
  have hconv_int : MeasureTheory.Integrable (fun x : ℝ × ℝ =>
      (∫ p : ℝ × ℝ, Jker ρ ε p * (L12Sub4.Glw (x.2 + p.2) - L12Sub4.Glw x.2))
        * L12Sub4.logF f x.1 x.2) := by
    refine MeasureTheory.Integrable.mono' (hFabs.const_mul (8 * Real.exp 8 * ε))
      (hconv_aesm.mul hFcont.aestronglyMeasurable) ?_
    filter_upwards with x
    have hpt := Khat_abs_sub_le hρ.moll hε0 hε1 x.2
    rw [Real.norm_eq_abs, abs_mul]
    calc |∫ p : ℝ × ℝ, Jker ρ ε p * (L12Sub4.Glw (x.2 + p.2) - L12Sub4.Glw x.2)|
            * |L12Sub4.logF f x.1 x.2|
        ≤ (8 * Real.exp 8 * ε * L12Sub4.Glw x.2) * |L12Sub4.logF f x.1 x.2| :=
          mul_le_mul_of_nonneg_right hpt (abs_nonneg _)
      _ = 8 * Real.exp 8 * ε * (L12Sub4.Glw x.2 * |L12Sub4.logF f x.1 x.2|) := by ring
  have hdiff_prod : Work.Construction.L12 (Jeps ρ ε f) 0 - Work.Construction.L12 f 0
      = ∫ x : ℝ × ℝ, (∫ p : ℝ × ℝ, Jker ρ ε p * (L12Sub4.Glw (x.2 + p.2) - L12Sub4.Glw x.2))
          * L12Sub4.logF f x.1 x.2 := by
    rw [hdiff_iter]
    exact (MeasureTheory.integral_prod (fun x : ℝ × ℝ =>
      (∫ p : ℝ × ℝ, Jker ρ ε p * (L12Sub4.Glw (x.2 + p.2) - L12Sub4.Glw x.2))
        * L12Sub4.logF f x.1 x.2) hconv_int).symm
  -- (3) the `ε`-bound
  have hbound := L12Sub4.ConvDiffBound (Jker ρ ε) L12Sub4.Glw (L12Sub4.logF f) (ε := ε)
    (B := 8 * Real.exp 8) hknn hki hk1 hksuppε hGcont (by positivity)
    hGsuble hε0 hε1 hFabs
  calc |Work.Construction.L12 (Jeps ρ ε f) 0 - Work.Construction.L12 f 0|
      = |∫ x : ℝ × ℝ, (∫ p : ℝ × ℝ, Jker ρ ε p * (L12Sub4.Glw (x.2 + p.2) - L12Sub4.Glw x.2))
          * L12Sub4.logF f x.1 x.2| := by rw [hdiff_prod]
    _ ≤ 8 * Real.exp 8 * ε * (∫ x : ℝ × ℝ, L12Sub4.Glw x.2 * |L12Sub4.logF f x.1 x.2|) := hbound
    _ ≤ 8 * Real.exp 8 * ε * (4 * Work.Spaces.HkNorm α 4 f) := by
        refine mul_le_mul_of_nonneg_left hFbd ?_
        positivity
    _ = 32 * Real.exp 8 * ε * Work.Spaces.HkNorm α 4 f := by ring

end Work.FTS.StrongEps
