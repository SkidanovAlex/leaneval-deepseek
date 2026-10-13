/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/EpsEngine/MeasAlt/EpsLDefs.lean` — an `ℝ≥0∞`-valued refinement of `EpsSq`

Fallback development for `Work.FTS.EpsEngine.hmeasIter_of_epsClass` (see
`Submission/Work/FTS/EpsEngine/NOTES_hmeasIter_FIRST_CONJUNCT_FALSE.md`).

`EpsSq α f = ∫_{Iz}∫_{Iθ} (f·epsW)²` is a *real* iterated integral, so it takes the junk value `0`
whenever the corresponding `∫⁻` is infinite (`MeasureTheory.integral_undef`).  Monotonicity
arguments with it are therefore delicate.  We introduce the honest `ℝ≥0∞`-valued size

  `EpsL α f := ∫⁻_{Iz} ∫⁻_{Iθ} ofReal ((f z θ · epsW α z θ)²)`

(the *iterated* lintegral, so that **no** Tonelli/measurability hypothesis is needed for the basic
comparisons) and prove

* `ofReal_integral_le_lintegral_ofReal` — `ofReal (∫ f) ≤ ∫⁻ ofReal f` for `0 ≤ f` (the general
  "real integral ≤ lintegral" bridge, valid *without* any measurability hypothesis, by splitting on
  `Integrable`: an integrable function is a.e. strongly measurable, and a non-integrable one has
  Bochner integral `0` by junk value);
* `ofReal_EpsSq_le_EpsL` — `ofReal (EpsSq α f) ≤ EpsL α f`, unconditionally;
* `EpsSq_le_EpsL_toReal` — `EpsSq α f ≤ (EpsL α f).toReal` as soon as `EpsL α f ≠ ⊤`;
* `EpsL_eq_ofReal_EpsSq` — `EpsL α f = ofReal (EpsSq α f)` when `EpsMem α f` holds (there the real
  iterated integral is an honest Bochner integral and the `ofReal`/`lintegral` bridge is an
  equality).
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.StrongEps.EpsSpace

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.EpsEngine

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false

/-! ## The `ofReal` / `lintegral` bridge -/

/-- **The real integral is at most the `lintegral` of its `ofReal`** (nonnegative integrand).  No
measurability is needed: either the function is integrable — and then the `ofReal`/`lintegral`
bridge is an equality — or the Bochner integral is `0` by junk value. -/
theorem ofReal_integral_le_lintegral_ofReal {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : α → ℝ} (hf : ∀ x, 0 ≤ f x) :
    ENNReal.ofReal (∫ x, f x ∂μ) ≤ ∫⁻ x, ENNReal.ofReal (f x) ∂μ := by
  by_cases h : Integrable f μ
  · rw [MeasureTheory.ofReal_integral_eq_lintegral_ofReal h (Eventually.of_forall hf)]
  · rw [integral_undef h, ENNReal.ofReal_zero]
    exact bot_le

/-- The same for set integrals (a set integral is the integral against the restricted measure). -/
theorem ofReal_setIntegral_le_lintegral_ofReal {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {s : Set α} {f : α → ℝ} (hf : ∀ x, 0 ≤ f x) :
    ENNReal.ofReal (∫ x in s, f x ∂μ) ≤ ∫⁻ x in s, ENNReal.ofReal (f x) ∂μ :=
  ofReal_integral_le_lintegral_ofReal (μ := μ.restrict s) hf

/-- The equality version of the bridge, for an integrable nonnegative integrand on a set. -/
theorem ofReal_setIntegral_eq_lintegral_ofReal {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {s : Set α} {f : α → ℝ} (hf : IntegrableOn f s μ) (hnn : ∀ x, 0 ≤ f x) :
    ENNReal.ofReal (∫ x in s, f x ∂μ) = ∫⁻ x in s, ENNReal.ofReal (f x) ∂μ :=
  MeasureTheory.ofReal_integral_eq_lintegral_ofReal (μ := μ.restrict s) hf
    (Eventually.of_forall hnn)

/-! ## The `ℝ≥0∞`-valued size `EpsL` -/

/-- **The `ℝ≥0∞`-valued weighted size of a profile**: the iterated lintegral of
`ofReal ((f·epsW)²)` over the quadrant `Iz × Iθ`. -/
def EpsL (α : ℝ) (f : Fn) : ℝ≥0∞ :=
  ∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
    ENNReal.ofReal ((f z θ * Work.FTS.StrongEps.epsW α z θ) ^ 2)

/-- **`ofReal (EpsSq α f) ≤ EpsL α f`, unconditionally.**  Both comparisons are the bridge
`ofReal_integral_le_lintegral_ofReal`. -/
theorem ofReal_EpsSq_le_EpsL (α : ℝ) (f : Fn) :
    ENNReal.ofReal (Work.FTS.StrongEps.EpsSq α f) ≤ EpsL α f := by
  have hinner : ∀ z : ℝ, ENNReal.ofReal (∫ θ in Work.Spaces.Iθ,
      (f z θ * Work.FTS.StrongEps.epsW α z θ) ^ 2)
      ≤ ∫⁻ θ in Work.Spaces.Iθ,
        ENNReal.ofReal ((f z θ * Work.FTS.StrongEps.epsW α z θ) ^ 2) := fun z =>
    ofReal_setIntegral_le_lintegral_ofReal (fun θ => sq_nonneg _)
  show ENNReal.ofReal (∫ z in Work.Spaces.Iz,
      ∫ θ in Work.Spaces.Iθ, (f z θ * Work.FTS.StrongEps.epsW α z θ) ^ 2) ≤ _
  exact (ofReal_setIntegral_le_lintegral_ofReal (fun z =>
      integral_nonneg (fun θ => sq_nonneg _))).trans
    (lintegral_mono hinner)

/-- **`EpsSq α f ≤ (EpsL α f).toReal`** whenever `EpsL α f` is finite. -/
theorem EpsSq_le_EpsL_toReal {α : ℝ} {f : Fn} (h : EpsL α f ≠ ⊤) :
    Work.FTS.StrongEps.EpsSq α f ≤ (EpsL α f).toReal :=
  (ENNReal.ofReal_le_iff_le_toReal h).mp (ofReal_EpsSq_le_EpsL α f)

/-- **The identification `EpsL α f = ofReal (EpsSq α f)` under `EpsMem`.** -/
theorem EpsL_eq_ofReal_EpsSq {α : ℝ} {f : Fn} (h : Work.FTS.StrongEps.EpsMem α f) :
    EpsL α f = ENNReal.ofReal (Work.FTS.StrongEps.EpsSq α f) := by
  set H : ℝ × ℝ → ℝ := fun q => (f q.1 q.2 * Work.FTS.StrongEps.epsW α q.1 q.2) ^ 2 with hH
  have hnn : ∀ q, 0 ≤ H q := fun q => sq_nonneg _
  have hset : IntegrableOn H (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)
      (volume : Measure (ℝ × ℝ)) := h
  have hae : AEMeasurable (fun q => ENNReal.ofReal (H q))
      ((volume : Measure (ℝ × ℝ)).restrict (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)) :=
    ENNReal.measurable_ofReal.comp_aemeasurable hset.aestronglyMeasurable.aemeasurable
  have h1 : (∫⁻ q in Work.Spaces.Iz ×ˢ Work.Spaces.Iθ, ENNReal.ofReal (H q))
      = ENNReal.ofReal (∫ q in Work.Spaces.Iz ×ˢ Work.Spaces.Iθ, H q) :=
    (ofReal_setIntegral_eq_lintegral_ofReal hset hnn).symm
  have h2 : (∫⁻ q in Work.Spaces.Iz ×ˢ Work.Spaces.Iθ, ENNReal.ofReal (H q))
      = ∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (H (z, θ)) :=
    setLIntegral_prod (fun q => ENNReal.ofReal (H q)) hae
  have h3 : (∫ q in Work.Spaces.Iz ×ˢ Work.Spaces.Iθ, H q)
      = Work.FTS.StrongEps.EpsSq α f := by
    rw [Work.FTS.StrongEps.EpsSq]
    exact setIntegral_prod H hset
  rw [show EpsL α f = ∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
      ENNReal.ofReal ((f z θ * Work.FTS.StrongEps.epsW α z θ) ^ 2) from rfl, ← h2, h1, h3]

end Work.FTS.EpsEngine
