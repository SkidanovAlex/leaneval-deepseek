import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.EllipticEst.StraightDefs
import Submission.Work.FTS.EllipticEst.sliceLimitLeftExists

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Honest.SelfAux

open MeasureTheory Set Filter
open scoped Topology

/-! ## Boundedness of `u'` on `(0, π/2)`

We prove the two auxiliary estimates on which `SliceDerivBound` rests:

* `abs_deriv_sub_pi_div_four_le` — Newton–Leibniz on `[θ, π/4]` for `θ ≤ π/4` and on
  `[π/4, θ]` for `π/4 ≤ θ`, i.e. `|u' θ - u' (π/4)| ≤ ∫_{(0,π/2)} |u''|`;
* `abs_deriv_le_integral` — the triangle inequality `|u' θ| ≤ |u' (π/4)| + |u' θ - u' (π/4)|`.

The template for the sub-integral estimate is
`Work.FTS.EllipticEst.sliceLim_abs_deriv_le_of_second_deriv_integrableOn`, which treats only
`θ ∈ (0, π/4)`; here the *symmetric* half `θ ∈ [π/4, π/2)` is handled as well, which is what
turns an upper bound near `0` into a bound on the whole open interval. -/

/-- **Newton–Leibniz across `π/4`.**  If `u'' = deriv (fun t => deriv u t)` is the derivative of
`u'` on `(0, π/2)` and `|u''|` is integrable there, then for every `θ ∈ (0, π/2)` the increment
of `u'` between `θ` and `π/4` is bounded by the total mass of `|u''|` on `(0, π/2)`.

The two sides of `π/4` are handled by Newton–Leibniz on `[θ, π/4]` (for `θ ≤ π/4`) respectively
on `[π/4, θ]` (for `π/4 ≤ θ`). -/
lemma abs_deriv_sub_pi_div_four_le {u : ℝ → ℝ}
    (hderiv : ∀ x ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      HasDerivAt (deriv u) (deriv (fun t : ℝ => deriv u t) x) x)
    (hg : MeasureTheory.IntegrableOn (fun θ : ℝ => |deriv (fun t : ℝ => deriv u t) θ|)
      (Set.Ioo (0 : ℝ) (Real.pi / 2)))
    {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    |deriv u θ - deriv u (Real.pi / 4)|
      ≤ ∫ s in Set.Ioo (0 : ℝ) (Real.pi / 2),
          |deriv (fun t : ℝ => deriv u t) s| := by
  have hc0 : (0 : ℝ) < Real.pi / 4 := by linarith [Real.pi_pos]
  have hclt : Real.pi / 4 < Real.pi / 2 := by linarith [Real.pi_pos]
  rcases le_total θ (Real.pi / 4) with hle | hle
  · -- `θ ≤ π/4`: Newton–Leibniz on `[θ, π/4]`
    have hsub : Set.Icc θ (Real.pi / 4) ⊆ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
      fun x hx => ⟨lt_of_lt_of_le hθ.1 hx.1, lt_of_le_of_lt hx.2 hclt⟩
    have hIcc : MeasureTheory.IntegrableOn
        (fun x : ℝ => |deriv (fun t : ℝ => deriv u t) x|) (Set.Icc θ (Real.pi / 4)) :=
      hg.mono_set hsub
    have hint : MeasureTheory.IntegrableOn (deriv (fun t : ℝ => deriv u t))
        (Set.Icc θ (Real.pi / 4)) :=
      MeasureTheory.Integrable.mono' hIcc
        (measurable_deriv (fun t : ℝ => deriv u t)).aestronglyMeasurable
        (Filter.Eventually.of_forall fun x => by rw [Real.norm_eq_abs])
    have hmain :=
      Work.FTS.EllipticEst.sliceLim_abs_sub_le_setIntegral (f := deriv u)
        (f' := fun t : ℝ => deriv (fun t' : ℝ => deriv u t') t)
        (a := θ) (b := Real.pi / 4) (c := Real.pi / 4) hle le_rfl
        (fun x hx => hderiv x (hsub hx)) hint
    have hmono : ∫ x in Set.Ioc θ (Real.pi / 4),
          |deriv (fun t : ℝ => deriv u t) x|
        ≤ ∫ s in Set.Ioo (0 : ℝ) (Real.pi / 2),
            |deriv (fun t : ℝ => deriv u t) s| :=
      MeasureTheory.setIntegral_mono_set hg
        (Filter.Eventually.of_forall fun x => abs_nonneg _)
        (Filter.Eventually.of_forall fun x hx =>
          ⟨lt_trans hθ.1 hx.1, lt_of_le_of_lt hx.2 hclt⟩)
    rw [abs_sub_comm]
    exact hmain.trans hmono
  · -- `π/4 ≤ θ`: Newton–Leibniz on `[π/4, θ]`
    have hsub : Set.Icc (Real.pi / 4) θ ⊆ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
      fun x hx => ⟨lt_of_lt_of_le hc0 hx.1, lt_of_le_of_lt hx.2 hθ.2⟩
    have hIcc : MeasureTheory.IntegrableOn
        (fun x : ℝ => |deriv (fun t : ℝ => deriv u t) x|) (Set.Icc (Real.pi / 4) θ) :=
      hg.mono_set hsub
    have hint : MeasureTheory.IntegrableOn (deriv (fun t : ℝ => deriv u t))
        (Set.Icc (Real.pi / 4) θ) :=
      MeasureTheory.Integrable.mono' hIcc
        (measurable_deriv (fun t : ℝ => deriv u t)).aestronglyMeasurable
        (Filter.Eventually.of_forall fun x => by rw [Real.norm_eq_abs])
    have hmain :=
      Work.FTS.EllipticEst.sliceLim_abs_sub_le_setIntegral (f := deriv u)
        (f' := fun t : ℝ => deriv (fun t' : ℝ => deriv u t') t)
        (a := Real.pi / 4) (b := θ) (c := θ) hle le_rfl
        (fun x hx => hderiv x (hsub hx)) hint
    have hmono : ∫ x in Set.Ioc (Real.pi / 4) θ,
          |deriv (fun t : ℝ => deriv u t) x|
        ≤ ∫ s in Set.Ioo (0 : ℝ) (Real.pi / 2),
            |deriv (fun t : ℝ => deriv u t) s| :=
      MeasureTheory.setIntegral_mono_set hg
        (Filter.Eventually.of_forall fun x => abs_nonneg _)
        (Filter.Eventually.of_forall fun x hx =>
          ⟨lt_trans hc0 hx.1, lt_of_le_of_lt hx.2 hθ.2⟩)
    exact hmain.trans hmono

/-- **`u'` is bounded on `(0, π/2)` by its value at `π/4` plus the mass of `|u''|`.** -/
lemma abs_deriv_le_of_second_deriv_integrableOn {u : ℝ → ℝ}
    (hderiv : ∀ x ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      HasDerivAt (deriv u) (deriv (fun t : ℝ => deriv u t) x) x)
    (hg : MeasureTheory.IntegrableOn (fun θ : ℝ => |deriv (fun t : ℝ => deriv u t) θ|)
      (Set.Ioo (0 : ℝ) (Real.pi / 2))) :
    ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      |deriv u θ| ≤ |deriv u (Real.pi / 4)|
        + ∫ s in Set.Ioo (0 : ℝ) (Real.pi / 2),
            |deriv (fun t : ℝ => deriv u t) s| := by
  intro θ hθ
  have hdiff := abs_deriv_sub_pi_div_four_le hderiv hg hθ
  have hsum : |deriv u θ| ≤ |deriv u (Real.pi / 4)|
      + |deriv u θ - deriv u (Real.pi / 4)| := by
    have hid : deriv u θ = deriv u (Real.pi / 4)
        + (deriv u θ - deriv u (Real.pi / 4)) := by ring
    rw [abs_le]
    constructor
    · linarith [neg_abs_le (deriv u (Real.pi / 4)),
        le_abs_self (deriv u (Real.pi / 4)),
        neg_abs_le (deriv u θ - deriv u (Real.pi / 4)),
        le_abs_self (deriv u θ - deriv u (Real.pi / 4)), hid]
    · linarith [neg_abs_le (deriv u (Real.pi / 4)),
        le_abs_self (deriv u (Real.pi / 4)),
        neg_abs_le (deriv u θ - deriv u (Real.pi / 4)),
        le_abs_self (deriv u θ - deriv u (Real.pi / 4)), hid]
  linarith

/-- **Boundedness of `u'` on `(0,π/2)` from the integrability of `u''`.**  For `u : ℝ → ℝ` of
class `C²` on the open interval `(0, π/2)` whose second derivative
`u'' = deriv (fun θ' => deriv u θ')` is integrable there, `u' = deriv u` is bounded on `(0, π/2)`.

Proof route: for `θ ∈ (0, π/4]`, Newton–Leibniz on `[θ, π/4]` gives
`|u' θ| ≤ |u' (π/4)| + ∫_{Ioo 0 (π/2)} |u''|` (the template is
`Work.FTS.EllipticEst.sliceLim_abs_deriv_le_of_second_deriv_integrableOn`, already proved in
`Submission/Work/FTS/EllipticEst/sliceLimitLeftExists.lean`); for `θ ∈ [π/4, π/2)` use the mirror
image on `[π/4, θ]`; combine the two bounds with `max`.  `u'` is differentiable on the open
interval with derivative `u''` because `u` is `C²` there (`ContDiffAt.derivWithin`).

Please declare it at the ROOT namespace (no `namespace` wrapper), so that its name is exactly
`SliceDerivBound`. -/
theorem SliceDerivBound (u : ℝ → ℝ)
    (hsm : ContDiffOn ℝ 2 u (Set.Ioo 0 (Real.pi / 2)))
    (hint : MeasureTheory.IntegrableOn (fun θ => deriv (fun θ' => deriv u θ') θ)
      (Set.Ioo 0 (Real.pi / 2))) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), |deriv u θ| ≤ M := by
  -- `u'` is differentiable on the open interval with derivative `u''`
  have hderiv : ∀ x ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      HasDerivAt (deriv u) (deriv (fun t : ℝ => deriv u t) x) x := by
    intro x hx
    have h2 : ContDiffAt ℝ 2 u x := hsm.contDiffAt (isOpen_Ioo.mem_nhds hx)
    have hd1 : ContDiffAt ℝ 1 (deriv u) x := h2.derivWithin (by norm_num)
    exact (hd1.differentiableAt (by norm_num)).hasDerivAt
  -- integrability of `|u''|` from integrability of `u''`
  have habs : MeasureTheory.IntegrableOn
      (fun θ : ℝ => |deriv (fun t : ℝ => deriv u t) θ|) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    hint.abs
  refine ⟨max 0 (|deriv u (Real.pi / 4)|
      + ∫ s in Set.Ioo (0 : ℝ) (Real.pi / 2), |deriv (fun t : ℝ => deriv u t) s|),
    le_max_left _ _, fun θ hθ => ?_⟩
  exact (abs_deriv_le_of_second_deriv_integrableOn hderiv habs θ hθ).trans (le_max_right _ _)

end Work.FTS.EllipticEst.Honest.SelfAux
