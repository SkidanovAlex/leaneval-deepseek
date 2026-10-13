import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.PressureOn.Defs
import Submission.Work.FTS.PressureOn.continuous_timeDeriv_pressurePotential
import Submission.Work.FTS.PressureOn.Connect.Clamp
import Submission.Work.FTS.PressureOn.Connect.BoundaryTime.deriv_zero_of_eq_zero_on_Icc

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Continuity of the Newtonian time derivative of a compactly supported strip field

`Work.FTS.PressureOn.Connect.BoundaryTime.continuousOn_timeDeriv_strip`: if
`f : ℝ³ → ℝ → ℝ³` is jointly continuous on the closed strip `ℝ³ × [0,S]`, its two-sided time
derivative `∂ₜ f` is jointly continuous there, and the spatial support of `f` on the strip is
contained in a ball `B(0,R)`, then

  `(x,t) ↦ -∫ y, ⟪∇Nfund (x - y), ∂ₜ f y t⟫`

is continuous on the closed strip `ℝ³ × [0,S]`.

This is the boundary-time (`t ∈ {0, S}` included) form of
`Work.FTS.PressureOn.continuous_timeDeriv_pressurePotential`, which assumes global joint
continuity of `f` and `∂ₜ f` together with a support radius that is *locally uniform in time*.

## Route

There are three steps.

* **Support of `∂ₜ f` on the strip.**  For `‖y‖ > R` the slice `s ↦ f y s` vanishes on all of
  `[0,S]`; hence `deriv (f y) s = 0` for every `s ∈ [0,S]`, including the endpoints: at an
  endpoint the two-sided derivative, if it exists, equals the (vanishing) one-sided derivative,
  and if it does not exist `deriv` is `0` anyway.  This is
  `Work.FTS.PressureOn.Connect.BoundaryTime.deriv_zero_of_eq_zero_on_Icc`.

* **Clamping the time variable.**  `G := fun y s => ∂ₜ f y (clampt S s)` is *globally* jointly
  continuous: `s ↦ clampt S s` retracts `ℝ` onto `[0,S]` and the pair
  `(y,s) ↦ (y, clampt S s)` maps everything into the closed strip, so the hypothesis `hd`
  composes (`ContinuousOn.comp_continuous`).  Moreover `G y s = 0` unless `‖y‖ ≤ max R 0`,
  uniformly in `s`, since `clampt S s ∈ [0,S]` always.  So the global shift lemma
  `Work.FTS.PressureOn.continuous_shifted_integral_joint` applies to `G` and yields continuity
  of `p ↦ ∫ z, ⟪∇Nfund z, G (p.1 - z) p.2⟫` on all of `ℝ³ × ℝ`.

* **Restricting and shifting back.**  On the strip `clampt S s = s`, so the clamped field may be
  replaced by `∂ₜ f` itself (`ContinuousOn.congr`), and the substitution `z = x - y`
  (`Work.FTS.PressureOn.integral_shift_nablaNfund`) converts the convolution form of the kernel
  into the defining form.  Negating gives the statement.

The spatial continuity hypothesis `hf` is not needed: the only place where `f` enters is the
support hypothesis, which `∂ₜ f` inherits on the strip.
-/

open FiniteTimeSingularity Set MeasureTheory Filter
open scoped Topology

set_option autoImplicit false

namespace Work.FTS.PressureOn.Connect.BoundaryTime

/-- **Support of the time derivative on the closed strip.**  If on the strip `ℝ³ × [0,S]` the
field `f` vanishes outside the ball `B(0,R)`, then so does `∂ₜ f`.  (The point of the statement
is the closed strip: at the boundary times the two-sided derivative is controlled by the
one-sided one, see `deriv_zero_of_eq_zero_on_Icc`.) -/
theorem timeDeriv_eq_zero_of_support_Icc
    {f : Work.FTS.PressureOn.R3 → ℝ → Work.FTS.PressureOn.R3} {S R : ℝ} (hS : 0 < S)
    (hsupp : ∀ s ∈ Set.Icc 0 S, ∀ y : Work.FTS.PressureOn.R3, f y s ≠ 0 → ‖y‖ ≤ R) :
    ∀ y : Work.FTS.PressureOn.R3, R < ‖y‖ → ∀ t ∈ Set.Icc 0 S,
      FiniteTimeSingularity.timeDeriv f y t = 0 := by
  intro y hy t ht
  have hfy : ∀ s ∈ Set.Icc 0 S, f y s = 0 := by
    intro s hs
    by_contra hne
    exact absurd (hsupp s hs y hne) (not_le.mpr hy)
  simpa only [FiniteTimeSingularity.timeDeriv] using
    deriv_zero_of_eq_zero_on_Icc hS hfy ht

set_option linter.unusedVariables false in
theorem continuousOn_timeDeriv_strip
    {f : Work.FTS.PressureOn.R3 → ℝ → Work.FTS.PressureOn.R3} {S : ℝ} (hS : 0 < S)
    (hf : ContinuousOn (fun p : Work.FTS.PressureOn.R3 × ℝ => f p.1 p.2)
      (Set.univ ×ˢ Set.Icc 0 S))
    (hd : ContinuousOn (fun p : Work.FTS.PressureOn.R3 × ℝ =>
      FiniteTimeSingularity.timeDeriv f p.1 p.2) (Set.univ ×ˢ Set.Icc 0 S))
    (hsupp : ∃ R : ℝ, ∀ s ∈ Set.Icc 0 S, ∀ y : Work.FTS.PressureOn.R3, f y s ≠ 0 → ‖y‖ ≤ R) :
    ContinuousOn (fun p : Work.FTS.PressureOn.R3 × ℝ =>
      -∫ y, inner ℝ (Work.FTS.PressureOn.nablaNfund (p.1 - y))
        (FiniteTimeSingularity.timeDeriv f y p.2)) (Set.univ ×ˢ Set.Icc 0 S) := by
  obtain ⟨R, hR⟩ := hsupp
  -- ## Step 1: the time derivative of `f` vanishes off `B(0,R)` on the strip
  have hzero : ∀ y : Work.FTS.PressureOn.R3, R < ‖y‖ → ∀ t ∈ Set.Icc 0 S,
      FiniteTimeSingularity.timeDeriv f y t = 0 :=
    timeDeriv_eq_zero_of_support_Icc hS hR
  set ρ : ℝ := max R 0 with hρ
  have hρR : R ≤ ρ := le_max_left R 0
  have hzero' : ∀ y : Work.FTS.PressureOn.R3, ρ < ‖y‖ → ∀ t ∈ Set.Icc 0 S,
      FiniteTimeSingularity.timeDeriv f y t = 0 :=
    fun y hy t ht => hzero y (lt_of_le_of_lt hρR hy) t ht
  -- ## Step 2: clamp the time variable, so that the field becomes globally continuous
  have hcontG : Continuous (fun p : Work.FTS.PressureOn.R3 × ℝ =>
      FiniteTimeSingularity.timeDeriv f p.1 (Work.FTS.PressureOn.Connect.clampt S p.2)) := by
    have hΦ : Continuous fun p : Work.FTS.PressureOn.R3 × ℝ =>
        ((p.1, Work.FTS.PressureOn.Connect.clampt S p.2) : Work.FTS.PressureOn.R3 × ℝ) :=
      continuous_fst.prodMk
        ((Work.FTS.PressureOn.Connect.lipschitzWith_clampt S).continuous.comp continuous_snd)
    have hmem : ∀ p : Work.FTS.PressureOn.R3 × ℝ,
        ((p.1, Work.FTS.PressureOn.Connect.clampt S p.2) : Work.FTS.PressureOn.R3 × ℝ) ∈
          Set.univ ×ˢ Set.Icc 0 S :=
      fun p => ⟨trivial, Work.FTS.PressureOn.Connect.clampt_mem_Icc hS.le p.2⟩
    exact hd.comp_continuous hΦ hmem
  -- the support of the clamped field is *globally* uniform in the time variable
  have hsuppG : ∀ t : ℝ, ∃ ρ' : ℝ, ∀ s ∈ Set.Ioo (t - 1) (t + 1), ∀ y : Work.FTS.PressureOn.R3,
      FiniteTimeSingularity.timeDeriv f y (Work.FTS.PressureOn.Connect.clampt S s) ≠ 0 →
        ‖y‖ ≤ ρ' := by
    refine fun _ => ⟨ρ, fun s _ y hy => ?_⟩
    by_contra hlt
    rw [not_le] at hlt
    exact hy (hzero' y hlt (Work.FTS.PressureOn.Connect.clampt S s)
      (Work.FTS.PressureOn.Connect.clampt_mem_Icc hS.le s))
  -- ## Step 3: global continuity of the shifted (convolution) form
  have hmain := Work.FTS.PressureOn.continuous_shifted_integral_joint
    (g := fun y s => FiniteTimeSingularity.timeDeriv f y (Work.FTS.PressureOn.Connect.clampt S s))
    hcontG hsuppG
  have hnon : ContinuousOn (fun p : Work.FTS.PressureOn.R3 × ℝ => ∫ z, inner ℝ
      (Work.FTS.PressureOn.nablaNfund z)
      (FiniteTimeSingularity.timeDeriv f (p.1 - z)
        (Work.FTS.PressureOn.Connect.clampt S p.2))) (Set.univ ×ˢ Set.Icc 0 S) :=
    hmain.continuousOn
  -- on the strip the clamp is the identity, so the clamped field may be replaced by `∂ₜ f`
  have hEqOn : Set.EqOn (fun p : Work.FTS.PressureOn.R3 × ℝ => ∫ z, inner ℝ
        (Work.FTS.PressureOn.nablaNfund z)
        (FiniteTimeSingularity.timeDeriv f (p.1 - z) p.2))
      (fun p : Work.FTS.PressureOn.R3 × ℝ => ∫ z, inner ℝ
        (Work.FTS.PressureOn.nablaNfund z)
        (FiniteTimeSingularity.timeDeriv f (p.1 - z)
          (Work.FTS.PressureOn.Connect.clampt S p.2))) (Set.univ ×ˢ Set.Icc 0 S) := by
    intro p hp
    simp only [Work.FTS.PressureOn.Connect.clampt_eq_self_of_mem hp.2]
  have hcont : ContinuousOn (fun p : Work.FTS.PressureOn.R3 × ℝ => ∫ z, inner ℝ
      (Work.FTS.PressureOn.nablaNfund z)
      (FiniteTimeSingularity.timeDeriv f (p.1 - z) p.2)) (Set.univ ×ˢ Set.Icc 0 S) :=
    hnon.congr hEqOn
  -- the substitution `z = x - y` turns the convolution form into the defining form
  refine (hcont.congr ?_).neg
  intro p _
  exact Work.FTS.PressureOn.integral_shift_nablaNfund
    (fun y => FiniteTimeSingularity.timeDeriv f y p.2) p.1

end Work.FTS.PressureOn.Connect.BoundaryTime
