/-
Copyright: work module for the Elgindi finite-time singularity project.

# Almost-everywhere bounds for a bounded angular slice

`Work.Elliptic.SliceBdd h` records the endpoint bounds for a smooth slice `h` vanishing at
`θ = 0, π/2` on the two half-intervals `(0, π/4)` and `(π/4, π/2)`.  The weighted
integration-by-parts identities `DivSinIdentityA/B` need these bounds *uniformly*, i.e. with a
single constant valid for almost every `θ ∈ Iθ = [0, π/2]`, together with the consequence of
`htU_interior_facts`

  `sin(2θ) · (h/sin 2θ)'' = h'' + 4 h - 4 cos(2θ) · (h/sin 2θ)'`

that the second derivative of the quotient is controlled by `1/sin(2θ)`.  This file packages
those facts in exactly the form used by the integrability of the weighted integrands.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.Interval.Basic
import Submission.Work.Elliptic.DivSinBddDefs
import Submission.Work.Elliptic.DivSinDefs
import Submission.Work.Elliptic.htU_interior_facts

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology Interval
open MeasureTheory Set Filter

namespace Work.Elliptic

set_option autoImplicit false

/-- The interior relation between the second derivatives of `h` and of its angular quotient
`u = SinQ h = h / sin(2θ)`:  `sin(2θ) u'' = h'' + 4h - 4 cos(2θ) u'` on `(0, π/2)`.
This is the rearrangement of the identity supplied by `htU_interior_facts`. -/
theorem SliceBdd_second_deriv_rel (h : ℝ → ℝ) (hh : Work.Elliptic.SmoothSlice h) :
    ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      Real.sin (2 * θ) * deriv (deriv (Work.Elliptic.SinQ h)) θ
        = deriv (deriv h) θ + 4 * h θ
          - 4 * Real.cos (2 * θ) * deriv (Work.Elliptic.SinQ h) θ := by
  have hf2 : ContDiffOn ℝ 2 h (Set.Icc 0 (Real.pi / 2)) :=
    (hh.mono (fun x hx => ⟨by linarith [hx.1], by linarith [hx.2, Real.pi_pos]⟩)).of_le le_top
  intro θ hθ
  exact (Work.Elliptic.htU_interior_facts h hf2).2.2.2.2.1 θ hθ

private lemma abs_add_sub_le (a b c : ℝ) : |a + b - c| ≤ |a| + |b| + |c| := by
  calc |a + b - c| = |(a + b) + (-c)| := by ring_nf
    _ ≤ |a + b| + |-c| := abs_add_le _ _
    _ = |a + b| + |c| := by rw [abs_neg]
    _ ≤ (|a| + |b|) + |c| := by linarith [abs_add_le a b]
    _ = |a| + |b| + |c| := by ring

/-- **Almost-everywhere bounds for a bounded slice.**  If `h` is smooth and `SliceBdd h` holds,
then there is a constant `C ≥ 0` such that for almost every `θ ∈ Iθ` the slice, its second
derivative, the quotient `u = SinQ h`, its derivative, and `sin(2θ) u''` are all bounded by `C`
in absolute value. -/
theorem SliceBdd_ae_bounds (h : ℝ → ℝ) (hh : Work.Elliptic.SmoothSlice h)
    (hb : Work.Elliptic.SliceBdd h) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      |h θ| ≤ C ∧ |deriv (deriv h) θ| ≤ C ∧ |Work.Elliptic.SinQ h θ| ≤ C
        ∧ |deriv (Work.Elliptic.SinQ h) θ| ≤ C
        ∧ |Real.sin (2 * θ) * deriv (deriv (Work.Elliptic.SinQ h)) θ| ≤ C := by
  obtain ⟨C, hC0, hA, _hB, hC1, hD, hE, hF, _hG, hH, hI, hJ⟩ := hb
  refine ⟨9 * C, by positivity, ?_⟩
  have hpi4 : Real.pi / 4 < 1 := by nlinarith [Real.pi_lt_four]
  -- move from `Iθ = Icc 0 (π/2)` to the open interval
  rw [Work.Spaces.Iθ, ← MeasureTheory.restrict_Ioo_eq_restrict_Icc]
  rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioo]
  rw [MeasureTheory.ae_iff]
  refine MeasureTheory.measure_mono_null ?_ (MeasureTheory.NullSingletonClass.measure_singleton (Real.pi / 4))
  intro θ hθ
  simp only [Set.mem_ofPred_eq, not_imp] at hθ
  obtain ⟨hθmem, hθnot⟩ := hθ
  by_contra hne
  apply hθnot
  have hrel := SliceBdd_second_deriv_rel h hh θ hθmem
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · -- `θ < π/4`: use the first half-interval bounds
    have hmem : θ ∈ Set.Ioo 0 (Real.pi / 4) := ⟨hθmem.1, hlt⟩
    have hθ1 : θ ≤ 1 := le_of_lt (lt_trans hlt hpi4)
    have hh_le : |h θ| ≤ C := by
      have hAθ := hA θ hmem
      have : C * θ ≤ C := by nlinarith [hC0, hθmem.1, hθ1]
      linarith [hAθ]
    have hd2 : |deriv (deriv h) θ| ≤ C := hC1 θ hmem
    have hu : |SinQ h θ| ≤ C := hD θ hmem
    have hu1 : |deriv (SinQ h) θ| ≤ C := hE θ hmem
    have hu2 : |Real.sin (2 * θ) * deriv (deriv (SinQ h)) θ| ≤ 9 * C := by
      rw [hrel]
      have step := abs_add_sub_le (deriv (deriv h) θ) (4 * h θ)
        (4 * Real.cos (2 * θ) * deriv (SinQ h) θ)
      have e1 : |4 * h θ| = 4 * |h θ| := by rw [abs_mul]; norm_num
      have e2 : |4 * Real.cos (2 * θ) * deriv (SinQ h) θ|
          = 4 * |Real.cos (2 * θ)| * |deriv (SinQ h) θ| := by rw [abs_mul, abs_mul]; ring
      have hcos : |Real.cos (2 * θ)| ≤ 1 := Real.abs_cos_le_one _
      have hmul : |Real.cos (2 * θ)| * |deriv (SinQ h) θ| ≤ 1 * C :=
        mul_le_mul hcos hu1 (abs_nonneg _) zero_le_one
      rw [e1, e2] at step
      nlinarith [step, hd2, hh_le, hmul, hC0]
    exact ⟨by linarith [hC0], by linarith [hd2, hC0], by linarith [hu, hC0],
      by linarith [hu1, hC0], hu2⟩
  · -- `θ > π/4`: use the second half-interval bounds
    have hmem : θ ∈ Set.Ioo (Real.pi / 4) (Real.pi / 2) := ⟨hgt, hθmem.2⟩
    have hθ2 : Real.pi / 2 - θ ≤ 1 := by linarith [hθmem.1, Real.pi_pos]
    have hh_le : |h θ| ≤ C := by
      have hFθ := hF θ hmem
      have : C * (Real.pi / 2 - θ) ≤ C := by nlinarith [hC0, hθmem.1, hθ2]
      linarith [hFθ]
    have hd2 : |deriv (deriv h) θ| ≤ C := hH θ hmem
    have hu : |SinQ h θ| ≤ C := hI θ hmem
    have hu1 : |deriv (SinQ h) θ| ≤ C := hJ θ hmem
    have hu2 : |Real.sin (2 * θ) * deriv (deriv (SinQ h)) θ| ≤ 9 * C := by
      rw [hrel]
      have step := abs_add_sub_le (deriv (deriv h) θ) (4 * h θ)
        (4 * Real.cos (2 * θ) * deriv (SinQ h) θ)
      have e1 : |4 * h θ| = 4 * |h θ| := by rw [abs_mul]; norm_num
      have e2 : |4 * Real.cos (2 * θ) * deriv (SinQ h) θ|
          = 4 * |Real.cos (2 * θ)| * |deriv (SinQ h) θ| := by rw [abs_mul, abs_mul]; ring
      have hcos : |Real.cos (2 * θ)| ≤ 1 := Real.abs_cos_le_one _
      have hmul : |Real.cos (2 * θ)| * |deriv (SinQ h) θ| ≤ 1 * C :=
        mul_le_mul hcos hu1 (abs_nonneg _) zero_le_one
      rw [e1, e2] at step
      nlinarith [step, hd2, hh_le, hmul, hC0]
    exact ⟨by linarith [hC0], by linarith [hd2, hC0], by linarith [hu, hC0],
      by linarith [hu1, hC0], hu2⟩

end Work.Elliptic
