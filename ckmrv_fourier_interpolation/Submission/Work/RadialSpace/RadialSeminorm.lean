import Mathlib
import Submission.Work.RadialSpace.Basic

/-!
# Radial derivatives and radial seminorms

For a function `f` on `R^n`, the **radial derivative** is the derivative of its
profile, transported back to `R^n`:

`radialDeriv f x = deriv (profile f) ‖x‖`.

For a radial function this is the genuine radial part of the derivative in the
direction of `x`.  The `l`-th radial derivative is `radialDerivPow l f`, and the
`k`-th radial seminorm is

`radialSeminorm k l f = ⨆ x, ‖x‖ ^ k * ‖(D^l f) x‖`,

valued in `ℝ≥0∞` so that no boundedness has to be assumed.  The main result of
the radial-seminorm theory is that for a *smooth radial* function the two
families of seminorms (the Schwartz seminorms and the radial seminorms) bound
each other, so that membership in the Schwartz space is equivalent to
finiteness of all radial seminorms.

## Main definitions

* `Work.RadialSpace.radialDeriv`
* `Work.RadialSpace.radialDerivPow`
* `Work.RadialSpace.radialSeminorm`
* `Work.RadialSpace.radialSeminormSum`
-/

open Filter Topology
open scoped SchwartzMap Topology ContDiff ENNReal

namespace Work.RadialSpace

variable {n : ℕ} [NeZero n]

/-- The radial derivative of a function on `R^n`: the derivative of its profile. -/
noncomputable def radialDeriv (f : EuclideanSpace ℝ (Fin n) → ℂ)
    (x : EuclideanSpace ℝ (Fin n)) : ℂ :=
  deriv (profile f) ‖x‖

/-- The `l`-th radial derivative of a function on `R^n`. -/
noncomputable def radialDerivPow (l : ℕ) (f : EuclideanSpace ℝ (Fin n) → ℂ) :
    EuclideanSpace ℝ (Fin n) → ℂ :=
  fun x => iteratedDeriv l (profile f) ‖x‖

@[simp] lemma radialDeriv_apply (f : EuclideanSpace ℝ (Fin n) → ℂ)
    (x : EuclideanSpace ℝ (Fin n)) : radialDeriv f x = deriv (profile f) ‖x‖ := rfl

@[simp] lemma radialDerivPow_apply (l : ℕ) (f : EuclideanSpace ℝ (Fin n) → ℂ)
    (x : EuclideanSpace ℝ (Fin n)) :
    radialDerivPow l f x = iteratedDeriv l (profile f) ‖x‖ := rfl

/-- The `k`-th radial seminorm `⨆ x, ‖x‖ ^ k * ‖D^l f x‖`, as an extended
nonnegative real. -/
noncomputable def radialSeminorm (k l : ℕ) (f : EuclideanSpace ℝ (Fin n) → ℂ) : ℝ≥0∞ :=
  ⨆ x : EuclideanSpace ℝ (Fin n), ENNReal.ofReal (‖x‖ ^ k * ‖iteratedDeriv l (profile f) ‖x‖‖)

/-- The explicit finite combination of radial seminorms that controls the
`(k, l)` Schwartz seminorm: all radial seminorms of weight at most `k + l` and
order at most `l`. -/
noncomputable def radialSeminormSum (k l : ℕ) (f : EuclideanSpace ℝ (Fin n) → ℂ) : ℝ≥0∞ :=
  ∑ j ∈ Finset.range (l + 1), ∑ m ∈ Finset.range (k + l + 1), radialSeminorm m j f

/-- Each pointwise radial derivative is bounded by the corresponding radial
seminorm. -/
lemma ofReal_le_radialSeminorm (k l : ℕ) (f : EuclideanSpace ℝ (Fin n) → ℂ)
    (x : EuclideanSpace ℝ (Fin n)) :
    ENNReal.ofReal (‖x‖ ^ k * ‖radialDerivPow l f x‖) ≤ radialSeminorm k l f :=
  le_iSup (fun y => ENNReal.ofReal (‖y‖ ^ k * ‖iteratedDeriv l (profile f) ‖y‖‖)) x

/-- A function with `‖x‖ ^ k * ‖D^l f x‖` bounded is `𝓢`-bounded in the `(k, l)`
seminorm. -/
lemma radialSeminorm_lt_top_of_bound {k l : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℂ} {C : ℝ}
    (hC : ∀ x, ‖x‖ ^ k * ‖radialDerivPow l f x‖ ≤ C) : radialSeminorm k l f < ⊤ := by
  have hle : radialSeminorm k l f ≤ ENNReal.ofReal (max C 0) :=
    iSup_le fun x => ENNReal.ofReal_le_ofReal (le_trans (hC x) (le_max_left C 0))
  exact lt_of_le_of_lt hle ENNReal.ofReal_lt_top

/-- The radial seminorm is monotone in the function: pointwise bounds give
seminorm bounds. -/
lemma radialSeminorm_le_of_le {k l : ℕ} {f g : EuclideanSpace ℝ (Fin n) → ℂ}
    (h : ∀ x, ‖x‖ ^ k * ‖radialDerivPow l f x‖ ≤ ‖x‖ ^ k * ‖radialDerivPow l g x‖) :
    radialSeminorm k l f ≤ radialSeminorm k l g :=
  iSup_le fun x => le_trans (ENNReal.ofReal_le_ofReal (h x))
    (ofReal_le_radialSeminorm k l g x)

omit [NeZero n] in
/-- On the unit ball the Schwartz seminorms of a smooth function are bounded (by
compactness), with no hypothesis of radiality. -/
theorem exists_bound_on_unit_ball (F : EuclideanSpace ℝ (Fin n) → ℂ)
    (hF : ContDiff ℝ Smooth F) (k l : ℕ) :
    ∃ C : ℝ, ∀ x : EuclideanSpace ℝ (Fin n), ‖x‖ ≤ 1 →
      ‖x‖ ^ k * ‖iteratedFDeriv ℝ l F x‖ ≤ C := by
  have hle : (l : ℕ∞ω) ≤ Smooth := by
    show ((l : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞)
    exact WithTop.coe_le_coe.mpr le_top
  have hF' : ContDiff ℝ (l : ℕ∞ω) F := hF.of_le hle
  have hcont : Continuous fun x : EuclideanSpace ℝ (Fin n) =>
      ‖x‖ ^ k * ‖iteratedFDeriv ℝ l F x‖ :=
    (continuous_norm.pow k).mul ((hF'.continuous_iteratedFDeriv (m := l) le_rfl).norm)
  obtain ⟨C, hC⟩ := isCompact_closedBall (0 : EuclideanSpace ℝ (Fin n)) 1 |>.exists_bound_of_continuousOn
    hcont.continuousOn
  refine ⟨C, fun x hx => ?_⟩
  have h := hC x (by simpa [Metric.mem_closedBall, dist_eq_norm] using hx)
  rwa [Real.norm_eq_abs, abs_of_nonneg (by positivity)] at h

end Work.RadialSpace
